/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Exchangeability.Core
import Exchangeability.Contractability
import Exchangeability.Probability.CondExp
import Exchangeability.Probability.CondIndep
import Exchangeability.Probability.TripleLawDropInfo
import Exchangeability.DeFinetti.MartingaleHelpers
import Exchangeability.DeFinetti.ViaMartingale.ShiftOperations
import Exchangeability.DeFinetti.ViaMartingale.LocalInfrastructure

/-!
# Pair-Law Equality from Contractability

This file proves the key pair-law equality: for a contractable sequence X,
the pair (U, W) has the same distribution as (U, W') where:
- U = first r coordinates
- W = future tail from m+1
- W' = X_r consed onto W

This is fundamental to the martingale approach proof of de Finetti's theorem.

## Main definitions

* `phi0`, `phi1` - Strictly increasing injections for contractability argument

## Main results

* `pair_law_eq_of_contractable` - The key pair-law equality (U, W) =^d (U, W')
* `condExp_indicator_eq_of_contractable` - CE drop-info via contraction
* `comap_consRV_eq_sup` - σ(consRV x t) = σ(x) ⊔ σ(t)
* `condExp_Xr_indicator_eq_of_contractable` - CE drop-info for X_r indicator

These are extracted from ViaMartingale.lean to enable modular imports.
-/

noncomputable section
open scoped MeasureTheory
open MeasureTheory Filter

namespace Exchangeability.DeFinetti.ViaMartingale

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
variable {μ : Measure Ω}

/-! ### Pair-Law Equality from Contractability

The key step: use two strictly increasing injections to show that
`(U, W) =^d (U, W')` where `W' = consRV (X r) W`.

**Setup for r ≤ m:**
- `U` := first r coordinates = `(X 0, ..., X (r-1))`
- `W` := future tail from m+1 = `shiftRV X (m+1)` = `(X (m+1), X (m+2), ...)`
- `W'` := cons of X_r onto W = `consRV (X r) W` = `(X r, X (m+1), X (m+2), ...)`

**Two increasing injections (both of length r + ∞):**
- `φ₀`: `0, 1, ..., r-1, m+1, m+2, ...` (skips indices r through m)
- `φ₁`: `0, 1, ..., r-1, r, m+1, m+2, ...` (skips indices r+1 through m)

By contractability, both give the same joint distribution. Projecting:
- `φ₀` gives `(U, W)`
- `φ₁` gives `(U, W')`

Hence `(U, W) =^d (U, W')`. Combined with `σ(W) ≤ σ(W')` from `comap_le_comap_consRV`,
Kallenberg 1.3 gives `U ⊥⊥ X_r | W`.
-/

/-- Injection φ₀ for contractability: indices 0,...,r-1, m+1, m+2, ...
    Skips indices r through m. -/
def phi0 (r m : ℕ) : ℕ → ℕ := fun n =>
  if n < r then n else n + (m - r + 1)

/-- Injection φ₁ for contractability: indices 0,...,r, m+1, m+2, ...
    Skips indices r+1 through m. -/
def phi1 (r m : ℕ) : ℕ → ℕ := fun n =>
  if n ≤ r then n else n + (m - r)

@[nolint unusedArguments]
lemma phi0_strictMono (r m : ℕ) (_hr : r ≤ m) : StrictMono (phi0 r m) := by
  intro i j hij
  simp only [phi0]
  by_cases hi : i < r
  · by_cases hj : j < r
    · simp [hi, hj, hij]
    · simp only [hi, if_true, hj, if_false]
      omega
  · simp only [hi, if_false]
    have hj : ¬j < r := fun h => hi (Nat.lt_of_lt_of_le hij (Nat.le_of_lt h))
    simp only [hj, if_false]
    omega

@[nolint unusedArguments]
lemma phi1_strictMono (r m : ℕ) (_hr : r ≤ m) : StrictMono (phi1 r m) := by
  intro i j hij
  simp only [phi1]
  by_cases hi : i ≤ r
  · by_cases hj : j ≤ r
    · simp [hi, hj, hij]
    · simp only [hi, if_true, hj, if_false]
      omega
  · simp only [hi, if_false]
    have hj : ¬j ≤ r := fun h => hi (Nat.le_trans (Nat.le_of_lt hij) h)
    simp only [hj, if_false]
    omega

omit [MeasurableSpace Ω] [MeasurableSpace α] in
/-- φ₀ and φ₁ agree on indices 0,...,r-1 (the first r coordinates). -/
lemma phi0_phi1_agree_on_first_r (r m i : ℕ) (hi : i < r) :
    phi0 r m i = phi1 r m i := by
  simp only [phi0, phi1, hi, Nat.le_of_lt hi, ↓reduceIte]

omit [MeasurableSpace Ω] [MeasurableSpace α] in
/-- φ₀ at index r gives m+1 (start of future tail). -/
lemma phi0_at_r (r m : ℕ) (hr : r ≤ m) : phi0 r m r = m + 1 := by
  simp [phi0]; omega

omit [MeasurableSpace Ω] [MeasurableSpace α] in
/-- φ₁ at index r gives r (the extra coordinate in W'). -/
lemma phi1_at_r (r m : ℕ) : phi1 r m r = r := by
  simp [phi1]

omit [MeasurableSpace Ω] [MeasurableSpace α] in
/-- φ₁ at index r+1+k gives m+1+k (same as φ₀ at index r+k). -/
lemma phi1_after_r (r m k : ℕ) (hr : r ≤ m) :
    phi1 r m (r + 1 + k) = m + 1 + k := by
  simp only [phi1]
  have h : ¬(r + 1 + k ≤ r) := by omega
  simp only [h, ↓reduceIte]
  omega

/-- **Key lemma:** Contractability gives pair-law equality `(U, W) =^d (U, W')`.

Given a contractable sequence X:
- `U` is the first r coordinates: `(X 0, ..., X (r-1))`
- `W` is the future tail from m+1: `shiftRV X (m+1)`
- `W'` is X_r consed onto W: `consRV (X r) (shiftRV X (m+1))`

Then `(U, W) =^d (U, W')` because both arise from strictly increasing
subsequences of the same length (via φ₀ and φ₁).

This is the pair-law hypothesis needed for Kallenberg 1.3.

**Proof strategy:**
1. Embed (Fin r → α) × (ℕ → α) into (ℕ → α) via concatenation
2. Show (U, W) and (U, W') map to reindexings of X via φ₀ and φ₁
3. By contractability, these reindexings have equal finite marginals
4. By π-system uniqueness, the embedded measures are equal
5. Pull back to show (U, W) =^d (U, W') -/
lemma pair_law_eq_of_contractable [IsProbabilityMeasure μ]
    {X : ℕ → Ω → α} (hContr : Contractable μ X) (hX : ∀ n, Measurable (X n))
    (r m : ℕ) (hr : r ≤ m) :
    let U := fun ω : Ω => (fun i : Fin r => X i ω)
    let W := shiftRV X (m+1)
    let W' := consRV (fun ω => X r ω) W
    Measure.map (fun ω => (U ω, W ω)) μ =
    Measure.map (fun ω => (U ω, W' ω)) μ := by
  intro U W W'

  -- Concatenation map: glue prefix (Fin r → α) and tail (ℕ → α) into (ℕ → α)
  let concat : (Fin r → α) × (ℕ → α) → (ℕ → α) := fun ⟨u, w⟩ n =>
    if h : n < r then u ⟨n, h⟩ else w (n - r)

  -- Split map: extract prefix and tail from (ℕ → α)
  let split : (ℕ → α) → (Fin r → α) × (ℕ → α) := fun f =>
    (fun i => f i.val, fun n => f (r + n))

  -- split ∘ concat = id
  have h_split_concat : ∀ p : (Fin r → α) × (ℕ → α), split (concat p) = p := fun ⟨u, w⟩ => by
    simp only [split, concat, Prod.mk.injEq]
    constructor
    · ext i
      have hi : (i : ℕ) < r := i.isLt
      simp only [hi, dite_true, Fin.eta]
    · ext n
      have h : ¬(r + n < r) := Nat.not_lt.mpr (Nat.le_add_right r n)
      simp only [h, dite_false, Nat.add_sub_cancel_left]

  -- Measurability of concat
  have h_concat_meas : Measurable concat := by
    rw [measurable_pi_iff]; intro n
    by_cases hn : n < r
    · simp only [concat, hn, dite_true]
      exact (measurable_pi_apply (⟨n, hn⟩ : Fin r)).comp measurable_fst
    · simp only [concat, hn, dite_false]
      exact (measurable_pi_apply (n - r : ℕ)).comp measurable_snd

  -- Measurability of split
  have h_split_meas : Measurable split := Measurable.prod
    (measurable_pi_iff.mpr fun i => measurable_pi_apply i.val)
    (measurable_pi_iff.mpr fun n => measurable_pi_apply (r + n))

  -- Define concatenated sequences
  let seq0 : Ω → ℕ → α := fun ω => concat (U ω, W ω)
  let seq1 : Ω → ℕ → α := fun ω => concat (U ω, W' ω)

  -- seq0 ω n = X (φ₀ n) ω
  have h_seq0 : ∀ ω n, seq0 ω n = X (phi0 r m n) ω := fun ω n => by
    simp only [seq0, concat, U, W, shiftRV, phi0]
    by_cases hn : n < r
    · simp only [hn, dite_true, ite_true]
    · simp only [hn, dite_false, ite_false]
      congr 1; omega

  -- seq1 ω n = X (φ₁ n) ω
  have h_seq1 : ∀ ω n, seq1 ω n = X (phi1 r m n) ω := fun ω n => by
    simp only [seq1, concat, U, W, W', consRV, shiftRV, phi1]
    by_cases hn : n < r
    · have hle : n ≤ r := Nat.le_of_lt hn
      simp only [hn, dite_true, hle, ite_true]
    · simp only [hn, dite_false]
      by_cases hn' : n = r
      · subst hn'; simp only [Nat.sub_self, le_refl, ite_true]
      · have hgt : r < n := Nat.lt_of_le_of_ne (Nat.not_lt.mp hn) (Ne.symm hn')
        simp only [Nat.not_le.mpr hgt, ite_false]
        -- Goal: (consRV (X r) (shiftRV X (m+1))) ω (n - r) = X (n + (m - r)) ω
        -- Since r < n, n - r = succ k for some k
        obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt hgt
        subst hk
        -- n = r + k + 1, so (r + k + 1) - r = k + 1
        -- match on (k+1) gives X (m + 1 + k) ω
        -- need: m + 1 + k = (r + k + 1) + (m - r)
        have h_idx_eq : (r + k + 1) - r = k + 1 := by omega
        have h_final : m + 1 + k = (r + k + 1) + (m - r) := by omega
        conv_lhs => simp only [consRV, shiftRV, h_idx_eq]
        conv_rhs => rw [← h_final]

  -- Measurability of seq0 and seq1
  have hU_meas : Measurable U := measurable_pi_iff.mpr fun i => hX i.val
  have hW_meas : Measurable W := measurable_pi_iff.mpr fun n => hX (m + 1 + n)
  have hW'_meas : Measurable W' := by
    simp only [W']
    rw [measurable_pi_iff]; intro n
    match n with
    | 0 => exact hX r
    | n' + 1 => exact hX (m + 1 + n')

  have hseq0_meas : Measurable seq0 := h_concat_meas.comp (hU_meas.prodMk hW_meas)
  have hseq1_meas : Measurable seq1 := h_concat_meas.comp (hU_meas.prodMk hW'_meas)

  -- Finite marginals agree by contractability
  have h_marginals : ∀ k (S : Set (Fin k → α)), MeasurableSet S →
      Measure.map (prefixProj (α := α) k) (Measure.map seq0 μ) S =
      Measure.map (prefixProj (α := α) k) (Measure.map seq1 μ) S := fun k S hS => by
    rw [Measure.map_map (measurable_prefixProj (α := α)) hseq0_meas,
        Measure.map_map (measurable_prefixProj (α := α)) hseq1_meas]
    -- prefixProj k ∘ seq0 = fun ω i => X (φ₀ i) ω
    have hcomp0 : prefixProj (α := α) k ∘ seq0 = fun ω (i : Fin k) => X (phi0 r m i) ω :=
      funext fun ω => funext fun i => h_seq0 ω i
    have hcomp1 : prefixProj (α := α) k ∘ seq1 = fun ω (i : Fin k) => X (phi1 r m i) ω :=
      funext fun ω => funext fun i => h_seq1 ω i
    rw [hcomp0, hcomp1]
    -- Both φ₀ and φ₁ are strictly increasing, so by contractability equal distribution
    exact congrArg (· S) (hContr.allStrictMono_eq k
      (fun i : Fin k => phi0 r m i.val) (fun i : Fin k => phi1 r m i.val)
      (fun i j hij => phi0_strictMono r m hr hij) (fun i j hij => phi1_strictMono r m hr hij))

  -- Measures on ℕ → α are equal by π-system uniqueness (need probability instances)
  haveI : IsProbabilityMeasure (Measure.map seq0 μ) := Measure.isProbabilityMeasure_map hseq0_meas.aemeasurable
  haveI : IsProbabilityMeasure (Measure.map seq1 μ) := Measure.isProbabilityMeasure_map hseq1_meas.aemeasurable
  have h_seq_eq : Measure.map seq0 μ = Measure.map seq1 μ :=
    Exchangeability.measure_eq_of_fin_marginals_eq_prob (α := α) h_marginals

  -- Pull back via split
  have h0 : Measure.map (fun ω => (U ω, W ω)) μ = Measure.map (split ∘ seq0) μ :=
    congrArg (Measure.map · μ) <| funext fun ω => (h_split_concat (U ω, W ω)).symm
  have h1 : Measure.map (fun ω => (U ω, W' ω)) μ = Measure.map (split ∘ seq1) μ :=
    congrArg (Measure.map · μ) <| funext fun ω => (h_split_concat (U ω, W' ω)).symm
  rw [h0, h1]
  -- Use Measure.map_map to factor through seq0/seq1
  rw [← Measure.map_map h_split_meas hseq0_meas, ← Measure.map_map h_split_meas hseq1_meas]
  rw [h_seq_eq]

/-- **Conditional expectation drop-info via true contraction (Kallenberg 1.3).**

This is the CORRECT version that uses the contraction structure σ(W) ⊆ σ(W')
rather than the broken triple-law approach.

Given contractability of X, for r < m:
- U = (X_0, ..., X_{r-1}) (first r coordinates)
- W = shiftRV X (m+1) (far future)
- W' = consRV (X r) W (X_r consed onto far future)

We have:
1. σ(W) ⊆ σ(W') via comap_le_comap_consRV
2. (U, W) =^d (U, W') via pair_law_eq_of_contractable

By Kallenberg Lemma 1.3 (condExp_indicator_eq_of_law_eq_of_comap_le):
  E[1_{U∈A} | σ(W')] = E[1_{U∈A} | σ(W)]

Since σ(W') = σ(X_r, W), this gives:
  E[1_{U∈A} | σ(X_r, W)] = E[1_{U∈A} | σ(W)]

which is exactly U ⊥⊥ X_r | W in indicator form.
-/
@[nolint unusedArguments]
lemma condExp_indicator_eq_of_contractable
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    [StandardBorelSpace α]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → α}
    (hContr : Contractable μ X)
    (hX_meas : ∀ n, Measurable (X n))
    {r m : ℕ} (hrm : r ≤ m)
    {A : Set (Fin r → α)} (hA : MeasurableSet A) :
    let U := fun ω : Ω => (fun i : Fin r => X i ω)
    let W := shiftRV X (m+1)
    let W' := consRV (fun ω => X r ω) W
    μ[Set.indicator (U ⁻¹' A) (fun _ => (1 : ℝ)) | MeasurableSpace.comap W' inferInstance]
      =ᵐ[μ]
    μ[Set.indicator (U ⁻¹' A) (fun _ => (1 : ℝ)) | MeasurableSpace.comap W inferInstance] := by
  -- Define the key random variables
  let U := fun ω : Ω => (fun i : Fin r => X i ω)
  let W := shiftRV X (m+1)
  let W' := consRV (fun ω => X r ω) W

  -- Measurability
  have hU : Measurable U := by measurability
  have hW : Measurable W := measurable_pi_lambda _ fun n => hX_meas (m + 1 + n)
  have hW' : Measurable W' := measurable_pi_lambda _ fun
    | 0 => hX_meas r
    | n + 1 => hX_meas (m + 1 + n)

  -- Apply Kallenberg 1.3 with pair law and contraction σ(W) ⊆ σ(W')
  exact condExp_indicator_eq_of_law_eq_of_comap_le U W W' hU hW hW'
    (pair_law_eq_of_contractable hContr hX_meas r m hrm)
    (comap_le_comap_consRV (fun ω => X r ω) W) hA

/-- **The σ-algebra of W' = consRV (X r) W equals the join of σ(X_r) and σ(W).**

This is key for translating the Kallenberg 1.3 result to conditional independence.

**Proof idea:**
- (≤): Any set in σ(consRV x t) is the preimage of a measurable set in ℕ → α.
  Coordinate 0 gives σ(x), coordinates 1,2,... give σ(t), so it's in the join.
- (≥): x = (consRV x t) ∘ π₀ and t = tailRV (consRV x t), so both σ(x) and σ(t)
  are contained in σ(consRV x t). -/
lemma comap_consRV_eq_sup
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (x : Ω → α) (t : Ω → ℕ → α) :
    MeasurableSpace.comap (consRV x t) inferInstance =
    MeasurableSpace.comap x inferInstance ⊔ MeasurableSpace.comap t inferInstance := by
  apply le_antisymm
  -- (≤): σ(consRV x t) ≤ σ(x) ⊔ σ(t)
  -- Any set in comap (consRV x t) is a preimage of a product-measurable set in ℕ → α.
  -- Product σ-algebra is generated by coordinate projections.
  -- Coordinate 0 of consRV gives x, coordinate n+1 gives t n.
  · intro s hs
    obtain ⟨S, hS_meas, rfl⟩ := hs
    -- S is measurable in ℕ → α. We show consRV x t ⁻¹' S ∈ σ(x) ⊔ σ(t).
    -- Key: consRV x t factors through (x, t) via a measurable "cons" function.
    -- Define consSeq : α × (ℕ → α) → (ℕ → α) by consSeq (a, f) n = if n = 0 then a else f (n-1)
    let consSeq : α × (ℕ → α) → (ℕ → α) := fun ⟨a, f⟩ n =>
      match n with
      | 0 => a
      | n + 1 => f n
    -- consRV x t = consSeq ∘ (fun ω => (x ω, t ω))
    have h_factor : consRV x t = consSeq ∘ (fun ω => (x ω, t ω)) := by
      ext ω n
      simp only [Function.comp_apply, consRV, consSeq]
      cases n <;> rfl
    -- consSeq is measurable
    have h_consSeq_meas : Measurable consSeq := by
      rw [measurable_pi_iff]; intro n
      cases n with
      | zero => exact measurable_fst
      | succ k => exact (measurable_pi_apply k).comp measurable_snd
    -- So consRV x t ⁻¹' S = (fun ω => (x ω, t ω)) ⁻¹' (consSeq ⁻¹' S)
    rw [h_factor, Set.preimage_comp]
    -- consSeq ⁻¹' S is measurable in α × (ℕ → α)
    have hT : MeasurableSet (consSeq ⁻¹' S) := h_consSeq_meas hS_meas
    -- (fun ω => (x ω, t ω)) ⁻¹' T is in σ(x) ⊔ σ(t) for any T in product σ-algebra
    -- This follows from measurability of the pair function
    have h_pair_meas : @Measurable Ω (α × (ℕ → α))
        (MeasurableSpace.comap x inferInstance ⊔ MeasurableSpace.comap t inferInstance)
        (MeasurableSpace.prod inferInstance inferInstance)
        (fun ω => (x ω, t ω)) := by
      apply Measurable.prod
      -- x is measurable from σ(x) ⊔ σ(t) to α
      · have hx : @Measurable Ω α (MeasurableSpace.comap x inferInstance) inferInstance x :=
          Measurable.of_comap_le le_rfl
        exact Measurable.mono hx le_sup_left le_rfl
      -- t is measurable from σ(x) ⊔ σ(t) to ℕ → α
      · have ht : @Measurable Ω (ℕ → α) (MeasurableSpace.comap t inferInstance) inferInstance t :=
          Measurable.of_comap_le le_rfl
        exact Measurable.mono ht le_sup_right le_rfl
    exact h_pair_meas hT
  -- (≥): σ(x) ⊔ σ(t) ≤ σ(consRV x t)
  · apply sup_le
    -- σ(x) ≤ σ(consRV x t) via coordinate 0
    · intro s hs
      obtain ⟨S, hS_meas, rfl⟩ := hs
      -- s = x ⁻¹' S, need to show it's in σ(consRV x t)
      -- x ω = (consRV x t ω) 0, so x ⁻¹' S = (consRV x t) ⁻¹' {f | f 0 ∈ S}
      exact ⟨{f | f 0 ∈ S}, measurable_pi_apply 0 hS_meas, by ext ω; simp [consRV]⟩
    -- σ(t) ≤ σ(consRV x t)
    · exact comap_le_comap_consRV x t

-- NOTE: A lemma `pair_law_Xr_eq_of_contractable` was removed from here because it had
-- type errors (different codomain types). The correct pair law is `pair_law_eq_of_contractable`.

/-- **Conditional expectation drop-info for X_r-indicator via true contraction.**

This is the key lemma for restructuring block_coord_condIndep.
Given contractability of X, for r < m and B ∈ σ(X_r):

  E[1_{X_r ∈ B} | σ(U, W)] = E[1_{X_r ∈ B} | σ(W)]

where U = firstRMap X r and W = shiftRV X (m+1).

**Proof strategy:**
The direct Kallenberg 1.3 approach has type issues (W and W' need the same type).
Two correct approaches:
1. Use `pair_law_eq_of_contractable` with (U, W) =^d (U, W') where W' = consRV(X_r, W),
   then translate via σ(W') = σ(X_r) ⊔ σ(W) (from comap_consRV_eq_sup).
   This gives E[f(U) | σ(X_r, W)] = E[f(U) | σ(W)], i.e., U ⊥⊥ X_r | W.
   By symmetry of CI, this gives X_r ⊥⊥ U | W which is the goal.
2. Embed into a common type space by viewing W as a tuple (default, W) to match W' = (U, W). -/
@[nolint unusedArguments]
lemma condExp_Xr_indicator_eq_of_contractable
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    [StandardBorelSpace α]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → α}
    (hContr : Contractable μ X)
    (hX_meas : ∀ n, Measurable (X n))
    {r m : ℕ} (hrm : r ≤ m)
    {B : Set α} (hB : MeasurableSet B) :
    let Y := X r
    let U := fun ω : Ω => (fun i : Fin r => X i ω)
    let W := shiftRV X (m+1)
    μ[Set.indicator (Y ⁻¹' B) (fun _ => (1 : ℝ))
       | MeasurableSpace.comap U inferInstance ⊔ MeasurableSpace.comap W inferInstance]
      =ᵐ[μ]
    μ[Set.indicator (Y ⁻¹' B) (fun _ => (1 : ℝ))
       | MeasurableSpace.comap W inferInstance] := by
  /-
  **Full proof outline:**

  Goal: X_r ⊥⊥ U | W (conditional independence in indicator form)

  **Step 1: Apply pair law**
  From `pair_law_eq_of_contractable`: (U, W) =^d (U, W') where W' = consRV(X_r, W)

  **Step 2: Apply Kallenberg 1.3**
  Since σ(W) ≤ σ(W') (via comap_le_comap_consRV) and (U, W) =^d (U, W'),
  Kallenberg 1.3 gives: E[f(U) | σ(W')] = E[f(U) | σ(W)]  a.e.

  **Step 3: Use comap_consRV_eq_sup**
  σ(W') = σ(consRV(X_r, W)) = σ(X_r) ⊔ σ(W)

  So: E[f(U) | σ(X_r, W)] = E[f(U) | σ(W)]  a.e.

  This is exactly U ⊥⊥ X_r | W in indicator form.

  **Step 4: Symmetry of conditional independence**
  U ⊥⊥ X_r | W implies X_r ⊥⊥ U | W

  This gives: E[g(X_r) | σ(U, W)] = E[g(X_r) | σ(W)]  a.e.

  Taking g = 1_{· ∈ B} yields the goal.
  -/
  intro Y U W

  -- Step 1: Get the pair law from contractability
  -- (U, W) =^d (U, W') where W' = consRV(X_r, W)
  let W' := consRV (fun ω => X r ω) W
  have h_pair := pair_law_eq_of_contractable hContr hX_meas r m hrm

  -- Step 2: Establish the contraction: σ(W) ⊆ σ(W')
  have h_le : MeasurableSpace.comap W inferInstance ≤ MeasurableSpace.comap W' inferInstance :=
    comap_le_comap_consRV (fun ω => X r ω) W

  -- Step 3: Apply Kallenberg 1.3 to get drop-info for U
  -- E[1_{U∈A} | σ(W')] = E[1_{U∈A} | σ(W)] for all measurable A
  -- This uses condExp_indicator_eq_of_law_eq_of_comap_le (fully proved)

  -- Measurability facts
  have hU_meas : Measurable U := by measurability
  have hW_meas : Measurable W := measurable_pi_iff.mpr fun n => hX_meas (m + 1 + n)
  have hW'_meas : Measurable W' := by
    -- consRV x t is measurable when x and t are measurable
    rw [measurable_pi_iff]; intro n
    cases n with
    | zero => exact hX_meas r
    | succ k => exact (measurable_pi_apply k).comp hW_meas

  -- Step 5: Establish conditional independence U ⊥⊥_W X_r
  -- From drop-info E[1_{U∈A}|σ(W')] = E[1_{U∈A}|σ(W)], we derive CondIndep μ U (X r) W
  -- This uses Kallenberg Lemma 1.3 (condExp_indicator_eq_of_law_eq_of_comap_le)
  have h_CI_UXrW : CondIndep μ U (X r) W := by
    -- Unfold CondIndep: need to show for all A, B measurable:
    -- E[1_{U∈A} * 1_{X_r∈B} | σ(W)] =ᵐ E[1_{U∈A} | σ(W)] * E[1_{X_r∈B} | σ(W)]
    intro A_U B_Xr hA_U hB_Xr

    -- IMPORTANT: Compute drop-info BEFORE defining local MeasurableSpace aliases
    -- to avoid instance pollution (see instance-pollution.md)
    have h_drop_raw :
        μ[Set.indicator (U ⁻¹' A_U) (fun _ => (1 : ℝ)) | MeasurableSpace.comap W' inferInstance]
        =ᵐ[μ]
        μ[Set.indicator (U ⁻¹' A_U) (fun _ => (1 : ℝ)) | MeasurableSpace.comap W inferInstance] :=
      condExp_indicator_eq_of_law_eq_of_comap_le U W W' hU_meas hW_meas hW'_meas h_pair h_le hA_U

    -- Set up notation (AFTER computing h_drop_raw)
    let mW : MeasurableSpace Ω := MeasurableSpace.comap W inferInstance
    let mW' : MeasurableSpace Ω := MeasurableSpace.comap W' inferInstance
    let indA := (U ⁻¹' A_U).indicator (fun _ => (1 : ℝ))
    let indB := ((X r) ⁻¹' B_Xr).indicator (fun _ => (1 : ℝ))

    -- Transfer h_drop_raw to local notation
    have h_drop : μ[indA | mW'] =ᵐ[μ] μ[indA | mW] := h_drop_raw

    -- σ-algebra relationships
    have hmW_le : mW ≤ _ := measurable_iff_comap_le.mp hW_meas
    have hmW'_le : mW' ≤ _ := measurable_iff_comap_le.mp hW'_meas
    haveI hσW : SigmaFinite (μ.trim hmW_le) :=
      (inferInstance : IsFiniteMeasure (μ.trim hmW_le)).toSigmaFinite
    haveI hσW' : SigmaFinite (μ.trim hmW'_le) :=
      (inferInstance : IsFiniteMeasure (μ.trim hmW'_le)).toSigmaFinite

    -- Integrability of indicators
    have hIndA_int : Integrable indA μ :=
      (integrable_const 1).indicator (hA_U.preimage hU_meas)
    have hIndB_int : Integrable indB μ :=
      (integrable_const 1).indicator (hB_Xr.preimage (hX_meas r))
    have hProd_int : Integrable (indA * indB) μ := by
      have hIndA_bdd : ∀ᵐ x ∂μ, ‖indA x‖ ≤ 1 := by filter_upwards with x; exact norm_indicator_one_le _ x
      exact hIndB_int.bdd_mul hIndA_int.aestronglyMeasurable hIndA_bdd

    -- Key: indB is mW'-measurable (X_r = W'(0) via consRV)
    have hXr_mW'_meas : @Measurable Ω α mW' _ (X r) := by
      -- W' = consRV (X r) W, so (X r) ω = W' ω 0
      -- W' is mW'-measurable (identity on comap)
      have hW'_ident : @Measurable Ω (ℕ → α) mW' _ W' := measurable_iff_comap_le.mpr le_rfl
      -- W' ω 0 is mW'-measurable via projection
      have h0_meas : @Measurable Ω α mW' _ (fun ω => W' ω 0) :=
        @Measurable.comp Ω (ℕ → α) α mW' _ _ (fun f => f 0) W'
          (measurable_pi_apply 0) hW'_ident
      -- X r = fun ω => W' ω 0 by definition of consRV
      have h_eq : (X r) = (fun ω => W' ω 0) := funext fun ω => by simp only [W', consRV]
      rw [h_eq]
      exact h0_meas
    have hIndB_mW'_meas : @Measurable Ω ℝ mW' _ indB :=
      (measurable_const.indicator hB_Xr).comp hXr_mW'_meas
    have hIndB_stronglyMeas_mW' : StronglyMeasurable[mW'] indB :=
      hIndB_mW'_meas.stronglyMeasurable

    -- Step 2: Tower property: condExp mW (condExp mW' f) = condExp mW f
    have h_tower_prod : μ[μ[indA * indB | mW'] | mW] =ᵐ[μ] μ[indA * indB | mW] :=
      condExp_condExp_of_le h_le hmW'_le

    -- Step 3: Pull-out for mW': E[indA * indB | mW'] =ᵐ E[indA | mW'] * indB
    have h_step1 : μ[indA * indB | mW'] =ᵐ[μ] μ[indA | mW'] * indB :=
      condExp_mul_of_stronglyMeasurable_right hIndB_stronglyMeas_mW' hProd_int hIndA_int

    -- Step 4: Apply drop-info: E[indA | mW'] * indB =ᵐ E[indA | mW] * indB
    have h_step2 : μ[indA | mW'] * indB =ᵐ[μ] μ[indA | mW] * indB := by
      filter_upwards [h_drop] with ω hω
      simp only [Pi.mul_apply]
      rw [hω]

    -- Combine steps
    have h_step12 : μ[indA * indB | mW'] =ᵐ[μ] μ[indA | mW] * indB :=
      h_step1.trans h_step2

    -- Step 5: Apply condExp mW to both sides (tower + congr)
    have h_step3 : μ[indA * indB | mW] =ᵐ[μ] μ[μ[indA | mW] * indB | mW] :=
      h_tower_prod.symm.trans (condExp_congr_ae h_step12)

    -- Step 6: Pull-out for mW: E[E[indA|mW] * indB | mW] =ᵐ E[indA|mW] * E[indB|mW]
    have hCondExpA_stronglyMeas : StronglyMeasurable[mW] (μ[indA | mW]) :=
      stronglyMeasurable_condExp
    have hIndB_bdd : ∀ᵐ x ∂μ, ‖indB x‖ ≤ 1 := by filter_upwards with x; exact norm_indicator_one_le _ x
    have h_prod_condA_indB_int : Integrable (μ[indA | mW] * indB) μ := by
      convert integrable_condExp.bdd_mul hIndB_int.aestronglyMeasurable hIndB_bdd using 2
      exact mul_comm _ _
    have h_step4 : μ[μ[indA | mW] * indB | mW] =ᵐ[μ] μ[indA | mW] * μ[indB | mW] :=
      condExp_mul_of_stronglyMeasurable_left hCondExpA_stronglyMeas h_prod_condA_indB_int hIndB_int

    -- Combine all steps
    exact h_step3.trans h_step4

  -- Step 6: Apply symmetry of conditional independence
  have h_CI_XrUW : CondIndep μ (X r) U W := (condIndep_symm μ U (X r) W).mp h_CI_UXrW

  -- Step 7: Apply the projection property
  -- If X_r ⊥⊥_W U, then E[1_{X_r∈B}|σ(U,W)] = E[1_{X_r∈B}|σ(W)]
  -- Use condExp_project_of_condIndep

  -- σ(U) ⊔ σ(W) = σ(U,W) by mathlib's comap_prodMk
  have h_sigma_eq : MeasurableSpace.comap U inferInstance ⊔ MeasurableSpace.comap W inferInstance =
                    MeasurableSpace.comap (fun ω => (U ω, W ω)) inferInstance :=
    (MeasurableSpace.comap_prodMk U W).symm

  -- Rewrite goal using the σ-algebra equality
  rw [h_sigma_eq]

  -- Apply the projection theorem
  exact condExp_project_of_condIndep μ (X r) U W (hX_meas r) hU_meas hW_meas h_CI_XrUW hB


end Exchangeability.DeFinetti.ViaMartingale
