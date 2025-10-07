/-
Copyright (c) 2025 exchangeability contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: exchangeability contributors
-/
import Mathlib.Probability.ConditionalExpectation
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Martingale.Basic
import Exchangeability.Contractability
import Exchangeability.Probability.CondExp

/-!
# Third proof of de Finetti via a martingale argument (Aldous)

This file contains Aldous's elegant martingale proof of de Finetti's theorem, as
presented in Kallenberg (2005), Section 1.2.

## Main results

* `contraction_independence`: If `(ξ, η) =^d (ξ, ζ)` and `σ(η) ⊆ σ(ζ)`, then
  `ξ ⊥⊥_η ζ` (Lemma 1.3 in Kallenberg).
  
  **Proof idea:** For any measurable set `B`, define
  `μ₁ = P[ξ ∈ B | η]` and `μ₂ = P[ξ ∈ B | ζ]`.
  Then `(μ₁, μ₂)` is a bounded martingale with `μ₁ =^d μ₂`, so
  `E(μ₂ - μ₁)² = Eμ₂² - Eμ₁² = 0`, implying `μ₁ = μ₂` a.s.
  By Doob's characterization (FMP 6.6), this gives conditional independence.

* `deFinetti_martingale`: If `ξ` is contractable, then the `ξₙ` are conditionally
  i.i.d. given the tail σ-algebra `𝒯_ξ = ⋂_n σ(θ_n ξ)`.
  
  **Proof idea:** From contractability, `(ξ_m, θ_m ξ) =^d (ξ_k, θ_k ξ)` for `k ≤ m`.
  Using the contraction-independence lemma and reverse martingale convergence:
  ```
  P[ξ_m ∈ B | θ_m ξ] = P[ξ_k ∈ B | θ_m ξ] → P[ξ_k ∈ B | 𝒯_ξ]
  ```
  This shows:
  - `P[ξ_m ∈ B | θ_m ξ] = P[ξ_m ∈ B | 𝒯_ξ]`, giving `ξ_m ⊥⊥_{𝒯_ξ} θ_m ξ`
  - By iteration, `ξ₁, ξ₂, ...` are conditionally independent given `𝒯_ξ`
  - `P[ξ_m ∈ B | 𝒯_ξ] = P[ξ₁ ∈ B | 𝒯_ξ]`, showing identical conditional laws

## References

* Olav Kallenberg, *Probabilistic Symmetries and Invariance Principles* (2005),
  Lemma 1.3 and third proof of Theorem 1.1 (page 28).
* David Aldous, *Exchangeability and related topics*, École d'Été de
  Probabilités de Saint-Flour XIII (1983).
-/

noncomputable section
open scoped MeasureTheory ProbabilityTheory Topology

namespace Exchangeability
namespace DeFinetti
namespace MartingaleApproach

open MeasureTheory Filter

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- `shiftProcess X m` is the process `n ↦ X (m + n)` (Kallenberg's θₘ ξ). -/
def shiftProcess (X : ℕ → Ω → α) (m : ℕ) : ℕ → Ω → α := fun n ω => X (m + n) ω

/-- The random path of a process: ω ↦ (n ↦ X n ω). -/
def path (X : ℕ → Ω → α) : Ω → (ℕ → α) := fun ω n => X n ω

/-- Shifted random path: ω ↦ (n ↦ X (m + n) ω). -/
def shiftRV (X : ℕ → Ω → α) (m : ℕ) : Ω → (ℕ → α) :=
  fun ω n => X (m + n) ω

section SequenceShift

variable {β : Type*} [MeasurableSpace β]

/-- Shift a sequence by dropping the first `d` entries. -/
def shiftSeq (d : ℕ) (f : ℕ → β) : ℕ → β := fun n => f (n + d)

@[simp]
lemma shiftSeq_apply (d : ℕ) (f : ℕ → β) (n : ℕ) :
    shiftSeq d f n = f (n + d) := rfl

lemma measurable_shiftSeq (d : ℕ) :
    Measurable (shiftSeq (β:=β) d) := by
  classical
  refine measurable_pi_iff.mpr ?_
  intro n
  -- Evaluation at `n + d` is measurable in the product σ-algebra.
  have h := (Pi.measurable_eval (fun _ : ℕ => β) (n + d))
  simpa [shiftSeq] using h

lemma forall_mem_erase {γ : Type*} [DecidableEq γ]
    {s : Finset γ} {a : γ} {P : γ → Prop} (ha : a ∈ s) :
    (∀ x ∈ s, P x) ↔ P a ∧ ∀ x ∈ s.erase a, P x := by
  constructor
  · intro h
    refine ⟨h _ ha, ?_⟩
    intro x hx
    exact h _ (Finset.mem_of_mem_erase hx)
  · rintro ⟨haP, hrest⟩ x hx
    by_cases hxa : x = a
    · simpa [hxa] using haP
    · have hx' : x ∈ s.erase a := by
        exact Finset.mem_erase.mpr ⟨hxa, hx⟩
      exact hrest _ hx'

end SequenceShift

section FinsetOrder

open Finset

lemma orderEmbOfFin_strictMono (s : Finset ℕ) :
    StrictMono fun i : Fin s.card => s.orderEmbOfFin rfl i := by
  classical
  simpa using (s.orderEmbOfFin rfl).strictMono

lemma orderEmbOfFin_mem (s : Finset ℕ) (i : Fin s.card) :
    s.orderEmbOfFin rfl i ∈ s := by
  classical
  simpa using Finset.orderEmbOfFin_mem (s:=s) (h:=rfl) i

end FinsetOrder

omit [MeasurableSpace Ω] [MeasurableSpace α] in
@[simp]
lemma path_apply (X : ℕ → Ω → α) (ω n) :
    path X ω n = X n ω := rfl

omit [MeasurableSpace Ω] [MeasurableSpace α] in
@[simp]
lemma shiftRV_apply (X : ℕ → Ω → α) (m ω n) :
    shiftRV X m ω n = X (m + n) ω := rfl

omit [MeasurableSpace Ω] [MeasurableSpace α] in
@[simp]
lemma shiftRV_zero (X : ℕ → Ω → α) : shiftRV X 0 = path X := by
  funext ω n; simp [shiftRV, path]

omit [MeasurableSpace Ω] [MeasurableSpace α] in
@[simp]
lemma shiftRV_comp_shiftProcess (X : ℕ → Ω → α) (m k : ℕ) :
    shiftRV (shiftProcess X m) k = shiftRV X (m + k) := by
  funext ω n; simp [shiftRV, shiftProcess, Nat.add_assoc]

omit [MeasurableSpace Ω] [MeasurableSpace α] in
@[simp]
lemma shiftProcess_zero (X : ℕ → Ω → α) : shiftProcess X 0 = X := by
  funext n ω; simp [shiftProcess]

omit [MeasurableSpace Ω] [MeasurableSpace α] in
@[simp]
lemma shiftProcess_add (X : ℕ → Ω → α) (m k : ℕ) :
    shiftProcess (shiftProcess X m) k = shiftProcess X (m + k) := by
  funext n ω; simp [shiftProcess, Nat.add_assoc]

omit [MeasurableSpace Ω] [MeasurableSpace α] in
lemma path_eq_shiftRV_zero (X : ℕ → Ω → α) : path X = shiftRV X 0 :=
  (shiftRV_zero X).symm

omit [MeasurableSpace Ω] [MeasurableSpace α] in
lemma shiftProcess_apply (X : ℕ → Ω → α) (m n ω) :
    shiftProcess X m n ω = X (m + n) ω := by
  rfl

/-- 𝔽ₘ := σ(θₘ X) = σ(ω ↦ (n ↦ X (m+n) ω)). -/
abbrev revFiltration (X : ℕ → Ω → α) (m : ℕ) : MeasurableSpace Ω :=
  MeasurableSpace.comap (shiftRV X m) inferInstance

@[simp]
lemma revFiltration_zero (X : ℕ → Ω → α) :
    revFiltration X 0 = MeasurableSpace.comap (path X) inferInstance := by
  simp [revFiltration]

/-- The tail σ-algebra for a process X: ⋂ₙ σ(Xₙ, Xₙ₊₁, ...). -/
def tailSigma (X : ℕ → Ω → α) : MeasurableSpace Ω :=
  ⨅ m, revFiltration X m

omit [MeasurableSpace Ω] in
@[simp]
lemma tailSigma_eq_iInf_rev (X : ℕ → Ω → α) :
    tailSigma X = ⨅ m, revFiltration X m := rfl

section Measurability

variable {X : ℕ → Ω → α}

lemma measurable_path (hX : ∀ n, Measurable (X n)) :
    Measurable (path X) := by
  classical
  simpa [path] using measurable_pi_iff.mpr hX

lemma measurable_shiftRV (hX : ∀ n, Measurable (X n)) (m : ℕ) :
    Measurable (shiftRV X m) := by
  classical
  simpa [shiftRV] using
    measurable_pi_iff.mpr (fun n => by simpa using hX (m + n))

end Measurability

lemma revFiltration_antitone (X : ℕ → Ω → α) :
    Antitone (revFiltration X) := by
  -- Goal: m ≤ k ⇒ revFiltration X k ≤ revFiltration X m (i.e., σ(θₖX) ⊆ σ(θₘX)).
  intro m k hmk
  classical
  have hcomp :
      shiftRV X k = (shiftSeq (α:=α) (k - m)) ∘ shiftRV X m := by
    funext ω n
    have hkm : m + (k - m) = k := by
      simpa [Nat.add_comm] using (Nat.sub_add_cancel hmk)
    have hsum :
        m + (n + (k - m)) = k + n := by
      calc
        m + (n + (k - m))
            = n + (m + (k - m)) := by
                simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        _ = n + k := by simpa [hkm]
        _ = k + n := Nat.add_comm _ _
    simp [shiftSeq, shiftRV, Function.comp, hsum]
  intro s hs
  simp [revFiltration, hcomp, Set.preimage_preimage, Function.comp] at hs ⊢
  rcases hs with ⟨t, ht, rfl⟩
  refine ⟨_, (measurable_shiftSeq (α:=α) (k - m)).measurableSet_preimage ht, rfl⟩

/-- If `X` is contractable, then so is each of its shifts `θₘ X`. -/
lemma shift_contractable {μ : Measure Ω} {X : ℕ → Ω → α}
    (hX : Contractable μ X) (m : ℕ) : Contractable μ (shiftProcess X m) := by
  -- For any strictly monotone k : Fin n → ℕ, need to show:
  -- (shiftProcess X m (k i))ᵢ ~ (shiftProcess X m i)ᵢ
  intro n k hk_mono
  -- Define k' i = m + k i (strictly monotone)
  let k' : Fin n → ℕ := fun i => m + k i
  have hk'_mono : StrictMono k' := by
    intro i j hij
    simp only [k']
    exact Nat.add_lt_add_left (hk_mono hij) m
  -- Also define j i = m + i (for the RHS)
  let j : Fin n → ℕ := fun i => m + i
  have hj_mono : StrictMono j := by
    intro i₁ i₂ h
    simp only [j]
    exact Nat.add_lt_add_left h m
  -- Apply contractability to k' and j
  have h1 := hX n k' hk'_mono
  have h2 := hX n j hj_mono
  -- Now connect the pieces:
  -- (shiftProcess X m (k i))ᵢ = (X (m + k i))ᵢ = (X (k' i))ᵢ
  -- ~ (X i)ᵢ (by h1)
  -- ~ (X (j i))ᵢ (by h2.symm)
  -- = (X (m + i))ᵢ = (shiftProcess X m i)ᵢ
  calc Measure.map (fun ω i => shiftProcess X m (k i) ω) μ
      = Measure.map (fun ω i => X (k' i) ω) μ := by congr
    _ = Measure.map (fun ω i => X i.val ω) μ := h1
    _ = Measure.map (fun ω i => X (j i) ω) μ := h2.symm
    _ = Measure.map (fun ω i => shiftProcess X m i.val ω) μ := by congr

/-- **Lemma 1.3 (contraction and independence).**

If `(ξ, η) =^d (ξ, ζ)` and `σ(η) ⊆ σ(ζ)`, then `ξ ⊥⊥_η ζ`.

**Proof sketch:** Fix a measurable set `B` and define:
- `μ₁ = P[ξ ∈ B | η]`
- `μ₂ = P[ξ ∈ B | ζ]`

Since `σ(η) ⊆ σ(ζ)`, we have that `μ₁` is `σ(η)`-measurable and `μ₂` is `σ(ζ)`-measurable,
making `(μ₁, μ₂)` a bounded martingale. From the distributional equality
`(ξ, η) =^d (ξ, ζ)`, we get `μ₁ =^d μ₂`, so:

```
E(μ₂ - μ₁)² = E μ₂² - E μ₁² = 0
```

Thus `μ₁ = μ₂` a.s., i.e., `P[ξ ∈ B | η] = P[ξ ∈ B | ζ]` a.s. By Doob's
characterization of conditional independence (FMP 6.6), this gives `ξ ⊥⊥_η ζ`. ∎

*Kallenberg (2005), Lemma 1.3.* -/
lemma contraction_independence
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ξ η ζ : Ω → α}
    (h_dist : Measure.map (fun ω => (ξ ω, η ω)) μ
              = Measure.map (fun ω => (ξ ω, ζ ω)) μ)
    (h_sigma : MeasurableSpace.comap η inferInstance ≤ MeasurableSpace.comap ζ inferInstance) :
    ProbabilityTheory.CondIndep ξ ζ η μ := by
  -- Proof strategy (wrapper around condexp_indicator_eq_of_dist_eq_and_le):
  -- Step 1: For each measurable B, apply condexp_indicator_eq_of_dist_eq_and_le
  --         to get: P[ξ ∈ B | η] = P[ξ ∈ B | ζ] a.s.
  -- Step 2: This shows that ξ and ζ have the same conditional distribution given η
  -- Step 3: Since σ(η) ⊆ σ(ζ), this implies ξ ⊥⊥_η ζ by Doob's characterization (FMP 6.6)
  --
  -- The key insight: condexp_indicator_eq_of_dist_eq_and_le gives the conditional
  -- expectation equality directly, which is exactly what we need for conditional independence.
  --
  -- TODO: Once CondIndep API is clarified in mathlib, formalize using:
  -- - condexp_indicator_eq_of_dist_eq_and_le (already stated above)
  -- - Doob's characterization of conditional independence
  sorry

/-- If `(ξ,η)` and `(ξ,ζ)` have the same law and `σ(η) ≤ σ(ζ)`,
then for all measurable `B`, the conditional expectations of `1_{ξ∈B}` coincide.

This is the key technical lemma that converts distributional equality into
conditional expectation equality. It's used to prove `condexp_convergence`. -/
lemma condexp_indicator_eq_of_dist_eq_and_le
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ξ : Ω → α} {η ζ : Ω → (ℕ → α)}
    (h_dist : Measure.map (fun ω => (ξ ω, η ω)) μ
            = Measure.map (fun ω => (ξ ω, ζ ω)) μ)
    (hσ : MeasurableSpace.comap η inferInstance ≤ MeasurableSpace.comap ζ inferInstance)
    (B : Set α) (hB : MeasurableSet B) :
    μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ ξ | MeasurableSpace.comap η inferInstance]
      =ᵐ[μ]
    μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ ξ | MeasurableSpace.comap ζ inferInstance] := by
  -- Proof sketch to implement in CondExp.lean:
  -- 1. Both sides are in [0,1] and in L² (indicators are bounded)
  -- 2. By hσ and tower property: E[(RHS - LHS) · g] = 0 for any g measurable w.r.t. σ(η)
  -- 3. Using h_dist, compare second moments:
  --    ∫ RHS² = ∫ LHS² (by distributional equality)
  --    Therefore ∫ (RHS - LHS)² = 0
  -- 4. Conclude RHS = LHS almost everywhere
  --
  -- Required lemmas from CondExp.lean:
  -- - condexp_tower: tower property for conditional expectation
  -- - condexp_L2_norm: ‖E[f|𝔾]‖₂ ≤ ‖f‖₂
  -- - indicator_L2: indicators are in L²
  -- - ae_eq_of_L2_norm_eq_zero: ‖f‖₂ = 0 ⇒ f = 0 a.e.
  sorry

/-- Cylinder version: contractability implies measure equality on finite cylinders.

For any finite index set and measurable sets, the measures of the corresponding
cylinders agree when comparing `(X_m, shiftRV X m)` and `(X_k, shiftRV X m)`. -/
lemma contractable_dist_eq_on_cylinders
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → α} (hX : Contractable μ X) (k m : ℕ) (hk : k ≤ m)
    (B : Set α) (hB : MeasurableSet B)
    (s : Finset ℕ) (t : ∀ i ∈ s, Set α) (ht : ∀ i (hi : i ∈ s), MeasurableSet (t i hi)) :
    μ {ω | X m ω ∈ B ∧ ∀ i (hi : i ∈ s), X (m + i) ω ∈ t i hi}
      = μ {ω | X k ω ∈ B ∧ ∀ i (hi : i ∈ s), X (m + i) ω ∈ t i hi} := by
  classical
  -- Remove the `0`-coordinate from the tail and fold it into the base set.
  set s0 : Finset ℕ := s.erase 0
  have hs0_subset : s0 ⊆ s := Finset.erase_subset _ _
  let t0 : ∀ i ∈ s0, Set α := fun i hi => t i (hs0_subset hi)
  have ht0 : ∀ i (hi : i ∈ s0), MeasurableSet (t0 i hi) := by
    intro i hi
    simpa [t0] using ht i (hs0_subset hi)
  let B0 : Set α :=
    if h0 : 0 ∈ s then B ∩ t 0 h0 else B
  have hB0 : MeasurableSet B0 := by
    classical
    by_cases h0 : 0 ∈ s
    · have h0_meas := ht 0 h0
      simpa [B0, h0, hB] using hB.inter h0_meas
    · simpa [B0, h0, hB]
  -- The event can be rewritten using the adjusted σ-algebra data.
  have h_event_rewrite :
      {ω | X m ω ∈ B ∧ ∀ i (hi : i ∈ s), X (m + i) ω ∈ t i hi}
        =
      {ω | X m ω ∈ B0 ∧ ∀ i (hi : i ∈ s0), X (m + i) ω ∈ t0 i hi} := by
    classical
    by_cases h0 : 0 ∈ s
    · -- With `0` present we fold its constraint into `B0`.
      ext ω; constructor <;> intro h
      · rcases h with ⟨hBm, htail⟩
        have h0_tail := htail 0 h0
        refine ⟨?_, ?_⟩
        · simpa [B0, h0, Nat.add_zero] using And.intro hBm h0_tail
        · intro i hi
          have hi_mem := hs0_subset hi
          have htail' := htail i hi_mem
          simpa [t0, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htail'
      · rcases h with ⟨hB0_mem, htail⟩
        have hBm : X m ω ∈ B := by
          have := hB0_mem
          simpa [B0, h0] using this.1
        have h0_tail : X (m + 0) ω ∈ t 0 h0 := by
          have := hB0_mem
          simpa [B0, h0, Nat.add_zero] using this.2
        refine ⟨hBm, ?_⟩
        intro i hi
        by_cases hi0 : i = 0
        · simpa [hi0, Nat.add_zero] using h0_tail
        · have hi_mem : i ∈ s0 := Finset.mem_erase.mpr ⟨hi0, hi⟩
          have := htail i hi_mem
          simpa [t0, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this
    · -- Without `0`, nothing changes.
      have hs0_eq : s0 = s := by
        simpa [s0, h0] using Finset.erase_eq_of_not_mem h0
      simp [B0, h0, hs0_eq, t0]
  -- Same rewrite for the `k`-version.
  have h_event_rewrite_k :
      {ω | X k ω ∈ B ∧ ∀ i (hi : i ∈ s), X (m + i) ω ∈ t i hi}
        =
      {ω | X k ω ∈ B0 ∧ ∀ i (hi : i ∈ s0), X (m + i) ω ∈ t0 i hi} := by
    classical
    by_cases h0 : 0 ∈ s
    · ext ω; constructor <;> intro h
      · rcases h with ⟨hBk, htail⟩
        have h0_tail := htail 0 h0
        refine ⟨?_, ?_⟩
        · have : X k ω ∈ B ∧ X (m + 0) ω ∈ t 0 h0 :=
            ⟨hBk, by simpa [Nat.add_zero] using h0_tail⟩
          simpa [B0, h0] using this
        · intro i hi
          have hi_mem := hs0_subset hi
          have htail' := htail i hi_mem
          simpa [t0, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htail'
      · rcases h with ⟨hB0_mem, htail⟩
        have hBk : X k ω ∈ B := by
          have := hB0_mem
          simpa [B0, h0] using this.1
        have h0_tail : X (m + 0) ω ∈ t 0 h0 := by
          have := hB0_mem
          simpa [B0, h0, Nat.add_zero] using this.2
        refine ⟨hBk, ?_⟩
        intro i hi
        by_cases hi0 : i = 0
        · simpa [hi0, Nat.add_zero] using h0_tail
        · have hi_mem : i ∈ s0 := Finset.mem_erase.mpr ⟨hi0, hi⟩
          have := htail i hi_mem
          simpa [t0, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this
    · have hs0_eq : s0 = s := by
        simpa [s0, h0] using Finset.erase_eq_of_not_mem h0
      simp [B0, h0, hs0_eq, t0]
  -- Work with the enumerated tail coordinates.
  let n := s0.card
  let tail : Fin n → ℕ := fun i => s0.orderEmbOfFin rfl i
  have htail_mono : StrictMono tail := orderEmbOfFin_strictMono s0
  have htail_mem : ∀ i, tail i ∈ s0 := orderEmbOfFin_mem s0
  -- Tail indices are strictly positive (since 0 was erased).
  have htail_pos : ∀ i, 0 < tail i := by
    intro i
    have hi_mem := htail_mem i
    have : tail i ≠ 0 := by
      have hi := Finset.mem_erase.mp hi_mem
      exact hi.1
    exact Nat.pos_of_ne_zero this
  -- Build the strictly monotone index lists for the contractability lemma.
  let k_m : Fin (n + 1) → ℕ :=
    Fin.cases 0 (fun i => tail i)
  let k_map_m : Fin (n + 1) → ℕ := fun i => m + k_m i
  let k_map_k : Fin (n + 1) → ℕ := fun i =>
    match i with
    | ⟨0, _⟩ => k
    | Fin.succ i' => m + tail i'
  -- TODO: prove `StrictMono k_m` and `StrictMono k_map_m`, `StrictMono k_map_k`,
  -- then use `Contractable.allStrictMono_eq` to compare the push-forward measures.
  -- The desired cylinders can be expressed as preimages of a measurable set of
  -- `(Fin (n + 1) → α)` under these maps.
  --
  -- Required sub-lemmas:
  -- * `StrictMono (Fin.cases 0 (fun i => tail i))`
  -- * `StrictMono fun i => m + k_m i`
  -- * `StrictMono fun i => match i with | 0 => k | Fin.succ i' => m + tail i'`
  -- * event measurability & identification with the original cylinder
  sorry

/-- Helper lemma: contractability gives the key distributional equality.

If `X` is contractable, then for any `k ≤ m`:
```
(X_m, θ_m X) =^d (X_k, θ_m X)
```
where `θ_m X` denotes the **random** shifted tail path `ω ↦ (n ↦ X(m + n) ω)`. -/
lemma contractable_dist_eq
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → α} (hX : Contractable μ X) (k m : ℕ) (hk : k ≤ m) :
    Measure.map (fun ω => (X m ω, shiftRV X m ω)) μ
      = Measure.map (fun ω => (X k ω, shiftRV X m ω)) μ := by
  -- Strategy: Use contractable_dist_eq_on_cylinders to show equality on cylinder sets,
  -- then extend to all measurable sets via the π-λ theorem.
  --
  -- 1. Cylinder sets of the form {(a, f) | a ∈ B, f(i) ∈ t_i for i ∈ s} generate
  --    the product σ-algebra on α × (ℕ → α)
  -- 2. By contractable_dist_eq_on_cylinders, both measures agree on all such cylinders
  -- 3. Apply Measure.ext_of_generateFrom_of_cover (π-λ theorem) to conclude equality
  --
  -- Required API:
  -- - MeasureTheory.generate_from_prod_cylinder: cylinders generate product σ-algebra
  -- - Measure.ext_of_generateFrom_of_cover: π-λ theorem for measures
  -- - Formalization of cylinder sets in the product space
  sorry

/-- **Key convergence result:** The extreme members agree after conditioning on the tail σ-algebra.

For any `k ≤ m` and measurable set `B`:
```
P[X_m ∈ B | θ_m X] = P[X_k ∈ B | θ_m X] → P[X_k ∈ B | 𝒯_X]  (as n → ∞)
```

This is proved using Lemma 1.3 (contraction-independence) followed by reverse
martingale convergence. -/
-- TODO: The following theorems require conditional expectation API that is not yet
-- fully developed in this codebase. The proof structure is documented for future work.

lemma condexp_convergence
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → α} (hX : Contractable μ X) (k m : ℕ) (hk : k ≤ m)
    (B : Set α) (hB : MeasurableSet B) :
    μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ (X m) | revFiltration X m]
      =ᵐ[μ]
    μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ (X k) | revFiltration X m] := by
  -- Proof strategy:
  -- 1. From contractable_dist_eq: (X_m, shiftRV X m) =^d (X_k, shiftRV X m)
  -- 2. Note that σ(shiftRV X m) = revFiltration X m is the same conditioning σ-algebra
  -- 3. Apply contraction_independence (or its condexp version) to get:
  --    Both conditional expectations equal the same value
  -- 4. Therefore they're equal almost everywhere
  --
  -- This requires from CondExp.lean:
  -- - condexp_indicator_eq_of_dist_eq_and_le: distributional equality → condexp equality
  -- - Tower property if needed
  sorry

lemma extreme_members_equal_on_tail
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → α} (hX : Contractable μ X) (m : ℕ) (B : Set α) (hB : MeasurableSet B) :
    μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ (X m) | tailSigma X]
      =ᵐ[μ]
    μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ (X 0) | tailSigma X] := by
  -- Proof strategy:
  -- 1. From condexp_convergence: 𝔼[1_{X_m∈B} | 𝔽ₙ] = 𝔼[1_{X_0∈B} | 𝔽ₙ] for all n ≥ m
  -- 2. Define reverse martingale: Mₙ := 𝔼[1_{X_m∈B} | 𝔽ₙ]
  -- 3. As n → ∞, 𝔽ₙ = revFiltration X n ↓ tailSigma X (by revFiltration_antitone)
  -- 4. By reverse martingale convergence (Lévy's downward theorem):
  --    Mₙ → 𝔼[1_{X_m∈B} | tailSigma X] a.s. and in L¹
  -- 5. Similarly for X_0: 𝔼[1_{X_0∈B} | 𝔽ₙ] → 𝔼[1_{X_0∈B} | tailSigma X]
  -- 6. Since Mₙ are all equal (from step 1), their limits are equal
  -- 7. Therefore the conclusion holds
  --
  -- This requires from CondExp.lean:
  -- - Reverse martingale convergence (condexp_tendsto_condexp_iInf)
  -- - Dominated convergence for L¹ functions
  sorry

section reverse_martingale

variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {X : ℕ → Ω → α}

/-- 𝔽ₘ = σ(θₘ X). -/
abbrev 𝔽 (m : ℕ) : MeasurableSpace Ω := revFiltration X m

/-- The reverse filtration is decreasing; packaged for the martingale API. -/
lemma filtration_antitone : Antitone 𝔽 := by
  intro m n hmn
  simpa [𝔽] using revFiltration_antitone X hmn

/-- Mₘ := 𝔼[1_{Xₖ∈B} | 𝔽ₘ].
The reverse martingale sequence for the indicator of X_k in B. -/
def M (k : ℕ) (B : Set α) : ℕ → Ω → ℝ :=
  fun m ω =>
    μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ (X k) | 𝔽 m] ω

-- TODO (CondExp.lean milestones):
-- (1) `0 ≤ M k B m ω ≤ 1` a.s.
--     API: `condexp_indicator_bounds`.
-- (2) For `m ≤ n`, `M k B n` is `𝔽 n`-measurable and
--     `μ[fun ω => M k B n ω | 𝔽 m] =ᵐ[μ] M k B m`.
--     API: `condexp_tower`, `condexp_stronglyMeasurable`.
-- (3) If `(X m, θₘ X) =^d (X k, θₘ X)`, then
--     `M m B m =ᵐ[μ] M k B m`.
--     API: `condexp_indicator_eq_of_dist_eq_and_le`.
-- (4) `(fun n => M k B n ω)` is a reverse martingale that converges
--     to `μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ (X k) | tailSigma X] ω`.
--     API: `condexp_tendsto_condexp_iInf` (Lévy's downward theorem) together with
--     `filtration_antitone` and `tailSigma_eq_iInf_rev`.

end reverse_martingale

/-- **Aldous' third proof of de Finetti's theorem.**

If `X` is contractable, then `X₁, X₂, ...` are conditionally i.i.d. given the
tail σ-algebra `𝒯_X = ⋂_n σ(θ_n X)`.

**Proof structure:**
1. From contractability: `(X_m, θ_m X) =^d (X_k, θ_k X)` for `k ≤ m ≤ n`
2. Define `𝒯_X = ⋂_n σ(θ_n X)` (tail σ-algebra)
3. Apply Lemma 1.3 + reverse martingale convergence:
   ```
   P[X_m ∈ B | θ_m X] = P[X_k ∈ B | θ_m X] → P[X_k ∈ B | 𝒯_X]
   ```
4. Conclude: `P[X_m ∈ B | θ_m X] = P[X_m ∈ B | 𝒯_X] = P[X_1 ∈ B | 𝒯_X]`
5. First equality: `X_m ⊥⊥_{𝒯_X} θ_m X` for all `m`
6. By iteration: `X₁, X₂, ...` conditionally independent given `𝒯_X`
7. Second equality: conditional laws agree, giving conditional i.i.d.

*Kallenberg (2005), third proof of Theorem 1.1 (page 28).* -/
theorem deFinetti_martingale
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {α : Type*} [MeasurableSpace α]
    (X : ℕ → Ω → α) (hX : Contractable μ X) :
    ∃ (ℱ : MeasurableSpace Ω) (ν : Ω → Measure α),
      (∀ ω, IsProbabilityMeasure (ν ω)) ∧
      -- The sequence is conditionally i.i.d. given ℱ = 𝒯_X with law ν
      (ℱ = tailSigma X) ∧
      -- Conditional i.i.d. property (to be formalized)
      sorry := by
  use tailSigma X
  -- Define ν ω = P[X₁ ∈ · | 𝒯_X](ω)
  -- Use extreme_members_equal_on_tail to show conditional laws agree
  -- Use contraction_independence iteratively to show conditional independence
  sorry

end MartingaleApproach
end DeFinetti
end Exchangeability
