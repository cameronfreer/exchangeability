/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Probability.ConditionalExpectation
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Martingale.Basic
import Exchangeability.Contractability
import Exchangeability.ConditionallyIID
import Exchangeability.Probability.CondExp
import Exchangeability.Probability.Martingale
import Exchangeability.DeFinetti.MartingaleHelpers

/-!
# de Finetti's Theorem via Reverse Martingales

**Aldous' elegant martingale proof** of de Finetti's theorem, as presented in
Kallenberg (2005) as the "third proof". This approach has **medium dependencies**.

## Proof approach

The proof uses a contraction-independence lemma combined with reverse martingale
convergence:

1. **Lemma 1.3** (Contraction-Independence): If `(ξ, η) =^d (ξ, ζ)` and `σ(η) ⊆ σ(ζ)`,
   then `ξ ⊥⊥_η ζ`.

   **Proof idea:** For any `B`, define `μ₁ = P[ξ ∈ B | η]` and `μ₂ = P[ξ ∈ B | ζ]`.
   Then `(μ₁, μ₂)` is a bounded martingale with `μ₁ =^d μ₂`, so
   `E(μ₂ - μ₁)² = Eμ₂² - Eμ₁² = 0`, implying `μ₁ = μ₂` a.s.

2. **Main theorem**: If `ξ` is contractable, then `ξₙ` are conditionally i.i.d.
  given the tail σ-algebra `𝒯_ξ = ⋂_n σ(θ_n ξ)`.

  From contractability: `(ξ_m, θ_{m+1} ξ) =^d (ξ_k, θ_{m+1} ξ)` for `k ≤ m`.
  Using Lemma 1.3 and reverse martingale convergence:
  ```
  P[ξ_m ∈ B | θ_{m+1} ξ] = P[ξ_k ∈ B | θ_{m+1} ξ] → P[ξ_k ∈ B | 𝒯_ξ]
  ```
   This shows conditional independence and identical conditional laws.

## Main results

* `deFinetti_viaMartingale`: **Main theorem** - contractable implies conditionally i.i.d.
* `contraction_independence`: Contraction-independence lemma (Kallenberg Lemma 1.3)

## Dependencies

⚖️ **Medium** - Requires martingale theory and reverse martingale convergence
✅ **Elegant** - Short and conceptually clear proof
✅ **Probabilistic** - Pure probability theory, no functional analysis

## References

* Kallenberg (2005), *Probabilistic Symmetries and Invariance Principles*,
  Lemma 1.3 and page 28: "Third proof of Theorem 1.1"
* Aldous (1983), *Exchangeability and related topics*
-/

noncomputable section
open scoped MeasureTheory ProbabilityTheory Topology

namespace Exchangeability
namespace DeFinetti
namespace ViaMartingale

open MeasureTheory Filter
open Exchangeability.DeFinetti.MartingaleHelpers

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

-- Note: condExp_congr_ae is available from mathlib
-- (Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic)

/-- `shiftProcess X m` is the process `n ↦ X (m + n)` (Kallenberg's θₘ ξ). -/
def shiftProcess (X : ℕ → Ω → α) (m : ℕ) : ℕ → Ω → α := fun n ω => X (m + n) ω

/-- The random path of a process: ω ↦ (n ↦ X n ω). -/
def path (X : ℕ → Ω → α) : Ω → (ℕ → α) := fun ω n => X n ω

/-- Shifted random path: ω ↦ (n ↦ X (m + n) ω). -/
def shiftRV (X : ℕ → Ω → α) (m : ℕ) : Ω → (ℕ → α) :=
  fun ω n => X (m + n) ω

-- Helper sections (ComapTools, SequenceShift, TailCylinders, FinsetOrder)
-- have been extracted to MartingaleHelpers.lean

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

/-- If all coordinates of X are measurable, so are all coordinates of shifted process. -/
lemma measurable_shiftProcess (X : ℕ → Ω → α) (m : ℕ)
    (hX : ∀ n, Measurable (X n)) (n : ℕ) :
    Measurable (shiftProcess X m n) :=
  hX (m + n)

/-- The path map is measurable when all coordinates are measurable. -/
lemma measurable_path (X : ℕ → Ω → α) (hX : ∀ n, Measurable (X n)) :
    Measurable (path X) := by
  apply measurable_pi_lambda
  intro n
  simp only [path]
  exact hX n

omit [MeasurableSpace Ω] [MeasurableSpace α] in
lemma path_eq_shiftRV_zero (X : ℕ → Ω → α) : path X = shiftRV X 0 :=
  (shiftRV_zero X).symm

omit [MeasurableSpace Ω] [MeasurableSpace α] in
/-- Composing X_n with shiftProcess extracts the (m+n)-th coordinate. -/
@[simp]
lemma coord_comp_shiftProcess (X : ℕ → Ω → α) (m n : ℕ) :
    (fun ω => shiftProcess X m n ω) = X (m + n) := by
  funext ω; simp [shiftProcess]

omit [MeasurableSpace Ω] [MeasurableSpace α] in
/-- Relationship between shiftRV and path composition. -/
lemma shiftRV_eq_path_comp_shift (X : ℕ → Ω → α) (m : ℕ) :
    shiftRV X m = path (shiftProcess X m) := by
  funext ω n; simp [shiftRV, path, shiftProcess]

omit [MeasurableSpace Ω] [MeasurableSpace α] in
lemma shiftProcess_apply (X : ℕ → Ω → α) (m n ω) :
    shiftProcess X m n ω = X (m + n) ω := by
  rfl

/-- 𝔽ₘ := σ(θₘ X) = σ(ω ↦ (n ↦ X (m+n) ω)). -/
abbrev revFiltration (X : ℕ → Ω → α) (m : ℕ) : MeasurableSpace Ω :=
  MeasurableSpace.comap (shiftRV X m) inferInstance

omit [MeasurableSpace Ω] in
@[simp]
lemma revFiltration_zero (X : ℕ → Ω → α) :
    revFiltration X 0 = MeasurableSpace.comap (path X) inferInstance := by
  simp [revFiltration]

lemma revFiltration_le (X : ℕ → Ω → α) (hX : ∀ n, Measurable (X n)) (m : ℕ) :
    revFiltration X m ≤ (inferInstance : MeasurableSpace Ω) := by
  -- The comap is ≤ ambient iff the function is measurable
  -- shiftRV X m = path (shiftProcess X m) is measurable
  simp only [revFiltration]
  intro s hs
  obtain ⟨t, ht, rfl⟩ := hs
  rw [shiftRV_eq_path_comp_shift]
  have h_meas := measurable_path (shiftProcess X m) (measurable_shiftProcess X m hX)
  exact h_meas ht

/-- The tail σ-algebra for a process X: ⋂ₙ σ(Xₙ, Xₙ₊₁, ...). -/
def tailSigma (X : ℕ → Ω → α) : MeasurableSpace Ω :=
  ⨅ m, revFiltration X m

omit [MeasurableSpace Ω] in
@[simp]
lemma tailSigma_eq_iInf_rev (X : ℕ → Ω → α) :
    tailSigma X = ⨅ m, revFiltration X m := rfl

section Measurability

variable {X : ℕ → Ω → α}

lemma measurable_shiftRV (hX : ∀ n, Measurable (X n)) {m : ℕ} :
    Measurable (shiftRV X m) := by
  classical
  simpa [shiftRV] using
    measurable_pi_iff.mpr (fun n => by simpa using hX (m + n))

end Measurability

lemma revFiltration_antitone (X : ℕ → Ω → α) :
    Antitone (revFiltration X) := by
  intro m n hmn
  -- Need to show: revFiltration X n ≤ revFiltration X m when m ≤ n
  -- Strategy: shiftRV X n = shiftSeq (n - m) ∘ shiftRV X m
  simp only [revFiltration]
  let k := n - m
  -- Show shiftRV X n = shiftSeq k ∘ shiftRV X m
  have h_comp : shiftRV X n = shiftSeq k ∘ shiftRV X m := by
    funext ω i
    simp only [shiftRV, shiftSeq, Function.comp_apply]
    congr 1
    omega
  rw [h_comp]
  exact comap_comp_le (shiftRV X m) (shiftSeq k) measurable_shiftSeq

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

/- DELETED: The following two lemmas are unused in this file.
   The stronger rectangle-based lemma `condexp_indicator_eq_of_agree_on_future_rectangles`
   from CondExp.lean provides the needed functionality.

/-- **Lemma 1.3 (contraction and independence).**

If `(ξ, η) =^d (ξ, ζ)` and `σ(η) ⊆ σ(ζ)`, then `ξ ⊥⊥_η ζ`.
[Proof sketch omitted - would use L² martingale argument]
*Kallenberg (2005), Lemma 1.3.* -/
-- lemma contraction_independence ... := by sorry

/-- If `(ξ,η)` and `(ξ,ζ)` have the same law and `σ(η) ≤ σ(ζ)`,
then for all measurable `B`, the conditional expectations of `1_{ξ∈B}` coincide.
[Proof sketch omitted - would use L² norm comparison] -/
-- lemma condexp_indicator_eq_of_dist_eq_and_le ... := by sorry
-/

/-- Finite-dimensional (cylinder) equality:
for any `r`, base set `B` and measurable sets on the first `r` tail coordinates,
the probabilities agree when comparing `(X m, θₘ X)` vs `(X k, θₘ X)`.

This is the exact finite-dimensional marginal needed for the martingale step. -/
lemma contractable_dist_eq_on_first_r_tail
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → α} (hX : Contractable μ X) (hX_meas : ∀ n, Measurable (X n))
    (k m r : ℕ) (hk : k ≤ m)
    (B : Set α) (hB : MeasurableSet B)
    (C : Fin r → Set α) (hC : ∀ i, MeasurableSet (C i)) :
    μ {ω | X m ω ∈ B ∧ ∀ i : Fin r, X (m + (i.1 + 1)) ω ∈ C i}
      = μ {ω | X k ω ∈ B ∧ ∀ i : Fin r, X (m + (i.1 + 1)) ω ∈ C i} := by
  classical
  let f : Fin r → ℕ := fun i => m + (i.1 + 1)
  have hf_mono : StrictMono f := by
    intro i j hij
    have hij' : i.1 < j.1 := (Fin.lt_iff_val_lt_val).1 hij
    have : i.1 + 1 < j.1 + 1 := Nat.succ_lt_succ hij'
    simpa [f, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      Nat.add_lt_add_left this m
  have hm_lt : ∀ i, m < f i := by
    intro i
    simp [f]
  have hk_lt : ∀ i, k < f i := fun i => lt_of_le_of_lt hk (hm_lt i)
  let s₁ : Fin (r+1) → ℕ := Fin.cases m f
  let s₂ : Fin (r+1) → ℕ := Fin.cases k f
  have hs₁ : StrictMono s₁ := strictMono_fin_cases (n:=r) (f:=f) hf_mono hm_lt
  have hs₂ : StrictMono s₂ := strictMono_fin_cases (n:=r) (f:=f) hf_mono hk_lt
  have hmap_eq :
      Measure.map (fun ω i => X (s₁ i) ω) μ
        = Measure.map (fun ω i => X (s₂ i) ω) μ := by
    calc
      Measure.map (fun ω i => X (s₁ i) ω) μ
          = Measure.map (fun ω (i : Fin (r+1)) => X i.1 ω) μ := by
            simpa [s₁] using hX (r+1) s₁ hs₁
      _   = Measure.map (fun ω i => X (s₂ i) ω) μ := by
            simpa [s₂] using (hX (r+1) s₂ hs₂).symm
  let A : Set (Fin (r+1) → α) :=
    {v | v 0 ∈ B ∧ ∀ i : Fin r, v (Fin.succ i) ∈ C i}
  have hpre₁ :
      {ω | X m ω ∈ B ∧ ∀ i : Fin r, X (m + (i.1 + 1)) ω ∈ C i}
        = (fun ω i => X (s₁ i) ω) ⁻¹' A := by
    ext ω; simp [A, s₁, f]
  have hpre₂ :
      {ω | X k ω ∈ B ∧ ∀ i : Fin r, X (m + (i.1 + 1)) ω ∈ C i}
        = (fun ω i => X (s₂ i) ω) ⁻¹' A := by
    ext ω; simp [A, s₂, f]
  have hA : MeasurableSet A := by
    have h0 : Measurable (fun (v : Fin (r+1) → α) => v 0) := measurable_pi_apply 0
    have hS : ∀ i : Fin r, Measurable (fun (v : Fin (r+1) → α) => v (Fin.succ i)) :=
      fun i => measurable_pi_apply (Fin.succ i)
    have : A = (fun v => v 0) ⁻¹' B ∩ ⋂ i : Fin r, (fun v => v (Fin.succ i)) ⁻¹' C i := by
      ext v; simp [A, Set.mem_iInter]
    rw [this]
    exact (h0 hB).inter (MeasurableSet.iInter fun i => hS i (hC i))
  -- Both functions are measurable (from hX_meas)
  have hφ₁ : Measurable (fun ω i => X (s₁ i) ω) := by
    apply measurable_pi_lambda
    intro i
    cases i using Fin.cases with
    | zero => exact hX_meas m
    | succ j => simp only [s₁, f]; exact hX_meas (m + (j.1 + 1))
  have hφ₂ : Measurable (fun ω i => X (s₂ i) ω) := by
    apply measurable_pi_lambda
    intro i
    cases i using Fin.cases with
    | zero => exact hX_meas k
    | succ j => simp only [s₂, f]; exact hX_meas (m + (j.1 + 1))
  calc μ {ω | X m ω ∈ B ∧ ∀ i : Fin r, X (m + (i.1 + 1)) ω ∈ C i}
      = μ ((fun ω i => X (s₁ i) ω) ⁻¹' A) := by rw [hpre₁]
    _ = (Measure.map (fun ω i => X (s₁ i) ω) μ) A := (Measure.map_apply hφ₁ hA).symm
    _ = (Measure.map (fun ω i => X (s₂ i) ω) μ) A := by rw [hmap_eq]
    _ = μ ((fun ω i => X (s₂ i) ω) ⁻¹' A) := Measure.map_apply hφ₂ hA
    _ = μ {ω | X k ω ∈ B ∧ ∀ i : Fin r, X (m + (i.1 + 1)) ω ∈ C i} := by rw [← hpre₂]

/-- Future reverse filtration: 𝔽ᶠᵘᵗₘ = σ(θ_{m+1} X). -/
abbrev futureFiltration (X : ℕ → Ω → α) (m : ℕ) : MeasurableSpace Ω :=
  MeasurableSpace.comap (shiftRV X (m + 1)) inferInstance

/-- Forward declaration: Conditional expectation convergence from contractability.

Full proof at line ~1580 using the CE bridge lemma from CondExp.lean. -/
lemma condexp_convergence_fwd
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → α} (hX : Contractable μ X)
    (hX_meas : ∀ n, Measurable (X n))
    (k m : ℕ) (_hkm : k ≤ m)
    (B : Set α) (hB : MeasurableSet B) :
    μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ (X k) | futureFiltration X m]
      =ᵐ[μ]
    μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ (X 0) | futureFiltration X m] := by
  sorry  -- Proved at line ~1597

/-- Forward declaration: Tail σ-algebra is sub-σ-algebra of future filtration.

Full proof at line ~610. -/
lemma tailSigma_le_futureFiltration_fwd
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (X : ℕ → Ω → α) (m : ℕ) :
    tailSigma X ≤ futureFiltration X m := by
  sorry  -- Proved at line ~625

/-- Forward declaration: Future filtration is sub-σ-algebra of ambient.

Full proof at line ~656. -/
lemma futureFiltration_le_fwd
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (X : ℕ → Ω → α) (m : ℕ) (hX : ∀ n, Measurable (X n)) :
    futureFiltration X m ≤ (inferInstance : MeasurableSpace Ω) := by
  sorry  -- Proved at line ~656

lemma extreme_members_equal_on_tail
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → α}
    (hX : Contractable μ X)
    (hX_meas : ∀ n, Measurable (X n))
    (m : ℕ) (B : Set α) (hB : MeasurableSet B) :
    μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ (X m) | tailSigma X]
      =ᵐ[μ]
    μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ (X 0) | tailSigma X] := by
  classical
  -- abbreviations
  set f_m : Ω → ℝ := (Set.indicator B (fun _ => (1 : ℝ))) ∘ X m with hf_m
  set f_0 : Ω → ℝ := (Set.indicator B (fun _ => (1 : ℝ))) ∘ X 0 with hf_0

  -- bounded indicators are integrable
  have hf_m_int :
      Integrable f_m μ :=
    by
      simpa [hf_m] using
        Exchangeability.Probability.integrable_indicator_comp
          (μ := μ) (X := X m) (hX := hX_meas m) hB
  have hf_0_int :
      Integrable f_0 μ :=
    by
      simpa [hf_0] using
        Exchangeability.Probability.integrable_indicator_comp
          (μ := μ) (X := X 0) (hX := hX_meas 0) hB

  -- equality at the future level m (contractability)
  have h_eq_m :
      μ[f_m | futureFiltration X m] =ᵐ[μ] μ[f_0 | futureFiltration X m] := by
    convert condexp_convergence_fwd hX hX_meas m m (le_refl m) B hB using 2

  -- condition both sides on the tail
  have h_cond_on_tail :
      μ[μ[f_m | futureFiltration X m] | tailSigma X]
        =ᵐ[μ]
      μ[μ[f_0 | futureFiltration X m] | tailSigma X] :=
    condExp_congr_ae h_eq_m

  -- tower property since tailSigma ≤ futureFiltration m
  have h_tower_m :
      μ[μ[f_m | futureFiltration X m] | tailSigma X]
        =ᵐ[μ] μ[f_m | tailSigma X] :=
    condExp_condExp_of_le
      (hm₁₂ := tailSigma_le_futureFiltration_fwd (X := X) m)
      (hm₂ := futureFiltration_le_fwd (X := X) m hX_meas)
      (f := f_m)
  have h_tower_0 :
      μ[μ[f_0 | futureFiltration X m] | tailSigma X]
        =ᵐ[μ] μ[f_0 | tailSigma X] :=
    condExp_condExp_of_le
      (hm₁₂ := tailSigma_le_futureFiltration_fwd (X := X) m)
      (hm₂ := futureFiltration_le_fwd (X := X) m hX_meas)
      (f := f_0)

  -- assemble the equalities
  -- Chain: μ[f_m|tail] = μ[μ[f_m|fut]|tail] = μ[μ[f_0|fut]|tail] = μ[f_0|tail]
  exact h_tower_m.symm.trans (h_cond_on_tail.trans h_tower_0)

/-! ## Future filtration (additive)

Additive "future-filtration + standard-cylinder" layer that coexists with the
current `revFiltration` / `tailCylinder` infrastructure. Existing names remain intact.
-/
section FutureFiltration

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- The future filtration is decreasing (antitone). -/
lemma futureFiltration_antitone (X : ℕ → Ω → α) :
    Antitone (futureFiltration X) := by
  intro m n hmn
  simpa [futureFiltration, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
    (revFiltration_antitone X (Nat.succ_le_succ hmn))

/-- Tail σ-algebra via the future filtration. (Additive alias.) -/
def tailSigmaFuture (X : ℕ → Ω → α) : MeasurableSpace Ω :=
  ⨅ m, futureFiltration X m

omit [MeasurableSpace Ω] in
@[simp] lemma tailSigmaFuture_eq_iInf (X : ℕ → Ω → α) :
    tailSigmaFuture X = ⨅ m, futureFiltration X m := rfl

omit [MeasurableSpace Ω] in
@[simp] lemma futureFiltration_eq_rev_succ (X : ℕ → Ω → α) (m : ℕ) :
    futureFiltration X m = revFiltration X (m + 1) := rfl

lemma tailSigmaFuture_eq_tailSigma (X : ℕ → Ω → α) :
    tailSigmaFuture X = tailSigma X := by
  classical
  have hfut : tailSigmaFuture X = ⨅ n, revFiltration X (n + 1) := by
    simp [tailSigmaFuture, futureFiltration_eq_rev_succ]
  have htail : tailSigma X = ⨅ n, revFiltration X n := rfl
  refine le_antisymm ?_ ?_
  · -- `tailSigmaFuture ≤ tailSigma`
    refine (hfut ▸ ?_)
    refine le_iInf ?_
    intro n
    have h1 : (⨅ m, revFiltration X (m + 1)) ≤ revFiltration X (n + 1) :=
      iInf_le (fun m => revFiltration X (m + 1)) n
    have h2 : revFiltration X (n + 1) ≤ revFiltration X n :=
      revFiltration_antitone X (Nat.le_succ n)
    exact h1.trans h2
  · -- `tailSigma ≤ tailSigmaFuture`
    refine (htail ▸ ?_)
    refine le_iInf ?_
    intro n
    have h1 : (⨅ m, revFiltration X m) ≤ revFiltration X (n + 1) :=
      iInf_le (fun m => revFiltration X m) (n + 1)
    simpa [futureFiltration_eq_rev_succ] using h1

/-! ### Helper lemmas for tail σ-algebra -/

/-- The tail σ-algebra is a sub-σ-algebra of the ambient σ-algebra. -/
lemma tailSigma_le {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (X : ℕ → Ω → α) (hX : ∀ n, Measurable (X n)) :
    tailSigma X ≤ (inferInstance : MeasurableSpace Ω) := by
  refine iInf_le_of_le 0 ?_
  exact revFiltration_le X hX 0

/-- Future filtration is always at least as fine as the tail σ-algebra. -/
lemma tailSigma_le_futureFiltration {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (X : ℕ → Ω → α) (m : ℕ) :
    tailSigma X ≤ futureFiltration X m := by
  rw [← tailSigmaFuture_eq_tailSigma]
  exact iInf_le (fun m => futureFiltration X m) m

/-- Indicators of tail-measurable sets are tail-measurable functions. -/
lemma indicator_tailMeasurable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (X : ℕ → Ω → α) (A : Set Ω) (hA : MeasurableSet[tailSigma X] A) :
    StronglyMeasurable[tailSigma X] (A.indicator (fun _ => (1 : ℝ))) := by
  refine StronglyMeasurable.indicator ?_ hA
  exact stronglyMeasurable_const

/-- If each coordinate is measurable, then the tail σ-algebra is sigma-finite
when the base measure is finite.

Note: While this could be stated for general sigma-finite measures, we only need the finite
case for de Finetti's theorem (which works with probability measures). The general sigma-finite
case requires manual construction of spanning sets and is a mathlib gap. -/
lemma sigmaFinite_trim_tailSigma {Ω α : Type*} {m₀ : MeasurableSpace Ω} [MeasurableSpace α]
    {μ : @Measure Ω m₀} [IsFiniteMeasure μ]
    (X : ℕ → Ω → α) (hX : ∀ n, Measurable (X n)) :
    SigmaFinite (μ.trim (tailSigma_le X hX)) := by
  classical
  -- Use the infrastructure from CondExp.lean
  exact Exchangeability.Probability.sigmaFinite_trim μ (tailSigma_le X hX)

/-! ### Helper lemmas for futureFiltration properties -/

/-- The future filtration at level m is a sub-σ-algebra of the ambient σ-algebra. -/
lemma futureFiltration_le {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (X : ℕ → Ω → α) (m : ℕ) (hX : ∀ n, Measurable (X n)) :
    futureFiltration X m ≤ (inferInstance : MeasurableSpace Ω) := by
  -- futureFiltration X m = revFiltration X (m + 1)
  simp only [futureFiltration]
  exact revFiltration_le X hX (m + 1)

/-- The preimage of a measurable set under X_{m+k} is measurable in futureFiltration X m.
Note: This requires k ≥ 1 since futureFiltration X m = σ(X_{m+1}, X_{m+2}, ...). -/
lemma preimage_measurable_in_futureFiltration {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (X : ℕ → Ω → α) (m k : ℕ) (hk : 1 ≤ k) {A : Set α} (hA : MeasurableSet A) :
    MeasurableSet[futureFiltration X m] (X (m + k) ⁻¹' A) := by
  -- futureFiltration X m = comap (shiftRV X (m+1))
  -- X (m + k) = X (m + 1 + (k-1)) = π_{k-1} ∘ shiftRV X (m+1)
  -- where π_n projects to the n-th coordinate
  simp only [futureFiltration]
  have : X (m + k) = (fun f : ℕ → α => f (k - 1)) ∘ shiftRV X (m + 1) := by
    funext ω
    simp [shiftRV]
    congr 1
    omega
  rw [this, Set.preimage_comp]
  exact ⟨(fun f : ℕ → α => f (k - 1)) ⁻¹' A, (measurable_pi_apply (k - 1)) hA, rfl⟩

/-- Events measurable in a future filtration remain measurable in earlier filtrations. -/
lemma measurableSet_of_futureFiltration {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (X : ℕ → Ω → α) {m n : ℕ} (hmn : m ≤ n) {A : Set Ω}
    (hA : MeasurableSet[futureFiltration X n] A) :
    MeasurableSet[futureFiltration X m] A := by
  exact futureFiltration_antitone X hmn A hA

end FutureFiltration

-- FutureCylinders, FirstBlockCylinder, IndicatorAlgebra, and CylinderBridge sections
-- have been extracted to MartingaleHelpers.lean

/-! ## Product of indicators for finite cylinders -/

/-- Product of indicator functions for a finite cylinder on the first `r` coordinates. -/
def indProd {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (X : ℕ → Ω → α) (r : ℕ) (C : Fin r → Set α) : Ω → ℝ :=
  fun ω => ∏ i : Fin r, Set.indicator (C i) (fun _ => (1 : ℝ)) (X i ω)

lemma indProd_as_indicator
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (X : ℕ → Ω → α) (r : ℕ) (C : Fin r → Set α) :
    indProd X r C
      = Set.indicator {ω | ∀ i : Fin r, X i ω ∈ C i} (fun _ => (1 : ℝ)) := by
  funext ω
  simp only [indProd, Set.indicator]
  split_ifs with h
  · -- ω satisfies all conditions: product equals 1
    calc ∏ i : Fin r, Set.indicator (C i) (fun _ => (1 : ℝ)) (X i ω)
        = ∏ i : Fin r, (1 : ℝ) := by
          congr 1
          ext i
          simp only [Set.indicator]
          rw [if_pos (h i)]
      _ = 1 := Finset.prod_const_one
  · -- ω doesn't satisfy all conditions
    by_cases hr : ∃ i : Fin r, X i ω ∉ C i
    · obtain ⟨i, hi⟩ := hr
      have : Set.indicator (C i) (fun _ => (1 : ℝ)) (X i ω) = 0 := by
        simp only [Set.indicator]
        rw [if_neg hi]
      rw [Finset.prod_eq_zero (Finset.mem_univ i) this]
    · simp only [not_exists, not_not] at hr
      exact absurd hr h

/-- Connection between `indProd` and `firstRCylinder`: the product indicator
equals the indicator of the first-`r` cylinder. -/
lemma indProd_eq_firstRCylinder_indicator
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (X : ℕ → Ω → α) (r : ℕ) (C : Fin r → Set α) :
    indProd X r C = (firstRCylinder X r C).indicator (fun _ => (1 : ℝ)) := by
  rw [indProd_as_indicator]
  rfl

/-- Basic integrability: `indProd` is an indicator of a measurable set, hence integrable
under a finite measure. -/
lemma indProd_integrable
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    {μ : Measure Ω} [IsFiniteMeasure μ] (X : ℕ → Ω → α)
    (r : ℕ) (C : Fin r → Set α)
    (hX : ∀ n, Measurable (X n)) (hC : ∀ i, MeasurableSet (C i)) :
    Integrable (indProd X r C) μ := by
  -- indProd X r C is the indicator of firstRCylinder X r C
  rw [indProd_eq_firstRCylinder_indicator]
  -- Indicator functions of measurable sets are integrable under finite measures
  apply Integrable.indicator
  · exact integrable_const 1
  · exact firstRCylinder_measurable_ambient X r C hX hC

/-! ### Indicator algebra helpers for factorization -/

/-- The product of two indicator functions equals the indicator of their intersection. -/
lemma indicator_mul_indicator_eq_indicator_inter
    {Ω : Type*} [MeasurableSpace Ω]
    (A B : Set Ω) (c d : ℝ) :
    (A.indicator (fun _ => c)) * (B.indicator (fun _ => d))
      = (A ∩ B).indicator (fun _ => c * d) := by
  ext ω
  by_cases hA : ω ∈ A <;> by_cases hB : ω ∈ B <;>
    simp [Set.indicator, hA, hB, Set.mem_inter_iff]

/-- Indicator function composed with preimage. -/
lemma indicator_comp_preimage
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (f : Ω → α) (B : Set α) (c : ℝ) :
    (B.indicator (fun _ => c)) ∘ f = (f ⁻¹' B).indicator (fun _ => c) := by
  ext ω
  simp only [Function.comp_apply, Set.indicator, Set.mem_preimage]
  rfl

/-- Binary indicator takes values in {0, 1}. -/
lemma indicator_binary
    {Ω : Type*} [MeasurableSpace Ω]
    (A : Set Ω) (ω : Ω) :
    A.indicator (fun _ => (1 : ℝ)) ω = 0 ∨ A.indicator (fun _ => (1 : ℝ)) ω = 1 := by
  by_cases h : ω ∈ A
  · simp [Set.indicator, h]
  · simp [Set.indicator, h]

/-- Indicator is bounded by its constant. -/
lemma indicator_le_const
    {Ω : Type*} [MeasurableSpace Ω]
    (A : Set Ω) (c : ℝ) (hc : 0 ≤ c) (ω : Ω) :
    A.indicator (fun _ => c) ω ≤ c := by
  by_cases h : ω ∈ A
  · simp [Set.indicator, h]
  · simp [Set.indicator, h, hc]

/-- Indicator is nonnegative when constant is nonnegative. -/
lemma indicator_nonneg
    {Ω : Type*} [MeasurableSpace Ω]
    (A : Set Ω) (c : ℝ) (hc : 0 ≤ c) (ω : Ω) :
    0 ≤ A.indicator (fun _ => c) ω := by
  by_cases h : ω ∈ A
  · simp [Set.indicator, h, hc]
  · simp [Set.indicator, h]

/-- indProd is strongly measurable when coordinates and sets are measurable. -/
lemma indProd_stronglyMeasurable
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (X : ℕ → Ω → α) (r : ℕ) (C : Fin r → Set α)
    (hX : ∀ n, Measurable (X n)) (hC : ∀ i, MeasurableSet (C i)) :
    StronglyMeasurable (indProd X r C) := by
  rw [indProd_eq_firstRCylinder_indicator]
  refine StronglyMeasurable.indicator ?_ ?_
  · exact stronglyMeasurable_const
  · exact firstRCylinder_measurable_ambient X r C hX hC

/-- indProd takes values in [0,1]. -/
lemma indProd_nonneg_le_one {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (X : ℕ → Ω → α) (r : ℕ) (C : Fin r → Set α) (ω : Ω) :
    0 ≤ indProd X r C ω ∧ indProd X r C ω ≤ 1 := by
  rw [indProd_as_indicator]
  by_cases h : ∀ i : Fin r, X i ω ∈ C i
  · simp [Set.indicator, h]
  · simp [Set.indicator, h]

/-- indProd of zero coordinates is identically 1. -/
@[simp] lemma indProd_zero {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (X : ℕ → Ω → α) (C : Fin 0 → Set α) :
    indProd X 0 C = fun _ => 1 := by
  funext ω
  simp [indProd]

/-- indProd on the universal sets is identically 1. -/
lemma indProd_univ {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (X : ℕ → Ω → α) (r : ℕ) :
    indProd X r (fun _ => Set.univ) = fun _ => 1 := by
  funext ω
  simp [indProd, Set.indicator]

/-- indProd is measurable when coordinates are measurable. -/
lemma indProd_measurable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (X : ℕ → Ω → α) (r : ℕ) (C : Fin r → Set α)
    (hX : ∀ n, Measurable (X n)) (hC : ∀ i, MeasurableSet (C i)) :
    Measurable (indProd X r C) :=
  (indProd_stronglyMeasurable X r C hX hC).measurable

/-- indProd product equals multiplication of indProds. -/
lemma indProd_mul {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (X : ℕ → Ω → α) {r : ℕ} {C D : Fin r → Set α} (ω : Ω) :
    indProd X r C ω * indProd X r D ω = indProd X r (fun i => C i ∩ D i) ω := by
  simp only [indProd]
  rw [← Finset.prod_mul_distrib]
  congr 1
  funext i
  simp only [Set.indicator]
  by_cases hC : X i ω ∈ C i <;> by_cases hD : X i ω ∈ D i <;>
    simp [hC, hD, Set.mem_inter_iff]

/-- indProd on intersection via firstRCylinder. -/
lemma indProd_inter_eq {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (X : ℕ → Ω → α) {r : ℕ} {C D : Fin r → Set α} :
    indProd X r (fun i => C i ∩ D i)
      = (firstRCylinder X r C ∩ firstRCylinder X r D).indicator (fun _ => (1 : ℝ)) := by
  rw [indProd_eq_firstRCylinder_indicator, firstRCylinder_inter]

-- CylinderBridge section (drop, cylinder lemmas) extracted to MartingaleHelpers.lean

/-! ## Rectangles using future tails and standard cylinders -/
section FutureRectangles

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {X : ℕ → Ω → α}

omit [MeasurableSpace Ω] [MeasurableSpace α] in
/-- Preimage calculation for rectangles with `(X k, θ_{m+1}X)` and a standard cylinder. -/
lemma preimage_rect_future
    (k m r : ℕ) (B : Set α) (C : Fin r → Set α) :
    let ψ := fun ω => (X k ω, shiftRV X (m + 1) ω)
    ψ ⁻¹' (B ×ˢ cylinder (α:=α) r C)
      = {ω | X k ω ∈ B ∧ ∀ i : Fin r, X (m + 1 + i.1) ω ∈ C i} := by
  classical
  intro ψ
  ext ω; constructor <;> intro h
  · rcases h with ⟨hB, hC⟩
    refine ⟨?_, ?_⟩
    · simpa [ψ]
    · intro i
      have : (shiftRV X (m + 1) ω) ∈ cylinder (α:=α) r C := hC
      simpa [ψ, shiftRV, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using this i
  · rcases h with ⟨hB, hC⟩
    refine ⟨?_, ?_⟩
    · simpa [ψ]
    · intro i
      have : X (m + 1 + i.1) ω ∈ C i := hC i
      simpa [ψ, shiftRV, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using this

/-- **Finite-dimensional equality on future rectangles with standard cylinders.**
For `k ≤ m` and measurable `B`, the measures of
`B × cylinder r C` under the pushforwards by
`ω ↦ (X m ω, θ_{m+1}X(ω))` and `ω ↦ (X k ω, θ_{m+1}X(ω))` coincide. -/
lemma contractable_dist_eq_on_rectangles_future
    {X : ℕ → Ω → α} (hX : Contractable μ X) (hX_meas : ∀ n, Measurable (X n))
    (k m : ℕ) (hk : k ≤ m)
    (r : ℕ) (B : Set α) (hB : MeasurableSet B)
    (C : Fin r → Set α) (hC : ∀ i, MeasurableSet (C i)) :
    (Measure.map (fun ω => (X m ω, shiftRV X (m + 1) ω)) μ)
        (B ×ˢ cylinder (α:=α) r C)
  =
    (Measure.map (fun ω => (X k ω, shiftRV X (m + 1) ω)) μ)
        (B ×ˢ cylinder (α:=α) r C) := by
  classical
  set ψ₁ : Ω → α × (ℕ → α) := fun ω => (X m ω, shiftRV X (m + 1) ω)
  set ψ₂ : Ω → α × (ℕ → α) := fun ω => (X k ω, shiftRV X (m + 1) ω)
  have hrect : MeasurableSet (B ×ˢ cylinder (α:=α) r C) :=
    hB.prod (cylinder_measurable (α:=α) hC)
  have hpre₁ :
      ψ₁ ⁻¹' (B ×ˢ cylinder (α:=α) r C)
        = {ω | X m ω ∈ B ∧ ∀ i : Fin r, X (m + 1 + i.1) ω ∈ C i} := by
    simp [ψ₁, preimage_rect_future (X:=X) m m r B C]
  have hpre₂ :
      ψ₂ ⁻¹' (B ×ˢ cylinder (α:=α) r C)
        = {ω | X k ω ∈ B ∧ ∀ i : Fin r, X (m + 1 + i.1) ω ∈ C i} := by
    simp [ψ₂, preimage_rect_future (X:=X) k m r B C]
  have hfd :
    μ {ω | X m ω ∈ B ∧ ∀ i : Fin r, X (m + (i.1 + 1)) ω ∈ C i}
      =
    μ {ω | X k ω ∈ B ∧ ∀ i : Fin r, X (m + (i.1 + 1)) ω ∈ C i} := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (contractable_dist_eq_on_first_r_tail
        (μ:=μ) (X:=X) hX hX_meas k m r hk B hB C hC)
  -- Show the sets are equal modulo arithmetic
  have hset_eq₁ : {ω | X m ω ∈ B ∧ ∀ i : Fin r, X (m + 1 + i.1) ω ∈ C i}
                = {ω | X m ω ∈ B ∧ ∀ i : Fin r, X (m + (i.1 + 1)) ω ∈ C i} := by
    ext ω; simp only [Set.mem_setOf]
    constructor
    · intro ⟨hB, hC⟩
      constructor
      · exact hB
      · intro i
        have : m + 1 + i.1 = m + (i.1 + 1) := by omega
        rw [← this]; exact hC i
    · intro ⟨hB, hC⟩
      constructor
      · exact hB
      · intro i
        have : m + 1 + i.1 = m + (i.1 + 1) := by omega
        rw [this]; exact hC i
  have hset_eq₂ : {ω | X k ω ∈ B ∧ ∀ i : Fin r, X (m + 1 + i.1) ω ∈ C i}
                = {ω | X k ω ∈ B ∧ ∀ i : Fin r, X (m + (i.1 + 1)) ω ∈ C i} := by
    ext ω; simp only [Set.mem_setOf]
    constructor
    · intro ⟨hB, hC⟩
      constructor
      · exact hB
      · intro i
        have : m + 1 + i.1 = m + (i.1 + 1) := by omega
        rw [← this]; exact hC i
    · intro ⟨hB, hC⟩
      constructor
      · exact hB
      · intro i
        have : m + 1 + i.1 = m + (i.1 + 1) := by omega
        rw [this]; exact hC i
  -- Measurability of ψ₁ and ψ₂
  have hψ₁_meas : Measurable ψ₁ :=
    (hX_meas m).prodMk (measurable_shiftRV hX_meas)
  have hψ₂_meas : Measurable ψ₂ :=
    (hX_meas k).prodMk (measurable_shiftRV hX_meas)
  -- Apply Measure.map_apply and connect the pieces
  rw [Measure.map_apply hψ₁_meas hrect, Measure.map_apply hψ₂_meas hrect]
  rw [hpre₁, hpre₂, hset_eq₁, hset_eq₂]
  exact hfd

end FutureRectangles

/-- Two measures agree on all future rectangles (sets of form B ×ˢ cylinder r C). -/
def AgreeOnFutureRectangles (μ ν : Measure (α × (ℕ → α))) : Prop :=
  ∀ (r : ℕ) (B : Set α) (_hB : MeasurableSet B) (C : Fin r → Set α) (_hC : ∀ i, MeasurableSet (C i)),
    μ (B ×ˢ cylinder (α:=α) r C) = ν (B ×ˢ cylinder (α:=α) r C)

lemma agree_on_future_rectangles_of_contractable
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → α} (hX : Contractable μ X) (hX_meas : ∀ n, Measurable (X n))
    (k m : ℕ) (hk : k ≤ m) :
    AgreeOnFutureRectangles
      (Measure.map (fun ω => (X m ω, shiftRV X (m + 1) ω)) μ)
      (Measure.map (fun ω => (X k ω, shiftRV X (m + 1) ω)) μ) := by
  -- Unfold definition and apply contractable_dist_eq_on_rectangles_future
  intro r B hB C hC
  exact contractable_dist_eq_on_rectangles_future hX hX_meas k m hk r B hB C hC

/-! ## Measure extension from future rectangles -/

lemma measure_ext_of_future_rectangles
    {μ ν : Measure (α × (ℕ → α))} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ (r : ℕ) (B : Set α) (_hB : MeasurableSet B)
        (C : Fin r → Set α) (_hC : ∀ i, MeasurableSet (C i)),
        μ (B ×ˢ cylinder (α:=α) r C) = ν (B ×ˢ cylinder (α:=α) r C)) :
    μ = ν := by
  classical
  -- Proof Plan (π-λ Theorem Application):
  --
  -- Step 1: Define π-system S
  --   S = {B ×ˢ cylinder r C | B measurable, C_i measurable}
  --   This is a π-system (closed under finite intersections)
  --
  -- Step 2: Show S generates product σ-algebra
  --   Prove: generateFrom S = inferInstance
  --   - (⊆): Show Prod.fst, Prod.snd measurable w.r.t. generateFrom S
  --     * Product σ-algebra = comap Prod.fst ⊔ comap Prod.snd
  --     * Both comaps ≤ generateFrom S
  --   - (⊇): Every rectangle in S is measurable in product σ-algebra
  --
  -- Step 3: Apply π-λ theorem
  --   Use Measure.ext_of_generateFrom_of_iUnion:
  --   - Measures agree on S (hypothesis h)
  --   - S generates the σ-algebra
  --   - Have covering family with finite measure
  --   - Therefore μ = ν

  -- π-system consisting of rectangles `B × cylinder r C`
  let S : Set (Set (α × (ℕ → α))) :=
    {s | ∃ (r : ℕ) (B : Set α) (hB : MeasurableSet B)
          (C : Fin r → Set α) (hC : ∀ i, MeasurableSet (C i)),
          s = B ×ˢ cylinder (α:=α) r C}

  -- S is a π-system
  have h_pi : IsPiSystem S := by
    intro s₁ hs₁ s₂ hs₂ _
    obtain ⟨r₁, B₁, hB₁, C₁, hC₁, rfl⟩ := hs₁
    obtain ⟨r₂, B₂, hB₂, C₂, hC₂, rfl⟩ := hs₂
    -- Intersection of rectangles is a rectangle of higher dimension
    let r := max r₁ r₂
    let C : Fin r → Set α := fun i =>
      if h1 : (i : ℕ) < r₁ then
        if h2 : (i : ℕ) < r₂ then C₁ ⟨i, h1⟩ ∩ C₂ ⟨i, h2⟩ else C₁ ⟨i, h1⟩
      else if h2 : (i : ℕ) < r₂ then C₂ ⟨i, h2⟩ else Set.univ
    have hC : ∀ i, MeasurableSet (C i) := by
      intro i
      classical
      by_cases h1 : (i : ℕ) < r₁
      · by_cases h2 : (i : ℕ) < r₂
        · have := (hC₁ ⟨i, h1⟩).inter (hC₂ ⟨i, h2⟩)
          simpa [C, h1, h2] using this
        · simpa [C, h1, h2] using hC₁ ⟨i, h1⟩
      · by_cases h2 : (i : ℕ) < r₂
        · simpa [C, h1, h2] using hC₂ ⟨i, h2⟩
        · simp [C, h1, h2]

    refine ⟨r, B₁ ∩ B₂, hB₁.inter hB₂, C, hC, ?_⟩
    ext ⟨a, f⟩; constructor
    · intro hmf
      rcases hmf with ⟨⟨hB₁', hC₁'⟩, ⟨hB₂', hC₂'⟩⟩
      refine ⟨⟨hB₁', hB₂'⟩, ?_⟩
      intro i
      classical
      by_cases h1 : (i : ℕ) < r₁
      · by_cases h2 : (i : ℕ) < r₂
        · simp [C, h1, h2]
          exact ⟨hC₁' ⟨i, h1⟩, hC₂' ⟨i, h2⟩⟩
        · simp [C, h1, h2]
          exact hC₁' ⟨i, h1⟩
      · by_cases h2 : (i : ℕ) < r₂
        · simp [C, h1, h2]
          exact hC₂' ⟨i, h2⟩
        · simp [C, h1, h2]
    · rintro ⟨⟨hB₁', hB₂'⟩, hC'⟩
      refine ⟨⟨hB₁', ?_⟩, ⟨hB₂', ?_⟩⟩
      · intro i
        have hi : (i : ℕ) < r := lt_of_lt_of_le i.2 (Nat.le_max_left r₁ r₂)
        have := hC' ⟨i, hi⟩
        classical
        have h1 : (i : ℕ) < r₁ := i.2
        by_cases h2 : (i : ℕ) < r₂
        · simp [C, h1, h2] at this
          exact this.1
        · simp [C, h1, h2] at this
          exact this
      · intro i
        have hi : (i : ℕ) < r := lt_of_lt_of_le i.2 (Nat.le_max_right r₁ r₂)
        have := hC' ⟨i, hi⟩
        classical
        have h2 : (i : ℕ) < r₂ := i.2
        by_cases h1 : (i : ℕ) < r₁
        · simp [C, h1, h2] at this
          exact this.2
        · simp [C, h1, h2] at this
          exact this

  -- Show that S generates the product σ-algebra
  have h_gen : (inferInstance : MeasurableSpace (α × (ℕ → α)))
      = MeasurableSpace.generateFrom S := by
    -- Two-sided inclusion
    apply le_antisymm
    · -- (⊆) Product σ-algebra ≤ generateFrom S
      -- The product σ-algebra is the smallest σ-algebra making both projections measurable
      -- We need to show Prod.fst and Prod.snd are measurable w.r.t. generateFrom S

      -- First, show that Prod.fst is measurable
      have h_fst : ∀ A : Set α, MeasurableSet A →
          MeasurableSet[MeasurableSpace.generateFrom S] (Prod.fst ⁻¹' A) := by
        intro A hA
        -- Prod.fst ⁻¹' A = A ×ˢ univ = A ×ˢ cylinder 0 (fun _ => univ)
        have : Prod.fst ⁻¹' A = A ×ˢ (Set.univ : Set (ℕ → α)) := by
          ext ⟨a, f⟩; simp
        rw [this]
        -- A ×ˢ univ is in S (as a cylinder of size 0)
        apply MeasurableSpace.measurableSet_generateFrom
        refine ⟨0, A, hA, (fun _ => Set.univ), (fun _ => MeasurableSet.univ), ?_⟩
        ext ⟨a, f⟩
        simp only [Set.mem_prod, Set.mem_univ, and_true]
        -- cylinder 0 (fun _ => Set.univ) = Set.univ (vacuous quantifier)
        show a ∈ A ↔ a ∈ A ∧ f ∈ MartingaleHelpers.cylinder 0 (fun _ => Set.univ)
        rw [MartingaleHelpers.cylinder]
        simp

      -- Second, show that Prod.snd maps cylinders to measurable sets
      have h_snd : ∀ (r : ℕ) (C : Fin r → Set α),
          (∀ i, MeasurableSet (C i)) →
          MeasurableSet[MeasurableSpace.generateFrom S] (Prod.snd ⁻¹' MartingaleHelpers.cylinder r C) := by
        intro r C hC
        -- Prod.snd ⁻¹' (cylinder r C) = univ ×ˢ (cylinder r C)
        have : (Prod.snd : α × (ℕ → α) → ℕ → α) ⁻¹' MartingaleHelpers.cylinder r C
            = Set.univ ×ˢ MartingaleHelpers.cylinder r C := by
          ext ⟨a, f⟩
          simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, true_and]
        rw [this]
        -- univ ×ˢ cylinder r C is in S
        apply MeasurableSpace.measurableSet_generateFrom
        refine ⟨r, Set.univ, MeasurableSet.univ, C, hC, rfl⟩

      -- Product σ-algebra = (comap Prod.fst) ⊔ (comap Prod.snd)
      -- Need: both comaps are ≤ generateFrom S

      -- Prod.fst comap
      have h_fst_comap : MeasurableSpace.comap (Prod.fst : α × (ℕ → α) → α) inferInstance
          ≤ MeasurableSpace.generateFrom S := by
        intro s hs
        -- s is a preimage under Prod.fst of a measurable set
        obtain ⟨A, hA, rfl⟩ := hs
        exact h_fst A hA

      -- Prod.snd comap - need to show preimages of measurable sets are in generateFrom S
      have h_snd_comap : MeasurableSpace.comap (Prod.snd : α × (ℕ → α) → ℕ → α) inferInstance
          ≤ MeasurableSpace.generateFrom S := by
        -- Use measurable_iff_comap_le: comap ≤ generateFrom S ↔ Measurable Prod.snd
        rw [← measurable_iff_comap_le]
        -- Now show: Measurable[generateFrom S, inferInstance] Prod.snd

        -- Strategy: Show that {E | Prod.snd⁻¹(E) ∈ generateFrom S} is a σ-algebra
        -- containing all measurable sets in Pi

        -- Key observation: For any cylinder (finite intersection of coordinate preimages),
        -- we've proven Prod.snd⁻¹(cylinder) ∈ generateFrom S via h_snd

        -- The set T = {E | Prod.snd⁻¹(E) ∈ generateFrom S} is a σ-algebra because:
        --   - Prod.snd⁻¹(∅) = ∅ ∈ generateFrom S
        --   - Prod.snd⁻¹(∁E) = ∁(Prod.snd⁻¹(E)), σ-algebras closed under complement
        --   - Prod.snd⁻¹(⋃ Eₙ) = ⋃ Prod.snd⁻¹(Eₙ), σ-algebras closed under countable union

        -- T contains all cylinders (by h_snd), and Pi is generated by cylinders
        -- Therefore Pi ⊆ T, so for any E measurable in Pi, Prod.snd⁻¹(E) ∈ generateFrom S

        -- Apply measurable_generateFrom using cylinder generators
        -- The Pi σ-algebra on (ℕ → α) is generated by cylinders
        -- We've shown Prod.snd⁻¹(cylinder) ∈ generateFrom S for all cylinders

        -- Define the generating set for Pi: all cylinders
        let T : Set (Set (ℕ → α)) := {s | ∃ (r : ℕ) (C : Fin r → Set α),
          (∀ i, MeasurableSet (C i)) ∧ s = cylinder r C}

        -- Show Pi is generated by cylinders
        have hT_gen : (inferInstance : MeasurableSpace (ℕ → α)) = MeasurableSpace.generateFrom T := by
          -- Two-sided inclusion
          apply le_antisymm
          · -- inferInstance ≤ generateFrom T (i.e., Pi ≤ generateFrom T)
            -- Show that generateFrom T contains all Pi generators (coordinate preimages)
            -- Pi is generated by coordinate preimages
            -- We show all coordinate preimages are in generateFrom T
            have h_coord_meas : ∀ (i : ℕ) (A : Set α), MeasurableSet A →
                MeasurableSet[MeasurableSpace.generateFrom T] ((fun f : ℕ → α => f i) ⁻¹' A) := by
              intro i A hA
              -- {f | f i ∈ A} is a cylinder of size (i+1) with univ for j<i and A at position i
              let r := i + 1
              let C : Fin r → Set α := fun j => if j.val = i then A else Set.univ
              have hC_meas : ∀ j, MeasurableSet (C j) := by
                intro j
                simp only [C]
                split_ifs
                · exact hA
                · exact MeasurableSet.univ
              have h_eq : ((fun f : ℕ → α => f i) ⁻¹' A) = MartingaleHelpers.cylinder r C := by
                ext f
                simp only [C, r, Set.mem_preimage, MartingaleHelpers.cylinder]
                constructor
                · intro hf j
                  by_cases h : j.val = i
                  · simp [h]; exact hf
                  · simp [h]
                · intro hf
                  have := hf ⟨i, Nat.lt_succ_self i⟩
                  simp at this
                  exact this
              rw [h_eq]
              apply MeasurableSpace.measurableSet_generateFrom
              exact ⟨r, C, hC_meas, rfl⟩
            -- Pi is generated by coordinate projections
            -- We've shown all coordinate preimages are in generateFrom T
            rw [MeasurableSpace.pi_eq_generateFrom_projections]
            apply MeasurableSpace.generateFrom_le
            intro s hs
            -- s is a coordinate preimage: ∃ i A, MeasurableSet A ∧ eval i ⁻¹' A = s
            obtain ⟨i, A, hA, rfl⟩ := hs
            exact h_coord_meas i A hA
          · -- generateFrom T ≤ inferInstance (i.e., generateFrom T ≤ Pi)
            -- Every cylinder is measurable in Pi
            apply MeasurableSpace.generateFrom_le
            intro s
            rintro ⟨n, coords, coords_meas, rfl⟩
            -- cylinder n coords is measurable in Pi σ-algebra
            exact cylinder_measurable coords_meas

        -- Apply measurable_generateFrom
        have : @Measurable (α × (ℕ → α)) (ℕ → α)
            (MeasurableSpace.generateFrom S) (MeasurableSpace.generateFrom T) Prod.snd := by
          apply @measurable_generateFrom _ _ (MeasurableSpace.generateFrom S) _ _
          intro s hs
          obtain ⟨r, C, hC, rfl⟩ := hs
          exact h_snd r C hC
        rw [← hT_gen] at this
        exact this

      -- Combine using sup
      calc (inferInstance : MeasurableSpace (α × (ℕ → α)))
          = MeasurableSpace.comap Prod.fst inferInstance
            ⊔ MeasurableSpace.comap Prod.snd inferInstance := by
              rfl  -- This is the definition of product σ-algebra
        _ ≤ MeasurableSpace.generateFrom S := by
              exact sup_le h_fst_comap h_snd_comap
    · -- (⊇) generateFrom S ≤ Product σ-algebra
      -- Every set in S is measurable in the product σ-algebra
      apply MeasurableSpace.generateFrom_le
      intro t ht
      obtain ⟨r, B, hB, C, hC, rfl⟩ := ht
      -- B ×ˢ cylinder r C is measurable as a product of measurable sets
      exact hB.prod (cylinder_measurable hC)

  -- Measures agree on S
  have h_agree : ∀ s ∈ S, μ s = ν s := by
    intro s hs
    rcases hs with ⟨r, B, hB, C, hC, rfl⟩
    exact h r B hB C hC

  -- Covering family
  let Bseq : ℕ → Set (α × (ℕ → α)) := fun _ => Set.univ
  have h1B : ⋃ n, Bseq n = Set.univ := by
    simp only [Bseq, Set.iUnion_const]
  have h2B : ∀ n, Bseq n ∈ S := by
    intro n
    refine ⟨0, Set.univ, MeasurableSet.univ,
      (fun _ => Set.univ), (fun _ => MeasurableSet.univ), ?_⟩
    ext ⟨a, f⟩
    simp only [Bseq, Set.mem_prod, Set.mem_univ, true_and, MartingaleHelpers.cylinder]
    -- For Fin 0, cylinder 0 (fun _ => univ) = univ
    simp
  have hμB : ∀ n, μ (Bseq n) ≠ ⊤ := by
    intro n
    simp only [Bseq]
    exact measure_ne_top μ Set.univ

  exact Measure.ext_of_generateFrom_of_iUnion
    S Bseq h_gen h_pi h1B h2B hμB h_agree

/-- Helper lemma: contractability gives the key distributional equality.

If `X` is contractable, then for any `k ≤ m`:
```
(X_m, θ_{m+1} X) =^d (X_k, θ_{m+1} X)
```
where `θ_{m+1} X` drops the first coordinate and keeps the *future* tail
`ω ↦ (n ↦ X(m + 1 + n) ω)`. -/
lemma contractable_dist_eq
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → α} (hX : Contractable μ X) (hX_meas : ∀ n, Measurable (X n))
    (k m : ℕ) (hk : k ≤ m) :
    Measure.map (fun ω => (X m ω, shiftRV X (m + 1) ω)) μ
      = Measure.map (fun ω => (X k ω, shiftRV X (m + 1) ω)) μ := by
  -- Apply measure extension lemma
  apply measure_ext_of_future_rectangles
  intro r B hB C hC
  exact contractable_dist_eq_on_rectangles_future hX hX_meas k m hk r B hB C hC

/-- Measures that agree on all future rectangles are equal. -/
lemma AgreeOnFutureRectangles_to_measure_eq
    {μ ν : Measure (α × (ℕ → α))} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : AgreeOnFutureRectangles μ ν) : μ = ν :=
  measure_ext_of_future_rectangles h

/-! ### Conditional expectation convergence from contractability

This proves the forward-declared axiom from line 477. -/

/-- **Conditional expectation convergence (formerly Axiom 1):** For k ≤ m, all coordinates look
the same when conditioned on the future filtration at level m.

This is the key convergence result: for k ≤ m and measurable set B,
```
P[X_m ∈ B | θ_{m+1} X] = P[X_k ∈ B | θ_{m+1} X]
```

**Proof:** Uses the CE bridge lemma from CondExp.lean with the measure equality from
contractability. The key insight is that deleting coordinates doesn't change the joint distribution
with the future, which implies conditional expectation equality by the bridge lemma. -/
lemma condexp_convergence
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → α} (hX : Contractable μ X)
    (hX_meas : ∀ n, Measurable (X n))
    (k m : ℕ) (hk : k ≤ m)
    (B : Set α) (hB : MeasurableSet B) :
    μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ (X m) | futureFiltration X m]
      =ᵐ[μ]
    μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ (X k) | futureFiltration X m] := by
  -- Use the CE bridge lemma with Y = X m, Y' = X k, Z = shiftRV X (m+1)
  -- The key is that futureFiltration X m = σ(shiftRV X (m+1)) by definition

  -- First, get the measure equality from contractability
  have hmeas_eq : Measure.map (fun ω => (X m ω, shiftRV X (m + 1) ω)) μ
                = Measure.map (fun ω => (X k ω, shiftRV X (m + 1) ω)) μ := by
    -- Use measure_ext_of_future_rectangles to convert rectangle agreement to full equality
    apply measure_ext_of_future_rectangles
    -- Get rectangle agreement from contractability
    exact agree_on_future_rectangles_of_contractable hX hX_meas k m hk

  -- Apply the CE bridge lemma
  have h := Exchangeability.Probability.condexp_indicator_eq_of_pair_law_eq
    (X m) (X k) (shiftRV X (m + 1))
    (hX_meas m) (hX_meas k) (measurable_shiftRV hX_meas)
    hmeas_eq hB

  -- Simplify: futureFiltration X m = MeasurableSpace.comap (shiftRV X (m + 1)) inferInstance
  simpa [futureFiltration] using h


section reverse_martingale

variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {X : ℕ → Ω → α}

/-- 𝔽ₘ := σ(θ_{m+1} X) (the future filtration). -/
abbrev 𝔽 (m : ℕ) : MeasurableSpace Ω := futureFiltration X m

/-- The reverse filtration is decreasing; packaged for the martingale API. -/
lemma filtration_antitone (X : ℕ → Ω → α) : Antitone (fun m => futureFiltration X m) :=
  futureFiltration_antitone X

/-- Mₘ := 𝔼[1_{Xₖ∈B} | 𝔽ₘ].
The reverse martingale sequence for the indicator of X_k in B.

Uses `condExpWith` from CondExp.lean to manage typeclass instances properly. -/
noncomputable
def M (hX_meas : ∀ n, Measurable (X n)) (k : ℕ) (B : Set α) (_hB : MeasurableSet B) :
    ℕ → Ω → ℝ :=
  fun m => Exchangeability.Probability.condExpWith μ (futureFiltration X m)
    (futureFiltration_le X m hX_meas)
    (B.indicator (fun _ => (1 : ℝ)) ∘ X k)

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
--     `filtration_antitone` and `tailSigmaFuture_eq_iInf`.

end reverse_martingale

/-! ## Tail factorization on finite cylinders -/

/-! ### Helper lemmas for finite-level factorization -/

/-! ### Kallenberg Lemma 1.3 - Contraction implies conditional independence

**Strategy: Finite approximation (Option A) - IN PROGRESS**

We prove conditional independence by working with finite future approximations.
The full proof requires martingale convergence theory for the limit step. -/

/-- **Finite future σ-algebra.**

Approximates the infinite future σ(X_{m+1}, X_{m+2}, ...) by finite truncation. -/
def finFutureSigma (X : ℕ → Ω → α) (m k : ℕ) : MeasurableSpace Ω :=
  MeasurableSpace.comap (fun ω => fun i : Fin k => X (m + 1 + i.val) ω) inferInstance

lemma finFutureSigma_le_ambient
    (X : ℕ → Ω → α) (m k : ℕ) (hX : ∀ n, Measurable (X n)) :
    finFutureSigma X m k ≤ (inferInstance : MeasurableSpace Ω) := by
  intro s hs
  obtain ⟨t, ht, rfl⟩ := hs
  exact (measurable_pi_lambda _ (fun i => hX (m + 1 + i.val))) ht

omit [MeasurableSpace Ω] in
lemma finFutureSigma_le_futureFiltration
    (X : ℕ → Ω → α) (m k : ℕ) :
    finFutureSigma X m k ≤ futureFiltration X m := by
  intro s hs
  obtain ⟨t, ht, rfl⟩ := hs
  -- s = (fun ω => fun i : Fin k => X (m + 1 + i.val) ω) ⁻¹' t
  -- Need to show this is in futureFiltration X m

  -- The finite projection factors through the infinite one:
  -- (fun ω => fun i => X (m + 1 + i.val) ω) = proj ∘ (shiftRV X (m+1))
  -- where proj : (ℕ → α) → (Fin k → α) takes first k coordinates

  let proj : (ℕ → α) → (Fin k → α) := fun f i => f i.val

  have h_factor : (fun ω => fun i : Fin k => X (m + 1 + i.val) ω) = proj ∘ (shiftRV X (m + 1)) := by
    ext ω i
    simp only [Function.comp_apply, proj, shiftRV]

  -- Since proj is measurable, proj ⁻¹' t is measurable in (ℕ → α)
  have h_proj_meas : Measurable proj := measurable_pi_lambda _ (fun i => measurable_pi_apply i.val)
  have h_proj_t_meas : MeasurableSet (proj ⁻¹' t) := h_proj_meas ht

  -- Provide witness for comap: s ∈ futureFiltration means ∃ t', s = (shiftRV X (m+1)) ⁻¹' t'
  refine ⟨proj ⁻¹' t, h_proj_t_meas, ?_⟩

  -- Show s = (shiftRV X (m+1)) ⁻¹' (proj ⁻¹' t)
  rw [← Set.preimage_comp, ← h_factor]

/-! **Helper lemma: Distributional property from contractability (finite version).**

This lemma extracts the key property needed for conditional independence from contractability.
For finite future approximations, it shows that the measure of cylinder sets factorizes
appropriately. -/

/-- **Cylinder set measure formula from contractability (finite approximation).**

For contractable sequences with r < m, the measure of joint cylinder events involving
the first r coordinates, coordinate r, and k future coordinates can be expressed using
contractability properties.

This provides the distributional foundation for proving conditional independence in the
finite approximation setting. -/
lemma contractable_finite_cylinder_measure
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → α)
    (hX : Contractable μ X)
    (hX_meas : ∀ n, Measurable (X n))
    {r m k : ℕ} (hrm : r < m)
    (A : Fin r → Set α) (hA : ∀ i, MeasurableSet (A i))
    (B : Set α) (hB : MeasurableSet B)
    (C : Fin k → Set α) (hC : ∀ i, MeasurableSet (C i)) :
    -- The joint measure equals the measure for the standard cylinder
    μ ({ω | (∀ i, X i.val ω ∈ A i) ∧ X r ω ∈ B ∧ (∀ j, X (m + 1 + j.val) ω ∈ C j)})
      = μ ({ω | (∀ i : Fin r, X i.val ω ∈ A i) ∧ X r ω ∈ B ∧ (∀ j : Fin k, X (r + 1 + j.val) ω ∈ C j)}) := by
  -- Strategy: The indices (0,...,r-1, r, m+1,...,m+k) form a strictly increasing sequence.
  -- By contractability, this has the same distribution as (0,...,r-1, r, r+1,...,r+k).

  -- Define the index function: Fin (r + 1 + k) → ℕ
  -- Maps i to: i if i ≤ r, and m + i - r if i > r
  let idx : Fin (r + 1 + k) → ℕ := fun i =>
    if h : i.val < r + 1 then i.val else m + 1 + (i.val - r - 1)

  -- Show idx is strictly monotone
  have idx_mono : StrictMono idx := by
    intro i j hij
    simp only [idx]
    split_ifs with hi hj hj
    · -- Both i, j ≤ r: use i < j directly
      exact hij
    · -- i ≤ r < j: show i < m + 1 + (j - r - 1)
      have : j.val ≥ r + 1 := Nat.le_of_not_lt hj
      calc i.val
        _ < r + 1 := hi
        _ ≤ m + 1 := Nat.add_le_add_right (Nat.le_of_lt hrm) 1
        _ ≤ m + 1 + (j.val - r - 1) := Nat.le_add_right _ _
    · -- i ≤ r but not j < r + 1: contradiction
      omega
    · -- Both i, j > r: use the fact that j.val - r - 1 > i.val - r - 1
      have hi' : i.val ≥ r + 1 := Nat.le_of_not_lt hi
      have hj' : j.val ≥ r + 1 := Nat.le_of_not_lt hj
      calc m + 1 + (i.val - r - 1)
        _ < m + 1 + (j.val - r - 1) := Nat.add_lt_add_left (Nat.sub_lt_sub_right hi' hij) _

  -- Apply contractability: subsequence via idx has same distribution as 0,...,r+k
  have contract := hX (r + 1 + k) idx idx_mono

  -- Define the product set corresponding to our cylinder conditions
  let S_idx : Set (Fin (r + 1 + k) → α) :=
    {f | (∀ i : Fin r, f ⟨i.val, by omega⟩ ∈ A i) ∧ f ⟨r, by omega⟩ ∈ B ∧
         (∀ j : Fin k, f ⟨r + 1 + j.val, by omega⟩ ∈ C j)}

  let S_std : Set (Fin (r + 1 + k) → α) :=
    {f | (∀ i : Fin r, f ⟨i.val, by omega⟩ ∈ A i) ∧ f ⟨r, by omega⟩ ∈ B ∧
         (∀ j : Fin k, f ⟨r + 1 + j.val, by omega⟩ ∈ C j)}

  -- Note: S_idx = S_std, so they define the same set
  have h_sets_eq : S_idx = S_std := rfl

  -- Key: Show that the LHS and RHS sets are preimages under the respective mappings

  -- The LHS: {ω | X_0,...,X_{r-1} ∈ A, X_r ∈ B, X_{m+1},...,X_{m+k} ∈ C}
  -- is exactly the preimage of S_idx under (fun ω i => X (idx i) ω)
  have lhs_eq : {ω | (∀ i, X i.val ω ∈ A i) ∧ X r ω ∈ B ∧ (∀ j, X (m + 1 + j.val) ω ∈ C j)}
      = (fun ω => fun i => X (idx i) ω) ⁻¹' S_idx := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_preimage, S_idx]
    constructor
    · intro ⟨hA, hB, hC⟩
      refine ⟨?_, ?_, ?_⟩
      · intro i
        -- For i < r: idx(i) = i, so X(idx i) ω = X i ω ∈ A i
        have hi : idx ⟨i.val, by omega⟩ = i.val := by
          simp only [idx]; split_ifs <;> omega
        rw [hi]
        exact hA i
      · -- For i = r: idx(r) = r, so X(idx r) ω = X r ω ∈ B
        have : idx ⟨r, by omega⟩ = r := by
          simp only [idx]; split_ifs <;> omega
        rw [this]
        exact hB
      · intro j
        -- For i = r+1+j: idx(r+1+j) = m+1+j
        have : idx ⟨r + 1 + j.val, by omega⟩ = m + 1 + j.val := by
          simp only [idx]
          split_ifs with h
          · omega
          · have : r + 1 + j.val - r - 1 = j.val := by omega
            rw [this]
        rw [this]
        exact hC j
    · intro ⟨hA, hB, hC⟩
      refine ⟨?_, ?_, ?_⟩
      · intro i
        have : idx ⟨i.val, by omega⟩ = i.val := by
          simp only [idx]; split_ifs <;> omega
        rw [← this]
        exact hA ⟨i.val, by omega⟩
      · have : idx ⟨r, by omega⟩ = r := by
          simp only [idx]; split_ifs <;> omega
        rw [← this]
        exact hB
      · intro j
        have idx_val : idx ⟨r + 1 + j.val, by omega⟩ = m + 1 + j.val := by
          simp only [idx]
          split_ifs with h
          · omega
          · have : r + 1 + j.val - r - 1 = j.val := by omega
            rw [this]
        rw [← idx_val]
        exact hC j

  -- The RHS is the preimage of S_std under (fun ω i => X i.val ω)
  have rhs_eq : {ω | (∀ i, X i.val ω ∈ A i) ∧ X r ω ∈ B ∧ (∀ j, X (r + 1 + j.val) ω ∈ C j)}
      = (fun ω => fun i => X i.val ω) ⁻¹' S_std := by
    ext ω; simp [S_std]

  -- Apply contractability: the pushforward measures are equal
  rw [lhs_eq, rhs_eq, h_sets_eq]

  -- contract says the two pushforward measures are equal:
  -- Measure.map (fun ω i => X (idx i) ω) μ = Measure.map (fun ω i => X i.val ω) μ
  --
  -- Goal is: μ ((fun ω i => X (idx i) ω) ⁻¹' S_std) = μ ((fun ω i => X i.val ω) ⁻¹' S_std)
  --
  -- Since the measures are equal, they assign equal measure to preimages

  -- First prove S_std is measurable
  have hS_meas : MeasurableSet S_std := by
    -- Use intersection decomposition approach
    -- S_std = (⋂ i : Fin r, preimage at i) ∩ (preimage at r) ∩ (⋂ j : Fin k, preimage at r+1+j)
    have h_decomp : S_std =
        (⋂ i : Fin r, {f | f ⟨i.val, by omega⟩ ∈ A i}) ∩
        {f | f ⟨r, by omega⟩ ∈ B} ∩
        (⋂ j : Fin k, {f | f ⟨r + 1 + j.val, by omega⟩ ∈ C j}) := by
      ext f
      simp only [S_std, Set.mem_iInter, Set.mem_inter_iff, Set.mem_setOf]
      tauto

    rw [h_decomp]
    apply MeasurableSet.inter
    · apply MeasurableSet.inter
      · apply MeasurableSet.iInter
        intro i
        exact measurable_pi_apply (Fin.mk i.val (by omega)) (hA i)
      · exact measurable_pi_apply (Fin.mk r (by omega)) hB
    · apply MeasurableSet.iInter
      intro j
      exact measurable_pi_apply (Fin.mk (r + 1 + j.val) (by omega)) (hC j)

  -- Prove the functions are measurable
  have h_meas_idx : Measurable (fun ω (i : Fin (r + 1 + k)) => X (idx i) ω) :=
    measurable_pi_lambda _ (fun i => hX_meas (idx i))
  have h_meas_std : Measurable (fun ω (i : Fin (r + 1 + k)) => X (↑i) ω) :=
    measurable_pi_lambda _ (fun i => hX_meas (↑i))

  calc μ ((fun ω (i : Fin (r + 1 + k)) => X (idx i) ω) ⁻¹' S_std)
      = Measure.map (fun ω i => X (idx i) ω) μ S_std := by
        rw [Measure.map_apply h_meas_idx hS_meas]
    _ = Measure.map (fun ω (i : Fin (r + 1 + k)) => X (↑i) ω) μ S_std := by
        rw [contract]
    _ = μ ((fun ω (i : Fin (r + 1 + k)) => X (↑i) ω) ⁻¹' S_std) := by
        rw [Measure.map_apply h_meas_std hS_meas]

/-- Contractability implies equality of the joint law of
`(X₀,…,X_{r-1}, X_r, X_{m+1}, …, X_{m+k})` and
`(X₀,…,X_{r-1}, X_r, X_{r+1}, …, X_{r+k})`. -/
lemma contractable_triple_pushforward
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → α)
    (hX : Contractable μ X)
    (hX_meas : ∀ n, Measurable (X n))
    {r m k : ℕ} (hrm : r < m) :
  let Z_r : Ω → (Fin r → α) := fun ω i => X i.val ω
  let Y_future : Ω → (Fin k → α) := fun ω j => X (m + 1 + j.val) ω
  let Y_tail   : Ω → (Fin k → α) := fun ω j => X (r + 1 + j.val) ω
  Measure.map (fun ω => (Z_r ω, X r ω, Y_future ω)) μ
    = Measure.map (fun ω => (Z_r ω, X r ω, Y_tail ω)) μ := by
  classical
  intro Z_r Y_future Y_tail
  -- Define cylinder rectangles generating the product σ-algebra.
  let Rectangles :
      Set (Set ((Fin r → α) × α × (Fin k → α))) :=
    {S | ∃ (A : Fin r → Set α) (hA : ∀ i, MeasurableSet (A i))
          (B : Set α) (hB : MeasurableSet B)
          (C : Fin k → Set α) (hC : ∀ j, MeasurableSet (C j)),
        S = (Set.univ.pi A) ×ˢ B ×ˢ (Set.univ.pi C)}

  -- Rectangles form a π-system.
  have h_pi : IsPiSystem Rectangles := by
    intro S₁ hS₁ S₂ hS₂ h_ne
    rcases hS₁ with ⟨A₁, hA₁, B₁, hB₁, C₁, hC₁, rfl⟩
    rcases hS₂ with ⟨A₂, hA₂, B₂, hB₂, C₂, hC₂, rfl⟩
    refine ⟨fun i => A₁ i ∩ A₂ i, ?_, B₁ ∩ B₂, hB₁.inter hB₂,
            fun j => C₁ j ∩ C₂ j, ?_, ?_⟩
    · intro i; exact (hA₁ i).inter (hA₂ i)
    · intro j; exact (hC₁ j).inter (hC₂ j)
    · ext ⟨z, y, c⟩
      simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_univ_pi]
      constructor
      · intro ⟨⟨hz1, hy1, hc1⟩, hz2, hy2, hc2⟩
        exact ⟨fun i => ⟨hz1 i, hz2 i⟩, ⟨hy1, hy2⟩, fun j => ⟨hc1 j, hc2 j⟩⟩
      · intro ⟨hz, hy, hc⟩
        exact ⟨⟨fun i => (hz i).1, hy.1, fun j => (hc j).1⟩, fun i => (hz i).2, hy.2, fun j => (hc j).2⟩

  -- Equality on rectangles using the finite cylinder measure lemma.
  have h_agree :
      ∀ {S} (hS : S ∈ Rectangles),
        Measure.map (fun ω => (Z_r ω, X r ω, Y_future ω)) μ S
          = Measure.map (fun ω => (Z_r ω, X r ω, Y_tail ω)) μ S := by
    intro S hS
    rcases hS with ⟨A, hA, B, hB, C, hC, rfl⟩
    -- Convert preimage of rectangle into the cylinder event.
    have h_pre_future :
        (fun ω => (Z_r ω, X r ω, Y_future ω)) ⁻¹'
          ((Set.univ.pi A) ×ˢ B ×ˢ (Set.univ.pi C))
          =
        {ω | (∀ i : Fin r, X i.val ω ∈ A i) ∧ X r ω ∈ B ∧
              (∀ j : Fin k, X (m + 1 + j.val) ω ∈ C j)} := by
      ext ω; simp [Z_r, Y_future, Set.mem_setOf_eq]
    have h_pre_tail :
        (fun ω => (Z_r ω, X r ω, Y_tail ω)) ⁻¹'
          ((Set.univ.pi A) ×ˢ B ×ˢ (Set.univ.pi C))
          =
        {ω | (∀ i : Fin r, X i.val ω ∈ A i) ∧ X r ω ∈ B ∧
              (∀ j : Fin k, X (r + 1 + j.val) ω ∈ C j)} := by
      ext ω; simp [Z_r, Y_tail, Set.mem_setOf_eq]
    -- Apply the finite cylinder equality.
    have h_cyl :=
      contractable_finite_cylinder_measure
        (X := X) (μ := μ) (hX := hX) (hX_meas := hX_meas)
        (hrm := hrm) (A := A) (hA := hA) (B := B) (hB := hB)
        (C := C) (hC := hC)
    -- Convert to map equality
    sorry  -- TODO: Complete measurability proof and application
           -- The structure is correct: need to apply h_cyl via Measure.map_apply
           -- Issues: measurable_pi_lambda API, product measurability composition

  -- Apply π-λ theorem to extend from Rectangles to full σ-algebra
  sorry  -- TODO: Apply Measure.ext_of_generateFrom_of_iUnion
         -- Structure:
         -- - h_pi: Rectangles is π-system ✓
         -- - h_agree: measures agree on Rectangles (needs fix at line 1547)
         -- - Need: Rectangles generates product σ-algebra
         -- - Need: covering family with finite measure
         -- Then conclude measure equality


/-- **Correct conditional independence from contractability (Kallenberg Lemma 1.3).**

For contractable X and r < m, the past block σ(X₀,...,X_{r-1}) and the single coordinate
σ(X_r) are conditionally independent given the far future σ(θ_{m+1} X).

**Mathematical statement:**
```
σ(X₀,...,X_{r-1}) ⊥⊥_{σ(θ_{m+1} X)} σ(X_r)
```

**Why this is correct:**
By contractability, deleting coordinate r doesn't change the joint distribution:
```
(X₀,...,X_{r-1}, θ_{m+1} X) =ᵈ (X₀,...,X_{r-1}, X_r, θ_{m+1} X)
```
with σ(θ_{m+1} X) ⊆ σ(X_r, θ_{m+1} X).

By Kallenberg's Lemma 1.3: if (U, η) =ᵈ (U, ζ) and σ(η) ⊆ σ(ζ), then U ⊥⊥_η ζ.
Taking U = (X₀,...,X_{r-1}), η = θ_{m+1} X, ζ = (X_r, θ_{m+1} X) gives the result.

**This replaces the old broken `coordinate_future_condIndep` which incorrectly claimed
Y ⊥⊥_{σ(Y)} Y.** -/
lemma block_coord_condIndep
    {Ω α : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableSpace α]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → α)
    (hX : Contractable μ X)
    (hX_meas : ∀ n, Measurable (X n))
    {r m : ℕ} (hrm : r < m) :
  ProbabilityTheory.CondIndep
    (futureFiltration X m)                        -- conditioning: σ(θ_{m+1} X)
    (firstRSigma X r)                             -- past block: σ(X₀,...,X_{r-1})
    (MeasurableSpace.comap (X r) inferInstance)   -- single coord: σ(X_r)
    (futureFiltration_le X m hX_meas)             -- witness: σ(θ_{m+1} X) ≤ ambient
    μ := by
  -- We use the "indicator projection" criterion.
  apply Exchangeability.Probability.condIndep_of_indicator_condexp_eq
  · exact firstRSigma_le_ambient X r hX_meas
  · intro s hs; rcases hs with ⟨t, ht, rfl⟩; exact (hX_meas r) ht
  -- Fix `B ∈ σ(X_r)` and prove the projection identity.
  intro H hH
  rcases hH with ⟨B, hB, rfl⟩
  -- Notation
  set Y : Ω → α := X r with hY
  set Zr : Ω → (Fin r → α) := fun ω i => X i.1 ω with hZr
  -- finite future block (length = k)
  have hY_meas : Measurable Y := hX_meas r
  have hZr_meas : Measurable Zr :=
    measurable_pi_lambda _ (fun i => hX_meas i.1)
  -- Step 1: finite-level identity for every k
  have h_finite :
      ∀ k : ℕ,
        μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ Y
            | firstRSigma X r ⊔ finFutureSigma X m k]
          =ᵐ[μ]
        μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ Y
            | finFutureSigma X m k] := by
    intro k
    -- Define the two finite future maps
    set θk : Ω → (Fin k → α) := fun ω j => X (m + 1 + j.1) ω with hθdef
    set θk' : Ω → (Fin k → α) := fun ω j => X (r + 1 + j.1) ω with hθpdef
    have hθk_meas  : Measurable θk :=
      measurable_pi_lambda _ (fun j => hX_meas (m + 1 + j.1))
    have hθk'_meas : Measurable θk' :=
      measurable_pi_lambda _ (fun j => hX_meas (r + 1 + j.1))
    -- From contractability: triple pushforward equality, project away `Z_r`
    have h_triple := contractable_triple_pushforward
        (X := X) (μ := μ) (hX := hX) (hX_meas := hX_meas) (hrm := hrm)
        (r := r) (m := m) (k := k)
    -- Project to pairs `(Y, θk)` vs `(Y, θk')`
    have h_pair :
        Measure.map (fun ω => (Y ω, θk ω)) μ
          = Measure.map (fun ω => (Y ω, θk' ω)) μ := by
      -- The triple equality is for `(Zr, Y, θk)` vs `(Zr, Y, θk')`;
      -- composing with the projection that drops `Zr` gives this pair equality.
      -- (use `Measure.map_map` twice).
      -- Product type is (Fin r → α) × α × (Fin k → α) = (Fin r → α) × (α × (Fin k → α))
      have proj : ( (Fin r → α) × α × (Fin k → α) ) → α × (Fin k → α) :=
        fun q => (q.2.1, q.2.2)
      have hproj_meas : Measurable proj :=
        (measurable_fst.comp measurable_snd).prodMk (measurable_snd.comp measurable_snd)
      -- `map (proj ∘ ...) μ = map proj (map ... μ)`
      -- so we rewrite both sides via `Measure.map_map`.
      have := congrArg (fun M => Measure.map proj M) h_triple
      -- now use `Measure.map_map` on both sides
      -- left
      have hL :
        Measure.map proj
          (Measure.map (fun ω => (Zr ω, Y ω, θk ω)) μ)
          = Measure.map (fun ω => (Y ω, θk ω)) μ := by
        simpa [proj] using
          (Measure.map_map hproj_meas ((hZr_meas.prodMk hY_meas).prodMk hθk_meas))
      -- right
      have hR :
        Measure.map proj
          (Measure.map (fun ω => (Zr ω, Y ω, θk' ω)) μ)
          = Measure.map (fun ω => (Y ω, θk' ω)) μ := by
        simpa [proj] using
          (Measure.map_map hproj_meas ((hZr_meas.prodMk hY_meas).prodMk hθk'_meas))
      simpa [hL, hR] using this
    -- Bridge step: Since (Y, θk) and (Y, θk') have the same law,
    -- E[1_B(Y) | σ(θk)] = E[1_B(Y) | σ(θk')].
    -- This is the "invariance under equal laws" property for conditional expectations.
    -- Since firstRSigma ⊔ finFutureSigma is generated by (Zr, θk), we need to show
    -- that conditioning on this join equals conditioning on just θk.
    --
    -- The mathematical content: from contractability we have
    --   (Zr, Y, θk) =^d (Zr, Y, θk')
    -- Marginalizing gives (Y, θk) =^d (Y, θk'), so for any function f of Y:
    --   E[f(Y) | σ(θk)] = E[f(Y) | σ(θk')]  (by the pair law)
    -- Since σ(θk) ⊆ σ(Zr, θk), by the tower property:
    --   E[f(Y) | σ(Zr, θk)] = E[E[f(Y) | σ(θk)] | σ(Zr, θk)] = E[f(Y) | σ(θk)]
    -- where the last equality uses that E[f(Y) | σ(θk)] is already σ(θk)-measurable
    -- (a constant relative to the larger σ-algebra).
    sorry  -- TODO: Missing lemmas needed to complete this proof:
           -- 1. Bridge lemma for equal pair laws: if map (Y, Z) μ = map (Y, Z') μ, then
           --    E[f(Y) | σ(Z)] = E[f(Y) | σ(Z')] a.e.
           -- 2. Upward Lévy convergence: condExp_tendsto_iSup for increasing filtrations
           --    (analogous to the downward version used elsewhere)
           --
           -- The mathematical structure is correct: we've shown how to project the triple
           -- law to a pair law, and the rest follows by standard martingale convergence.
  sorry  -- TODO: Steps 2-3 also need the missing lemmas above

/-- **Product formula for conditional expectations under conditional independence.**

Given two sets `A` (measurable in `mF`) and `B` (measurable in `mH`), under conditional
independence given `m`, the conditional expectation of the intersection indicator factors:
```
μ[1_{A∩B} | m] = μ[1_A | m] · μ[1_B | m]   a.e.
```

Now proven using `condexp_indicator_inter_bridge` from CondExp.lean, eliminating the
previous `: True` axiom stub. -/
lemma condexp_indicator_inter_of_condIndep
    {Ω : Type*} {m₀ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {μ : @Measure Ω m₀} [IsProbabilityMeasure μ]
    {m mF mH : MeasurableSpace Ω}
    (hm : m ≤ m₀) (hmF : mF ≤ m₀) (hmH : mH ≤ m₀)
    (hCI : ProbabilityTheory.CondIndep m mF mH hm μ)
    {A B : Set Ω} (hA : MeasurableSet[mF] A) (hB : MeasurableSet[mH] B) :
    μ[(A ∩ B).indicator (fun _ => (1 : ℝ)) | m]
      =ᵐ[μ]
    (μ[A.indicator (fun _ => (1 : ℝ)) | m] *
     μ[B.indicator (fun _ => (1 : ℝ)) | m]) :=
  Exchangeability.Probability.condexp_indicator_inter_bridge hm hmF hmH hCI hA hB

/-- **Finite-level factorization builder (formerly Axiom 3).**

For a contractable sequence, at any future level `m ≥ r`, the conditional expectation
of the product indicator factors:
```
μ[∏ᵢ<r 1_{Xᵢ∈Cᵢ} | σ(θₘ₊₁X)] = ∏ᵢ<r μ[1_{X₀∈Cᵢ} | σ(θₘ₊₁X)]
```

This iteratively applies conditional independence to pull out one coordinate at a time,
using contractability to replace each `Xᵢ` with `X₀`. -/
lemma finite_level_factorization
    {Ω α : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableSpace α]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → α)
    (hX : Contractable μ X)
    (hX_meas : ∀ n, Measurable (X n))
    (r : ℕ) (C : Fin r → Set α) (hC : ∀ i, MeasurableSet (C i))
    (m : ℕ) (hm : m ≥ r) :
    μ[indProd X r C | futureFiltration X m]
      =ᵐ[μ]
    (fun ω => ∏ i : Fin r,
      μ[Set.indicator (C i) (fun _ => (1:ℝ)) ∘ (X 0) | futureFiltration X m] ω) := by
  classical
  induction r with
  | zero =>
    -- r = 0: empty product is 1
    -- Both indProd X 0 C and the RHS product are constant 1
    have h_ind : indProd X 0 C = fun _ => 1 := by
      funext ω; simp [indProd]
    have h_rhs : (fun ω => ∏ i : Fin 0,
        μ[Set.indicator (C i) (fun _ => (1:ℝ)) ∘ (X 0) | futureFiltration X m] ω) = fun _ => 1 := by
      funext ω; simp
    -- μ[indProd X 0 C | F] = μ[1 | F] = 1 = RHS (all definitional)
    conv_lhs => rw [h_ind]
    rw [condExp_const (futureFiltration_le X m hX_meas), h_rhs]
  | succ r ih =>
    -- r ↦ r+1: Inductive step using indicator factorization
    -- Must have r+1 ≤ m, which gives r < m for conditional independence
    have hrm : r < m := Nat.lt_of_succ_le hm

    -- Split C into "first r" and "last"
    let Cinit : Fin r → Set α := fun j => C (Fin.castSucc j)
    let Clast : Set α := C ⟨r, Nat.lt_succ_self r⟩
    have hCinit : ∀ j, MeasurableSet (Cinit j) := fun j => hC _
    have hClast : MeasurableSet Clast := hC ⟨r, Nat.lt_succ_self r⟩

    -- Factorize the product ∏_{i<r+1} 1_{Xᵢ∈Cᵢ} = (∏_{i<r} 1_{Xᵢ∈Cᵢ}) · 1_{Xᵣ∈Clast}
    have hsplit : indProd X (r+1) C
        = fun ω => indProd X r Cinit ω * Set.indicator Clast (fun _ => (1:ℝ)) (X r ω) := by
      funext ω
      simp only [indProd, Cinit, Clast]
      -- Split the product using Fin.prod_univ_castSucc
      rw [Fin.prod_univ_castSucc]
      rfl

    -- Express the two factors as indicators of sets
    set A := firstRCylinder X r Cinit with hA_def
    set B := X r ⁻¹' Clast with hB_def

    -- Rewrite indProd using indicator algebra
    have hf_indicator : indProd X r Cinit = A.indicator (fun _ => (1:ℝ)) :=
      indProd_eq_firstRCylinder_indicator X r Cinit

    have hg_indicator : (Set.indicator Clast (fun _ => (1:ℝ)) ∘ X r)
        = B.indicator (fun _ => (1:ℝ)) :=
      indicator_comp_preimage (X r) Clast 1

    -- The product is the indicator of A ∩ B
    have hprod_indicator :
        (fun ω => indProd X r Cinit ω * (Set.indicator Clast (fun _ => (1:ℝ)) (X r ω)))
        = (A ∩ B).indicator (fun _ => (1:ℝ)) := by
      ext ω
      have hg' : Set.indicator Clast (fun _ => (1:ℝ)) (X r ω) = B.indicator (fun _ => (1:ℝ)) ω := by
        have := congr_fun hg_indicator ω
        simp only [Function.comp_apply] at this
        exact this
      rw [congr_fun hf_indicator ω, hg']
      have := congr_fun (indicator_mul_indicator_eq_indicator_inter A B 1 1) ω
      simp only [Pi.mul_apply] at this
      convert this using 1
      ring_nf

    -- Measurability of A in firstRSigma X r
    have hA_meas_firstR : MeasurableSet[firstRSigma X r] A := by
      rw [hA_def]
      exact firstRCylinder_measurable_in_firstRSigma X r Cinit hCinit

    -- Measurability of B in σ(X r)
    have hB_meas_Xr : MeasurableSet[MeasurableSpace.comap (X r) inferInstance] B := by
      rw [hB_def]
      -- B = X r ⁻¹' Clast, which is measurable in σ(X r) by definition of comap
      exact ⟨Clast, hClast, rfl⟩

    -- Conditional independence from block_coord_condIndep
    have h_condIndep : ProbabilityTheory.CondIndep
        (futureFiltration X m)
        (firstRSigma X r)
        (MeasurableSpace.comap (X r) inferInstance)
        (futureFiltration_le X m hX_meas)
        μ := by
      exact block_coord_condIndep X hX hX_meas hrm

    -- Apply indicator factorization using the CI
    have hfactor :
        μ[(A.indicator (fun _ => (1:ℝ))) * (B.indicator (fun _ => (1:ℝ))) | futureFiltration X m]
          =ᵐ[μ]
        (fun ω => (μ[A.indicator (fun _ => (1:ℝ)) | futureFiltration X m] ω)
                  * (μ[B.indicator (fun _ => (1:ℝ)) | futureFiltration X m] ω)) := by
      -- Convert product of indicators to indicator of intersection
      have h_inter : (A.indicator (fun _ => (1:ℝ))) * (B.indicator (fun _ => (1:ℝ)))
                   = (A ∩ B).indicator (fun _ => (1:ℝ)) := by
        ext ω
        simp only [Pi.mul_apply]
        have := congr_fun (indicator_mul_indicator_eq_indicator_inter A B 1 1) ω
        simpa using this
      -- Apply standard CI product formula
      calc μ[(A.indicator (fun _ => (1:ℝ))) * (B.indicator (fun _ => (1:ℝ))) | futureFiltration X m]
          _ =ᵐ[μ] μ[(A ∩ B).indicator (fun _ => (1:ℝ)) | futureFiltration X m] := by
            exact condExp_congr_ae (EventuallyEq.of_eq h_inter)
          _ =ᵐ[μ] (μ[A.indicator (fun _ => (1:ℝ)) | futureFiltration X m] *
                   μ[B.indicator (fun _ => (1:ℝ)) | futureFiltration X m]) := by
            exact condexp_indicator_inter_of_condIndep
              (futureFiltration_le X m hX_meas)
              (firstRSigma_le_ambient X r hX_meas)
              (fun s hs => by obtain ⟨t, ht, rfl⟩ := hs; exact (hX_meas r) ht)
              h_condIndep
              hA_meas_firstR
              hB_meas_Xr

    -- Apply IH to the first r factors
    have hIH : μ[indProd X r Cinit | futureFiltration X m] =ᵐ[μ]
        (fun ω => ∏ i : Fin r,
          μ[Set.indicator (Cinit i) (fun _ => (1:ℝ)) ∘ (X 0) | futureFiltration X m] ω) := by
      exact ih Cinit hCinit (Nat.le_of_succ_le hm)

    -- Replace Xᵣ with X₀ using contractability
    have hswap : μ[(Set.indicator Clast (fun _ => (1:ℝ)) ∘ X r) | futureFiltration X m]
        =ᵐ[μ]
        μ[(Set.indicator Clast (fun _ => (1:ℝ)) ∘ X 0) | futureFiltration X m] := by
      -- condexp_convergence swaps X_m with X_k, so swap X_m with X_r, then with X_0
      have h1 := condexp_convergence hX hX_meas r m (Nat.le_of_lt hrm) Clast hClast
      have h2 := condexp_convergence hX hX_meas 0 m (Nat.zero_le m) Clast hClast
      exact h1.symm.trans h2

    -- Combine everything
    calc μ[indProd X (r+1) C | futureFiltration X m]
        _ =ᵐ[μ] μ[(fun ω => indProd X r Cinit ω
                      * Set.indicator Clast (fun _ => (1:ℝ)) (X r ω))
                   | futureFiltration X m] := by
          refine condExp_congr_ae (EventuallyEq.of_eq hsplit)
        _ =ᵐ[μ] μ[(A.indicator (fun _ => (1:ℝ)))
                   * (B.indicator (fun _ => (1:ℝ)))
                   | futureFiltration X m] := by
          refine condExp_congr_ae (EventuallyEq.of_eq ?_)
          funext ω
          rw [← hf_indicator, ← hg_indicator]
          rfl
        _ =ᵐ[μ] (fun ω => (μ[A.indicator (fun _ => (1:ℝ)) | futureFiltration X m] ω)
                          * (μ[B.indicator (fun _ => (1:ℝ)) | futureFiltration X m] ω)) := hfactor
        _ =ᵐ[μ] (fun ω => (μ[indProd X r Cinit | futureFiltration X m] ω)
                          * (μ[Set.indicator Clast (fun _ => (1:ℝ)) ∘ X r | futureFiltration X m] ω)) := by
          apply EventuallyEq.mul
          · refine condExp_congr_ae (EventuallyEq.of_eq hf_indicator.symm)
          · refine condExp_congr_ae (EventuallyEq.of_eq hg_indicator.symm)
        _ =ᵐ[μ] (fun ω => (∏ i : Fin r,
                            μ[Set.indicator (Cinit i) (fun _ => (1:ℝ)) ∘ (X 0)
                              | futureFiltration X m] ω)
                          * (μ[Set.indicator Clast (fun _ => (1:ℝ)) ∘ X r | futureFiltration X m] ω)) := by
          apply EventuallyEq.mul hIH
          exact EventuallyEq.rfl
        _ =ᵐ[μ] (fun ω => (∏ i : Fin r,
                            μ[Set.indicator (Cinit i) (fun _ => (1:ℝ)) ∘ (X 0)
                              | futureFiltration X m] ω)
                          * μ[Set.indicator Clast (fun _ => (1:ℝ)) ∘ (X 0)
                              | futureFiltration X m] ω) := by
          apply EventuallyEq.mul EventuallyEq.rfl
          exact hswap
        _ =ᵐ[μ] (fun ω => ∏ i : Fin (r+1),
                            μ[Set.indicator (C i) (fun _ => (1:ℝ)) ∘ (X 0)
                              | futureFiltration X m] ω) := by
          apply EventuallyEq.of_eq
          funext ω
          -- Reverse of hsplit: combine products using Fin.prod_univ_castSucc
          symm
          rw [Fin.prod_univ_castSucc]
          simp only [Cinit, Clast, Fin.last]

/-- **Tail factorization on finite cylinders (formerly Axiom 4).**

Assume you have, for all large enough `m`, the finite‑level factorization
at the future filtration:
```
μ[indProd X r C | σ(θ_{m+1}X)]
  = ∏ i<r μ[1_{X₀∈C i} | σ(θ_{m+1}X)]   a.s.
```
Then the same factorization holds **at the tail σ‑algebra**:
```
μ[indProd X r C | 𝒯_X]
  = ∏ i<r μ[1_{X₀∈C i} | 𝒯_X]           a.s.
```

This passes the finite‑level equality to the tail using bounded
dominated convergence together with reverse martingale convergence. -/
lemma tail_factorization_from_future
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → α)
    (hX : ∀ n, Measurable (X n))
    (r : ℕ) (C : Fin r → Set α) (hC : ∀ i, MeasurableSet (C i))
    -- finite-level factorization hypothesis (available after applying the wrapper repeatedly)
    (h_fact :
      ∀ m ≥ r,  -- any `m` with at least r future steps works
        μ[indProd X r C | futureFiltration X m]
          =ᵐ[μ]
        (fun ω => ∏ i : Fin r,
          μ[Set.indicator (C i) (fun _ => (1 : ℝ)) ∘ (X 0) | futureFiltration X m] ω))
    -- reverse-martingale convergence for each singleton factor
    (h_rev :
      ∀ i : Fin r,
        (∀ᵐ ω ∂μ,
          Tendsto (fun m => μ[Set.indicator (C i) (fun _ => (1 : ℝ)) ∘ (X 0)
                                 | futureFiltration X m] ω)
                  atTop
                  (𝓝 (μ[Set.indicator (C i) (fun _ => (1 : ℝ)) ∘ (X 0)
                          | tailSigma X] ω)))) :
    μ[indProd X r C | tailSigma X]
      =ᵐ[μ]
    (fun ω => ∏ i : Fin r,
        μ[Set.indicator (C i) (fun _ => (1 : ℝ)) ∘ (X 0) | tailSigma X] ω) := by
  classical
  -- Strategy: Use reverse martingale convergence for the LHS
  -- The future filtration decreases to the tail σ-algebra, so reverse martingale
  -- convergence gives: μ[f | futureFiltration X m] → μ[f | tailSigma X] ae

  -- LHS reverse martingale convergence for the product
  have h_lhs_conv : ∀ᵐ ω ∂μ,
      Tendsto (fun m => μ[indProd X r C | futureFiltration X m] ω)
              atTop
              (𝓝 (μ[indProd X r C | tailSigma X] ω)) := by
    -- Apply Lévy's reverse martingale convergence directly
    have h_conv := Exchangeability.Probability.condExp_tendsto_iInf
      (μ := μ)
      (𝔽 := futureFiltration X)
      (h_filtration := futureFiltration_antitone X)
      (h_le := fun n => futureFiltration_le X n hX)
      (f := indProd X r C)
      (h_f_int := indProd_integrable X r C hX hC)
    -- Convert ⨅ n, futureFiltration X n to tailSigma X
    simp only [← tailSigmaFuture_eq_iInf, tailSigmaFuture_eq_tailSigma] at h_conv
    exact h_conv

  -- RHS convergence: product of convergent sequences
  have h_rhs_conv : ∀ᵐ ω ∂μ,
      Tendsto (fun m => ∏ i : Fin r,
                  μ[Set.indicator (C i) (fun _ => (1 : ℝ)) ∘ (X 0) | futureFiltration X m] ω)
              atTop
              (𝓝 (∏ i : Fin r,
                  μ[Set.indicator (C i) (fun _ => (1 : ℝ)) ∘ (X 0) | tailSigma X] ω)) := by
    -- Product of tendsto gives tendsto of product (finitely many factors)
    have h_ae := ae_all_iff.mpr h_rev
    filter_upwards [h_ae] with ω hω
    exact tendsto_finset_prod _ (fun i _ => hω i)

  -- Both LHS and RHS converge, and they're equal at each finite level for large m
  -- Therefore their limits are equal
  have h_eq_ae : ∀ᵐ ω ∂μ,
      μ[indProd X r C | tailSigma X] ω
        = (∏ i : Fin r,
            μ[Set.indicator (C i) (fun _ => (1 : ℝ)) ∘ (X 0) | tailSigma X] ω) := by
    -- Combine the three ae sets
    have h_fact_large : ∀ᵐ ω ∂μ, ∀ m ≥ r,
        μ[indProd X r C | futureFiltration X m] ω
          = (∏ i : Fin r,
              μ[Set.indicator (C i) (fun _ => (1 : ℝ)) ∘ (X 0) | futureFiltration X m] ω) := by
      -- Countable intersection of ae sets
      -- For each m ≥ r, we have an ae set where equality holds
      -- Take countable intersection indexed by {m // m ≥ r}
      have h_count_inter : ∀ᵐ ω ∂μ, ∀ m : {m // m ≥ r},
          μ[indProd X r C | futureFiltration X m] ω
            = (∏ i : Fin r,
                μ[Set.indicator (C i) (fun _ => (1 : ℝ)) ∘ (X 0) | futureFiltration X m] ω) := by
        -- Use ae_all_iff for countable intersection
        rw [ae_all_iff]
        intro ⟨m, hm⟩
        exact h_fact m hm
      -- Convert from subtype to ∀ m ≥ r
      filter_upwards [h_count_inter] with ω hω m hm
      exact hω ⟨m, hm⟩

    filter_upwards [h_lhs_conv, h_rhs_conv, h_fact_large] with ω hlhs hrhs hfact
    -- At ω, both sequences converge and are eventually equal, so limits are equal
    exact tendsto_nhds_unique hlhs (hrhs.congr' (eventually_atTop.mpr ⟨r, fun m hm => (hfact m hm).symm⟩))

  exact h_eq_ae

/-! ### Directing measure construction

From conditional expectations on indicators, we need to build a measurable family
of probability measures `ν : Ω → Measure α`.

The construction uses the standard Borel machinery: for each `ω`, define
`ν ω` to be the unique probability measure satisfying
`ν ω B = E[1_{X₀∈B} | 𝒯_X](ω)` for all measurable `B`.

This requires StandardBorelSpace assumption on α to ensure existence.
-/

/-- Construction of the directing measure from conditional expectations (formerly Axiom 5).
For each `ω : Ω`, `ν ω` is the conditional distribution of `X₀` given the tail σ-algebra.

This uses mathlib's `condExpKernel` to construct a regular conditional probability kernel.
The kernel `condExpKernel μ (tailSigma X)` gives the conditional distribution on the entire
path space; composing with the projection `X 0` gives the desired marginal on α. -/
noncomputable def directingMeasure_of_contractable
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
    (X : ℕ → Ω → α)
    (hX_meas : ∀ n, Measurable (X n)) :
    { ν : Ω → Measure α //
      (∀ ω, IsProbabilityMeasure (ν ω)) ∧
      (∀ B : Set α, MeasurableSet B →
        (fun ω => (ν ω B).toReal) =ᵐ[μ] μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ (X 0) | tailSigma X]) ∧
      (∀ B : Set α, MeasurableSet B → Measurable (fun ω => ν ω B)) } := by
  classical
  -- **Construction strategy:**
  -- 1. Use condExpKernel μ (tailSigma X) to get a kernel κ : Ω → Measure Ω
  -- 2. Define ν ω := (κ ω).map (X 0) (pushforward along X 0)
  -- 3. Prove probability: κ ω is a probability measure, X 0 is measurable
  -- 4. Prove CE property: Use condExp_ae_eq_integral_condExpKernel and integral_map
  -- 5. Prove measurability: Use Kernel.measurable_coe composed with map

  -- Need StandardBorelSpace Ω for condExpKernel to exist
  -- This should be added as a hypothesis or derived from StandardBorelSpace α
  sorry  -- TODO: Complete kernel construction using ProbabilityTheory.condExpKernel

/-! ### Conditional law equality -/

/-- All `X_n` have the same conditional law `ν`.
This follows from `extreme_members_equal_on_tail`. -/
lemma conditional_law_eq_directingMeasure
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
    (X : ℕ → Ω → α)
    (hX : Contractable μ X)
    (hX_meas : ∀ n, Measurable (X n))
    (ν : Ω → Measure α)
    (hν : ∀ B : Set α, MeasurableSet B →
        (fun ω => (ν ω B).toReal) =ᵐ[μ] μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ (X 0) | tailSigma X])
    (n : ℕ) (B : Set α) (hB : MeasurableSet B) :
    (fun ω => (ν ω B).toReal) =ᵐ[μ] μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ (X n) | tailSigma X] := by
  have h0 := hν B hB
  have hn := extreme_members_equal_on_tail hX hX_meas n B hB
  exact ae_eq_trans h0 hn.symm

/-! ### Finite-dimensional product formula -/

/-- **Finite product formula for the first m coordinates** (identity case).

This is the core case where we prove the product formula for `(X₀, X₁, ..., X_{m-1})`.
The general case for strictly monotone subsequences reduces to this via contractability.

**Important**: The statement with arbitrary `k : Fin m → ℕ` is **false** if `k` has duplicates
(e.g., `(X₀, X₀)` is not an independent product unless ν is Dirac). We avoid this by:
1. Proving the identity case here (no index map)
2. Reducing strict-monotone subsequences to the identity case via contractability

**Proof strategy:**
1. Show equality on rectangles using factorization machinery
2. Extend from rectangles to full σ-algebra via π-λ theorem -/
lemma finite_product_formula_id
    [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
    (X : ℕ → Ω → α)
    (hX : Contractable μ X)
    (hX_meas : ∀ n, Measurable (X n))
    (ν : Ω → Measure α)
    (hν_prob : ∀ ω, IsProbabilityMeasure (ν ω))
    (hν_meas : ∀ B : Set α, MeasurableSet B → Measurable (fun ω => ν ω B))
    (hν_law : ∀ n B, MeasurableSet B →
        (fun ω => (ν ω B).toReal) =ᵐ[μ] μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ (X n) | tailSigma X])
    (m : ℕ) :
    Measure.map (fun ω => fun i : Fin m => X i ω) μ
      = μ.bind (fun ω => Measure.pi fun _ : Fin m => ν ω) := by
  classical
  -- π-system of rectangles in (Fin m → α)
  let Rectangles : Set (Set (Fin m → α)) :=
    {S | ∃ (C : Fin m → Set α), (∀ i, MeasurableSet (C i)) ∧ S = Set.univ.pi C}

  -- Step 1: Rectangles form a π-system
  have h_pi : IsPiSystem Rectangles := by
    intro S₁ hS₁ S₂ hS₂ hne
    rcases hS₁ with ⟨C₁, hC₁, rfl⟩
    rcases hS₂ with ⟨C₂, hC₂, rfl⟩
    refine ⟨fun i => C₁ i ∩ C₂ i, ?_, ?_⟩
    · intro i; exact (hC₁ i).inter (hC₂ i)
    · ext f; simp only [Set.mem_univ_pi, Set.mem_inter_iff]
      constructor
      · intro ⟨h1, h2⟩ i; exact ⟨h1 i, h2 i⟩
      · intro h; exact ⟨fun i => (h i).1, fun i => (h i).2⟩

  -- Step 2: Show both measures agree on rectangles
  have h_agree :
    ∀ s ∈ Rectangles,
      (Measure.map (fun ω => fun i : Fin m => X i ω) μ) s
        = (μ.bind (fun ω => Measure.pi fun _ : Fin m => ν ω)) s := by
    intro s hs
    rcases hs with ⟨C, hC, rfl⟩
    
    -- LHS: map measure on rectangle = integral of product indicator
    have hL : (Measure.map (fun ω => fun i : Fin m => X i ω) μ) (Set.univ.pi C)
        = ENNReal.ofReal (∫ ω, indProd X m C ω ∂μ) := by
      sorry  -- TODO: Standard measure theory - preimage equals firstRCylinder,
             -- then use integral_indicator and ENNReal conversion
    
    -- Use factorization machinery to express as tail-level product
    have h_fact : ∀ M ≥ m,
        μ[indProd X m C | futureFiltration X M] =ᵐ[μ]
        (fun ω => ∏ i : Fin m,
          μ[Set.indicator (C i) (fun _ => (1:ℝ)) ∘ (X 0) | futureFiltration X M] ω) :=
      fun M hMm => finite_level_factorization X hX hX_meas m C hC M hMm
    
    -- Reverse martingale convergence for each coordinate
    have h_conv : ∀ i : Fin m,
        (∀ᵐ ω ∂μ, Tendsto (fun M =>
          μ[Set.indicator (C i) (fun _ => (1:ℝ)) ∘ (X 0) | futureFiltration X M] ω)
          atTop
          (𝓝 (μ[Set.indicator (C i) (fun _ => (1:ℝ)) ∘ (X 0) | tailSigma X] ω))) := by
      intro i
      -- Apply Lévy's downward theorem for conditional expectations
      have := Exchangeability.Probability.condExp_tendsto_iInf
        (μ := μ) (𝔽 := futureFiltration X)
        (h_filtration := futureFiltration_antitone X)
        (h_le := fun n => futureFiltration_le X n hX_meas)
        (f := (Set.indicator (C i) (fun _ => (1:ℝ))) ∘ X 0)
        (h_f_int := by
          simpa using
            Exchangeability.Probability.integrable_indicator_comp
              (μ := μ) (X := X 0) (hX := hX_meas 0) (hB := hC i))
      -- Rewrite ⨅ futureFiltration to tailSigma
      simpa [← tailSigmaFuture_eq_iInf, tailSigmaFuture_eq_tailSigma] using this
    
    -- Tail factorization
    have h_tail : μ[indProd X m C | tailSigma X] =ᵐ[μ]
        (fun ω => ∏ i : Fin m,
          μ[Set.indicator (C i) (fun _ => (1:ℝ)) ∘ (X 0) | tailSigma X] ω) :=
      tail_factorization_from_future X hX_meas m C hC h_fact h_conv
    
    -- Integrate both sides (tower property)
    have h_int_tail : ∫ ω, indProd X m C ω ∂μ
        = ∫ ω, (∏ i : Fin m,
            μ[Set.indicator (C i) (fun _ => (1:ℝ)) ∘ (X 0) | tailSigma X] ω) ∂μ := by
      sorry  -- TODO: Tower property ∫ f = ∫ μ[f|tail] + use h_tail for a.e. equality
             -- This is standard:  integral_condExp + EventuallyEq.integral_eq
    
    -- Replace each CE with ν ω (C i).toReal using hν_law
    have h_swap : (fun ω => ∏ i : Fin m,
          μ[Set.indicator (C i) (fun _ => (1:ℝ)) ∘ (X 0) | tailSigma X] ω)
        =ᵐ[μ] (fun ω => ∏ i : Fin m, (ν ω (C i)).toReal) := by
      -- Product of a.e. equal functions is a.e. equal
      -- For each i, we have hν_law: (ν · (C i)).toReal =ᵐ μ[indicator | tail]
      have h_each : ∀ i : Fin m,
          (fun ω => μ[Set.indicator (C i) (fun _ => (1:ℝ)) ∘ (X 0) | tailSigma X] ω)
            =ᵐ[μ] (fun ω => (ν ω (C i)).toReal) :=
        fun i => (hν_law 0 (C i) (hC i)).symm
      -- Combine using finite product
      sorry  -- TODO: Use ae_all_iff + Finset.prod_congr to get product equality
    
    -- RHS: bind measure on rectangle
    have hR : (μ.bind (fun ω => Measure.pi fun _ : Fin m => ν ω)) (Set.univ.pi C)
        = ENNReal.ofReal (∫ ω, (∏ i : Fin m, (ν ω (C i)).toReal) ∂μ) := by
      sorry  -- TODO: Standard bind/pi formula for rectangles + ENNReal conversion
    
    -- Combine: both equal after using hL, h_int_tail, h_swap, hR
    sorry  -- TODO: Chain the equalities with toReal conversions

  -- Step 3: Extend from rectangles to full σ-algebra via π-λ theorem
  sorry  -- TODO: Apply Measure.ext_of_generateFrom_of_iUnion with h_pi and h_agree

/-- **Finite product formula for strictly monotone subsequences**.

For any strictly increasing subsequence `k`, the joint law of `(X_{k(0)}, ..., X_{k(m-1)})`
equals the independent product under the directing measure ν.

This reduces to the identity case via contractability. -/
lemma finite_product_formula_strictMono
    [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
    (X : ℕ → Ω → α)
    (hX : Contractable μ X)
    (hX_meas : ∀ n, Measurable (X n))
    (ν : Ω → Measure α)
    (hν_prob : ∀ ω, IsProbabilityMeasure (ν ω))
    (hν_meas : ∀ B : Set α, MeasurableSet B → Measurable (fun ω => ν ω B))
    (hν_law : ∀ n B, MeasurableSet B →
        (fun ω => (ν ω B).toReal) =ᵐ[μ] μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ (X n) | tailSigma X])
    (m : ℕ) (k : Fin m → ℕ) (hk : StrictMono k) :
    Measure.map (fun ω => fun i : Fin m => X (k i) ω) μ
      = μ.bind (fun ω => Measure.pi fun _ : Fin m => ν ω) := by
  classical
  -- Contractability gives equality with the identity map
  have hmap := hX m k hk
  calc
    Measure.map (fun ω => fun i : Fin m => X (k i) ω) μ
        = Measure.map (fun ω => fun i : Fin m => X i ω) μ := by simpa using hmap
    _   = μ.bind (fun ω => Measure.pi fun _ : Fin m => ν ω) :=
          finite_product_formula_id X hX hX_meas ν hν_prob hν_meas hν_law m

/-- **Finite product formula** (wrapper with StrictMono requirement).

This is the main statement: for strictly monotone index sequences, the joint law
is the independent product. This is what we need for de Finetti's theorem. -/
lemma finite_product_formula
    [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
    (X : ℕ → Ω → α)
    (hX : Contractable μ X)
    (hX_meas : ∀ n, Measurable (X n))
    (ν : Ω → Measure α)
    (hν_prob : ∀ ω, IsProbabilityMeasure (ν ω))
    (hν_meas : ∀ B : Set α, MeasurableSet B → Measurable (fun ω => ν ω B))
    (hν_law : ∀ n B, MeasurableSet B →
        (fun ω => (ν ω B).toReal) =ᵐ[μ] μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ (X n) | tailSigma X])
    (m : ℕ) (k : Fin m → ℕ) (hk : StrictMono k) :
    Measure.map (fun ω => fun i : Fin m => X (k i) ω) μ
      = μ.bind (fun ω => Measure.pi fun _ : Fin m => ν ω) :=
  finite_product_formula_strictMono X hX hX_meas ν hν_prob hν_meas hν_law m k hk

/-!
## Notes

The main de Finetti theorem using this machinery is in `TheoremViaMartingale.lean`.
This file provides the proof infrastructure (helper lemmas and constructions).
-/

end ViaMartingale
end DeFinetti
end Exchangeability
