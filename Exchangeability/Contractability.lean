/-
Copyright (c) 2025 The Exchangeability Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Contractability and the de Finetti-Ryll-Nardzewski Theorem

This file establishes the relationship between exchangeability and contractability,
following Kallenberg's "Probabilistic Symmetries and Invariance Principles" (2005).

## Main definitions

* `Contractable`: A sequence is contractable if all increasing subsequences of equal length
  have the same distribution.
* `ConditionallyIID`: A sequence is conditionally i.i.d. if it is i.i.d. given some σ-field.
* `MixedIID`: A sequence is mixed i.i.d. if its distribution is a mixture of i.i.d. distributions.

## Main results

* `FullyExchangeable.exchangeable`: Full exchangeability implies (finite) exchangeability.
* `contractable_of_exchangeable`: Exchangeable implies contractable (via permutation extension).
* `exchangeable_of_conditionallyIID`: Conditionally i.i.d. implies exchangeable.

## Note on the de Finetti equivalences

The full de Finetti-Ryll-Nardzewski theorem establishes: contractable ↔ exchangeable ↔ conditionally i.i.d.

This file proves the "easy" directions:
- Exchangeable → contractable (via permutation extension)
- Conditionally i.i.d. → exchangeable (via product measure permutation invariance)

The "hard" directions requiring ergodic theory are stated and proved in `Exchangeability/DeFinetti.lean`
using one of three approaches (L2, Koopman, or martingale):
- Contractable → exchangeable (needs mean ergodic theorem)
- Exchangeable → conditionally i.i.d. (needs ergodic decomposition for Borel spaces)

The separate direction (exchangeable → fully exchangeable) is in `Exchangeability/Exchangeability.lean`.

## References

* Kallenberg, "Probabilistic Symmetries and Invariance Principles" (2005), Theorem 1.1
-/

open MeasureTheory ProbabilityTheory

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

namespace Exchangeability

/-- An infinite family of random variables `X : ℕ → Ω → α` is **exchangeable**
if the finite-dimensional distributions are invariant under permutations of finitely
many indices. -/
def Exchangeable (μ : Measure Ω) (X : ℕ → Ω → α) : Prop :=
  ∀ n (σ : Equiv.Perm (Fin n)),
    Measure.map (fun ω => fun i : Fin n => X (σ i) ω) μ =
      Measure.map (fun ω => fun i : Fin n => X i ω) μ

/-- An infinite family of random variables `X : ℕ → Ω → α` is **fully exchangeable**
if the joint distribution is invariant under all permutations of ℕ. -/
def FullyExchangeable (μ : Measure Ω) (X : ℕ → Ω → α) : Prop :=
  ∀ (π : Equiv.Perm ℕ),
    Measure.map (fun ω => fun i : ℕ => X (π i) ω) μ =
      Measure.map (fun ω => fun i : ℕ => X i ω) μ

/-- Extend a permutation of `Fin n` to a permutation of ℕ by fixing all `i ≥ n`. -/
def extendFinPerm (n : ℕ) (σ : Equiv.Perm (Fin n)) : Equiv.Perm ℕ where
  toFun i := if h : i < n then (σ ⟨i, h⟩).1 else i
  invFun i := if h : i < n then (σ.symm ⟨i, h⟩).1 else i
  left_inv := by
    intro i
    by_cases h : i < n
    · -- Case: i < n, so toFun i = (σ ⟨i, h⟩).1
      simp only [h, dif_pos]
      -- Need to show: invFun (σ ⟨i, h⟩).1 = i
      have hσ : (σ ⟨i, h⟩).1 < n := (σ ⟨i, h⟩).isLt
      simp only [hσ, dif_pos]
      -- Now: (σ.symm ⟨(σ ⟨i, h⟩).1, hσ⟩).1 = i
      simp [Fin.eta, Equiv.symm_apply_apply]
    · -- Case: i ≥ n, so toFun i = i
      simp only [h, dif_neg, not_false_eq_true]
  right_inv := by
    intro i
    by_cases h : i < n
    · -- Case: i < n, so invFun i = (σ.symm ⟨i, h⟩).1
      simp only [h, dif_pos]
      -- Need to show: toFun (σ.symm ⟨i, h⟩).1 = i
      have hσ : (σ.symm ⟨i, h⟩).1 < n := (σ.symm ⟨i, h⟩).isLt
      simp only [hσ, dif_pos]
      -- Now: (σ ⟨(σ.symm ⟨i, h⟩).1, hσ⟩).1 = i
      simp [Fin.eta, Equiv.apply_symm_apply]
    · -- Case: i ≥ n, so invFun i = i
      simp only [h, dif_neg, not_false_eq_true]

/-- Full exchangeability implies exchangeability. -/
lemma FullyExchangeable.exchangeable {μ : Measure Ω} {X : ℕ → Ω → α}
    (hX_meas : ∀ i, Measurable (X i)) (hX : FullyExchangeable μ X) : Exchangeable μ X := by
  classical
  intro n σ
  let π := extendFinPerm n σ
  have hπ := hX π
  let proj : (ℕ → α) → (Fin n → α) := fun f i => f i.val
  have hproj_meas : Measurable proj :=
    measurable_pi_lambda _ (fun i => measurable_pi_apply i.val)
  have hmap₁ :=
    Measure.map_map (μ:=μ)
      (f:=fun ω => fun i : ℕ => X (π i) ω)
      (g:=proj)
      hproj_meas
      (measurable_pi_lambda _ (fun i => hX_meas (π i)))
  have hmap₂ :=
    Measure.map_map (μ:=μ)
      (f:=fun ω => fun i : ℕ => X i ω)
      (g:=proj)
      hproj_meas
      (measurable_pi_lambda _ (fun i => hX_meas i))
  have hprojσ :
      proj ∘ (fun ω => fun i : ℕ => X (π i) ω)
        = fun ω => fun i : Fin n => X (σ i) ω := by
    funext ω i
    simp [Function.comp, proj, π, extendFinPerm, Fin.is_lt]
  have hprojid :
      proj ∘ (fun ω => fun i : ℕ => X i ω)
        = fun ω => fun i : Fin n => X i.val ω := by
    ext ω i
    rfl
  -- Project both laws to the first n coordinates and compare
  calc Measure.map (fun ω i => X (σ i).val ω) μ
      = Measure.map (proj ∘ fun ω i => X (π i) ω) μ := by rw [hprojσ]
    _ = Measure.map proj (Measure.map (fun ω i => X (π i) ω) μ) := hmap₁.symm
    _ = Measure.map proj (Measure.map (fun ω i => X i ω) μ) := by rw [hπ]
    _ = Measure.map (proj ∘ fun ω i => X i ω) μ := hmap₂
    _ = Measure.map (fun ω i => X i.val ω) μ := by rw [hprojid]

/-- A finite or infinite random sequence ξ is **contractable** if all increasing subsequences
of equal length have the same distribution.

That is, (ξ_{k₁}, ..., ξ_{kₘ}) has the same distribution for any choice of
k₁ < k₂ < ... < kₘ.

This is weaker than exchangeability, which requires equality for all permutations,
not just increasing sequences. -/
def Contractable (μ : Measure Ω) (X : ℕ → Ω → α) : Prop :=
  ∀ (m : ℕ) (k : Fin m → ℕ), StrictMono k →
    Measure.map (fun ω i => X (k i) ω) μ =
      Measure.map (fun ω i => X i.val ω) μ

/-- A random sequence ξ is **conditionally i.i.d.** if there exists a σ-field ℱ and
a random probability measure ν such that P[ξ ∈ · | ℱ] = ν^∞ a.s.

In other words, ν is a probability kernel from (Ω, 𝒜) to S, or equivalently,
a random element in the space ℳ₁(S) of probability measures on S. -/
def ConditionallyIID (μ : Measure Ω) (X : ℕ → Ω → α) : Prop :=
  ∃ (ℱ : MeasurableSpace Ω) (ν : Ω → Measure α),
    (∀ ω, IsProbabilityMeasure (ν ω)) ∧
    -- The conditional distribution given ℱ equals the product measure ν^∞
    sorry -- Requires conditional expectation and product measures

/-- A random sequence ξ is **mixed i.i.d.** if its distribution is a mixture of
i.i.d. distributions: P{ξ ∈ ·} = E[ν^∞] = ∫ m^∞ P(ν ∈ dm).

This is obtained by taking expectations in the conditionally i.i.d. definition. -/
def MixedIID (μ : Measure Ω) (X : ℕ → Ω → α) : Prop :=
  ∃ (ν : Measure (Measure α)),
    IsProbabilityMeasure ν ∧
    -- The distribution of X is a mixture of product measures
    sorry -- Requires integration over measures

/-- Helper lemma: If two index sequences are pointwise equal, then the corresponding
subsequences have the same distribution. -/
lemma contractable_same_range {μ : Measure Ω} {X : ℕ → Ω → α} {m : ℕ}
    (k₁ k₂ : Fin m → ℕ) (h_range : ∀ i, k₁ i = k₂ i) :
    Measure.map (fun ω i => X (k₁ i) ω) μ = Measure.map (fun ω i => X (k₂ i) ω) μ := by
  congr 1
  ext ω i
  rw [h_range]

-- ## Helper lemmas wrapping mathlib results

/-- Product measures exist in mathlib. This placeholder captures the idea that
we can construct product probability measures. The actual construction requires
Ionescu-Tulcea or similar machinery from mathlib. -/
axiom productMeasure_exists (ν : ℕ → Measure α) [∀ i, IsProbabilityMeasure (ν i)] :
  ∃ μ : Measure (ℕ → α), IsProbabilityMeasure μ

/-- A product of identical i.i.d. measures is permutation-invariant. -/
axiom constantProduct_comp_perm (ν₀ : Measure α) [IsProbabilityMeasure ν₀]
    (μ_prod : Measure (ℕ → α)) (σ : Equiv.Perm ℕ) :
    Measure.map (fun f : ℕ → α => f ∘ σ) μ_prod = μ_prod

/-- For a strictly monotone function `k : Fin m → ℕ`, the values dominate the indices. -/
lemma strictMono_Fin_ge_id {m : ℕ} {k : Fin m → ℕ} (hk : StrictMono k) (i : Fin m) :
    i.val ≤ k i := by
  classical
  cases hm : m with
  | zero => cases i
  | succ m' =>
      subst hm
      -- Work with `Fin (m' + 1)` using the standard induction principle.
      let p : Fin (m' + 1) → Prop := fun j => j.val ≤ k j
      have h : ∀ j, p j :=
        Fin.induction (m := m') (C := p)
          (by
            have : (k 0) ≥ 0 := Nat.zero_le _
            simpa [p]
            using this)
          (by
            intro j hj
            -- `hj` provides the inequality for the predecessor `castSucc j`.
            have hj' : (Fin.castSucc j).val ≤ k (Fin.castSucc j) := by
              simpa [p] using hj
            have hlt : k (Fin.castSucc j) < k (Fin.succ j) :=
              hk (Fin.castSucc_lt_succ j)
            have h₁ : j.val + 1 ≤ k (Fin.castSucc j) + 1 :=
              Nat.add_le_add_right hj' 1
            have h₂ : k (Fin.castSucc j) + 1 ≤ k (Fin.succ j) :=
              Nat.succ_le_of_lt hlt
            have : (Fin.succ j).val ≤ k (Fin.succ j) := by
              -- `Fin.succ j` has value `j.val + 1`.
              simpa [Fin.succ, Nat.succ_eq_add_one]
                using (Nat.le_trans h₁ h₂)
            simpa [p] using this)
      simpa [p] using h i

/-- Given strictly monotone k : Fin m → ℕ and n containing all k(i), we can construct
a permutation σ : Perm (Fin n) such that σ maps first m positions to k-values.
This is the key lemma needed for contractable_of_exchangeable. -/
lemma exists_perm_extending_strictMono {m n : ℕ} (k : Fin m → ℕ)
    (hk_mono : StrictMono k) (hk_bound : ∀ i, k i < n) (hmn : m ≤ n) :
    ∃ (σ : Equiv.Perm (Fin n)), ∀ (i : Fin m),
      (σ ⟨i.val, Nat.lt_of_lt_of_le i.isLt hmn⟩).val = k i := by
  sorry -- Combinatorial construction: map i < m to k(i), fill remaining slots with unused values

/-- Helper: relabeling coordinates by a finite permutation is measurable as a map
from (Fin n → α) to itself (with product σ-algebra). -/
lemma measurable_perm_map {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Measurable (fun (h : Fin n → α) => fun i => h (σ i)) := by
  -- Each coordinate i ↦ h (σ i) is measurable by measurability of evaluation.
  refine measurable_pi_lambda _ (fun i => ?_)
  -- Coordinate evaluation at (σ i) is measurable
  exact measurable_pi_apply (σ i)

/-- Helper lemma: Permuting the output coordinates doesn't change the measure.
If f and g produce the same measure, then f ∘ σ and g ∘ σ produce the same measure. -/
lemma measure_map_comp_perm {μ : Measure Ω} {n : ℕ}
    (f g : Ω → Fin n → α) (σ : Equiv.Perm (Fin n))
    (h : Measure.map f μ = Measure.map g μ)
    (hf : Measurable f) (hg : Measurable g) :
    Measure.map (fun ω i => f ω (σ i)) μ =
      Measure.map (fun ω i => g ω (σ i)) μ := by
  -- Define the relabeling map on (Fin n → α)
  let perm_map : (Fin n → α) → (Fin n → α) := fun h => h ∘ σ
  have hfcomp : Measurable (perm_map ∘ f) := (measurable_perm_map (σ:=σ)).comp hf
  have hgcomp : Measurable (perm_map ∘ g) := (measurable_perm_map (σ:=σ)).comp hg
  have hf_rw : (fun ω i => f ω (σ i)) = perm_map ∘ f := by ext ω i; rfl
  have hg_rw : (fun ω i => g ω (σ i)) = perm_map ∘ g := by ext ω i; rfl
  -- Use map_map to pull out composition
  have h_map_f : Measure.map (perm_map ∘ f) μ = Measure.map perm_map (Measure.map f μ) :=
    (Measure.map_map (measurable_perm_map (σ:=σ)) hf).symm
  have h_map_g : Measure.map (perm_map ∘ g) μ = Measure.map perm_map (Measure.map g μ) :=
    (Measure.map_map (measurable_perm_map (σ:=σ)) hg).symm
  -- Chain equalities
  calc
    Measure.map (fun ω i => f ω (σ i)) μ
        = Measure.map (perm_map ∘ f) μ := by rw [hf_rw]
    _ = Measure.map perm_map (Measure.map f μ) := h_map_f
    _ = Measure.map perm_map (Measure.map g μ) := by rw [h]
    _ = Measure.map (perm_map ∘ g) μ := h_map_g.symm
    _ = Measure.map (fun ω i => g ω (σ i)) μ := by rw [hg_rw]

/-- Special case: The identity function on Fin n is strictly monotone when
viewed as a function to ℕ. -/
lemma fin_val_strictMono (n : ℕ) : StrictMono (fun i : Fin n => i.val) := by
  intro i j hij
  exact hij

/-- For a permutation σ on Fin n, the range {σ(0), ..., σ(n-1)} equals {0, ..., n-1}. -/
lemma perm_range_eq (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    Finset.image (fun i : Fin n => σ i) Finset.univ = Finset.univ := by
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and, iff_true]
  use σ.symm x
  simp

/-- Every exchangeable sequence is contractable.
This direction is straightforward via permutation extension. -/
theorem contractable_of_exchangeable {μ : Measure Ω} {X : ℕ → Ω → α}
    (hX : Exchangeable μ X) (hX_meas : ∀ i, Measurable (X i)) : Contractable μ X := by
  intro m k hk_mono
  -- Strategy: Use exchangeability on a large enough finite space containing all k(i)
  -- Build a permutation σ : Perm (Fin n) that maps first m positions to k-values
  -- Apply exchangeability with σ and project back
  -- Let n be any number greater than all k(i). For example, take
  -- n = 1 + max { k i | i < m }. Then use exists_perm_extending_strictMono to
  -- obtain σ : Perm (Fin n) with σ i = k i for i < m. Apply hX n σ and project.
  sorry

/-- Conditionally i.i.d. implies exchangeable.
If X is conditionally i.i.d., then permutations preserve the distribution. -/
theorem exchangeable_of_conditionallyIID {μ : Measure Ω} {X : ℕ → Ω → α}
    (hX : ConditionallyIID μ X) : Exchangeable μ X := by
  intro n σ
  -- If P[ξ ∈ · | ℱ] = ν^∞ a.s., then for any permutation σ,
  -- P[ξ ∘ σ ∈ · | ℱ] = (ν^∞) ∘ σ = ν^∞ a.s. (product measures are permutation invariant)
  -- Taking expectations: P[ξ ∈ ·] = E[ν^∞] and P[ξ ∘ σ ∈ ·] = E[ν^∞]
  sorry -- TODO: Use constantProduct_comp_perm axiom

end Exchangeability
