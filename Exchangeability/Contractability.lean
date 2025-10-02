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

* `exchangeable_of_contractable`: Every contractable sequence is exchangeable (trivial).
* `contractable_of_exchangeable`: Every exchangeable infinite sequence is contractable.
* `deFinetti_RyllNardzewski`: For Borel spaces, contractable ↔ exchangeable ↔ conditionally i.i.d.

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
    · have hσ : (σ ⟨i, h⟩).1 < n := (σ ⟨i, h⟩).isLt
      simp [h, hσ, extendFinPerm]
    · simp [h, extendFinPerm]
  right_inv := by
    intro i
    by_cases h : i < n
    · have hσ : (σ.symm ⟨i, h⟩).1 < n := (σ.symm ⟨i, h⟩).isLt
      simp [h, hσ, extendFinPerm]
    · simp [h, extendFinPerm]

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

/-- Helper lemma: If we have two increasing sequences that index the same set,
then the corresponding subsequences have the same distribution (by contractability). -/
lemma contractable_same_range {μ : Measure Ω} {X : ℕ → Ω → α}
    (hX : Contractable μ X) {m : ℕ} (k₁ k₂ : Fin m → ℕ)
    (hk₁ : StrictMono k₁) (hk₂ : StrictMono k₂)
    (h_range : ∀ i, k₁ i = k₂ i) :
    Measure.map (fun ω i => X (k₁ i) ω) μ = Measure.map (fun ω i => X (k₂ i) ω) μ := by
  congr 1
  ext ω i
  rw [h_range]

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
  have h_map_f : Measure.map (perm_map ∘ f) μ = Measure.map perm_map (Measure.map f μ) := by
    simpa [Function.comp] using
      (Measure.map_map (μ:=μ) (f:=f) (g:=perm_map)
        (hg:=(measurable_perm_map (σ:=σ))) (hf:=hf))
  have h_map_g : Measure.map (perm_map ∘ g) μ = Measure.map perm_map (Measure.map g μ) := by
    simpa [Function.comp] using
      (Measure.map_map (μ:=μ) (f:=g) (g:=perm_map)
        (hg:=(measurable_perm_map (σ:=σ))) (hf:=hg))
  -- Chain equalities
  calc
    Measure.map (fun ω i => f ω (σ i)) μ
        = Measure.map (perm_map ∘ f) μ := by simpa [hf_rw]
    _ = Measure.map perm_map (Measure.map f μ) := h_map_f
    _ = Measure.map perm_map (Measure.map g μ) := by simpa [h]
    _ = Measure.map (perm_map ∘ g) μ := by simpa [Function.comp] using h_map_g.symm
    _ = Measure.map (fun ω i => g ω (σ i)) μ := by simpa [hg_rw]

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

/-- **Theorem 1.1 (de Finetti-Ryll-Nardzewski)**: Every exchangeable sequence is contractable.

Kallenberg states this is "trivial", but with our definitions it requires showing that
selecting indices via a strictly monotone function gives the same distribution as
selecting the first m indices. This follows from exchangeability via a permutation argument.

Note: The triviality in Kallenberg comes from his definition where exchangeability
already includes invariance under selecting arbitrary subsets, not just permutations
of {0,...,n-1}. -/
theorem contractable_of_exchangeable {μ : Measure Ω} {X : ℕ → Ω → α}
    (hX : Exchangeable μ X) (hX_meas : ∀ i, Measurable (X i)) : Contractable μ X := by
  intro m k hk_mono
  
  -- We need: map (fun ω i => X (k i) ω) μ = map (fun ω i => X i.val ω) μ
  
  -- Strategy: Use exchangeability on a space large enough to contain all k(i)
  -- Let n = k(m-1) + 1, so all k(i) < n for i < m
  
  -- Special case: if m = 0, the result is trivial
  cases m with
  | zero =>
    -- When m = 0, both maps Ω → (Fin 0 → α) are equal since Fin 0 → α has unique element
    congr; ext ω i; exact Fin.elim0 i
  | succ m' =>
    -- n is chosen to contain all values k(0), ..., k(m)
    let n := k ⟨m', Nat.lt_succ_self m'⟩ + 1
    
    -- Build a permutation σ : Perm (Fin n) that maps i ↦ k(i) for i < m+1
    -- This requires: k(i) < n for all i, which follows from strict monotonicity
    have hk_bound : ∀ i : Fin (m' + 1), k i < n := by
      intro i
      simp only [n]
      have : k i ≤ k ⟨m', Nat.lt_succ_self m'⟩ := by
        apply StrictMono.monotone hk_mono
        exact Fin.le_last i
      omega
    
    -- The construction of this permutation is complex - we need to:
    -- 1. Map each i < m+1 to k(i)
    -- 2. Fill in the remaining slots with the unused values
    -- This is a standard finite permutation construction but tedious in Lean
    
    sorry

/-- For infinite sequences, contractability implies exchangeability.

This is the non-trivial direction of the de Finetti-Ryll-Nardzewski theorem.
The proof uses the mean ergodic theorem. -/
-- Sorting permutation for a given σ : Perm (Fin n): there exists ρ with σ ∘ ρ strictly increasing
lemma exists_sort_perm_of_perm {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    ∃ ρ : Equiv.Perm (Fin n), StrictMono (fun i : Fin n => (σ (ρ i)).val) := by
  refine ⟨σ.symm, ?_⟩
  -- With ρ = σ.symm, we have (σ (ρ i)) = i, hence monotonicity reduces to fin_val_strictMono
  intro i j hij
  simpa [Equiv.apply_symm_apply] using (fin_val_strictMono n hij)

theorem exchangeable_of_contractable {μ : Measure Ω} {X : ℕ → Ω → α}
    [IsProbabilityMeasure μ]
    (hX : Contractable μ X)
    (hX_meas : ∀ i : ℕ, Measurable (X i)) : Exchangeable μ X := by
  intro n σ
  
  -- We need to show: (X_{σ(0)}, ..., X_{σ(n-1)}) has same distribution as (X_0, ..., X_{n-1})
  
  -- Step 1: Use ρ = σ.symm, which makes i ↦ (σ (ρ i)).val = i ↦ i.val strictly increasing
  let ρ := σ.symm
  have hρ_mono : StrictMono (fun i : Fin n => (σ (ρ i)).val) := by
    intro i j hij
    simpa [ρ, Equiv.apply_symm_apply] using fin_val_strictMono n hij
  
  -- Define the two maps Ω → (Fin n → α) we want to compare
  let f : Ω → (Fin n → α) := fun ω i => X i.val ω
  let g : Ω → (Fin n → α) := fun ω i => X (σ (ρ i)).val ω
  
  -- Measurability of f and g
  have hf : Measurable f :=
    measurable_pi_lambda _ (fun i => hX_meas i.val)
  have hg : Measurable g :=
    measurable_pi_lambda _ (fun i => hX_meas ((σ (ρ i)).val))
  
  -- Step 2: Key observation: g = f because σ (ρ i) = σ (σ.symm i) = i
  have h_g_eq_f : g = f := by
    ext ω i
    simp only [g, f, ρ]
    congr 1
    simp [Equiv.apply_symm_apply]
  
  -- So map g μ = map f μ is trivial
  have h_base : Measure.map g μ = Measure.map f μ := by rw [h_g_eq_f]
  
  -- Step 3: The issue with this approach
  -- Target: map (fun ω i => X (σ i).val ω) μ = map (fun ω i => X i.val ω) μ
  -- What we know: g = f, so map g μ = map f μ (trivial)
  --
  -- The problem: contractability gives us equality for SORTED sequences,
  -- but σ might not preserve order. To connect sorted to unsorted versions,
  -- we need permutation invariance... which is exactly what we're trying to prove!
  --
  -- Kallenberg's proof uses the "mean ergodic theorem" (FMP 10.6), not
  -- this direct combinatorial approach. The ergodic theory machinery provides
  -- a different route that avoids this circularity.
  --
  -- For now, we defer this as it requires substantial ergodic theory development.
  sorry

/-- **Theorem 1.1 (de Finetti-Ryll-Nardzewski)**: For Borel spaces,
contractable ↔ exchangeable ↔ conditionally i.i.d.

For general measurable spaces, we have:
- contractable ↔ exchangeable (always)
- conditionally i.i.d. → exchangeable (always)
- exchangeable → conditionally i.i.d. (only for Borel spaces) -/
theorem deFinetti_RyllNardzewski {μ : Measure Ω} {X : ℕ → Ω → α}
    [IsProbabilityMeasure μ] (hX_meas : ∀ i, Measurable (X i)) (hBorel : sorry) : -- Borel space condition
    Contractable μ X ↔ Exchangeable μ X ∧ ConditionallyIID μ X := by
  constructor
  · intro hC
    constructor
    · exact exchangeable_of_contractable hC hX_meas
    · -- contractable → conditionally i.i.d. (requires Borel space)
      -- This is the deep direction, using ergodic theory
      sorry
  · intro ⟨hE, hCIID⟩
    -- conditionally i.i.d. → contractable (trivial via exchangeable)
    exact contractable_of_exchangeable hE hX_meas

/-- Conditionally i.i.d. implies exchangeable (for any measurable space). -/
theorem exchangeable_of_conditionallyIID {μ : Measure Ω} {X : ℕ → Ω → α}
    (hX : ConditionallyIID μ X) : Exchangeable μ X := by
  -- If X is conditionally i.i.d., then permuting doesn't change the distribution
  -- since each ξᵢ has the same conditional distribution ν
  
  -- More precisely: If P[ξ ∈ · | ℱ] = ν^∞ a.s., then for any permutation σ,
  -- P[ξ ∘ σ ∈ · | ℱ] = (ν^∞) ∘ σ = ν^∞ a.s. (product measures are permutation invariant)
  
  -- Taking expectations: P[ξ ∈ ·] = E[ν^∞] and P[ξ ∘ σ ∈ ·] = E[ν^∞]
  -- So the distributions are equal.
  
  sorry

/-- Mixed i.i.d. implies exchangeable. -/
theorem exchangeable_of_mixedIID {μ : Measure Ω} {X : ℕ → Ω → α}
    (hX : MixedIID μ X) : Exchangeable μ X := by
  -- A mixture of i.i.d. distributions is exchangeable
  sorry

end Exchangeability
