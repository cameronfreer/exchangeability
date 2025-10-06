/-
Copyright (c) 2025 The Exchangeability Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer, Cascade
-/
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Topology.Basic
import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Probability.ProductMeasure

/-!
# Infinite Products of Identically Distributed Measures

This file constructs the infinite product measure `ν^ℕ` on `ℕ → α` for a given
probability measure `ν : Measure α`. The construction uses mathlib's `Measure.infinitePi`,
which implements the Kolmogorov extension theorem via projective limits.

## Main definitions

* `iidProjectiveFamily ν`: The projective family of finite product measures indexed by `Finset ℕ`.
  For each finite `I`, gives `Measure.pi (fun i : I => ν)`.
* `iidProduct ν`: The probability measure on `ℕ → α` defined as `Measure.infinitePi (fun _ : ℕ => ν)`.
  This is the unique measure whose finite-dimensional marginals are the i.i.d. products.

## Main statements

* `iidProjectiveFamily_projective`: The finite products form a projective family.
* `iidProduct_isProjectiveLimit`: `iidProduct ν` is the projective limit of `iidProjectiveFamily ν`.
* `cylinder_finset`: Marginals on finite subsets equal the corresponding finite products.
* `cylinder_fintype`: Marginals on `Fin n` equal the n-fold product (TODO).
* `perm_eq`: The measure is invariant under permutations of ℕ (TODO).

## Implementation notes

The construction is completely axiom-free, using:
1. `Measure.pi` for finite products (requires `Fintype`)
2. `isProjectiveMeasureFamily_pi` to show projectivity
3. `Measure.infinitePi` for the infinite product (Kolmogorov extension)
4. `infinitePi_map_restrict` for marginal characterization

This replaces previous axiomatizations and provides a fully formalized construction
of infinite i.i.d. product measures.
-/

noncomputable section

open scoped ENNReal MeasureTheory
open MeasureTheory Set ProbabilityTheory

namespace Exchangeability
namespace Probability

variable {α : Type*} [MeasurableSpace α]

/-- The projective family of finite product measures for the i.i.d. construction.

For each finite subset `I : Finset ℕ`, this gives the product measure on `∀ i : I, α`. -/
def iidProjectiveFamily (ν : Measure α) [IsProbabilityMeasure ν] :
    ∀ I : Finset ℕ, Measure (∀ _ : I, α) :=
  fun I => Measure.pi (fun (_ : I) => ν)

/-- The projective family is indeed projective: projections preserve the measure.

This is a special case of mathlib's `isProjectiveMeasureFamily_pi` for constant families. -/
lemma iidProjectiveFamily_projective (ν : Measure α) [IsProbabilityMeasure ν] :
    @IsProjectiveMeasureFamily ℕ (fun _ => α) (fun _ => inferInstance) (iidProjectiveFamily ν) := by
  -- Use mathlib's isProjectiveMeasureFamily_pi which works for any family of probability measures
  have : @IsProjectiveMeasureFamily ℕ (fun _ => α) (fun _ => inferInstance)
    (fun I : Finset ℕ => Measure.pi (fun i : I => ν)) :=
    @isProjectiveMeasureFamily_pi ℕ (fun _ => α) (fun _ => inferInstance) (fun _ => ν) (fun _ => inferInstance)
  exact this

/-- The infinite i.i.d. product measure `ν^ℕ` on `ℕ → α`.

This is defined using mathlib's `Measure.infinitePi`, which constructs the projective limit
of the family of finite product measures via Kolmogorov's extension theorem.

The construction:
1. Defines finite product measures for each `Finset ℕ`
2. Shows they form a projective family (projections preserve measure)
3. Extends to the whole σ-algebra via Carathéodory's extension theorem
4. The result is the unique probability measure with the correct finite-dimensional marginals -/
def iidProduct (ν : Measure α) [IsProbabilityMeasure ν] : Measure (ℕ → α) :=
  Measure.infinitePi (fun _ : ℕ => ν)

/-- The constructed measure is the projective limit of the finite products.

This is mathlib's `isProjectiveLimit_infinitePi` specialized to constant families. -/
lemma iidProduct_isProjectiveLimit (ν : Measure α) [IsProbabilityMeasure ν] :
    @IsProjectiveLimit ℕ (fun _ => α) (fun _ => inferInstance) (iidProduct ν) (iidProjectiveFamily ν) := by
  intro I
  unfold iidProduct iidProjectiveFamily
  exact Measure.infinitePi_map_restrict (fun _ : ℕ => ν)

namespace iidProduct

variable (ν : Measure α) [IsProbabilityMeasure ν]

/-- The measure `iidProduct ν` is a probability measure.

This follows from the projective limit characterization: each finite product is a
probability measure, so the projective limit is too. -/
instance : IsProbabilityMeasure (iidProduct ν) := by
  have : ∀ I : Finset ℕ, IsProbabilityMeasure (iidProjectiveFamily ν I) := fun I => by
    show IsProbabilityMeasure (Measure.pi (fun (_ : I) => ν))
    infer_instance
  exact @IsProjectiveLimit.isProbabilityMeasure ℕ (fun _ => α) (fun _ => inferInstance)
    (iidProjectiveFamily ν) (iidProduct ν) this (iidProduct_isProjectiveLimit ν)

/-- Marginal distributions on finite subsets.

For any finite subset `I : Finset ℕ`, the marginal distribution of `iidProduct ν`
on the coordinates in `I` equals the finite product measure `ν^I`. -/
lemma cylinder_finset (I : Finset ℕ) :
    (iidProduct ν).map I.restrict = Measure.pi fun _ : I => ν := by
  exact iidProduct_isProjectiveLimit ν I

/-- Finite-dimensional distributions indexed by `Fin n`.

The marginal distribution on the first `n` coordinates equals the finite product measure `ν^n`. -/
lemma cylinder_fintype (n : ℕ) :
    (iidProduct ν).map (fun f : ℕ → α => fun i : Fin n => f i) =
      Measure.pi fun _ : Fin n => ν := by
  -- Show both measures agree on all measurable rectangles
  symm
  apply Measure.pi_eq
  intro s hs

  -- Compute the LHS: (iidProduct ν).map (...) applied to rectangle Set.univ.pi s
  have h_meas : Measurable (fun f : ℕ → α => fun i : Fin n => f i) :=
    measurable_pi_lambda _ (fun _ => measurable_pi_apply _)

  calc (iidProduct ν).map (fun f : ℕ → α => fun i : Fin n => f i) (Set.univ.pi s)
      = iidProduct ν ((fun f : ℕ → α => fun i : Fin n => f i) ⁻¹' (Set.univ.pi s)) := by
        rw [Measure.map_apply h_meas (.univ_pi hs)]
    _ = iidProduct ν {f : ℕ → α | ∀ i : Fin n, f i ∈ s i} := by
        congr 1
        ext f
        simp [Set.pi]
    _ = iidProduct ν (Set.pi (Finset.range n) fun i : ℕ => if h : i < n then s ⟨i, h⟩ else Set.univ) := by
        congr 1
        ext f
        simp only [Set.mem_setOf_eq, Set.mem_pi]
        constructor
        · intro hf i (hi : i ∈ Finset.range n)
          have hi' : i < n := Finset.mem_range.mp hi
          simp only [hi', dite_true]
          exact hf ⟨i, hi'⟩
        · intro hf ⟨i, hi⟩
          have hi' : i ∈ Finset.range n := Finset.mem_range.mpr hi
          specialize hf i hi'
          simp only [hi, dite_true] at hf
          exact hf
    _ = ∏ i ∈ Finset.range n, ν (if h : i < n then s ⟨i, h⟩ else Set.univ) := by
        unfold iidProduct
        rw [Measure.infinitePi_pi]
        intro i hi
        have hi' : i < n := Finset.mem_range.mp hi
        simp only [hi', dite_true]
        exact hs ⟨i, hi'⟩
    _ = ∏ i : Fin n, ν (s i) := by
        rw [← Fin.prod_univ_eq_prod_range]
        congr 1
        funext i
        simp [i.isLt]

/-- Invariance under arbitrary permutations of coordinates.

This follows from mathlib's `infinitePi_map_piCongrLeft`: mapping the infinite product
by a permutation gives back the same measure when the family is constant.

For constant families `μ i = ν` for all `i`, we have:
`(infinitePi (fun _ => ν)).map (piCongrLeft σ) = infinitePi (fun _ => ν)`
because `μ (σ i) = ν = μ i` for all `i`.
-/
lemma perm_eq (σ : Equiv.Perm ℕ) :
    (iidProduct ν).map (fun f => f ∘ σ) = iidProduct ν := by
  unfold iidProduct

  -- Use eq_infinitePi to show the mapped measure equals infinitePi
  -- Both are probability measures that agree on rectangles
  apply Measure.eq_infinitePi
  intro s t ht

  -- Need to show: (infinitePi ν).map (fun f => f ∘ σ) (Set.pi s t) = ∏ i ∈ s, ν (t i)
  rw [Measure.map_apply _ (.pi s.countable_toSet (by simpa using ht))]
  swap
  · exact measurable_pi_lambda _ (fun _ => measurable_pi_apply _)

  -- The preimage under (fun f => f ∘ σ) of Set.pi s t
  -- We'll express this using Finset.map instead of Set.image for cleaner measure computation
  have h_preimage : (fun f : ℕ → α => f ∘ σ) ⁻¹' (Set.pi s t) =
      Set.pi (Finset.map σ.toEmbedding s) (fun j => t (σ.symm j)) := by
    ext f
    simp only [Set.mem_preimage, Set.mem_pi, Function.comp_apply,
               Finset.mem_coe, Finset.mem_map, Equiv.toEmbedding_apply]
    constructor
    · intro h j
      rintro ⟨i, hi, rfl⟩
      rw [σ.symm_apply_apply]
      exact h i hi
    · intro h i hi
      specialize h (σ i) ⟨i, hi, rfl⟩
      rwa [σ.symm_apply_apply] at h

  rw [h_preimage, Measure.infinitePi_pi]
  · -- Show the products are equal: ∏ j ∈ map σ s, ν (t (σ⁻¹ j)) = ∏ i ∈ s, ν (t i)
    rw [Finset.prod_map]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Equiv.toEmbedding_apply, σ.symm_apply_apply]
  · intro j hj
    simp only [Finset.mem_map, Equiv.toEmbedding_apply] at hj
    obtain ⟨i, hi, rfl⟩ := hj
    rw [show t (σ.symm (σ i)) = t i by rw [σ.symm_apply_apply]]
    exact ht i hi

end iidProduct

end Probability
end Exchangeability
