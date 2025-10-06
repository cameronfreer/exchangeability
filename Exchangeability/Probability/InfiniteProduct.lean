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
  -- Strategy: Use measure uniqueness on rectangles (Measure.pi_eq)
  -- For each rectangle {f | ∀ i, f i ∈ s i}, show both measures assign the same value
  -- This follows from:
  -- 1. LHS: Use infinitePi properties and the fact that Fin n ≃ Finset.range n
  -- 2. RHS: Direct from Measure.pi_pi
  -- Both give ∏ i, ν (s i)

  sorry  -- TODO: Apply Measure.pi_eq and show agreement on rectangles

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
  -- For constant families, infinitePi_map_piCongrLeft gives us what we need
  -- Since (fun _ => ν) ∘ σ.symm = (fun _ => ν), we have the invariance

  -- The hard part is showing (fun f => f ∘ σ) = MeasurableEquiv.piCongrLeft σ.symm
  -- This is a definitional obstacle - leave as sorry with clear strategy
  sorry  -- TODO: Use Measure.infinitePi_map_piCongrLeft after showing function equality

end iidProduct

end Probability
end Exchangeability
