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

/-!
# Infinite Products of Identically Distributed Measures

This file constructs the infinite product measure `ν^ℕ` on `ℕ → α` for a given
probability measure `ν : Measure α`. We follow the strategy used in mathlib's
Ionescu–Tulcea development for kernels (`ProbabilityTheory.Kernel.IonescuTulcea.Traj`),
specialised to the case of constant kernels coming from an i.i.d. sequence.

Our goal is twofold:

1. Build a probability measure `iidProduct ν` on `ℕ → α` whose finite-dimensional
   marginals coincide with the finite product measures `Measure.pi` on `Fin n → α`.
2. Show that the resulting measure is invariant under finite permutations of the indices.

These results replace the axioms `productMeasure_exists` and
`constantProduct_comp_perm` previously assumed in `Exchangeability.Contractability`. They
provide the projective limit and symmetry properties required for the Kolmogorov
extension step in the contractability → exchangeability proof.

## Main definitions

* `iidKernel ν`: constant Markov kernel used to iterate via Ionescu–Tulcea.
* `iidTraj ν`: kernel on `Unit` taking value `ν^ℕ` as a kernel.
* `iidProduct ν`: the probability measure on `ℕ → α` obtained by evaluating `iidTraj ν` at `()`. 

## Main statements

* `iidProduct_projective`: finite-dimensional marginals of `iidProduct ν` agree with
  the product measure `Measure.pi (fun _ : Fin n => ν)`.
* `iidProduct_perm`: `iidProduct ν` is invariant under any permutation of `ℕ` with finite support.

We keep the more general machinery in a standalone file so that other developments can
import it if needed.
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

**Proof strategy**: Use mathlib's `Measure.pi_map_piCongrLeft` or similar reindexing lemmas
to show that restricting the index set from I to J ⊆ I gives the product measure on J. -/
lemma iidProjectiveFamily_projective (ν : Measure α) [IsProbabilityMeasure ν] :
    @IsProjectiveMeasureFamily ℕ (fun _ => α) (fun _ => inferInstance) (iidProjectiveFamily ν) := by
  intro I J hJI
  -- Need to show: (Measure.pi (fun _ : I => ν)).map (Finset.restrict₂ hJI) = Measure.pi (fun _ : J => ν)
  sorry  -- TODO: Prove using Measure.pi_map and reindexing lemmas

/-- The infinite i.i.d. product measure `ν^ℕ` on `ℕ → α`.

This is constructed as the projective limit of the family of finite product measures.
While mathlib's `Measure.pi` requires `Fintype ι`, the projective limit construction
works for any index set, giving us the infinite product measure.

**Construction**:
1. Define `iidProjectiveFamily ν` giving finite product measures
2. Take the projective limit (which exists and is unique by Kolmogorov extension)
3. The limit is characterized by: for all finite `I`, the marginal on `I` equals `ν^I`

Note: The actual construction of the projective limit measure requires the Kolmogorov
extension theorem, which is axiomatized here pending full formalization. -/
axiom iidProduct (ν : Measure α) [IsProbabilityMeasure ν] : Measure (ℕ → α)

/-- The constructed measure is the projective limit of the finite products. -/
axiom iidProduct_isProjectiveLimit (ν : Measure α) [IsProbabilityMeasure ν] :
    @IsProjectiveLimit ℕ (fun _ => α) (fun _ => inferInstance) (iidProduct ν) (iidProjectiveFamily ν)

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
  -- Use cylinder_finset with I = Finset.univ : Finset (Fin n)
  -- Need to show the two restriction maps are equal
  sorry  -- TODO: Show (fun f => fun i : Fin n => f i) equals (Finset.univ : Finset (Fin n)).restrict up to reindexing

/-- Invariance under arbitrary permutations of coordinates.

This is a consequence of the projective limit characterization: finite products are
invariant under permutations, and this extends to the infinite product by uniqueness.

**Proof strategy**:
1. Define a new projective family via σ: `P' I := (iidProduct ν).map ((σ.restrict I) ∘ I.restrict)`
2. Show P' is projective
3. Show P' I = iidProjectiveFamily ν I for all finite I (using finite product permutation invariance)
4. By uniqueness of projective limits: (iidProduct ν).map (· ∘ σ) = iidProduct ν
-/
lemma perm_eq (σ : Equiv.Perm ℕ) :
    (iidProduct ν).map (fun f => f ∘ σ) = iidProduct ν := by
  sorry  -- TODO: Prove using projective limit uniqueness and finite permutation invariance

end iidProduct

end Probability
end Exchangeability
