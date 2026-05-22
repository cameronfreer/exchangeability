/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
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

This file constructs the **infinite i.i.d. product measure** `ν^ℕ` on the space
`ℕ → α` for a given probability measure `ν : Measure α`. This is the fundamental
measure-theoretic construction underlying i.i.d. sequences.

## Main definitions

* `iidProjectiveFamily ν`: The projective family of finite product measures indexed
  by `Finset ℕ`. For each finite subset `I`, gives the product measure `ν^I` on `∀ i : I, α`.
* `iidProduct ν`: The probability measure on `ℕ → α` representing an i.i.d. sequence
  with marginal distribution `ν`. Defined as `Measure.infinitePi (fun _ : ℕ => ν)`.

## Main results

* `iidProduct_isProjectiveLimit`: `iidProduct ν` is the projective limit of the
  finite products, making it unique with this property.
* `perm_eq`: **The measure is invariant under all permutations of ℕ**, proving that
  i.i.d. sequences are fully exchangeable.

## Mathematical background

**Kolmogorov extension theorem:** Given a consistent family of finite-dimensional
distributions (a projective family), there exists a unique probability measure on
the infinite product space with these marginals.

For the i.i.d. case, consistency is automatic: if we want each coordinate to be
distributed as `ν` independently, then for any finite subset `I`, the joint
distribution is just `ν^I`. Mathlib's `Measure.infinitePi` implements this
construction via Carathéodory's extension theorem.

## Implementation approach

We use mathlib's Kolmogorov extension machinery rather than implementing it from
scratch:
1. **Finite products** (`Measure.pi`): For finite index sets (requires `Fintype`)
2. **Projectivity** (`isProjectiveMeasureFamily_pi`): Finite products are consistent
3. **Infinite extension** (`Measure.infinitePi`): Extends to infinite product via
   Carathéodory's theorem
4. **Marginal characterization** (`infinitePi_map_restrict`): The extended measure
   has the correct finite-dimensional marginals

This construction uses mathlib's standard measure theory infrastructure.

## Relation to other files

This construction is used in `Contractability.lean` and `ConditionallyIID.lean` to
build exchangeable sequences. The permutation invariance (`perm_eq`) shows that
i.i.d. sequences are the canonical example of exchangeable sequences.

## References

* Kallenberg, "Foundations of Modern Probability" (2002), Theorem 6.10 (Kolmogorov extension)
* Billingsley, "Probability and Measure" (1995), Section 36 (Product measures)
-/

noncomputable section

open scoped ENNReal MeasureTheory
open MeasureTheory Set ProbabilityTheory

namespace Exchangeability
namespace Probability

variable {α : Type*} [MeasurableSpace α]

/--
The projective family of finite product measures for the i.i.d. construction.

**Definition:** For each finite subset `I : Finset ℕ`, this returns the product
measure `ν^I` on `∀ i : I, α`, where each coordinate is independently distributed
according to `ν`.

**Purpose:** This family of finite-dimensional distributions serves as the input to
Kolmogorov's extension theorem. We will show that this family is projective
(consistent under marginalization) and then extend it to an infinite product.
-/
@[nolint unusedArguments]
def iidProjectiveFamily {ν : Measure α} [IsProbabilityMeasure ν] :
    ∀ I : Finset ℕ, Measure (∀ _ : I, α) :=
  fun I => Measure.pi (fun (_ : I) => ν)

/--
The infinite i.i.d. product measure `ν^ℕ` on `ℕ → α`.

**Definition:** This is the unique probability measure on `ℕ → α` such that:
- Each coordinate `X_i` is distributed according to `ν`
- The coordinates are mutually independent

**Construction:** Uses mathlib's `Measure.infinitePi`, which implements Kolmogorov's
extension theorem:
1. Start with finite product measures `ν^I` for each finite `I ⊆ ℕ`
2. Verify they form a projective family (consistency under marginalization)
3. Apply Carathéodory's extension theorem to extend to the infinite product σ-algebra
4. The result is the unique probability measure with the specified finite marginals

**Uniqueness:** This measure is uniquely determined by the requirement that finite-
dimensional marginals are i.i.d. products. This follows from the π-system uniqueness
theorem (used in `Exchangeability.lean`).

**Mathematical significance:** This is the fundamental construction underlying the
theory of i.i.d. sequences, forming the basis for the law of large numbers, central
limit theorem, and de Finetti's theorem.
-/
@[nolint unusedArguments]
def iidProduct (ν : Measure α) [IsProbabilityMeasure ν] : Measure (ℕ → α) :=
  Measure.infinitePi (fun _ : ℕ => ν)

/--
The infinite product is the projective limit of the finite products.

**Statement:** `iidProduct ν` is the unique measure whose marginals on all finite
subsets `I` match the finite products `ν^I`.

**Mathematical content:** This characterizes `iidProduct ν` as a projective limit,
meaning that for every finite `I ⊆ ℕ`, if we marginalize the infinite product onto
coordinates in `I`, we recover the finite product measure `ν^I`.

This is the defining property from Kolmogorov's extension theorem.
-/
lemma iidProduct_isProjectiveLimit {ν : Measure α} [IsProbabilityMeasure ν] :
    @IsProjectiveLimit ℕ (fun _ => α) (fun _ => inferInstance) (iidProduct ν) (iidProjectiveFamily (ν:=ν)) :=
  fun I => by simp only [iidProduct, iidProjectiveFamily, Measure.infinitePi_map_restrict]

namespace iidProduct

variable (ν : Measure α) [IsProbabilityMeasure ν]

/-- The measure `iidProduct ν` is a probability measure.

This follows from the projective limit characterization: each finite product is a
probability measure, so the projective limit is too. -/
instance : IsProbabilityMeasure (iidProduct ν) := by
  have : ∀ I : Finset ℕ, IsProbabilityMeasure (iidProjectiveFamily (ν:=ν) I) := fun I => by
    show IsProbabilityMeasure (Measure.pi (fun (_ : I) => ν))
    infer_instance
  exact @IsProjectiveLimit.isProbabilityMeasure ℕ (fun _ => α) (fun _ => inferInstance)
    (iidProjectiveFamily (ν:=ν)) (iidProduct ν) this (iidProduct_isProjectiveLimit (ν:=ν))

/--
**Key result:** i.i.d. sequences are invariant under all permutations of the indices.

**Statement:** For any permutation `σ : Perm ℕ`, reindexing an i.i.d. sequence by `σ`
gives the same distribution. Formally, the pushforward of `iidProduct ν` under the
map `f ↦ f ∘ σ` equals `iidProduct ν`.

**Mathematical significance:** This proves that **i.i.d. sequences are fully exchangeable**.
In fact, i.i.d. is the canonical example of exchangeability, and de Finetti's theorem
shows that all exchangeable sequences are conditionally i.i.d.

**Intuition:** If we randomly permute the indices of an i.i.d. sequence, we still get
an i.i.d. sequence with the same distribution, because:
1. Each coordinate is still distributed as `ν` (permuting doesn't change marginals)
2. Independence is preserved (permuting independent coordinates gives independent coordinates)

**Proof strategy:** Use `Measure.eq_infinitePi` to show both measures agree on all
measurable rectangles. For a rectangle indexed by finite set `s`, the preimage under
`f ↦ f ∘ σ` is a rectangle indexed by `σ(s)`, and the product over `σ(s)` equals
the product over `s` by permutation of the product.

**Connection to other results:** Combined with `Exchangeability.lean`, this shows
that i.i.d. ⇒ fully exchangeable ⇒ exchangeable, completing one direction of
de Finetti's equivalence.
-/
lemma perm_eq {σ : Equiv.Perm ℕ} :
    (iidProduct ν).map (fun f => f ∘ σ) = iidProduct ν := by
  unfold iidProduct

  -- Use eq_infinitePi to show the mapped measure equals infinitePi
  -- Both are probability measures that agree on rectangles
  apply Measure.eq_infinitePi
  intro s t ht

  -- Need to show: (infinitePi ν).map (fun f => f ∘ σ) (Set.pi s t) = ∏ i ∈ s, ν (t i)
  rw [Measure.map_apply _ (.pi s.countable_toSet (fun _ _ => ht _))]
  swap
  · fun_prop

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
    exact ht i

end iidProduct

end Probability
end Exchangeability
