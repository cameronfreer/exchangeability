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

* `iidProjectiveFamily_projective`: The finite products form a projective family
  (projections preserve the measure).
* `iidProduct_isProjectiveLimit`: `iidProduct ν` is the projective limit of the
  finite products, making it unique with this property.
* `cylinder_finset`: For any finite subset `I`, the marginal distribution on `I`
  equals the finite product `ν^I`.
* `cylinder_fintype`: The distribution on the first `n` coordinates equals `ν^n`.
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
def iidProjectiveFamily {ν : Measure α} [IsProbabilityMeasure ν] :
    ∀ I : Finset ℕ, Measure (∀ _ : I, α) :=
  fun I => Measure.pi (fun (_ : I) => ν)

/--
The finite product measures form a projective family (consistency condition).

**Statement:** The family `iidProjectiveFamily ν` satisfies the projectivity
condition: if `J ⊆ I`, then marginalizing `ν^I` onto coordinates in `J` gives `ν^J`.

**Mathematical content:** This is the consistency requirement for Kolmogorov's
extension theorem. For i.i.d. sequences, consistency is automatic because each
coordinate is independently distributed.

**Proof:** This is a special case of mathlib's `isProjectiveMeasureFamily_pi`,
which proves projectivity for any family of probability measures. For constant
families (same measure on each coordinate), the result is immediate.
-/
lemma iidProjectiveFamily_projective {ν : Measure α} [IsProbabilityMeasure ν] :
    @IsProjectiveMeasureFamily ℕ (fun _ => α) (fun _ => inferInstance) (iidProjectiveFamily (ν:=ν)) :=
  @isProjectiveMeasureFamily_pi ℕ (fun _ => α) (fun _ => inferInstance) (fun _ => ν) (fun _ => inferInstance)

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
Marginal distributions on arbitrary finite subsets match the finite products.

**Statement:** For any finite subset `I ⊆ ℕ`, the marginal distribution of
`iidProduct ν` on the coordinates indexed by `I` equals the product measure `ν^I`.

**Intuition:** If we project an i.i.d. sequence onto a finite set of coordinates,
we get a finite i.i.d. sample with the same marginal distribution.

This is a direct consequence of the projective limit characterization.
-/
lemma cylinder_finset {I : Finset ℕ} :
    (iidProduct ν).map I.restrict = Measure.pi fun _ : I => ν :=
  iidProduct_isProjectiveLimit (ν:=ν) I

/--
The distribution on the first `n` coordinates is the n-fold product `ν^n`.

**Statement:** The marginal distribution of `iidProduct ν` on `{0, 1, ..., n-1}`
equals the n-fold product measure on `Fin n → α`.

**Intuition:** The first `n` coordinates of an i.i.d. sequence form a finite i.i.d.
sample of size `n`.

**Proof strategy:** Show that both measures agree on all measurable rectangles
(sets of the form `∏ᵢ Sᵢ`). This uses `Measure.pi_eq` and the characterization
of `iidProduct` via `infinitePi_pi`.
-/
lemma cylinder_fintype {n : ℕ} :
    (iidProduct ν).map (fun f : ℕ → α => fun i : Fin n => f i) =
      Measure.pi fun _ : Fin n => ν := by
  -- Show both measures agree on all measurable rectangles
  symm
  apply Measure.pi_eq
  intro s hs

  -- Compute the LHS: (iidProduct ν).map (...) applied to rectangle Set.univ.pi s
  have h_meas : Measurable (fun f : ℕ → α => fun i : Fin n => f i) := by
    measurability

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
  · measurability

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
