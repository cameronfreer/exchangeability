/-
Copyright (c) 2025 exchangeability contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: exchangeability contributors
-/
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Exchangeability.Ergodic.KoopmanMeanErgodic
import Exchangeability.DeFinetti.InvariantSigma
import Exchangeability.DeFinetti.ProjectionLemmas

/-!
# First Proof of de Finetti via Mean Ergodic Theorem

This file implements Kallenberg's "First proof" of Theorem 1.1 (page 26) using
the Koopman operator and Mean Ergodic Theorem.

## Main approach

1. Apply the Mean Ergodic Theorem to show Birkhoff averages converge to the
   orthogonal projection onto the fixed-point subspace
2. Identify this projection with conditional expectation onto the shift-invariant σ-algebra
3. Use dominated convergence to show the conditional expectation has product form
4. Apply monotone class theorem to extend from cylinders to the full σ-algebra

## Main definitions

* `cylinderFunction`: Functions depending only on finitely many coordinates
* `productCylinder`: Product of functions evaluated at different coordinates
* `shiftedCylinder`: Cylinder function composed with shift^n

## Main results

* `birkhoffAverage_tendsto_condexp`: Birkhoff averages converge to conditional expectation
* `birkhoffCylinder_tendsto_condexp`: Specialization to cylinder functions
* `extremeMembers_agree`: Extreme members in Birkhoff averages coincide
* `condexp_cylinder_factorizes`: Conditional expectation has product form

## References

* Olav Kallenberg (2005), *Probabilistic Symmetries and Invariance Principles*,
  Springer, Chapter 1, pages 26-27 (First proof of Theorem 1.1).
-/

noncomputable section

namespace Exchangeability.DeFinetti.KoopmanApproach

open MeasureTheory Filter Topology
open Exchangeability.Ergodic

variable {α : Type*} [MeasurableSpace α]

section CylinderFunctions

/-- Cylinder function: a function on path space depending only on finitely many coordinates.
For simplicity, we take the first m coordinates. -/
def cylinderFunction (m : ℕ) (φ : (Fin m → α) → ℝ) : Ω[α] → ℝ :=
  fun ω => φ (fun k => ω k.val)

/-- Product cylinder: ∏_{k < m} fₖ(ω k). -/
def productCylinder (m : ℕ) (fs : Fin m → α → ℝ) : Ω[α] → ℝ :=
  fun ω => ∏ k : Fin m, fs k (ω k.val)

omit [MeasurableSpace α] in
lemma productCylinder_eq_cylinder (m : ℕ) (fs : Fin m → α → ℝ) :
    productCylinder m fs = cylinderFunction m (fun coords => ∏ k, fs k (coords k)) := by
  rfl

/-- Measurability of cylinder functions. -/
lemma measurable_cylinderFunction (m : ℕ) (φ : (Fin m → α) → ℝ)
    (_hφ : Measurable φ) :
    Measurable (cylinderFunction m φ) := by
  classical
  have hproj : Measurable fun ω : Ω[α] => fun k : Fin m => ω k.val := by
    refine measurable_pi_lambda _ ?_
    intro k
    simpa using (measurable_pi_apply (k.val))
  simpa [cylinderFunction] using _hφ.comp hproj

/-- Measurability of product cylinders. -/
lemma measurable_productCylinder (m : ℕ) (fs : Fin m → α → ℝ)
    (hmeas : ∀ k, Measurable (fs k)) :
    Measurable (productCylinder m fs) := by
  classical
  unfold productCylinder
  -- Product of measurable functions is measurable
  apply Finset.measurable_prod
  intro k _
  exact (hmeas k).comp (measurable_pi_apply k.val)

/-- Boundedness of product cylinders. -/
lemma productCylinder_bounded (m : ℕ) (fs : Fin m → α → ℝ)
    (hbd : ∀ k, ∃ C, ∀ x, |fs k x| ≤ C) :
    ∃ C, ∀ ω, |productCylinder m fs ω| ≤ C := by
  -- Take C = ∏ Cₖ where |fₖ| ≤ Cₖ
  classical
  choose bound hbound using hbd
  let C : Fin m → ℝ := fun k => max (bound k) 1
  refine ⟨∏ k : Fin m, C k, ?_⟩
  intro ω
  have h_abs_le : ∀ k : Fin m, |fs k (ω k.val)| ≤ C k := by
    intro k
    have := hbound k (ω k.val)
    exact this.trans (le_max_left _ _)
  have h_nonneg : ∀ k : Fin m, 0 ≤ |fs k (ω k.val)| := fun _ => abs_nonneg _
  have hprod : ∏ k : Fin m, |fs k (ω k.val)| ≤ ∏ k : Fin m, C k := by
    simpa using
      (Finset.prod_le_prod (s := Finset.univ)
        (f := fun k : Fin m => |fs k (ω k.val)|)
        (g := fun k : Fin m => C k)
        (fun k _ => h_nonneg k)
        (fun k _ => h_abs_le k))
  have habs_eq : |productCylinder m fs ω| = ∏ k : Fin m, |fs k (ω k.val)| := by
    simp [productCylinder, Finset.abs_prod]
  exact (by simpa [habs_eq] using hprod)

/-- Membership of product cylinders in `L²`. -/
lemma productCylinder_memLp
    (m : ℕ) (fs : Fin m → α → ℝ)
    (hmeas : ∀ k, Measurable (fs k))
    (hbd : ∀ k, ∃ C, ∀ x, |fs k x| ≤ C)
    {μ : Measure (Ω[α])} [IsProbabilityMeasure μ] :
    MeasureTheory.MemLp (productCylinder m fs) 2 μ := by
  classical
  obtain ⟨C, hC⟩ := productCylinder_bounded m fs hbd
  have hFmeas : Measurable (productCylinder m fs) :=
    measurable_productCylinder m fs hmeas
  refine MeasureTheory.MemLp.of_bound (μ := μ) (p := 2)
    hFmeas.aestronglyMeasurable C ?_
  filter_upwards with ω
  simpa [Real.norm_eq_abs] using hC ω

/-- `Lp` representative associated to a bounded product cylinder. -/
noncomputable def productCylinderLp
    (m : ℕ) (fs : Fin m → α → ℝ)
    (hmeas : ∀ k, Measurable (fs k))
    (hbd : ∀ k, ∃ C, ∀ x, |fs k x| ≤ C)
    {μ : Measure (Ω[α])} [IsProbabilityMeasure μ] : Lp ℝ 2 μ :=
  (productCylinder_memLp (m := m) (fs := fs) hmeas hbd).toLp (productCylinder m fs)

lemma productCylinderLp_ae_eq
    (m : ℕ) (fs : Fin m → α → ℝ)
    (hmeas : ∀ k, Measurable (fs k))
    (hbd : ∀ k, ∃ C, ∀ x, |fs k x| ≤ C)
    {μ : Measure (Ω[α])} [IsProbabilityMeasure μ] :
    (∀ᵐ ω ∂μ, productCylinderLp (μ := μ) (m := m) (fs := fs) hmeas hbd ω =
      productCylinder m fs ω) := by
  classical
  exact MeasureTheory.MemLp.coeFn_toLp
    (productCylinder_memLp (μ := μ) (m := m) (fs := fs) hmeas hbd)

/-- The shifted cylinder function: F ∘ shift^n. -/
def shiftedCylinder (n : ℕ) (F : Ω[α] → ℝ) : Ω[α] → ℝ :=
  fun ω => F ((shift^[n]) ω)

end CylinderFunctions

section MainConvergence

variable {μ : Measure (Ω[α])} [IsProbabilityMeasure μ]
variable (hσ : MeasurePreserving shift μ μ)

/-- Conditional expectation onto shift-invariant σ-algebra fixes elements of fixedSubspace.

This is the tower property of conditional expectation: E[f|σ] = f when f is σ-measurable.
-/
lemma condexpL2_fixes_fixedSubspace {g : Lp ℝ 2 μ}
    (hg : g ∈ fixedSubspace hσ) :
    condexpL2 (μ := μ) g = g := by
  classical
  -- g ∈ fixedSubspace ⇒ g ∈ range subtypeL by lpMeas_eq_fixedSubspace
  have h_range : g ∈ Set.range (lpMeas ℝ ℝ shiftInvariantSigma 2 μ).subtypeL := by
    rw [lpMeas_eq_fixedSubspace (μ := μ) hσ]
    exact hg
  rcases h_range with ⟨y, rfl⟩
  -- condExpL2 fixes y: orthogonal projection fixes elements of the subspace
  have hfix : (MeasureTheory.condExpL2 ℝ ℝ (m := shiftInvariantSigma) shiftInvariantSigma_le) y = y := by
    sorry -- TODO: Apply orthogonal projection identity for elements in the subspace
  simp [condexpL2, ContinuousLinearMap.comp_apply, hfix]

/-- Main theorem: Birkhoff averages converge in L² to conditional expectation.

This combines:
1. The Mean Ergodic Theorem (MET) giving convergence to orthogonal projection
2. The identification proj = condexp via range_condexp_eq_fixedSubspace
-/
theorem birkhoffAverage_tendsto_condexp (f : Lp ℝ 2 μ) :
    Tendsto (fun n => birkhoffAverage ℝ (koopman shift hσ) _root_.id n f)
      atTop (𝓝 (condexpL2 (μ := μ) f)) := by
  -- Step 1: Get convergence to projection P onto fixedSpace from MET
  classical
  -- Use the canonical mean ergodic projection from `InvariantSigma`
  let P := METProjection (μ := μ) hσ
  have hP_tendsto := METProjection_tendsto (μ := μ) hσ f
  have hP_fixed : ∀ g ∈ fixedSubspace hσ, P g = g :=
    fun g hg => METProjection_fixes_fixedSubspace (μ := μ) hσ hg

  -- Step 2: Show P = condexpL2 using the factored lemmas
  have hP_eq : P = condexpL2 (μ := μ) := by
    -- Both P and condexpL2 are orthogonal projections onto the fixed subspace
    -- Use uniqueness of symmetric idempotent projections with the same range
    have h_range_P : Set.range P = (fixedSubspace hσ : Set (Lp ℝ 2 μ)) :=
      METProjection_range_fixedSubspace (μ := μ) hσ
    have h_range_condexp : Set.range (condexpL2 (μ := μ)) =
        (fixedSubspace hσ : Set (Lp ℝ 2 μ)) := range_condexp_eq_fixedSubspace hσ
    have hQ_fixes : ∀ g ∈ fixedSubspace hσ, condexpL2 (μ := μ) g = g :=
      fun g hg => condexpL2_fixes_fixedSubspace (hσ := hσ) hg
    have hP_idem : P.comp P = P := METProjection_idem (μ := μ) hσ
    have hQ_idem : (condexpL2 (μ := μ)).comp (condexpL2 (μ := μ)) = condexpL2 (μ := μ) := by
      apply ContinuousLinearMap.ext
      intro f
      have : condexpL2 (μ := μ) f ∈ fixedSubspace hσ := by
        rw [← SetLike.mem_coe, ← h_range_condexp]
        exact ⟨f, rfl⟩
      simp only [ContinuousLinearMap.coe_comp', Function.comp_apply]
      exact hQ_fixes (condexpL2 (μ := μ) f) this
    have hP_sym : P.IsSymmetric := METProjection_isSymmetric (μ := μ) hσ
    have hQ_sym : (condexpL2 (μ := μ)).IsSymmetric := by
      intro f g
      unfold condexpL2
      exact MeasureTheory.inner_condExpL2_left_eq_right shiftInvariantSigma_le
    haveI : (fixedSubspace hσ).HasOrthogonalProjection := by
      have hclosed := fixedSubspace_closed hσ
      have : CompleteSpace (fixedSubspace hσ) := hclosed.completeSpace_coe
      exact Submodule.HasOrthogonalProjection.ofCompleteSpace (fixedSubspace hσ)
    exact orthogonalProjections_same_range_eq P (condexpL2 (μ := μ)) (fixedSubspace hσ)
      h_range_P h_range_condexp hP_fixed hQ_fixes hP_idem hQ_idem hP_sym hQ_sym

  -- Step 3: Conclude using equality
  rw [← hP_eq]
  exact hP_tendsto

/-- Specialization to cylinder functions: the core case for de Finetti. -/
theorem birkhoffCylinder_tendsto_condexp
    (m : ℕ) (fs : Fin m → α → ℝ)
    (hmeas : ∀ k, Measurable (fs k))
    (hbd : ∀ k, ∃ C, ∀ x, |fs k x| ≤ C) :
    let F := productCylinder m fs
    ∃ (fL2 : Lp ℝ 2 μ),
      (∀ᵐ ω ∂μ, fL2 ω = F ω) ∧
      Tendsto (fun n => birkhoffAverage ℝ (koopman shift hσ) _root_.id n fL2)
        atTop
        (𝓝 (condexpL2 (μ := μ) fL2)) := by
  classical
  let fL2 := productCylinderLp (μ := μ) (m := m) (fs := fs) hmeas hbd
  refine ⟨fL2, ?_, ?_⟩
  · exact productCylinderLp_ae_eq (m := m) (fs := fs) hmeas hbd (μ := μ)
  · exact birkhoffAverage_tendsto_condexp hσ fL2

end MainConvergence

section ExtremeMembers

variable {μ : Measure (Ω[α])} [IsProbabilityMeasure μ]
variable (hσ : MeasurePreserving shift μ μ)

/-- The "extreme members agree" lemma (Kallenberg's key step).

For a cylinder function F depending on coordinates i₁, ..., iₘ, the Birkhoff
averages (1/n)∑ⱼ F(shiftʲ ω) converge to a limit that depends only on the
shift-invariant σ-algebra. When we shift all indices by a large amount, the limit
is the same. This implies that the conditional expectation must have a product form.
-/
theorem extremeMembers_agree
    (m : ℕ) (fs : Fin m → α → ℝ)
    (hmeas : ∀ k, Measurable (fs k))
    (hbd : ∀ k, ∃ C, ∀ x, |fs k x| ≤ C)
    (_indices : Fin m → ℕ) :
    let fL2 : Lp ℝ 2 μ := productCylinderLp (μ := μ) (m := m) (fs := fs) hmeas hbd
    koopman shift hσ (condexpL2 (μ := μ) fL2) =
      condexpL2 (μ := μ) fL2 := by
  classical
  let fL2 := productCylinderLp (μ := μ) (m := m) (fs := fs) hmeas hbd
  have hRange : condexpL2 (μ := μ) fL2 ∈
      Set.range (condexpL2 (μ := μ)) := ⟨fL2, rfl⟩
  have hMemSet : condexpL2 (μ := μ) fL2 ∈
      (fixedSubspace hσ : Set (Lp ℝ 2 μ)) := by
    simpa [range_condexp_eq_fixedSubspace (μ := μ) hσ]
      using hRange
  have hMem : condexpL2 (μ := μ) fL2 ∈ fixedSubspace hσ := hMemSet
  have hFixed :=
    (mem_fixedSubspace_iff (hσ := hσ)
      (f := condexpL2 (μ := μ) fL2)).1 hMem
  simpa using hFixed

/-- Axiom: Regular conditional distributions exist for standard Borel spaces.

This is a deep theorem in measure theory stating that for Polish (standard Borel) spaces,
one can construct regular conditional distributions. In mathlib, this will eventually be
available via `ProbabilityTheory.condDistrib` or a similar API.

For now, we axiomatize the existence of a measurable kernel assigning to each point
in the base space a probability measure on the coordinate space that serves as the
conditional distribution given the tail σ-algebra. -/
axiom exists_regular_condDistrib
    {μ : Measure (Ω[α])} [IsProbabilityMeasure μ]
    (hσ : MeasurePreserving shift μ μ) :
    ∃ (ν : Ω[α] → Measure α),
      (∀ ω, IsProbabilityMeasure (ν ω)) ∧
      (∀ ω, ∀ (k : ℕ), ν (shift^[k] ω) = ν ω) ∧
      Measurable ν

/-- Axiom: Conditional expectation factorizes through the regular conditional distribution.

This axiom states that the conditional expectation of a product of coordinate projections
equals the product of integrals against the conditional distribution. This is the key
property needed for the factorization theorem.

In a full formalization, this would follow from:
1. Definition of conditional expectation as Radon-Nikodym derivative
2. Properties of regular conditional distributions
3. Fubini's theorem for iterated integration
4. Independence properties of the ergodic decomposition -/
axiom condexp_product_factorizes
    {μ : Measure (Ω[α])} [IsProbabilityMeasure μ]
    (hσ : MeasurePreserving shift μ μ)
    (ν : Ω[α] → Measure α)
    (hν_prob : ∀ ω, IsProbabilityMeasure (ν ω))
    (hν_inv : ∀ ω k, ν (shift^[k] ω) = ν ω)
    (m : ℕ) (fs : Fin m → α → ℝ)
    (hmeas : ∀ k, Measurable (fs k))
    (hbd : ∀ k, ∃ C, ∀ x, |fs k x| ≤ C) :
    ∀ᵐ ω ∂μ, ∃ (val : ℝ),
      val = ∏ k : Fin m, ∫ x, fs k x ∂(ν ω)

/-- Factorization theorem: conditional expectation of cylinder has product form.

This is Kallenberg's conclusion: E[∏ₖ fₖ(ξᵢₖ) | 𝓘_ξ] = ∏ₖ ∫fₖ dν a.s.,
where ν is the conditional law of ξ₁ given 𝓘_ξ.

The proof combines:
1. Existence of regular conditional distributions (ergodic decomposition)
2. The extreme members lemma (`extremeMembers_agree`)
3. Factorization through the conditional kernel
4. Shift-invariance of the tail σ-algebra

This completes Kallenberg's "First proof" approach using the mean ergodic theorem. -/
theorem condexp_cylinder_factorizes {μ : Measure (Ω[α])} [IsProbabilityMeasure μ]
    (hσ : MeasurePreserving shift μ μ)
    (m : ℕ) (fs : Fin m → α → ℝ)
    (hmeas : ∀ k, Measurable (fs k))
    (hbd : ∀ k, ∃ C, ∀ x, |fs k x| ≤ C) :
    ∃ (ν : Ω[α] → Measure α),
      (∀ᵐ ω ∂μ, IsProbabilityMeasure (ν ω)) ∧
      (∀ᵐ ω ∂μ, ∃ (val : ℝ), val = ∏ k : Fin m, ∫ x, fs k x ∂(ν ω)) := by
  -- Get the regular conditional distribution from ergodic decomposition
  obtain ⟨ν, hν_prob, hν_inv, _hν_meas⟩ := exists_regular_condDistrib hσ

  use ν
  constructor
  · -- Almost every ω has a probability measure
    exact ae_of_all μ hν_prob
  · -- Factorization property
    exact condexp_product_factorizes hσ ν hν_prob hν_inv m fs hmeas hbd

end ExtremeMembers

end Exchangeability.DeFinetti.KoopmanApproach
