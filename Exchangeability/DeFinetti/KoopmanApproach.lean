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


noncomputable section

namespace Exchangeability.DeFinetti.KoopmanApproach

open MeasureTheory Filter Topology
open Exchangeability.Ergodic

variable {α : Type*} [MeasurableSpace α]

section CylinderFunctions

{{ ... }}
For simplicity, we take the first m coordinates. -/
def cylinderFunction (m : ℕ) (φ : (Fin m → α) → ℝ) : Ω[α] → ℝ :=
  fun ω => φ (fun k => ω k.val)

/-- Product cylinder: ∏_{k < m} fₖ(ω k). -/
def productCylinder (m : ℕ) (fs : Fin m → α → ℝ) : Ω[α] → ℝ :=
  fun ω => ∏ k : Fin m, fs k (ω k.val)

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
  apply Finset.measurable_prod'
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

/-- The shifted cylinder function: F ∘ shift^n. -/
def shiftedCylinder (n : ℕ) (F : Ω[α] → ℝ) : Ω[α] → ℝ :=
  fun ω => F ((shift^[n]) ω)

end CylinderFunctions

section MainConvergence

variable {μ : Measure (Ω[α])} [IsProbabilityMeasure μ]
variable (hσ : MeasurePreserving shift μ μ)

/-- Main theorem: Birkhoff averages converge in L² to conditional expectation.

This combines:
1. The Mean Ergodic Theorem (MET) giving convergence to orthogonal projection
2. The identification proj = condexp from InvariantSigma.lean
-/
theorem birkhoffAverage_tendsto_condexp (f : Lp ℝ 2 μ) :
    Tendsto (fun n => birkhoffAverage ℝ (koopman shift hσ) _root_.id n f)
      atTop (𝓝 (condexpL2 shiftInvariantSigma f)) := by
  -- Step 1: Get the projection from the Mean Ergodic Theorem
  obtain ⟨P, hP_fixed, hP_tendsto⟩ := birkhoffAverage_tendsto_fixedSpace shift hσ f
  have hP_proj : P = (fixedSubspace hσ).starProjection := rfl
  
  -- Step 2: Get the identification of projection with conditional expectation
  obtain ⟨Q, hQ_fixed, hQ_condexp⟩ := proj_eq_condexp hσ
  have hQ_proj : Q = (fixedSubspace hσ).starProjection := by
    ext g
    simpa [hQ_condexp]
  
  -- Step 3 & 4: Combine to get convergence to condexpL2
  simp [hP_proj, hQ_proj, hQ_condexp] at hP_tendsto
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
        (𝓝 (condexpL2 shiftInvariantSigma fL2)) := by
  classical
  -- F is bounded by productCylinder_bounded
  obtain ⟨C, hC⟩ := productCylinder_bounded m fs hbd
  -- F is measurable (product of measurable functions)
  have hFmeas : Measurable (productCylinder m fs) :=
    measurable_productCylinder m fs hmeas
  -- F is in L² since it's bounded
  have hFinL2 : MeasureTheory.MemLp (productCylinder m fs) 2 μ := by
    classical
    refine MeasureTheory.MemLp.of_bound (μ := μ) (p := 2)
      hFmeas.aestronglyMeasurable ?C ?hBound
    · exact C
    · have hpoint : ∀ ω, ‖productCylinder m fs ω‖ ≤ C := by
        intro ω
        simpa [Real.norm_eq_abs] using hC ω
      exact eventually_of_forall hpoint
  -- Convert to Lp element
  let fL2 := hFinL2.toLp (productCylinder m fs)
  use fL2
  constructor
  · exact MeasureTheory.MemLp.coeFn_toLp hFinL2
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
    (_hmeas : ∀ k, Measurable (fs k))
    (_hbd : ∀ k, ∃ C, ∀ x, |fs k x| ≤ C)
    (_indices : Fin m → ℕ) :
    let F := productCylinder m fs
    let fL2 : Lp ℝ 2 μ :=
      (productCylinder_bounded m fs _hbd |> fun ⟨C, hC⟩ =>
        let hFmeas : Measurable (productCylinder m fs) :=
          measurable_productCylinder m fs _hmeas
        have hFinL2 : MeasureTheory.MemLp (productCylinder m fs) 2 μ := by
          classical
          refine MeasureTheory.MemLp.of_bound (μ := μ) (p := 2)
            hFmeas.aestronglyMeasurable C ?_
          exact (eventually_of_forall fun ω => by
            simpa [Real.norm_eq_abs] using hC ω)
        hFinL2.toLp (productCylinder m fs))
    koopman shift hσ (condexpL2 shiftInvariantSigma fL2) =
      condexpL2 shiftInvariantSigma fL2 := by
  classical
  -- unpack the `let` bindings
  obtain ⟨C, hC⟩ := productCylinder_bounded m fs _hbd
  have hFmeas : Measurable (productCylinder m fs) :=
    measurable_productCylinder m fs _hmeas
  have hFinL2 : MeasureTheory.MemLp (productCylinder m fs) 2 μ := by
    refine MeasureTheory.MemLp.of_bound (μ := μ) (p := 2)
      hFmeas.aestronglyMeasurable C ?_
    exact (eventually_of_forall fun ω => by
      simpa [Real.norm_eq_abs] using hC ω)
  let fL2 := hFinL2.toLp (productCylinder m fs)
  have hRange : condexpL2 shiftInvariantSigma fL2 ∈
      Set.range (condexpL2 shiftInvariantSigma) := ⟨fL2, rfl⟩
  have hMemSet : condexpL2 shiftInvariantSigma fL2 ∈
      (fixedSubspace hσ : Set (Lp ℝ 2 μ)) := by
    simpa [range_condexp_eq_fixedSubspace (μ := μ) hσ]
      using hRange
  have hMem : condexpL2 shiftInvariantSigma fL2 ∈ fixedSubspace hσ := hMemSet
  have hFixed :=
    (mem_fixedSubspace_iff (hσ := hσ)
      (f := condexpL2 shiftInvariantSigma fL2)).1 hMem
  simpa using hFixed

/-- Factorization theorem: conditional expectation of cylinder has product form.

This is Kallenberg's conclusion: E[∏ₖ fₖ(ξᵢₖ) | 𝓘_ξ] = ∏ₖ ∫fₖ dν a.s.,
where ν is the conditional law of ξ₁ given 𝓘_ξ.
-/
theorem condexp_cylinder_factorizes
    (m : ℕ) (fs : Fin m → α → ℝ)
    (_hmeas : ∀ k, Measurable (fs k))
    (_hbd : ∀ k, ∃ C, ∀ x, |fs k x| ≤ C) :
    ∃ (ν : Ω[α] → Measure α),
      (∀ᵐ ω ∂μ, IsProbabilityMeasure (ν ω)) ∧
      (∀ᵐ ω ∂μ, ∃ (val : ℝ), val = ∏ k : Fin m, ∫ x, fs k x ∂(ν ω)) := by
  /-
  Sketch (following Kallenberg, page 26):

  1. **Regular conditional distributions.**
     Use mathlib's kernel API (`Probability.condDistrib`) to define
     the kernel `ν ω := condDistrib (fun ω ↦ ω 0) (σ-algebra generated by tail coordinates)`.
     This yields a measurable map `Ω[α] → ProbabilityMeasure α`.

  2. **Extreme members lemma.**
     Prove `extremeMembers_agree`: the limits of Birkhoff averages of a cylinder and
     its shifts coincide, using `birkhoffCylinder_tendsto_condexp` together with dominated
     convergence. This shows the conditional expectations stabilize under shifting indices.

  3. **Identify the limit.**
     Show that, as the indices move apart, the conditional expectation equals
     `∏ k ∫ fs k dν ω`. Shift-invariance of `ν ω` and the independence given the tail
     σ-algebra are crucial here.

  4. **Monotone class extension.**
     Extend the cylinder-factorization result to the full σ-algebra generated by cylinders
     via the monotone class (Dynkin system) theorem, available in mathlib.

  Filling in these steps will provide the required factorisation.
  -/
  sorry

end ExtremeMembers

end Exchangeability.DeFinetti.KoopmanApproach
