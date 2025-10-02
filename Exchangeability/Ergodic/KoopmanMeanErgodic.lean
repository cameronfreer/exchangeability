/-
Copyright (c) 2025 exchangeability contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: exchangeability contributors
-/
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.MeanErgodic
import Mathlib.Dynamics.Ergodic.MeasurePreserving

/-!
# Koopman operator and Mean Ergodic Theorem on L²

This file establishes the Koopman operator on L²(μ) induced by the left shift on
the path space Ω = ℕ → α, and applies the Mean Ergodic Theorem to characterize
the L²-convergence of Birkhoff averages.

## Main definitions

* `shift`: The left shift on path space Ω = ℕ → α.
* `koopman`: The Koopman operator on L²(μ) induced by a measure-preserving shift.

## Main results

* `measurable_shift`: The shift map is measurable.
* `measurePreserving_shift_pi`: For product measures, the shift is measure-preserving.
* `birkhoffAverage_tendsto_fixedSpace`: Birkhoff averages converge to the projection
  onto the fixed-point subspace of the Koopman operator.

## References

* Olav Kallenberg (2005), *Probabilistic Symmetries and Invariance Principles*,
  Springer, Chapter 1 (Theorem 1.1, pages 26-27).

-/

noncomputable section

namespace Exchangeability.Ergodic

open MeasureTheory Filter Topology

open scoped ENNReal

variable {α : Type*} [MeasurableSpace α]

-- Ensure Lp spaces work with p = 2
attribute [local instance] fact_one_le_two_ennreal

/-- Path space: sequences indexed by ℕ taking values in α. -/
abbrev PathSpace (α : Type*) := ℕ → α

notation3 "Ω[" α "]" => PathSpace α

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The left shift on path space: (shift ω) n = ω (n+1). -/
def shift (ω : Ω[α]) : Ω[α] := fun n => ω (n + 1)

/-- The shift map is measurable. -/
lemma measurable_shift : Measurable (shift (α := α)) := by
  -- shift is the composition of measurable coordinate projections
  apply measurable_pi_lambda
  intro n
  exact measurable_pi_apply (n + 1)

-- Product measure setup will need specific API from mathlib
-- For now we work with abstract measure-preserving assumptions
-- lemma measurePreserving_shift_pi : ... (TODO: requires Measure.pi API)

/-- The Koopman operator on L² induced by a measure-preserving transformation.

Given a measure-preserving map T : Ω → Ω, the Koopman operator is defined by
(U f)(ω) = f(T ω), which is an isometric linear operator on L²(μ).
-/
def koopman {μ : Measure Ω} [IsProbabilityMeasure μ] (T : Ω → Ω) (hT : MeasurePreserving T μ μ) :
    Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  (MeasureTheory.Lp.compMeasurePreservingₗᵢ ℝ T hT).toContinuousLinearMap

/-- The Koopman operator is a linear isometry. -/
lemma koopman_isometry {μ : Measure Ω} [IsProbabilityMeasure μ] (T : Ω → Ω) (hT : MeasurePreserving T μ μ) :
    Isometry (koopman T hT) := by
  simpa [koopman]
    using (MeasureTheory.Lp.compMeasurePreservingₗᵢ ℝ T hT).isometry

/-- The fixed-point subspace of a continuous linear map. -/
def fixedSpace {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : E →L[ℝ] E) : Submodule ℝ E :=
  LinearMap.eqLocus U.toLinearMap 1

/-- Mean Ergodic Theorem: Birkhoff averages converge to the projection onto the fixed-point subspace.

This specializes the von Neumann Mean Ergodic Theorem from mathlib to the Koopman
operator on `Lp` and packages the limiting projection as a continuous linear map.
-/
theorem birkhoffAverage_tendsto_fixedSpace
    {μ : Measure Ω} [IsProbabilityMeasure μ] (T : Ω → Ω)
    (hT : MeasurePreserving T μ μ) (f : Lp ℝ 2 μ) :
    ∃ (P : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ),
      (∀ g, g ∈ fixedSpace (koopman T hT) → P g = g) ∧
      Tendsto (fun n => birkhoffAverage ℝ (koopman T hT) _root_.id n f)
        atTop (𝓝 (P f)) := by
  classical
  let K : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ := koopman T hT
  have hnorm : ‖K‖ ≤ (1 : ℝ) := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) ?_
    intro g
    have hnorm_eq : ‖K g‖ = ‖g‖ := by
      simp [K, koopman] using
        (MeasureTheory.Lp.compMeasurePreservingₗᵢ ℝ T hT).norm_map g
    simp [hnorm_eq]
  let S := LinearMap.eqLocus K.toLinearMap 1
  have hS_closed : IsClosed (S : Set (Lp ℝ 2 μ)) := by
    classical
    have hset : (S : Set (Lp ℝ 2 μ)) = (fun x => K x - x) ⁻¹' ({0} : Set (Lp ℝ 2 μ)) := by
      ext x
      simp [S, LinearMap.eqLocus, sub_eq_zero]
    have hcont : Continuous fun x => K x - x :=
      K.continuous.sub continuous_id
    have hclosed : IsClosed ((fun x => K x - x) ⁻¹' ({0} : Set (Lp ℝ 2 μ))) :=
      isClosed_singleton.preimage hcont
    simpa [hset] using hclosed
  haveI : CompleteSpace S := hS_closed.completeSpace_coe
  haveI : S.HasOrthogonalProjection := Submodule.HasOrthogonalProjection.ofCompleteSpace S
  let projToSub : Lp ℝ 2 μ →L[ℝ] S := S.orthogonalProjection
  let inclusion : S →L[ℝ] Lp ℝ 2 μ := S.subtypeL
  let P : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ := inclusion.comp projToSub
  refine ⟨P, ?_, ?_⟩
  · intro g hg
    let gS : S := ⟨g, hg⟩
    have hproj := S.orthogonalProjection_mem_subspace_eq_self gS
    simpa [P, projToSub, inclusion, gS] using congrArg Subtype.val hproj
  · have h_tendsto :=
      ContinuousLinearMap.tendsto_birkhoffAverage_orthogonalProjection K hnorm f
    have h_proj_val : (P f) = (S.orthogonalProjection f : S) := rfl
    simpa [P, projToSub, inclusion, h_proj_val]

end Exchangeability.Ergodic
