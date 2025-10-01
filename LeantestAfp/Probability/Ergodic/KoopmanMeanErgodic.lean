/-
Copyright (c) 2025 leantest-afp contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: leantest-afp contributors
-/
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
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

namespace LeantestAfp.Probability.Ergodic

open MeasureTheory Filter Topology

open scoped ENNReal

variable {α : Type*} [MeasurableSpace α]

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
  haveI : Fact (1 ≤ (2 : ℝ≥0∞)) := fact_one_le_two_ennreal
  (MeasureTheory.Lp.compMeasurePreservingₗᵢ ℝ T hT).toContinuousLinearMap

/-- The Koopman operator is a linear isometry. -/
lemma koopman_isometry {μ : Measure Ω} [IsProbabilityMeasure μ] (T : Ω → Ω) (hT : MeasurePreserving T μ μ) :
    Isometry (koopman T hT) := by
  classical
  haveI : Fact (1 ≤ (2 : ℝ≥0∞)) := fact_one_le_two_ennreal
  let L := MeasureTheory.Lp.compMeasurePreservingₗᵢ ℝ T hT
  have hL : Isometry fun f : Lp ℝ 2 μ => L f := L.isometry
  simpa [koopman, L] using hL

/-- The Birkhoff average of a continuous linear operator.

For a continuous linear map U : E → E, the n-th Birkhoff average is
(1/n) * ∑_{k=0}^{n-1} Uᵏ f.
-/
def birkhoffAverage {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : E →L[ℝ] E) (n : ℕ) (f : E) : E :=
  match n with
  | 0 => 0
  | n + 1 => (1 / ((n + 1) : ℝ)) • (∑ k ∈ Finset.range (n + 1), (U ^ k) f)

/-- The fixed-point subspace of a continuous linear map. -/
def fixedSpace {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : E →L[ℝ] E) : Submodule ℝ E :=
  { carrier := {f | U f = f}
    add_mem' := by
      intro f g hf hg
      simp only [Set.mem_setOf_eq] at hf hg ⊢
      simp [hf, hg]
    zero_mem' := by simp
    smul_mem' := by
      intro c f hf
      simp only [Set.mem_setOf_eq] at hf ⊢
      simp [hf] }

/-- Mean Ergodic Theorem: Birkhoff averages converge to the projection onto the fixed-point subspace.

This is the key theorem connecting dynamics to functional analysis. For a contraction
(or isometry) U on a Hilbert space, the Birkhoff averages converge strongly to the
orthogonal projection onto the fixed-point subspace.

TODO: This requires the von Neumann Mean Ergodic Theorem from mathlib.
For now we state it as a sorry to establish the API.
-/
theorem birkhoffAverage_tendsto_fixedSpace
    {μ : Measure Ω} [IsProbabilityMeasure μ] (T : Ω → Ω) (hT : MeasurePreserving T μ μ) (f : Lp ℝ 2 μ) :
    ∃ (P : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ),
      (∀ g, (koopman T hT) (P g) = P g) ∧
      Tendsto (fun n => birkhoffAverage (koopman T hT) n f) atTop (𝓝 (P f)) := by
  sorry
  -- The proof would invoke the Mean Ergodic Theorem from mathlib:
  -- 1. Show koopman T hT is a contraction (actually an isometry)
  -- 2. Apply MET to get convergence to orthogonal projection onto fixed space
  -- 3. The limit P is characterized as the unique fixed point of a certain averaging process

end LeantestAfp.Probability.Ergodic
