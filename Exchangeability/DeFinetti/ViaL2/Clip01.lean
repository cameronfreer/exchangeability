/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# Clip01: Clamping to [0,1]

This file defines `clip01`, which clamps real values to the interval [0,1],
and proves basic properties used in L¹ convergence arguments.

## Main definitions

* `clip01 x`: Clamps `x` to the interval `[0,1]` via `max 0 (min 1 x)`

## Main results

* `clip01_range`: `0 ≤ clip01 x ≤ 1`
* `clip01_1Lipschitz`: `clip01` is 1-Lipschitz
* `abs_clip01_sub_le`: `|clip01 x - clip01 y| ≤ |x - y|`
* `continuous_clip01`: `clip01` is continuous
* `l1_convergence_under_clip01`: L¹ convergence is preserved under `clip01`
-/

noncomputable section

namespace Exchangeability.DeFinetti.ViaL2.Helpers

open MeasureTheory Filter Topology

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Clip a real to the interval `[0,1]`. -/
@[simp] def clip01 (x : ℝ) : ℝ := max 0 (min 1 x)

lemma clip01_range (x : ℝ) : 0 ≤ clip01 x ∧ clip01 x ≤ 1 := by
  unfold clip01
  constructor
  · exact le_max_left _ _
  · apply max_le
    · linarith
    · exact min_le_left _ _

/-- `clip01` is 1-Lipschitz. -/
lemma clip01_1Lipschitz : LipschitzWith 1 clip01 := by
  exact (LipschitzWith.id.const_min 1).const_max 0

/-- Pointwise contraction from the 1-Lipschitzness. -/
lemma abs_clip01_sub_le (x y : ℝ) : |clip01 x - clip01 y| ≤ |x - y| := by
  simpa [Real.dist_eq] using (clip01_1Lipschitz.dist_le_mul x y)

/-- `clip01` is continuous. -/
lemma continuous_clip01 : Continuous clip01 :=
  clip01_1Lipschitz.continuous

/-- **L¹-stability under 1-Lipschitz post-composition.**
If `∫ |fₙ - f| → 0`, then `∫ |clip01 ∘ fₙ - clip01 ∘ f| → 0`.

This follows from mathlib's `LipschitzWith.norm_compLp_sub_le`: Since `clip01` is 1-Lipschitz
and maps 0 to 0, we have `‖clip01 ∘ f - clip01 ∘ g‖₁ ≤ 1 * ‖f - g‖₁`. -/
lemma l1_convergence_under_clip01
    {μ : Measure Ω} {fn : ℕ → Ω → ℝ} {f : Ω → ℝ}
    (h_meas : ∀ n, AEMeasurable (fn n) μ) (hf : AEMeasurable f μ)
    (h_integrable : ∀ n, Integrable (fun ω => fn n ω - f ω) μ)
    (h : Tendsto (fun n => ∫ ω, |fn n ω - f ω| ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, |clip01 (fn n ω) - clip01 (f ω)| ∂μ) atTop (𝓝 0) := by
  have hmono (n : ℕ) : ∫ ω, |clip01 (fn n ω) - clip01 (f ω)| ∂μ ≤ ∫ ω, |fn n ω - f ω| ∂μ := by
    apply integral_mono_ae
    · apply Integrable.mono (h_integrable n).abs
      · have h1 : AEStronglyMeasurable (fun ω => clip01 (fn n ω)) μ :=
          continuous_clip01.comp_aestronglyMeasurable (h_meas n).aestronglyMeasurable
        have h2 : AEStronglyMeasurable (fun ω => clip01 (f ω)) μ :=
          continuous_clip01.comp_aestronglyMeasurable hf.aestronglyMeasurable
        exact (h1.sub h2).norm
      · filter_upwards with ω
        simp [Real.norm_eq_abs]
        exact abs_clip01_sub_le (fn n ω) (f ω)
    · exact (h_integrable n).abs
    · filter_upwards with ω
      exact abs_clip01_sub_le (fn n ω) (f ω)
  refine squeeze_zero ?_ hmono h
  intro n
  apply integral_nonneg
  intro ω
  exact abs_nonneg _

end Exchangeability.DeFinetti.ViaL2.Helpers
