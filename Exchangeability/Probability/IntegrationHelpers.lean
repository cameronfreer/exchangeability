/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Integration Helper Lemmas

Convenience wrappers around mathlib's integration theory, providing specialized
lemmas for common patterns in the de Finetti proofs.

## Main Results

* `abs_integral_mul_le_L2`: Cauchy-Schwarz inequality for L² functions
* `integral_pushforward_id`: Integral of identity under pushforward measure
* `integral_pushforward_sq_diff`: Integral of squared difference under pushforward

These lemmas eliminate boilerplate by wrapping mathlib's general theorems.

## Implementation Notes

The file has no project dependencies - imports only mathlib.
-/

noncomputable section

namespace Exchangeability.Probability.IntegrationHelpers

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Cauchy-Schwarz Inequality -/

/-- **Cauchy-Schwarz inequality for L² real-valued functions.**

For integrable functions f, g in L²(μ):
  |∫ f·g dμ| ≤ (∫ f² dμ)^(1/2) · (∫ g² dμ)^(1/2)

This is Hölder's inequality specialized to p = q = 2.

We use the fact that `MemLp f 2 μ` means f is in L²(μ), and apply the
L² inner product Cauchy-Schwarz inequality. -/
lemma abs_integral_mul_le_L2
    [IsFiniteMeasure μ] {f g : Ω → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |∫ ω, f ω * g ω ∂μ|
      ≤ (∫ ω, (f ω) ^ 2 ∂μ) ^ (1/2 : ℝ) * (∫ ω, (g ω) ^ 2 ∂μ) ^ (1/2 : ℝ) := by
  -- TODO: Apply Hölder's inequality for p = q = 2
  -- See CAUCHY_SCHWARZ_RESEARCH_NOTES.md for mathlib API details
  sorry

/-! ### Pushforward Measure Integrals -/

/-- **Integral of identity function under pushforward measure.**

For measurable f:  ∫ x, x d(f₊μ) = ∫ ω, f ω dμ

Eliminates boilerplate of proving `AEStronglyMeasurable id`. -/
lemma integral_pushforward_id
    {μ : Measure Ω} {f : Ω → ℝ} (hf : Measurable f) :
    ∫ x, x ∂(Measure.map f μ) = ∫ ω, f ω ∂μ :=
  integral_map hf.aemeasurable aestronglyMeasurable_id

/-- **Integral of squared difference under pushforward measure.**

For measurable f and constant c:
  ∫ x, (x - c)² d(f₊μ) = ∫ ω, (f ω - c)² dμ -/
lemma integral_pushforward_sq_diff
    {μ : Measure Ω} {f : Ω → ℝ} (hf : Measurable f) (c : ℝ) :
    ∫ x, (x - c) ^ 2 ∂(Measure.map f μ) = ∫ ω, (f ω - c) ^ 2 ∂μ := by
  rw [integral_map hf.aemeasurable]
  exact (continuous_id.sub continuous_const).pow 2 |>.aestronglyMeasurable

/-- **Integral of continuous function under pushforward.**

For measurable f and continuous g:
  ∫ x, g x d(f₊μ) = ∫ ω, g (f ω) dμ -/
lemma integral_pushforward_continuous
    {μ : Measure Ω} {f : Ω → ℝ} {g : ℝ → ℝ}
    (hf : Measurable f) (hg : Continuous g) :
    ∫ x, g x ∂(Measure.map f μ) = ∫ ω, g (f ω) ∂μ := by
  rw [integral_map hf.aemeasurable]
  exact hg.aestronglyMeasurable

end Exchangeability.Probability.IntegrationHelpers
