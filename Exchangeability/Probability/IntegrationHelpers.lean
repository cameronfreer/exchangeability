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

This is Hölder's inequality specialized to p = q = 2. -/
lemma abs_integral_mul_le_L2
    {μ : Measure Ω} {f g : Ω → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |∫ ω, f ω * g ω ∂μ|
      ≤ (∫ ω, (f ω) ^ 2 ∂μ) ^ (1/2 : ℝ) * (∫ ω, (g ω) ^ 2 ∂μ) ^ (1/2 : ℝ) := by
  sorry

/-! ### Pushforward Measure Integrals -/

/-- **Integral of identity function under pushforward measure.**

For measurable f:  ∫ x, x d(f₊μ) = ∫ ω, f ω dμ

Eliminates boilerplate of proving `AEStronglyMeasurable id`. -/
lemma integral_pushforward_id
    {μ : Measure Ω} {f : Ω → ℝ} (hf : Measurable f) :
    ∫ x, x ∂(Measure.map f μ) = ∫ ω, f ω ∂μ := by
  have h_ae : AEStronglyMeasurable (id : ℝ → ℝ) (Measure.map f μ) :=
    aestronglyMeasurable_id
  rw [← integral_map hf.aemeasurable h_ae]
  rfl

/-- **Integral of squared difference under pushforward measure.**

For measurable f and constant c:
  ∫ x, (x - c)² d(f₊μ) = ∫ ω, (f ω - c)² dμ -/
lemma integral_pushforward_sq_diff
    {μ : Measure Ω} {f : Ω → ℝ} (hf : Measurable f) (c : ℝ) :
    ∫ x, (x - c) ^ 2 ∂(Measure.map f μ) = ∫ ω, (f ω - c) ^ 2 ∂μ := by
  have h_ae : AEStronglyMeasurable (fun x : ℝ => (x - c) ^ 2) (Measure.map f μ) := by
    exact (continuous_id.sub continuous_const).pow 2 |>.aestronglyMeasurable
  rw [← integral_map hf.aemeasurable h_ae]
  rfl

/-- **Integral of continuous function under pushforward.**

For measurable f and continuous g:
  ∫ x, g x d(f₊μ) = ∫ ω, g (f ω) dμ -/
lemma integral_pushforward_continuous
    {μ : Measure Ω} {f : Ω → ℝ} {g : ℝ → ℝ}
    (hf : Measurable f) (hg : Continuous g) :
    ∫ x, g x ∂(Measure.map f μ) = ∫ ω, g (f ω) ∂μ := by
  have h_ae : AEStronglyMeasurable g (Measure.map f μ) := hg.aestronglyMeasurable
  rw [← integral_map hf.aemeasurable h_ae]
  rfl

end Exchangeability.Probability.IntegrationHelpers
