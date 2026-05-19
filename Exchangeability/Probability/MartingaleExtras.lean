/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.MeasureTheory.MeasurableSpace.Prod
import Mathlib.MeasureTheory.Function.FactorsThrough

/-!
# Martingale Helper Lemmas (Fully Proved)

This file contains **fully-proved** helper lemmas related to martingales and conditional expectations.
These are extracted from exploratory work and may be useful for future developments.

**All lemmas here are complete** - no axioms, no sorries.

## Contents

1. **Reverse conditional expectation helpers**:
   - `revCE`: Definition of reverse martingale along decreasing filtration

2. **Fatou-type lemmas**:
   - `lintegral_fatou_ofReal_norm`: Fatou's lemma for `ENNReal.ofReal ∘ ‖·‖`

## References

* Durrett, *Probability: Theory and Examples* (2019), Section 5.5
* Williams, *Probability with Martingales* (1991)
-/

noncomputable section
open scoped MeasureTheory ProbabilityTheory Topology
open MeasureTheory Filter Set Function

namespace Exchangeability.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## Reverse Conditional Expectation Helpers -/

/-- Reverse martingale along a decreasing chain: `X n := condExp μ (F n) f`. -/
def revCE (μ : Measure Ω) (F : ℕ → MeasurableSpace Ω) (f : Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  μ[f | F n]

/-! ## Fatou-Type Lemmas -/

/-- Fatou's lemma on `ENNReal.ofReal ∘ ‖·‖` along an a.e. pointwise limit.

If `u n x → g x` a.e., then `∫⁻ ‖g‖ ≤ liminf (∫⁻ ‖u n‖)`. -/
@[nolint unusedArguments]
lemma lintegral_fatou_ofReal_norm
  {α β : Type*} [MeasurableSpace α] {μ : Measure α}
  [MeasurableSpace β] [NormedAddCommGroup β] [BorelSpace β]
  {u : ℕ → α → β} {g : α → β}
  (hae : ∀ᵐ x ∂μ, Tendsto (fun n => u n x) atTop (nhds (g x)))
  (hu_meas : ∀ n, AEMeasurable (fun x => ENNReal.ofReal ‖u n x‖) μ)
  (_hg_meas : AEMeasurable (fun x => ENNReal.ofReal ‖g x‖) μ) :
  ∫⁻ x, ENNReal.ofReal ‖g x‖ ∂μ
    ≤ liminf (fun n => ∫⁻ x, ENNReal.ofReal ‖u n x‖ ∂μ) atTop := by
  have hae_ofReal :
      ∀ᵐ x ∂μ,
        Tendsto (fun n => ENNReal.ofReal ‖u n x‖) atTop
                (nhds (ENNReal.ofReal ‖g x‖)) :=
    hae.mono (fun x hx =>
      ((ENNReal.continuous_ofReal.comp continuous_norm).tendsto _).comp hx)
  calc ∫⁻ x, ENNReal.ofReal ‖g x‖ ∂μ
      = ∫⁻ x, liminf (fun n => ENNReal.ofReal ‖u n x‖) atTop ∂μ :=
          lintegral_congr_ae (hae_ofReal.mono fun x hx => hx.liminf_eq.symm)
    _ ≤ liminf (fun n => ∫⁻ x, ENNReal.ofReal ‖u n x‖ ∂μ) atTop :=
          lintegral_liminf_le' hu_meas

end Exchangeability.Probability
