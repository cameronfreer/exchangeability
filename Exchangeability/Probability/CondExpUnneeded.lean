/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Probability.ConditionalExpectation

/-!
# Unneeded Conditional Expectation Lemmas

This file contains conditional expectation lemmas that were drafted but are not
currently used in the main development. They have compilation errors that need
to be fixed if they are ever needed.

These lemmas were originally in CondExpHelpers.lean but were moved here to
unblock the build of ViaMartingale.lean.

## Contents

* `tendsto_set_integral_mul_of_L1`: DCT for set integrals with bounded factor
* `tendsto_condexp_L1`: Wrapper for conditional expectation L¹ continuity

Both lemmas have sorry placeholders and syntax errors in the Filter.Tendsto notation.
-/

noncomputable section
open scoped MeasureTheory ENNReal
open MeasureTheory ProbabilityTheory Set Filter

namespace MeasureTheory

/-!
## Convergence lemmas for bounded measurable extension
-/

/-- **DCT for set integrals of products with a fixed bounded factor.**

When `hn → h` in L¹ and `g` is bounded, then `hn * g → h * g` in set integrals.
This is used in the approximation argument for extending conditional independence. -/
lemma tendsto_set_integral_mul_of_L1 {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {h : Ω → ℝ} {hn : ℕ → Ω → ℝ} {g : Ω → ℝ}
    {s : Set Ω} (Cg : ℝ)
    (hg_bound : ∀ᵐ ω ∂μ, ‖g ω‖ ≤ Cg)
    (hs : MeasurableSet s)
    (h_int : Integrable h μ)
    (hn_int : ∀ n, Integrable (hn n) μ)
    (hg_int : Integrable g μ)
    (hL1 : Tendsto (fun n => ∫⁻ ω, ‖hn n ω - h ω‖₊ ∂μ) atTop (nhds 0)) :
    Tendsto (fun n => ∫ ω in s, (hn n ω * g ω) ∂μ) atTop (nhds (∫ ω in s, (h ω * g ω) ∂μ)) := by
  -- Strategy: ‖(hn - h) * g‖ ≤ Cg * ‖hn - h‖
  -- So if ‖hn - h‖ → 0 in L¹, then ‖(hn * g) - (h * g)‖ → 0 in L¹
  -- Then set integrals converge by continuity of integration
  sorry

/-- **Wrapper for conditional expectation L¹ continuity.**

This wraps mathlib's lemma for L¹ continuity of conditional expectation,
protecting against lemma name changes across mathlib versions. -/
lemma tendsto_condexp_L1 {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (m : MeasurableSpace Ω) (hm : m ≤ inferInstance)
    {fn : ℕ → Ω → ℝ} {f : Ω → ℝ}
    (h_int : ∀ n, Integrable (fn n) μ) (hf : Integrable f μ)
    (hL1 : Tendsto (fun n => ∫⁻ ω, ‖fn n ω - f ω‖₊ ∂μ) atTop (nhds 0)) :
    Tendsto (fun n => μ[fn n | m]) atTop (nhds (μ[f | m])) := by
  -- Replace with the proper mathlib lemma:
  -- Option 1: Use condexpL1 as a continuous linear map
  -- Option 2: Use direct L¹ convergence + tower property
  -- For now, we admit this as a wrapper
  sorry

end MeasureTheory
