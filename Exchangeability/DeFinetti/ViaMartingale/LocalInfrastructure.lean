/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Constructions.Cylinders
import Exchangeability.DeFinetti.MartingaleHelpers
import Exchangeability.Probability.CondExp
import Exchangeability.Probability.CondIndep

/-!
# Local Infrastructure Lemmas for ViaMartingale

This file contains helper lemmas that unblock the martingale approach proof by providing
targeted results that should eventually be contributed to mathlib. Each is marked with
its intended mathlib home.

## Main sections

* `PiFiniteProjections` - σ-algebra structure of infinite product spaces
* `ProbabilityMeasureHelpers` - Integrability and bounds on probability spaces
* `CondDistribUniqueness` - Conditional distribution uniqueness under factorization
* `ConditionalIndependence` - Conditional independence projection lemmas

These lemmas are extracted from ViaMartingale.lean to enable modular imports.
-/

noncomputable section
open scoped MeasureTheory
open MeasureTheory Filter

namespace Exchangeability.DeFinetti.ViaMartingale

/-! ### Probability Measure Helpers -/

section ProbabilityMeasureHelpers

/-- **[Mathlib candidate:MeasureTheory.Integral.Bochner]**

On a probability space, a bounded measurable function is integrable.

This is a standard fact: if `‖f‖ ≤ C` a.e. on a probability measure, then
`∫ ‖f‖ ≤ C·μ(univ) = C < ∞`, so `f` is integrable.

**Proof strategy:**
Use mathlib's `Integrable.of_mem_Icc` for functions bounded in an interval.
-/
lemma integrable_of_bounded_on_prob
    {α : Type*} [MeasurableSpace α] {ν : Measure α} [IsProbabilityMeasure ν]
    {h : α → ℝ} (hmeas : Measurable h) {C : ℝ}
    (hB : ∀ᵐ x ∂ν, ‖h x‖ ≤ C) : Integrable h ν := by
  by_cases hC : 0 ≤ C
  · -- If C ≥ 0, use that h is bounded in [-C, C]
    apply MeasureTheory.Integrable.of_mem_Icc (-C) C hmeas.aemeasurable
    filter_upwards [hB] with x hx
    rw [Set.mem_Icc]
    rw [Real.norm_eq_abs] at hx
    rwa [abs_le] at hx
  · -- If C < 0, then ‖h‖ ≤ C < 0 a.e. contradicts ‖h‖ ≥ 0
    push Not at hC
    apply MeasureTheory.Integrable.of_mem_Icc 0 0 hmeas.aemeasurable
    filter_upwards [hB] with x hx
    rw [Set.mem_Icc]
    have : ‖h x‖ = 0 := by linarith [norm_nonneg (h x)]
    rw [Real.norm_eq_abs] at this
    simp [abs_eq_zero] at this
    simp [this]

lemma norm_indicator_one_le {α : Type*} (S : Set α) (x : α) :
    ‖Set.indicator S (fun _ : α => (1 : ℝ)) x‖ ≤ 1 := by
  simp only [Real.norm_eq_abs]
  by_cases h : x ∈ S
  · simp [Set.indicator_of_mem h]
  · simp [Set.indicator_of_notMem h]

end ProbabilityMeasureHelpers

/-! ### Conditional Distribution Uniqueness -/

section CondDistribUniqueness

end CondDistribUniqueness

/-! ### Conditional Independence from Distributional Equality -/

section ConditionalIndependence

/-- **Helper lemma:** Marginal distribution projection from triple.
If two triple distributions are equal, then projecting to a pair by dropping one coordinate
preserves the equality. -/
private lemma map_pair_of_map_triple_eq
  {Ω α β γ δ : Type*}
  [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]
  {μ : Measure Ω}
  {f₁ f₂ : Ω → α × β × γ} {proj : α × β × γ → δ}
  (hf₁ : Measurable f₁) (hf₂ : Measurable f₂) (hproj : Measurable proj)
  (h_eq : Measure.map f₁ μ = Measure.map f₂ μ) :
  Measure.map (proj ∘ f₁) μ = Measure.map (proj ∘ f₂) μ := by
  rw [← Measure.map_map hproj hf₁, ← Measure.map_map hproj hf₂, h_eq]

end ConditionalIndependence

end Exchangeability.DeFinetti.ViaMartingale
