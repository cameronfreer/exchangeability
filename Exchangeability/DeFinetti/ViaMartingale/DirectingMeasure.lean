/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Kernel.Condexp
import Exchangeability.DeFinetti.ViaMartingale.FutureFiltration
import Exchangeability.DeFinetti.ViaMartingale.CondExpConvergence

/-!
# Directing Measure Construction

From conditional expectations on indicators, we build a measurable family
of probability measures `ν : Ω → Measure α`.

The construction uses the standard Borel machinery: for each `ω`, define
`ν ω` to be the unique probability measure satisfying
`ν ω B = E[1_{X₀∈B} | 𝒯_X](ω)` for all measurable `B`.

This requires StandardBorelSpace assumption on α to ensure existence.

## Main definitions

* `directingMeasure X hX ω` - The directing measure at ω

## Main results

* `directingMeasure_isProb` - Each directing measure is a probability measure
* `directingMeasure_measurable_eval` - Directing measure is measurable in ω
* `directingMeasure_X0_marginal` - ν ω B = E[1_{X₀∈B} | tail](ω) a.e.
* `conditional_law_eq_directingMeasure` - All X_n have directing measure as conditional law
-/

noncomputable section
open scoped MeasureTheory
open MeasureTheory ProbabilityTheory

namespace Exchangeability.DeFinetti.ViaMartingale

/-! ### Directing measure construction -/

section Directing

/-- **Directing measure**: conditional distribution of `X₀` given the tail σ-algebra.

Constructed using `condExpKernel` API: for each ω, evaluate the conditional expectation kernel
at ω to get a measure on Ω, then push forward along X₀.

Concretely: `directingMeasure ω = (condExpKernel μ (tailSigma X) ω).map (X 0)`
-/
@[nolint unusedArguments]
noncomputable def directingMeasure
    {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
    (X : ℕ → Ω → α) (_hX : ∀ n, Measurable (X n)) (ω : Ω) : Measure α :=
  (ProbabilityTheory.condExpKernel μ (tailSigma X) ω).map (X 0)

/-- `directingMeasure` evaluates measurably on measurable sets.

Uses: `Kernel.measurable_coe` and `Measure.map_apply`. -/
@[measurability, fun_prop]
lemma directingMeasure_measurable_eval
    {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
    (X : ℕ → Ω → α) (hX : ∀ n, Measurable (X n)) :
    ∀ (B : Set α), MeasurableSet B →
      Measurable (fun ω => directingMeasure (μ := μ) X hX ω B) := by
  intro B hB
  classical
  have hS : MeasurableSet ((X 0) ⁻¹' B) := (hX 0) hB
  let κ := ProbabilityTheory.condExpKernel μ (tailSigma X)
  simp only [directingMeasure, Measure.map_apply (hX 0) hB]
  exact (ProbabilityTheory.Kernel.measurable_coe κ hS).mono (tailSigma_le X hX) le_rfl

/-- The directing measure is (pointwise) a probability measure.

Uses: `isProbability_condExpKernel` and map preserves probability. -/
lemma directingMeasure_isProb
    {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
    (X : ℕ → Ω → α) (hX : ∀ n, Measurable (X n)) :
    ∀ ω, IsProbabilityMeasure (directingMeasure (μ := μ) X hX ω) :=
  fun _ => Measure.isProbabilityMeasure_map (hX 0).aemeasurable

/-- **X₀-marginal identity**: the conditional expectation of the indicator
of `X 0 ∈ B` given the tail equals the directing measure of `B` (toReal).

Uses: `condExp_ae_eq_integral_condExpKernel` and `integral_indicator_one`. -/
lemma directingMeasure_X0_marginal
    {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
    (X : ℕ → Ω → α) (hX : ∀ n, Measurable (X n))
    (B : Set α) (hB : MeasurableSet B) :
  (fun ω => (directingMeasure (μ := μ) X hX ω B).toReal)
    =ᵐ[μ]
  μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ (X 0) | tailSigma X] := by
  classical
  let κ := ProbabilityTheory.condExpKernel μ (tailSigma X)
  have hInt : Integrable (fun ω => (Set.indicator B (fun _ => (1 : ℝ)) (X 0 ω))) μ :=
    (integrable_const 1).indicator ((hX 0) hB)
  -- Identify the kernel integral with evaluation of `directingMeasure` on `B`
  have hId : (fun ω => ∫ x, (Set.indicator B (fun _ => (1 : ℝ)) (X 0 x)) ∂κ ω) =
             (fun ω => (directingMeasure (μ := μ) X hX ω B).toReal) := by
    funext ω
    simp only [show (fun x => Set.indicator B (fun _ => (1 : ℝ)) (X 0 x)) =
                    Set.indicator ((X 0) ⁻¹' B) (fun _ => (1 : ℝ)) by ext x; simp [Set.indicator],
               directingMeasure, Measure.map_apply (hX 0) hB]
    exact MeasureTheory.integral_indicator_one ((hX 0) hB)
  -- Combine: rewrite with hId then apply condExp kernel equality
  calc (fun ω => (directingMeasure (μ := μ) X hX ω B).toReal)
      = (fun ω => ∫ x, (Set.indicator B (fun _ => (1 : ℝ)) (X 0 x)) ∂κ ω) := hId.symm
    _ =ᵐ[μ] μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ (X 0) | tailSigma X] :=
        (condExp_ae_eq_integral_condExpKernel (tailSigma_le X hX) hInt).symm

end Directing

/-! ### Conditional law equality -/

/-- General form: All `X_n` have the same conditional law `ν`.
This follows from `extreme_members_equal_on_tail`. -/
@[nolint unusedArguments]
lemma conditional_law_eq_of_X0_marginal
    {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
    (X : ℕ → Ω → α)
    (hX : Contractable μ X)
    (hX_meas : ∀ n, Measurable (X n))
    (ν : Ω → Measure α)
    (hν : ∀ B : Set α, MeasurableSet B →
        (fun ω => (ν ω B).toReal) =ᵐ[μ] μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ (X 0) | tailSigma X])
    (n : ℕ) (B : Set α) (hB : MeasurableSet B) :
    (fun ω => (ν ω B).toReal) =ᵐ[μ] μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ (X n) | tailSigma X] :=
  (hν B hB).trans (extreme_members_equal_on_tail hX hX_meas n B hB).symm

/-- **All coordinates share the directing measure as their conditional law.**

This is the key "common ending" result: the directing measure `ν` constructed from
the tail σ-algebra satisfies the marginal identity for all coordinates, not just X₀. -/
lemma conditional_law_eq_directingMeasure
    {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
    (X : ℕ → Ω → α)
    (hX : Contractable μ X)
    (hX_meas : ∀ n, Measurable (X n))
    (n : ℕ) (B : Set α) (hB : MeasurableSet B) :
    (fun ω => (directingMeasure (μ := μ) X hX_meas ω B).toReal)
      =ᵐ[μ]
    μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ (X n) | tailSigma X] := by
  -- Apply the general lemma with ν := directingMeasure X hX_meas
  exact conditional_law_eq_of_X0_marginal X hX hX_meas (directingMeasure X hX_meas)
    (fun B hB => directingMeasure_X0_marginal X hX_meas B hB) n B hB

end Exchangeability.DeFinetti.ViaMartingale
