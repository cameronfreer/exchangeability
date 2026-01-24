/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import ForMathlib.MeasureTheory.Measure.TrimInstances

/-!
# Lipschitz Properties of Conditional Expectation

This file provides operator-theoretic properties of conditional expectation,
particularly its L¹ nonexpansivity.

## Main Results

* `condExp_L1_lipschitz`: Conditional expectation is L¹-nonexpansive:
  `‖E[f|m] - E[g|m]‖₁ ≤ ‖f - g‖₁`

* `condExp_abs_le_of_abs_le`: Conditional expectation preserves monotonicity
  in absolute value

* `integrable_of_bounded`: Bounded measurable functions are integrable on
  finite measures (utility lemma)

## Mathematical Context

These operator-theoretic properties are fundamental in:
1. Proving convergence of martingale sequences
2. Showing conditional expectation defines a projection operator on L¹
3. Applying fixed-point arguments in probability theory

The L¹ nonexpansivity follows from the key inequality `∫|E[f|m]| ≤ ∫|f|`
(mathlib's `integral_abs_condExp_le`), combined with linearity.

## Suggested Mathlib Location

`Mathlib.MeasureTheory.Function.ConditionalExpectation.Lipschitz`

## References

* Kallenberg (2005), *Probabilistic Symmetries and Invariance Principles*
* Williams (1991), *Probability with Martingales*, Chapter 9
-/

open MeasureTheory Filter Set Function

namespace CondExp

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Bounded measurable functions are integrable on finite measures. -/
lemma integrable_of_bounded [IsFiniteMeasure μ]
    {f : Ω → ℝ} (hf : Measurable f) (hbd : ∃ C, ∀ ω, |f ω| ≤ C) :
    Integrable f μ :=
  hbd.elim fun C hC => Integrable.of_bound hf.aestronglyMeasurable C (ae_of_all μ hC)

/-- Product of integrable and bounded measurable functions is integrable. -/
lemma integrable_of_bounded_mul [IsFiniteMeasure μ]
    {f g : Ω → ℝ} (hf : Integrable f μ) (hg : Measurable g)
    (hbd : ∃ C, ∀ ω, |g ω| ≤ C) :
    Integrable (f * g) μ := by
  have : f * g = fun ω => g ω * f ω := funext fun _ => mul_comm _ _
  rw [this]
  obtain ⟨C, hC⟩ := hbd
  have hbd_ae : ∀ᵐ ω ∂μ, ‖g ω‖ ≤ C := by
    filter_upwards with ω
    exact (Real.norm_eq_abs _).symm ▸ hC ω
  exact Integrable.bdd_mul hf hg.aestronglyMeasurable hbd_ae

/-- Conditional expectation preserves monotonicity in absolute value.

If |f| ≤ |g| everywhere, then |E[f|m]| ≤ E[|g||m]. -/
lemma condExp_abs_le_of_abs_le [IsFiniteMeasure μ]
    {m : MeasurableSpace Ω} (_hm : m ≤ ‹_›)
    {f g : Ω → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (h : ∀ ω, |f ω| ≤ |g ω|) :
    ∀ᵐ ω ∂μ, |μ[f|m] ω| ≤ μ[(fun ω' => |g ω'|)|m] ω := by
  have h_lower : ∀ ω, -(|g ω|) ≤ f ω := fun ω =>
    (neg_le_neg (h ω)).trans (neg_abs_le (f ω))
  have h_upper : ∀ ω, f ω ≤ |g ω| := fun ω => (le_abs_self (f ω)).trans (h ω)
  have hg_abs : Integrable (fun ω => |g ω|) μ := hg.abs
  have lower_bd := condExp_mono (m := m) hg_abs.neg hf (ae_of_all μ h_lower)
  have upper_bd := condExp_mono (m := m) hf hg_abs (ae_of_all μ h_upper)
  have hneg_eq : μ[(fun ω => -(|g ω|))|m] =ᵐ[μ] fun ω => -(μ[(fun ω' => |g ω'|)|m] ω) :=
    condExp_neg (fun ω => |g ω|) m
  filter_upwards [lower_bd, upper_bd, hneg_eq] with ω hlower hupper hneg
  have hlower' : -(μ[(fun ω' => |g ω'|)|m] ω) ≤ μ[f|m] ω := hneg ▸ hlower
  exact abs_le.mpr ⟨hlower', hupper⟩

/-- **Conditional expectation is L¹-nonexpansive.**

For integrable functions f, g, the conditional expectation is contractive in L¹:
```
‖E[f|m] - E[g|m]‖₁ ≤ ‖f - g‖₁
```

This follows from `integral_abs_condExp_le` applied to `f - g`. -/
theorem condExp_L1_lipschitz [IsFiniteMeasure μ]
    {m : MeasurableSpace Ω} (_hm : m ≤ ‹_›)
    {f g : Ω → ℝ} (hf : Integrable f μ) (hg : Integrable g μ) :
    ∫ ω, |μ[f|m] ω - μ[g|m] ω| ∂μ ≤ ∫ ω, |f ω - g ω| ∂μ := by
  have h_linear : ∀ᵐ ω ∂μ, μ[f|m] ω - μ[g|m] ω = μ[(f - g)|m] ω :=
    EventuallyEq.symm (condExp_sub hf hg m)
  calc ∫ ω, |μ[f|m] ω - μ[g|m] ω| ∂μ
      = ∫ ω, |μ[(f - g)|m] ω| ∂μ := integral_congr_ae (h_linear.mono fun _ h => congrArg _ h)
    _ ≤ ∫ ω, |(f - g) ω| ∂μ := integral_abs_condExp_le (f - g)
    _ = ∫ ω, |f ω - g ω| ∂μ := rfl

/-- Conditional expectation pull-out property for bounded measurable functions.

If g is m-measurable and bounded, then E[f·g|m] = E[f|m]·g a.e. -/
theorem condExp_mul_pullout {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ m₀)
    {f g : Ω → ℝ} (hf : Integrable f μ)
    (hg_meas : @Measurable Ω ℝ m _ g)
    (hg_bd : ∃ C, ∀ ω, |g ω| ≤ C) :
    μ[f * g|m] =ᵐ[μ] fun ω => μ[f|m] ω * g ω := by
  have hg_strong : StronglyMeasurable[m] g := hg_meas.stronglyMeasurable
  obtain ⟨C, hC⟩ := hg_bd
  have hg_bound : ∀ᵐ ω ∂μ, ‖g ω‖ ≤ C := ae_of_all μ fun ω => (Real.norm_eq_abs _).le.trans (hC ω)
  haveI : SigmaFinite (μ.trim hm) := MeasureTheory.Measure.sigmaFinite_trim μ hm
  have h := condExp_stronglyMeasurable_mul_of_bound hm hg_strong hf C hg_bound
  -- f * g = g * f pointwise, so μ[f * g|m] =ᵃᵉ μ[g * f|m] = g · μ[f|m]
  have hcomm : f * g =ᵐ[μ] g * f := by filter_upwards with ω; simp only [Pi.mul_apply]; ring
  have step1 : μ[f * g|m] =ᵐ[μ] μ[g * f|m] := condExp_congr_ae hcomm
  have step2 : (fun ω => g ω * μ[f|m] ω) =ᵐ[μ] (fun ω => μ[f|m] ω * g ω) := by
    filter_upwards with ω; ring
  exact step1.trans (h.trans step2)

end CondExp
