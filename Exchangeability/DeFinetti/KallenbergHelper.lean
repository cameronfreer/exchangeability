/-
Helper lemmas for Kallenberg 1.3 proof - testing kernel-based approach
-/

import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Condexp
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

open MeasureTheory ProbabilityTheory

variable {Ω α β : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
variable [MeasurableSpace α] [StandardBorelSpace α]
variable [MeasurableSpace β] [StandardBorelSpace β] [Nonempty β]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Pull `f =ᵐ[map ζ μ] g` back along `ζ`. -/
lemma ae_comp_of_ae_eq_map
    {δ} [MeasurableSpace δ]
    {ζ : Ω → β} (hζ : Measurable ζ)
    {f g : β → δ} (h : f =ᵐ[Measure.map ζ μ] g) :
    (fun ω => f (ζ ω)) =ᵐ[μ] (fun ω => g (ζ ω)) := by
  sorry -- Will fill in after checking structure
