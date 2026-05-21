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

