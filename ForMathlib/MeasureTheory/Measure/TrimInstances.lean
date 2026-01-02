/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.MeasureTheory.Measure.Trim

/-!
# Instance Lemmas for Trimmed Measures

This file provides instance lemmas showing that `μ.trim hm` inherits finiteness
properties from the original measure `μ`.

## Main Results

* `isFiniteMeasure_trim`: If `μ` is a finite measure, then `μ.trim hm` is finite.
* `sigmaFinite_trim`: If `μ` is a finite measure, then `μ.trim hm` is sigma-finite.

## Implementation Notes

These lemmas are useful when working with conditional expectations on sub-σ-algebras,
where mathlib's `condExp` requires `SigmaFinite (μ.trim hm)`.

The proofs are straightforward: trimming preserves measure on measurable sets
(including `univ`), so finiteness transfers directly.

## References

* Kallenberg (2005), *Probabilistic Symmetries and Invariance Principles*
-/

open MeasureTheory

namespace MeasureTheory.Measure

variable {Ω : Type*} {m₀ : MeasurableSpace Ω}

/-- Trimmed measure is finite when the original measure is finite.

This is essential for conditional expectation on sub-σ-algebras: `condExp` requires
`SigmaFinite (μ.trim hm)`, which follows from this finiteness result. -/
lemma isFiniteMeasure_trim (μ : Measure Ω) [IsFiniteMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ m₀) :
    IsFiniteMeasure (μ.trim hm) := by
  classical
  -- univ is m-measurable, so trim agrees with μ on univ
  have hU : (μ.trim hm) Set.univ = μ Set.univ := by
    rw [trim_measurableSet_eq hm MeasurableSet.univ]
  -- Now measure_univ_lt_top comes from [IsFiniteMeasure μ]
  refine ⟨?_⟩
  simp [hU, measure_lt_top]

/-- Trimmed measure is sigma-finite when the original measure is finite.

This is the instance typically needed for `condExp` on sub-σ-algebras. -/
lemma sigmaFinite_trim (μ : Measure Ω) [IsFiniteMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ m₀) :
    SigmaFinite (μ.trim hm) := by
  haveI := isFiniteMeasure_trim μ hm
  infer_instance

end MeasureTheory.Measure
