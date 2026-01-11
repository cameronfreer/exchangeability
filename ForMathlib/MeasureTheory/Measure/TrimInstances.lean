/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.MeasureTheory.Measure.Trim

/-!
# Sigma-Finiteness for Trimmed Measures

This file provides a lemma showing that `μ.trim hm` is sigma-finite when `μ` is finite.

## Main Results

* `sigmaFinite_trim`: If `μ` is a finite measure, then `μ.trim hm` is sigma-finite.

## Implementation Notes

This lemma is useful when working with conditional expectations on sub-σ-algebras,
where mathlib's `condExp` requires `SigmaFinite (μ.trim hm)`.

Note: `IsFiniteMeasure (μ.trim hm)` is now provided by mathlib as an instance
(`MeasureTheory.Measure.isFiniteMeasure_trim`), so we only need the sigma-finite corollary.

## References

* Kallenberg (2005), *Probabilistic Symmetries and Invariance Principles*
-/

open MeasureTheory

namespace MeasureTheory.Measure

variable {Ω : Type*} {m₀ : MeasurableSpace Ω}

/-- Trimmed measure is sigma-finite when the original measure is finite.

This is the instance typically needed for `condExp` on sub-σ-algebras.
The finiteness of `μ.trim hm` is automatic via mathlib's `isFiniteMeasure_trim` instance. -/
lemma sigmaFinite_trim (μ : Measure Ω) [IsFiniteMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ m₀) :
    SigmaFinite (μ.trim hm) :=
  inferInstance

end MeasureTheory.Measure
