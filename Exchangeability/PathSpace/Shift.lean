/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Shift Operator on Path Space

This file defines the **left shift operator** on infinite sequences `ℕ → α` and
establishes its basic properties.

## Main definitions

* `shift`: The left shift operator that maps `ξ : ℕ → α` to `fun n => ξ (n + 1)`.
* `IsShiftInvariant`: Predicate for sets that are invariant under the shift map.

## Main results

* `shift_measurable`: The shift operator is measurable.
* `shift_comp_shift`: Composing shift with itself gives `fun ξ n => ξ (n + 2)`.
* `isShiftInvariant_iff`: Characterization of shift-invariant sets.

## Implementation notes

The shift operator is fundamental in ergodic theory and the study of stationary
processes. It appears in:
- Ergodic theory (Koopman operator, measure-preserving transformations)
- de Finetti's theorem (tail σ-algebras, shift-invariant σ-algebras)
- Martingale theory (reverse martingales, backward filtrations)

This file provides a single canonical definition to avoid duplication across the codebase.

## References

- Kallenberg (2005), *Probabilistic Symmetries and Invariance Principles*
- Fristedt-Gray (1997), *A Modern Approach to Probability Theory*
-/

open MeasureTheory

/-- Path space: sequences indexed by ℕ taking values in α. -/
abbrev PathSpace (α : Type*) := ℕ → α

/-- Notation `Ω[α]` for path space `ℕ → α`. -/
notation3 "Ω[" α "]" => PathSpace α

namespace Exchangeability.PathSpace

variable {α : Type*}

/-- The **left shift operator** on path space: `(shift ξ) n = ξ (n + 1)`.

This is the fundamental shift operation that "drops the first element" of a sequence.
-/
def shift : (ℕ → α) → (ℕ → α) := fun ξ n => ξ (n + 1)

@[simp]
lemma shift_apply (ξ : ℕ → α) (n : ℕ) : shift ξ n = ξ (n + 1) := rfl

/-- Composing shift with itself is shift by 2. More generally, shift^n shifts by n. -/
lemma shift_comp_shift : @shift α ∘ shift = fun ξ n => ξ (n + 2) := by
  ext ξ n
  simp only [Function.comp_apply, shift_apply]

/-- The shift operator is measurable.

**Proof:** shift is measurable iff for all i, the composition `(shift ξ) i` is measurable.
Since `(shift ξ) i = ξ (i + 1)`, this is the projection onto coordinate `(i + 1)`,
which is measurable by definition of the product σ-algebra.
-/
@[measurability]
lemma shift_measurable [MeasurableSpace α] : Measurable (@shift α) := by
  -- A function to a pi type is measurable iff each component is measurable
  rw [measurable_pi_iff]
  intro i
  -- The i-th component of shift ξ is ξ (i + 1)
  -- This is just the projection onto coordinate (i + 1)
  exact measurable_pi_apply (i + 1)

/-- Alternative name for `shift_measurable` (used in ergodic theory contexts). -/
@[measurability]
lemma measurable_shift [MeasurableSpace α] : Measurable (@shift α) := shift_measurable

/-- A set in the path space is **shift-invariant** if it equals its preimage under the shift.

This is the analogue of `T⁻¹(S) = S` from classical ergodic theory.
-/
def IsShiftInvariant (S : Set (ℕ → α)) : Prop :=
  shift ⁻¹' S = S

lemma isShiftInvariant_iff (S : Set (ℕ → α)) :
    IsShiftInvariant S ↔ ∀ ξ, ξ ∈ S ↔ shift ξ ∈ S := by
  unfold IsShiftInvariant
  constructor
  · intro h ξ
    -- turn set equality into pointwise membership equivalence
    have := congrArg (fun T : Set (ℕ → α) => ξ ∈ T) h
    -- note: ξ ∈ shift ⁻¹' S ↔ shift ξ ∈ S is definitionally true
    simpa using this.symm
  · intro h
    -- turn pointwise equivalence into set equality
    ext ξ
    simpa using (h ξ).symm

end Exchangeability.PathSpace
