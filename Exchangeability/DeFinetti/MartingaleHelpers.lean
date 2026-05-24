/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Basic
import Mathlib.Data.Real.Basic
import Exchangeability.PathSpace.CylinderHelpers

/-!
# Helper Lemmas for Martingale-based de Finetti Proof

This file contains technical helper lemmas extracted from `ViaMartingale.lean`.
These are general-purpose utilities for:
- Comap (pullback σ-algebra) operations
- Sequence shifting and manipulation
- Finset ordering and monotonicity
- Indicator algebra

## Main sections

* `ComapTools`: Comap σ-algebra utilities
* `SequenceShift`: Sequence shifting operations
* `FinsetOrder`: Finset ordering and strict monotonicity lemmas
* `IndicatorAlgebra`: Helper lemmas for indicator functions
-/

noncomputable section
open scoped MeasureTheory

namespace Exchangeability
namespace DeFinetti
namespace MartingaleHelpers

open MeasureTheory

section SequenceShift

variable {β : Type*} [MeasurableSpace β]

/-- Shift a sequence by dropping the first `d` entries. -/
def shiftSeq (d : ℕ) (f : ℕ → β) : ℕ → β := fun n => f (n + d)

@[measurability, fun_prop]
lemma measurable_shiftSeq {d : ℕ} :
    Measurable (shiftSeq (β:=β) d) := by
  unfold shiftSeq; fun_prop

end SequenceShift

section FinsetOrder

open Finset

lemma orderEmbOfFin_mem {s : Finset ℕ} {i : Fin s.card} :
    s.orderEmbOfFin rfl i ∈ s := by
  classical
  simp [Finset.orderEmbOfFin_mem (s:=s) (h:=rfl) i]

/-- If `f : Fin n → ℕ` is strictly monotone and `a < f i` for all `i`,
then `Fin.cases a f : Fin (n+1) → ℕ` is strictly monotone. -/
lemma strictMono_fin_cases
    {n : ℕ} {f : Fin n → ℕ} (hf : StrictMono f) {a : ℕ}
    (ha : ∀ i, a < f i) :
    StrictMono (Fin.cases a (fun i => f i)) := by
  intro i j hij
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases with
    | zero => exact absurd hij (lt_irrefl _)
    | succ j => simpa using ha j
  | succ i =>
    cases j using Fin.cases with
    | zero =>
      have : (Fin.succ i : Fin (n + 1)).1 < 0 := by
        set_option linter.unnecessarySimpa false in
        simpa [Fin.lt_def] using hij
      exact absurd this (Nat.not_lt.mpr (Nat.zero_le _))
    | succ j =>
      have hij' : i < j := (Fin.succ_lt_succ_iff).1 hij
      simpa using hf hij'

end FinsetOrder

section IndicatorAlgebra

/-- The product of two indicator functions equals the indicator of their intersection. -/
@[nolint unusedArguments]
lemma indicator_mul_indicator_eq_indicator_inter
    {Ω : Type*} [MeasurableSpace Ω]
    (A B : Set Ω) (c d : ℝ) :
    (A.indicator (fun _ => c)) * (B.indicator (fun _ => d))
      = (A ∩ B).indicator (fun _ => c * d) := by
  ext ω
  by_cases hA : ω ∈ A <;> by_cases hB : ω ∈ B <;>
    simp [Set.indicator, hA, hB, Set.mem_inter_iff]

/-- Indicator function composed with preimage. -/
@[nolint unusedArguments]
lemma indicator_comp_preimage
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (f : Ω → α) (B : Set α) (c : ℝ) :
    (B.indicator (fun _ => c)) ∘ f = (f ⁻¹' B).indicator (fun _ => c) := by
  ext ω
  simp only [Function.comp_apply, Set.indicator, Set.mem_preimage]
  rfl

/-- Indicator is nonnegative when constant is nonnegative. -/
@[nolint unusedArguments]
lemma indicator_nonneg
    {Ω : Type*} [MeasurableSpace Ω]
    (A : Set Ω) (c : ℝ) (hc : 0 ≤ c) (ω : Ω) :
    0 ≤ A.indicator (fun _ => c) ω := by
  by_cases h : ω ∈ A
  · simp [Set.indicator, h, hc]
  · simp [Set.indicator, h]

end IndicatorAlgebra

end MartingaleHelpers
end DeFinetti
end Exchangeability
