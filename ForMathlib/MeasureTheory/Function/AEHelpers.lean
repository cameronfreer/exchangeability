/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-!
# Combining Finitely Many A.E. Equalities

This file provides a utility lemma for combining finitely many a.e.-equalities
into an a.e.-equality of the finite sum.

## Main Results

* `finset_sum_ae_eq`: If each `f i` is a.e.-equal to `g i` on a finite index
  set `s`, then the pointwise sums over `s` are a.e.-equal.

## Mathematical Context

This lemma is useful when combining conditional expectation equalities, as in
de Finetti-type theorems where we need to show that sums of conditional
expectations converge. The key technique is induction on the finite set,
using `EventuallyEq.fun_add` to combine equalities at each step.

## Suggested Mathlib Location

`Mathlib.MeasureTheory.Function.AEEqFun` or
`Mathlib.MeasureTheory.Function.AEHelpers`

## References

* Williams (1991), *Probability with Martingales*, §9
-/

noncomputable section
open scoped MeasureTheory ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set

namespace MeasureTheory

variable {α ι β : Type*} [MeasurableSpace α] {μ : Measure α}

/-- **Combine finitely many a.e.-equalities into an a.e.-equality of the sum.**

If each `f i` is a.e.-equal to `g i` on a finite index set `s`, then the
pointwise sums over `s` are a.e.-equal. Uses `EventuallyEq.fun_add` to
combine equalities. -/
theorem finset_sum_ae_eq [AddCommMonoid β]
    (s : Finset ι) (f g : ι → α → β)
    (h : ∀ i ∈ s, f i =ᵐ[μ] g i) :
    (fun ω => ∑ i ∈ s, f i ω) =ᵐ[μ] (fun ω => ∑ i ∈ s, g i ω) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s' ha IH =>
    simpa [Finset.sum_insert, ha] using (h a (Finset.mem_insert_self _ _)).fun_add
      (IH fun i hi => h i (Finset.mem_insert_of_mem hi))

end MeasureTheory

end
