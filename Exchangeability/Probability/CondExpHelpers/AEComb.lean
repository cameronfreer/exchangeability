/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-!
# Combining Finitely Many A.E. Equalities

This file provides a key technical lemma for combining finitely many a.e.-equalities
into an a.e.-equality of the finite sum.

## Main results

* `finset_sum_ae_eq`: If each `f i` is a.e.-equal to `g i` on a finite index set `s`,
  then the pointwise sums over `s` are a.e.-equal.
-/

noncomputable section
open scoped MeasureTheory ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set

/-- **Combine finitely many a.e.-equalities into an a.e.-equality of the finite sum.**

If each `f i` is a.e.-equal to `g i` on a finite index set `s`, then the pointwise
sums over `s` are a.e.-equal. Uses `EventuallyEq.fun_add` to combine equalities.
-/
lemma finset_sum_ae_eq
    {α ι β : Type*} [MeasurableSpace α] {μ : Measure α}
    [AddCommMonoid β]
    (s : Finset ι) (f g : ι → α → β)
    (h : ∀ i ∈ s, f i =ᵐ[μ] g i) :
    (fun ω => ∑ i ∈ s, f i ω) =ᵐ[μ] (fun ω => ∑ i ∈ s, g i ω) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s' ha IH =>
    simpa [Finset.sum_insert, ha] using (h a (Finset.mem_insert_self _ _)).fun_add
      (IH fun i hi => h i (Finset.mem_insert_of_mem hi))

end
