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

This is the key technical lemma for extending conditional expectation properties from
individual terms to finite sums. If each `f i` is a.e.-equal to `g i` on a finite index
set `s`, then the pointwise sums over `s` are a.e.-equal.

**Why this works without timeout:** Uses `Finset.induction_on` which builds the result
incrementally without creating explicit intersections of all a.e. sets at once. The only
combination is the local `filter_upwards [h_a, IH']` which is tiny.

**Usage:** This is exactly the missing piece for Step 2 of the simple function factorization.
-/
lemma finset_sum_ae_eq
    {α ι β : Type*} [MeasurableSpace α] {μ : Measure α}
    [AddCommMonoid β]
    (s : Finset ι) (f g : ι → α → β)
    (h : ∀ i ∈ s, f i =ᵐ[μ] g i) :
    (fun ω => ∑ i ∈ s, f i ω) =ᵐ[μ] (fun ω => ∑ i ∈ s, g i ω) := by
  classical
  -- Induct on the finite set `s`.
  revert h
  refine Finset.induction_on s ?base ?step
  · -- Empty sum: both sides are the zero function.
    intro _; simp
  · intro a s ha IH h
    -- Split the hypothesis into the head and the tail.
    have h_a : f a =ᵐ[μ] g a := h a (by simp)
    have h_s : ∀ i ∈ s, f i =ᵐ[μ] g i := fun i hi => h i (by simp [hi])
    have IH' :
        (fun ω => ∑ i ∈ s, f i ω) =ᵐ[μ] (fun ω => ∑ i ∈ s, g i ω) :=
      IH h_s
    -- Add the two a.e.-equalities pointwise.
    have h_add :
        (fun ω => f a ω + ∑ i ∈ s, f i ω)
          =ᵐ[μ]
        (fun ω => g a ω + ∑ i ∈ s, g i ω) := by
      -- On the a.e. set where both `h_a` and `IH'` hold, the sums match.
      filter_upwards [h_a, IH'] with ω h1 h2
      simp [h1, h2]
    -- Reassemble the sums over `insert a s`.
    simpa [Finset.sum_insert, ha] using h_add

end
