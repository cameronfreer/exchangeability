/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Fin

/-!
# Window Machinery for Cesàro Averages

This file defines finite windows of consecutive indices used to express Cesàro averages
in the ViaL2 proof of de Finetti's theorem.

## Main definitions

* `window n k`: The finset `{n+1, n+2, ..., n+k}` of k consecutive indices starting from n+1

## Main results

* `window_card`: The window contains exactly k elements
* `mem_window_iff`: Characterization of window membership
* `sum_window_eq_sum_fin`: Sums over windows can be reindexed as sums over `Fin k`

## References

* Kallenberg (2005), *Probabilistic Symmetries and Invariance Principles*, Chapter 1
-/

namespace Exchangeability.DeFinetti.ViaL2

open scoped BigOperators

/-- **Finite window of consecutive indices.**

The window `{n+1, n+2, ..., n+k}` represented as a `Finset ℕ`.
Used to express Cesàro averages: `(1/k) * ∑_{i ∈ window n k} f(X_i)`. -/
def window (n k : ℕ) : Finset ℕ :=
  (Finset.range k).image fun i => n + i + 1

/-- The window contains exactly k elements. -/
lemma window_card (n k : ℕ) : (window n k).card = k := by
  classical
  unfold window
  refine (Finset.card_image_iff.mpr ?_).trans ?_
  · intro a ha b hb h
    have h' : n + a = n + b := by
      apply Nat.succ.inj
      simp only [Nat.succ_eq_add_one] at h ⊢
      omega
    exact Nat.add_left_cancel h'
  · simp only [Finset.card_range]

/-- Characterization of window membership. -/
lemma mem_window_iff {n k t : ℕ} :
    t ∈ window n k ↔ ∃ i : ℕ, i < k ∧ t = n + i + 1 := by
  classical
  unfold window
  constructor
  · intro ht
    rcases Finset.mem_image.mp ht with ⟨i, hi, rfl⟩
    refine ⟨i, ?_, rfl⟩
    simpa using hi
  · intro h
    rcases h with ⟨i, hi, rfl⟩
    refine Finset.mem_image.mpr ?_
    refine ⟨i, ?_, rfl⟩
    simpa using hi

/-- Sum over a window of length `k` can be reindexed as a sum over `Fin k`. -/
lemma sum_window_eq_sum_fin {β : Type*} [AddCommMonoid β]
    (n k : ℕ) (g : ℕ → β) :
    ∑ t ∈ window n k, g t = ∑ i : Fin k, g (n + i.val + 1) := by
  classical
  unfold window
  -- Show the image map used to define the window is injective
  have h_inj :
      ∀ a ∈ Finset.range k, ∀ b ∈ Finset.range k,
        (n + a + 1 = n + b + 1 → a = b) := by
    intro a ha b hb h
    have h' : a + 1 = b + 1 := by
      have : n + (a + 1) = n + (b + 1) := by
        omega
      exact Nat.add_left_cancel this
    exact Nat.succ.inj h'
  -- Convert the window sum to a range sum via the image definition
  have h_sum_range :
      ∑ t ∈ Finset.image (fun i => n + i + 1) (Finset.range k), g t
        = ∑ i ∈ Finset.range k, g (n + i + 1) :=
    Finset.sum_image <| by
      intro a ha b hb h
      exact h_inj a ha b hb h
  -- Replace the range sum with a sum over `Fin k`
  have h_range_to_fin :
      ∑ i ∈ Finset.range k, g (n + i + 1)
        = ∑ i : Fin k, g (n + i.val + 1) := by
    classical
    refine (Finset.sum_bij (fun (i : Fin k) _ => i.val)
        (fun i _ => by
          simp [Finset.mem_range, i.is_lt])
        (fun i hi j hj h => by
          exact Fin.ext h)
        (fun b hb => ?_)
        (fun i _ => rfl)).symm
    · rcases Finset.mem_range.mp hb with hb_lt
      refine ⟨⟨b, hb_lt⟩, ?_, rfl⟩
      simp
  simpa using h_sum_range.trans h_range_to_fin

end Exchangeability.DeFinetti.ViaL2
