/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# Product Bounds for Bounded Sequences

General lemmas about bounds on products of bounded sequences.
These are used in the contractability-based proof of de Finetti's theorem.

## Main results

* `abs_prod_le_one`: |∏ f| ≤ 1 when all |f i| ≤ 1
* `abs_prod_sub_prod_le`: |∏ f - ∏ g| ≤ ∑ |f_j - g_j| when factors bounded by 1
-/

namespace Exchangeability.Util

/-- Helper: |∏ f| ≤ 1 when all |f i| ≤ 1. -/
lemma abs_prod_le_one {n : ℕ} (f : Fin n → ℝ) (hf : ∀ i, |f i| ≤ 1) : |∏ i, f i| ≤ 1 := by
  rw [Finset.abs_prod]
  have h1 : ∏ i, |f i| ≤ ∏ _i : Fin n, (1 : ℝ) := by
    apply Finset.prod_le_prod
    · intro i _; exact abs_nonneg _
    · intro i _; exact hf i
  simp at h1
  exact h1

/-- Telescoping bound: |∏ f - ∏ g| ≤ ∑ |f_j - g_j| when factors are bounded by 1.

This is proved by induction using the identity:
  a*b - c*d = a*(b-d) + (a-c)*d
-/
lemma abs_prod_sub_prod_le {m : ℕ} (f g : Fin m → ℝ)
    (hf : ∀ i, |f i| ≤ 1) (hg : ∀ i, |g i| ≤ 1) :
    |∏ i, f i - ∏ i, g i| ≤ ∑ i, |f i - g i| := by
  induction m with
  | zero => simp
  | succ n ih =>
    rw [Fin.prod_univ_succ, Fin.prod_univ_succ, Fin.sum_univ_succ]
    let P_f := ∏ i : Fin n, f i.succ
    let P_g := ∏ i : Fin n, g i.succ
    -- Use identity: a*b - c*d = a*(b-d) + (a-c)*d
    have h1 : f 0 * P_f - g 0 * P_g = f 0 * (P_f - P_g) + (f 0 - g 0) * P_g := by ring
    have hPg : |P_g| ≤ 1 := abs_prod_le_one (fun i => g i.succ) (fun i => hg i.succ)
    calc |f 0 * P_f - g 0 * P_g|
        = |f 0 * (P_f - P_g) + (f 0 - g 0) * P_g| := by rw [h1]
      _ ≤ |f 0 * (P_f - P_g)| + |(f 0 - g 0) * P_g| := abs_add_le _ _
      _ = |f 0| * |P_f - P_g| + |f 0 - g 0| * |P_g| := by rw [abs_mul, abs_mul]
      _ ≤ 1 * |P_f - P_g| + |f 0 - g 0| * 1 := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_right (hf 0) (abs_nonneg _)
          · exact mul_le_mul_of_nonneg_left hPg (abs_nonneg _)
      _ = |P_f - P_g| + |f 0 - g 0| := by ring
      _ ≤ (∑ i : Fin n, |f i.succ - g i.succ|) + |f 0 - g 0| := by
          apply add_le_add_right
          exact ih (fun i => f i.succ) (fun i => g i.succ)
                   (fun i => hf i.succ) (fun i => hg i.succ)
      _ = |f 0 - g 0| + ∑ i : Fin n, |f i.succ - g i.succ| := by ring

/-- Helper: |a - b| ≤ |a| + |b|. -/
lemma abs_sub_le_abs_add (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  calc |a - b| = |a + (-b)| := by ring_nf
    _ ≤ |a| + |-b| := abs_add_le a (-b)
    _ = |a| + |b| := by rw [abs_neg]

end Exchangeability.Util
