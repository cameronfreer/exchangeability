/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Block Cesàro Average Definition

This file defines block Cesàro averages used in Kallenberg's L² approach to de Finetti's theorem.

## Main definitions

* `blockAvg f X m n ω`: The block average (1/n) ∑_{k=0}^{n-1} f(X_{m+k}(ω))

## Main results

* `blockAvg_measurable`: Block averages are measurable
* `blockAvg_abs_le_one`: Block averages of bounded functions are bounded

## References

* Kallenberg (2005), *Probabilistic Symmetries and Invariance Principles*, Chapter 1
-/

noncomputable section

namespace Exchangeability.DeFinetti.ViaL2

open MeasureTheory BigOperators
open scoped BigOperators

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- **Block Cesàro average** of a function along a sequence.

For a function `f : α → ℝ` and sequence `X : ℕ → Ω → α`, the block average
starting at index `m` with length `n` is:

  A_{m,n}(ω) := (1/n) ∑_{k=0}^{n-1} f(X_{m+k}(ω))

This is the building block for Kallenberg's L² convergence proof. -/
def blockAvg (f : α → ℝ) (X : ℕ → Ω → α) (m n : ℕ) (ω : Ω) : ℝ :=
  (n : ℝ)⁻¹ * (Finset.range n).sum (fun k => f (X (m + k) ω))

@[measurability, fun_prop]
lemma blockAvg_measurable
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (f : α → ℝ) (X : ℕ → Ω → α)
    (hf : Measurable f) (hX : ∀ i, Measurable (X i))
    (m n : ℕ) :
    Measurable (fun ω => blockAvg f X m n ω) := by
  classical
  unfold blockAvg
  fun_prop

lemma blockAvg_abs_le_one
    {Ω α : Type*} [MeasurableSpace Ω]
    (f : α → ℝ) (X : ℕ → Ω → α)
    (hf_bdd : ∀ x, |f x| ≤ 1)
    (m n : ℕ) :
    ∀ ω, |blockAvg f X m n ω| ≤ 1 := by
  classical
  intro ω
  unfold blockAvg
  have hsum_bound :
      |(Finset.range n).sum (fun k => f (X (m + k) ω))| ≤ (n : ℝ) := by
    calc |(Finset.range n).sum (fun k => f (X (m + k) ω))|
        ≤ (Finset.range n).sum (fun k => |f (X (m + k) ω)|) :=
          Finset.abs_sum_le_sum_abs (fun k => f (X (m + k) ω)) (Finset.range n)
      _ ≤ (Finset.range n).sum (fun _ => (1 : ℝ)) := by
          apply Finset.sum_le_sum
          intro k _
          exact hf_bdd (X (m + k) ω)
      _ = n := by
          have : (Finset.range n).card = n := Finset.card_range n
          simp [this]
  have hnonneg : 0 ≤ (n : ℝ)⁻¹ := inv_nonneg.mpr (by exact_mod_cast Nat.zero_le n)
  calc
    |(n : ℝ)⁻¹ * (Finset.range n).sum (fun k => f (X (m + k) ω))|
        = (n : ℝ)⁻¹ * |(Finset.range n).sum (fun k => f (X (m + k) ω))|
          := by simp [abs_mul, abs_of_nonneg hnonneg]
    _ ≤ (n : ℝ)⁻¹ * (n : ℝ)
          := by exact mul_le_mul_of_nonneg_left hsum_bound hnonneg
    _ ≤ 1 := by
        by_cases hn : n = 0
        · simp [hn]
        · have : (n : ℝ) ≠ 0 := by simp [hn]
          simp [this]

/-- `blockAvg f X m n` is in L²(μ) whenever `f` is bounded by 1, on any probability space.
Combines `blockAvg_measurable` + `blockAvg_abs_le_one` + `MemLp.of_bound`. -/
lemma blockAvg_memLp_two_of_abs_le_one
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (f : α → ℝ) (X : ℕ → Ω → α)
    (hf_meas : Measurable f) (hX_meas : ∀ i, Measurable (X i))
    (hf_bdd : ∀ x, |f x| ≤ 1) (m n : ℕ) :
    MemLp (blockAvg f X m n) 2 μ := by
  refine MemLp.of_bound (blockAvg_measurable f X hf_meas hX_meas m n).aestronglyMeasurable 1 ?_
  exact ae_of_all μ fun ω => (Real.norm_eq_abs _).le.trans (blockAvg_abs_le_one f X hf_bdd m n ω)

end Exchangeability.DeFinetti.ViaL2
