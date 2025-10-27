/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer, Claude (Anthropic)
-/
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Cesàro Convergence Helper Lemmas

Utility lemmas for proving L² convergence of Cesàro (block) averages to conditional
expectations. These helpers reduce friction in the main convergence proofs.

## Main Results

* `cesaroCoeff`: Coefficients for block average weighted sums
* `cesaroCoeff_sup_le`: Bound on supremum of coefficient differences
* `tendsto_eLpNorm_sub_of_tendsto_in_Lp`: Convert Lp metric convergence to eLpNorm form
* `setIntegral_le_eLpNorm_mul_measure`: Cauchy-Schwarz on set integrals

These lemmas support the proof that block averages of exchangeable sequences converge
to conditional expectations (Kallenberg Lemma 1.3 / de Finetti via L²).
-/

noncomputable section

open scoped BigOperators
open MeasureTheory Filter Topology

namespace Exchangeability.Probability.CesaroHelpers

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-! ### Cesàro Coefficients -/

/-- **Cesàro weights for block averages.**

The coefficient for index i in a block average starting at N with length n:
- 0 if i < N (before block)
- 1/n if N ≤ i < N+n (in block)
- 0 if i ≥ N+n (after block)

Used to express block average differences as weighted sums. -/
def cesaroCoeff (N n i : ℕ) : ℝ :=
  if i < N then 0 else if i < N + n then (1 : ℝ) / n else 0

lemma cesaroCoeff_of_lt_start {N n i : ℕ} (h : i < N) :
    cesaroCoeff N n i = 0 := by
  simp only [cesaroCoeff, h, ↓reduceIte]

lemma cesaroCoeff_of_in_block {N n i : ℕ} (h1 : N ≤ i) (h2 : i < N + n) :
    cesaroCoeff N n i = (1 : ℝ) / n := by
  simp only [cesaroCoeff]
  split_ifs with h3 h4
  · exact absurd h1 (not_le_of_gt h3)
  · rfl

lemma cesaroCoeff_of_ge_end {N n i : ℕ} (h : N + n ≤ i) :
    cesaroCoeff N n i = 0 := by
  simp only [cesaroCoeff]
  split_ifs with h1 h2
  · rfl
  · exact absurd h (not_le_of_gt h2)
  · rfl

/-- **Supremum bound on Cesàro coefficient differences.**

For block averages starting at 0 with lengths n and n', the supremum of
coefficient differences is bounded by max(1/n, 1/n').

This is the key estimate for applying Kallenberg's L² bound to show Cauchy property. -/
lemma cesaroCoeff_sup_le (n n' : ℕ) (hn : n ≠ 0) (hn' : n' ≠ 0) :
    ⨆ i : ℕ, |cesaroCoeff 0 n i - cesaroCoeff 0 n' i| ≤ max ((1 : ℝ) / n) (1 / n') := by
  -- The coefficient at any index i is in {0, 1/n} for the first block,
  -- {0, 1/n'} for the second block, so their difference is bounded
  apply ciSup_le
  intro i
  -- Case split on position of i
  by_cases h1 : i < min n n'
  · -- i in both blocks: coeff n i = 1/n, coeff n' i = 1/n'
    rw [cesaroCoeff_of_in_block (Nat.zero_le i) (by simp; exact Nat.lt_of_lt_of_le h1 (min_le_left n n')),
        cesaroCoeff_of_in_block (Nat.zero_le i) (by simp; exact Nat.lt_of_lt_of_le h1 (min_le_right n n'))]
    -- |1/n - 1/n'| ≤ max(1/n, 1/n')
    rcases le_total n n' with hle | hle
    · -- n ≤ n', so 1/n ≥ 1/n'
      have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
      have hn'_pos : (0 : ℝ) < n' := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn')
      have : (1 : ℝ) / n - 1 / n' ≥ 0 := by
        have : (1 : ℝ) / n' ≤ 1 / n := by
          apply div_le_div_of_nonneg_left <;> [exact zero_le_one; exact hn_pos; exact Nat.cast_le.mpr hle]
        linarith
      calc |1 / ↑n - 1 / ↑n'|
          = 1 / ↑n - 1 / ↑n' := abs_of_nonneg this
        _ ≤ 1 / ↑n := by linarith [show (0 : ℝ) ≤ 1 / ↑n' by positivity]
        _ ≤ max (1 / ↑n) (1 / ↑n') := le_max_left _ _
    · -- n' ≤ n, so 1/n' ≥ 1/n
      have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
      have hn'_pos : (0 : ℝ) < n' := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn')
      have : (1 : ℝ) / n - 1 / n' ≤ 0 := by
        have : (1 : ℝ) / n ≤ 1 / n' := by
          apply div_le_div_of_nonneg_left <;> [exact zero_le_one; exact hn'_pos; exact Nat.cast_le.mpr hle]
        linarith
      calc |1 / ↑n - 1 / ↑n'|
          = -(1 / ↑n - 1 / ↑n') := abs_of_nonpos this
        _ = 1 / ↑n' - 1 / ↑n := by ring
        _ ≤ 1 / ↑n' := by linarith [show (0 : ℝ) ≤ 1 / ↑n by positivity]
        _ ≤ max (1 / ↑n) (1 / ↑n') := le_max_right _ _
  · -- i outside common block
    by_cases h2 : i < max n n'
    · -- i in exactly one block
      rcases Nat.lt_or_ge i n with hin | hin
      · -- i < n but i ≥ n' (since i ≥ min n n')
        have hn'_le_i : n' ≤ i := Nat.le_of_not_lt (fun h => h1 (Nat.lt_min hin h))
        have h_in_n : i < 0 + n := by simpa using hin
        rw [cesaroCoeff_of_in_block (Nat.zero_le i) h_in_n,
            cesaroCoeff_of_ge_end (by simpa using hn'_le_i)]
        simp only [sub_zero, abs_div, abs_one]
        norm_num
        exact le_max_left _ _
      · -- i ≥ n but i < n' (since i < max n n')
        have h_i_lt_n' : i < n' := Nat.lt_of_lt_of_le h2 (Nat.le_max_right n n')
        have h_ge_n : 0 + n ≤ i := by simpa using hin
        rw [cesaroCoeff_of_ge_end h_ge_n,
            cesaroCoeff_of_in_block (Nat.zero_le i) (by simpa using h_i_lt_n')]
        simp only [zero_sub, abs_neg, abs_div, abs_one]
        norm_num
        exact le_max_right _ _
    · -- i ≥ max n n', so both coefficients are 0
      have hn_le : n ≤ i := Nat.le_of_not_lt (fun h => h2 (Nat.lt_of_lt_of_le h (Nat.le_max_left n n')))
      have hn'_le : n' ≤ i := Nat.le_of_not_lt (fun h => h2 (Nat.lt_of_lt_of_le h (Nat.le_max_right n n')))
      rw [cesaroCoeff_of_ge_end (by simpa using hn_le),
          cesaroCoeff_of_ge_end (by simpa using hn'_le)]
      simp only [sub_zero, abs_zero]
      exact le_max_of_le_left (one_div_nonneg.mpr (Nat.cast_nonneg n))

/-! ### Lp Convergence Utilities -/

/-- **Convert Lp metric convergence to eLpNorm form.**

If a sequence in Lp converges in the metric topology, then the eLpNorm
of differences from the limit tends to 0.

This bridges the gap between abstract Lp convergence and concrete eLpNorm bounds. -/
lemma tendsto_eLpNorm_sub_of_tendsto_in_Lp
    {μ : Measure Ω} [IsProbabilityMeasure μ] {p : ℝ≥0∞}
    {u : ℕ → Lp ℝ p μ} {v : Lp ℝ p μ}
    (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    (h : Tendsto u atTop (𝓝 v)) :
    Tendsto (fun n => eLpNorm (u n - v) p μ) atTop (𝓝 0) := by
  -- Metric convergence in Lp is exactly dist → 0
  have h_dist : Tendsto (fun n => dist (u n) v) atTop (𝓝 0) :=
    Metric.tendsto_atTop.mp h 1 zero_lt_one |> fun ⟨N, hN⟩ =>
      tendsto_atTop_of_eventually_const (N := N) (fun n hn => ?_)
  sorry -- Use Lp.dist_def to relate dist to eLpNorm

/-- **Cauchy-Schwarz on set integrals (probability measure).**

For a set A and function g ∈ L²(μ), the absolute value of ∫_A g is bounded
by the L² norm of g times √(μ A).

On probability spaces with μ A ≤ 1, this simplifies to |∫_A g| ≤ ‖g‖₂. -/
lemma setIntegral_le_eLpNorm_mul_measure
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (A : Set Ω) (hA : MeasurableSet A) {g : Ω → ℝ}
    (hg : MemLp g 2 μ) :
    |∫ x in A, g x ∂μ| ≤ (eLpNorm g 2 μ).toReal * (μ A).toReal ^ (1/2 : ℝ) := by
  -- Cauchy-Schwarz: ∫_A g = ∫ (indicator A g) ≤ ‖indicator A 1‖₂ * ‖g‖₂
  -- where ‖indicator A 1‖₂ = √(μ A)
  sorry

/-- **Simplified set integral bound for probability measures.**

On a probability space, |∫_A g| ≤ ‖g‖₂ since μ A ≤ 1. -/
lemma setIntegral_le_eLpNorm
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (A : Set Ω) (hA : MeasurableSet A) {g : Ω → ℝ}
    (hg : MemLp g 2 μ) :
    |∫ x in A, g x ∂μ| ≤ (eLpNorm g 2 μ).toReal := by
  calc |∫ x in A, g x ∂μ|
      ≤ (eLpNorm g 2 μ).toReal * (μ A).toReal ^ (1/2 : ℝ) :=
        setIntegral_le_eLpNorm_mul_measure A hA hg
    _ ≤ (eLpNorm g 2 μ).toReal * 1 := by
        apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
        have h_measure_le : (μ A).toReal ≤ 1 := by
          have : μ A ≤ 1 := prob_le_one
          cases' (μ A).eq_top_or_lt_top with h h
          · simp [h]
          · rw [ENNReal.toReal_le_toReal h ENNReal.one_ne_top]
            exact this
        calc (μ A).toReal ^ (1/2 : ℝ)
            ≤ 1 ^ (1/2 : ℝ) := Real.rpow_le_rpow ENNReal.toReal_nonneg h_measure_le (by norm_num : 0 ≤ (1 / 2 : ℝ))
          _ = 1 := by norm_num
    _ = (eLpNorm g 2 μ).toReal := mul_one _

end Exchangeability.Probability.CesaroHelpers
