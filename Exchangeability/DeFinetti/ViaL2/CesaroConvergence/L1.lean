/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Exchangeability.DeFinetti.ViaL2.BlockAvgDef
import Exchangeability.DeFinetti.ViaL2.BlockAverages
import Exchangeability.DeFinetti.ViaL2.CesaroConvergence.L2
import Exchangeability.DeFinetti.L2Helpers
import Exchangeability.Contractability
import Exchangeability.Probability.CondExp
import Exchangeability.Probability.IntegrationHelpers
import Exchangeability.Probability.LpNormHelpers
import Exchangeability.Probability.CenteredVariables
import Exchangeability.Probability.SigmaAlgebraHelpers
import Exchangeability.Util.FinsetHelpers
import Exchangeability.Tail.TailSigma
import Exchangeability.Tail.ShiftInvariantMeasure
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.InnerProductSpace.MeanErgodic

/-!
# Cesàro L¹ Convergence: `cesaro_to_condexp_L1`

L¹ version of `cesaro_to_condexp_L2` (from `CesaroConvergence/L2.lean`), derived
by L² → L¹ on a probability space (Cauchy–Schwarz). This is the convergence form
consumed by `AlphaConvergence.lean`.

## Main results

* `cesaro_to_condexp_L1`: L¹ convergence of block Cesàro averages to the tail
  conditional expectation

## References

* Kallenberg (2005), *Probabilistic Symmetries and Invariance Principles*,
  Chapter 1, "Second proof of Theorem 1.1"
-/

noncomputable section

namespace Exchangeability.DeFinetti.ViaL2

open MeasureTheory ProbabilityTheory BigOperators Filter Topology
open Exchangeability
open Exchangeability.DeFinetti.L2Helpers
open Exchangeability.Probability.CenteredVariables

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

open scoped BigOperators

lemma cesaro_to_condexp_L1
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} (hX_contract : Exchangeability.Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (f : ℝ → ℝ) (hf_meas : Measurable f) (hf_bdd : ∀ x, |f x| ≤ 1) :
    ∀ ε > 0, ∃ (M : ℕ), ∀ (m : ℕ), m ≥ M →
      ∫ ω, |(1 / (m : ℝ)) * ∑ i : Fin m, f (X i ω) -
             (μ[(f ∘ X 0) | TailSigma.tailSigma X] ω)| ∂μ < ε := by
  -- Get L² convergence from cesaro_to_condexp_L2
  obtain ⟨α_f, hα_L2, hα_tail, hα_conv, hα_eq⟩ := cesaro_to_condexp_L2 hX_contract hX_meas f hf_meas hf_bdd

  intro ε hε

  -- Convert L² convergence to L¹ convergence
  -- On probability spaces: ‖f - g‖₁ ≤ ‖f - g‖₂ (by Cauchy-Schwarz with ‖1‖₂ = 1)
  -- So L² → 0 implies L¹ → 0

  -- Available from cesaro_to_condexp_L2:
  -- • α_f : Ω → ℝ - the L² limit
  -- • hα_L2 : MemLp α_f 2 μ - α_f is in L²
  -- • hα_tail : Measurable[TailSigma.tailSigma X] α_f - α_f is tail-measurable
  -- • hα_conv : Tendsto (fun n => eLpNorm (blockAvg f X 0 n - α_f) 2 μ) atTop (𝓝 0)
  -- • hα_eq : α_f =ᵐ[μ] μ[f ∘ X 0 | TailSigma.tailSigma X]

  -- STEP 1: Convert eLpNorm convergence to plain integral form
  -- eLpNorm g 2 μ = (∫ |g|² ∂μ)^(1/2), so squaring both sides and using continuity
  -- First, show that each difference is in L²
  have h_diff_memLp : ∀ n, MemLp (fun ω => blockAvg f X 0 n ω - α_f ω) 2 μ := fun n =>
    (blockAvg_memLp_two_of_abs_le_one f X hf_meas hX_meas hf_bdd 0 n).sub hα_L2

  have hL2_integral : Tendsto (fun n => ∫ ω, (blockAvg f X 0 n ω - α_f ω)^2 ∂μ) atTop (𝓝 0) := by
    -- Define gn := blockAvg f X 0 n - α_f for notational convenience
    -- Goal: Tendsto (fun n => ∫ ω, (gn ω)² ∂μ) atTop (𝓝 0)
    -- From hα_conv: Tendsto (fun n => eLpNorm gn 2 μ) atTop (𝓝 0)

    -- Step 1: Convert ENNReal convergence to ℝ via ENNReal.tendsto_toReal
    have h_toReal : Tendsto (fun n => (eLpNorm (blockAvg f X 0 n - α_f) 2 μ).toReal) atTop (𝓝 0) := by
      rw [← ENNReal.toReal_zero]
      exact (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hα_conv

    -- Step 2: Square using Tendsto.pow (0² = 0)
    have h_sq : Tendsto (fun n => (eLpNorm (blockAvg f X 0 n - α_f) 2 μ).toReal ^ 2) atTop (𝓝 0) := by
      have h_zero_sq : (0 : ℝ) ^ 2 = 0 := by norm_num
      rw [← h_zero_sq]
      exact h_toReal.pow 2

    -- Step 3: Relate squared toReal to integral of squared function
    -- Key identity: For MemLp g 2 μ real-valued:
    --   (eLpNorm g 2 μ).toReal² = ∫ g² dμ
    suffices h_eq : ∀ n, (eLpNorm (blockAvg f X 0 n - α_f) 2 μ).toReal ^ 2 =
        ∫ ω, (blockAvg f X 0 n ω - α_f ω)^2 ∂μ by
      simp_rw [← h_eq]
      exact h_sq

    -- Prove the equality for each n using MemLp.eLpNorm_eq_integral_rpow_norm
    intro n
    have hgn_memLp : MemLp (blockAvg f X 0 n - α_f) 2 μ := h_diff_memLp n
    -- Use MemLp.eLpNorm_eq_integral_rpow_norm:
    -- eLpNorm g 2 μ = ENNReal.ofReal ((∫ a, ‖g a‖ ^ 2 ∂μ) ^ (1/2))
    have hp_ne_zero : (2 : ENNReal) ≠ 0 := by norm_num
    have hp_ne_top : (2 : ENNReal) ≠ ⊤ := by norm_num
    have h_eq_ofReal := MemLp.eLpNorm_eq_integral_rpow_norm hp_ne_zero hp_ne_top hgn_memLp
    simp only [ENNReal.toReal_ofNat, inv_eq_one_div] at h_eq_ofReal
    -- Now: eLpNorm g 2 μ = ENNReal.ofReal ((∫ a, ‖g a‖² ∂μ)^(1/2))
    -- Taking toReal: (eLpNorm g 2 μ).toReal = (∫ a, ‖g a‖² ∂μ)^(1/2) (for nonneg integral)
    -- First, establish the integral is nonneg (needed for ofReal/toReal)
    -- Note: Use (2 : ℝ) to match MemLp.eLpNorm_eq_integral_rpow_norm which uses p.toReal
    have h_integral_nonneg : 0 ≤ ∫ a, ‖(blockAvg f X 0 n - α_f) a‖ ^ (2 : ℝ) ∂μ :=
      integral_nonneg (fun _ => Real.rpow_nonneg (norm_nonneg _) _)
    -- Key: (eLpNorm g 2 μ).toReal² = ∫ g² dμ
    -- Compute step by step
    have h_sqrt_nonneg : 0 ≤ (∫ a, ‖(blockAvg f X 0 n - α_f) a‖ ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) :=
      Real.rpow_nonneg h_integral_nonneg _
    -- Step 1: First show (eLpNorm ...).toReal = (∫...)^(1/2)
    have h_toReal_eq : (eLpNorm (blockAvg f X 0 n - α_f) 2 μ).toReal =
        (∫ a, ‖(blockAvg f X 0 n - α_f) a‖ ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) := by
      rw [h_eq_ofReal]
      exact ENNReal.toReal_ofReal h_sqrt_nonneg
    -- Step 2: Square both sides: toReal² = ((∫...)^(1/2))² = ∫...
    calc (eLpNorm (blockAvg f X 0 n - α_f) 2 μ).toReal ^ 2
        = ((∫ a, ‖(blockAvg f X 0 n - α_f) a‖ ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ)) ^ 2 := by rw [h_toReal_eq]
      _ = (∫ a, ‖(blockAvg f X 0 n - α_f) a‖ ^ (2 : ℝ) ∂μ) ^ (1 / 2 * 2 : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul h_integral_nonneg]
          norm_cast
      _ = (∫ a, ‖(blockAvg f X 0 n - α_f) a‖ ^ (2 : ℝ) ∂μ) := by norm_num
      _ = ∫ ω, (blockAvg f X 0 n ω - α_f ω) ^ 2 ∂μ := by
          apply integral_congr_ae
          filter_upwards with a
          -- LHS: ‖(f - g) a‖ ^ (2:ℝ), RHS: (f a - g a) ^ 2
          -- Step 1: Convert ‖x‖^(2:ℝ) → |x|^2 (natural power)
          rw [Real.rpow_two, Real.norm_eq_abs]
          -- Step 2: |x|^2 = x^2 (sq_abs), then unfold Pi.sub
          simp only [sq_abs, Pi.sub_apply]

  -- STEP 2: Apply L2_tendsto_implies_L1_tendsto_of_bounded
  have hf_meas : ∀ n, Measurable (blockAvg f X 0 n) := by
    intro n
    exact blockAvg_measurable f X hf_meas hX_meas 0 n

  have hf_blockAvg_bdd : ∃ M, ∀ n ω, |blockAvg f X 0 n ω| ≤ M := by
    use 1
    intro n ω
    exact blockAvg_abs_le_one f X hf_bdd 0 n ω

  have hL1_conv : Tendsto (fun n => ∫ ω, |blockAvg f X 0 n ω - α_f ω| ∂μ) atTop (𝓝 0) :=
    Exchangeability.Probability.IntegrationHelpers.L2_tendsto_implies_L1_tendsto_of_bounded
      (fun n => blockAvg f X 0 n) α_f hf_meas hf_blockAvg_bdd hα_L2 hL2_integral

  -- STEP 3: Convert Tendsto to ∃ M, ∀ m ≥ M form using metric convergence
  rw [Metric.tendsto_atTop] at hL1_conv
  obtain ⟨M, hM⟩ := hL1_conv ε hε
  use M
  intro m hm

  -- STEP 4-5: Use a.e. equality and apply convergence bound
  -- hM states: dist (∫|blockAvg m - α_f|) 0 < ε
  -- Goal: ∫|(1/m)*∑ f(X i) - μ[f∘X 0|tail]| < ε
  -- These are equal by (a) blockAvg definition and (b) α_f =ᵐ μ[f∘X 0|tail]

  convert hM m hm using 1
  simp only [Real.dist_eq, sub_zero]
  -- Remove outer absolute value (integral of |...| is non-negative)
  rw [abs_of_nonneg]
  swap
  · apply integral_nonneg
    intro ω
    exact abs_nonneg _
  -- Show ∫|blockAvg m - α_f| = ∫|(1/m)*∑ - μ[f∘X 0|tail]|
  apply integral_congr_ae
  filter_upwards [hα_eq] with ω hω_eq
  -- blockAvg f X 0 m ω = (m : ℝ)⁻¹ * ∑ k ∈ Finset.range m, f (X k ω)
  -- which equals 1/m * ∑ i : Fin m, f (X i ω)
  rw [hω_eq]
  show _ = |blockAvg f X 0 m ω - _|
  congr 1
  -- Unfold blockAvg definition and convert between sum representations
  simp only [blockAvg, zero_add, one_div]
  -- Convert sum over Fin m to sum over Finset.range m
  congr 2
  exact (Finset.sum_range (fun i => f (X i ω))).symm

end Exchangeability.DeFinetti.ViaL2

