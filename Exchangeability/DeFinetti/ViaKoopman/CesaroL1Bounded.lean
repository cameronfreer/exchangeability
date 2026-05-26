/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Exchangeability.DeFinetti.ViaKoopman.CesaroL2ToL1

/-! # L¹ Cesàro Convergence for Bounded and Integrable Functions

This file contains:
- `L1_cesaro_convergence_bounded` - bounded case public lemma
- `L1_cesaro_convergence` - general integrable case via truncation
- `ce_lipschitz_convergence` - L¹ convergence through conditional expectation
-/

open Filter MeasureTheory

noncomputable section

namespace Exchangeability.DeFinetti.ViaKoopman

open MeasureTheory Filter Topology ProbabilityTheory
open Exchangeability.Ergodic
open Exchangeability.PathSpace
open scoped BigOperators RealInnerProductSpace

variable {α : Type*} [MeasurableSpace α]

-- Short notation for shift-invariant σ-algebra (used throughout this file)
local notation "mSI" => shiftInvariantSigma (α := α)


section CesaroL1Bounded

variable {μ : Measure (Ω[α])} [IsProbabilityMeasure μ] [StandardBorelSpace α]

omit [StandardBorelSpace α] in
/-- **L¹ Cesàro convergence for bounded functions**.

For a bounded measurable function g : α → ℝ, the Cesàro averages
`A_n(ω) = (1/(n+1)) ∑_{j=0}^n g(ω_j)` converge in L¹ to the conditional
expectation `μ[g(ω₀) | mSI]`.

This is a key ingredient for de Finetti's theorem via contractability. -/
lemma L1_cesaro_convergence_bounded
    {μ : Measure (Ω[α])} [IsProbabilityMeasure μ] [StandardBorelSpace α]
    (hσ : MeasurePreserving shift μ μ)
    (g : α → ℝ)
    (hg_meas : Measurable g) (hg_bd : ∃ Cg, ∀ x, |g x| ≤ Cg) :
    let A := fun n : ℕ => fun ω => (1 / ((n + 1) : ℝ)) * (Finset.range (n + 1)).sum (fun j => g (ω j))
    Tendsto (fun n =>
      ∫ ω, |A n ω - μ[(fun ω => g (ω 0)) | mSI] ω| ∂μ)
            atTop (𝓝 0) := by
  classical
  intro A
  -- Call optionB_L1_convergence_bounded theorem defined in CesaroL2ToL1
  exact optionB_L1_convergence_bounded hσ g hg_meas hg_bd

-- Iteration of shift by j steps applied to coordinate 0 gives coordinate j
omit [MeasurableSpace α] in
private lemma shift_iterate_apply_zero (j : ℕ) (ω : ℕ → α) :
    (shift^[j] ω) 0 = ω j := by
  rw [shift_iterate_apply]
  simp

omit [StandardBorelSpace α] in
/-- **L¹ Cesàro convergence for integrable functions**.

Extends the bounded case to general integrable functions by truncating g_M := max(min(g, M), -M),
applying the bounded case to each g_M, and letting M → ∞ using dominated convergence. -/
lemma L1_cesaro_convergence
    {μ : Measure (Ω[α])} [IsProbabilityMeasure μ] [StandardBorelSpace α]
    (hσ : MeasurePreserving shift μ μ)
    (g : α → ℝ)
    (hg_meas : Measurable g) (hg_int : Integrable (fun ω => g (ω 0)) μ) :
    let A := fun n : ℕ => fun ω => (1 / ((n + 1) : ℝ)) * (Finset.range (n + 1)).sum (fun j => g (ω j))
    Tendsto (fun n =>
      ∫ ω, |A n ω - μ[(fun ω => g (ω 0)) | mSI] ω| ∂μ)
            atTop (𝓝 0) := by
  intro A
  classical
  -- Strategy: Truncate g, apply bounded case, use dominated convergence (Kallenberg p.14)

  -- Step 1: Define truncation g_M M x = max (min (g x) M) (-M)
  let g_M : ℕ → α → ℝ := fun M x => max (min (g x) (M : ℝ)) (-(M : ℝ))

  -- Step 2: Each g_M is bounded by M
  have hg_M_bd : ∀ M, ∃ C, ∀ x, |g_M M x| ≤ C := by
    intro M
    use M
    intro x
    have h1 : -(M : ℝ) ≤ g_M M x := by
      simp only [g_M]
      exact le_max_right _ _
    have h2 : g_M M x ≤ (M : ℝ) := by
      simp only [g_M]
      exact max_le (min_le_right _ _) (by linarith : -(M : ℝ) ≤ (M : ℝ))
    exact abs_le.mpr ⟨by linarith, h2⟩

  -- Step 3: Each g_M is measurable
  have hg_M_meas : ∀ M, Measurable (g_M M) := fun M =>
    (hg_meas.min measurable_const).max measurable_const

  -- Step 4: Apply bounded case to each g_M
  have h_bdd : ∀ M, Tendsto (fun (n : ℕ) =>
      ∫ ω, |(1 / (↑(n + 1) : ℝ)) * (Finset.range (n + 1)).sum (fun j => g_M M (ω j))
            - μ[(fun ω => g_M M (ω 0)) | mSI] ω| ∂μ) atTop (𝓝 0) := by
    intro M
    -- Apply L1_cesaro_convergence_bounded to g_M M
    have h_bdd_M := L1_cesaro_convergence_bounded hσ (g_M M) (hg_M_meas M) (hg_M_bd M)
    -- The theorem defines A with (n + 1 : ℝ) which equals ↑n + ↑1
    -- We need ↑(n + 1), so show ↑(n + 1) = ↑n + ↑1 using Nat.cast_add
    convert h_bdd_M using 1
    funext n
    congr 1 with ω
    congr 1
    -- Show: 1 / ↑(n + 1) = 1 / (↑n + ↑1)
    rw [Nat.cast_add, Nat.cast_one]

  -- Step 5: Truncation error → 0 as M → ∞
  -- For any x, g_M M x = g x when M > |g x|
  have h_trunc_conv : ∀ x, ∀ᶠ M in atTop, g_M M x = g x := by
    intro x
    refine eventually_atTop.mpr ⟨Nat.ceil |g x| + 1, fun M hM => ?_⟩
    have hM' : |g x| < (M : ℝ) := by
      have : (Nat.ceil |g x| : ℝ) < M := by exact_mod_cast hM
      exact lt_of_le_of_lt (Nat.le_ceil _) this
    simp [g_M]
    have h_abs : -(M : ℝ) < g x ∧ g x < (M : ℝ) := abs_lt.mp hM'
    have h1 : -(M : ℝ) < g x := h_abs.1
    have h2 : g x < (M : ℝ) := h_abs.2
    simp [min_eq_left (le_of_lt h2), max_eq_left (le_of_lt h1)]

  -- For each ω, ∫|g(ω j) - g_M M (ω j)| → 0
  have h_trunc_L1 : Tendsto (fun M => ∫ ω, |g (ω 0) - g_M M (ω 0)| ∂μ) atTop (𝓝 0) := by
    -- Use dominated convergence: |g - g_M M| ≤ 2|g| and converges pointwise to 0
    have h_dom : ∀ M, (fun ω => |g (ω 0) - g_M M (ω 0)|) ≤ᵐ[μ] (fun ω => 2 * |g (ω 0)|) := by
      intro M
      refine ae_of_all μ (fun ω => ?_)
      have hg_M_le : |g_M M (ω 0)| ≤ |g (ω 0)| := by
        simp [g_M]
        -- Standard clamp inequality: clamping to [-M, M] doesn't increase absolute value
        have : |max (min (g (ω 0)) (M : ℝ)) (-(M : ℝ))| ≤ |g (ω 0)| := by
          -- Let v = max (min g M) (-M). Then -M ≤ v ≤ M and v is between g and 0 (or equal to g)
          set v := max (min (g (ω 0)) (M : ℝ)) (-(M : ℝ))
          -- Case 1: If |g| ≤ M, then v = g
          by_cases h : |g (ω 0)| ≤ (M : ℝ)
          · have hg_le : g (ω 0) ≤ (M : ℝ) := (abs_le.mp h).2
            have hg_ge : -(M : ℝ) ≤ g (ω 0) := (abs_le.mp h).1
            have : v = g (ω 0) := by
              simp [v, min_eq_left hg_le, max_eq_left hg_ge]
            rw [this]
          -- Case 2: If |g| > M, then |v| ≤ M < |g|
          · have hv_le : |v| ≤ (M : ℝ) := by
              have h1 : -(M : ℝ) ≤ v := le_max_right _ _
              have h2 : v ≤ (M : ℝ) := max_le (min_le_right _ _) (by linarith : -(M : ℝ) ≤ (M : ℝ))
              exact abs_le.mpr ⟨h1, h2⟩
            linarith
        exact this
      calc |g (ω 0) - g_M M (ω 0)|
          ≤ |g (ω 0)| + |g_M M (ω 0)| := abs_sub _ _
        _ ≤ |g (ω 0)| + |g (ω 0)| := by linarith [hg_M_le]
        _ = 2 * |g (ω 0)| := by ring
    have h_point : ∀ᵐ ω ∂μ, Tendsto (fun M => |g (ω 0) - g_M M (ω 0)|) atTop (𝓝 0) := by
      refine ae_of_all μ (fun ω => ?_)
      have h_eq := h_trunc_conv (ω 0)
      -- Eventually g_M M (ω 0) = g (ω 0), so |difference| = 0
      refine Tendsto.congr' (h_eq.mono fun M hM => ?_) tendsto_const_nhds
      simp [hM]
    have h_int : Integrable (fun ω => 2 * |g (ω 0)|) μ :=
      hg_int.norm.const_mul 2
    -- Apply dominated convergence theorem
    have h_meas : ∀ M, AEStronglyMeasurable (fun ω => |g (ω 0) - g_M M (ω 0)|) μ := fun M =>
      ((hg_meas.comp (measurable_pi_apply 0)).sub
        ((hg_M_meas M).comp (measurable_pi_apply 0))).norm.aestronglyMeasurable
    have h_dom' : ∀ M, (fun ω => ‖g (ω 0) - g_M M (ω 0)‖) ≤ᵐ[μ] (fun ω => 2 * ‖g (ω 0)‖) := by
      intro M
      filter_upwards [h_dom M] with ω h
      simpa [Real.norm_eq_abs] using h
    have h_point' : ∀ᵐ ω ∂μ, Tendsto (fun M => ‖g (ω 0) - g_M M (ω 0)‖) atTop (𝓝 0) := by
      filter_upwards [h_point] with ω h
      simpa [Real.norm_eq_abs] using h
    have h_int' : Integrable (fun ω => 2 * ‖g (ω 0)‖) μ := by
      simpa [Real.norm_eq_abs] using h_int
    have h_bound : ∀ n, ∀ᵐ a ∂μ, ‖|g (a 0) - g_M n (a 0)|‖ ≤ 2 * |g (a 0)| := fun n => by
      filter_upwards [h_dom n] with ω hω
      simp only [Real.norm_eq_abs, abs_abs]
      exact hω
    simpa using tendsto_integral_of_dominated_convergence (fun ω => 2 * |g (ω 0)|) h_meas h_int h_bound h_point

  -- Step 6: CE L¹-continuity
  have h_ce_trunc_L1 : Tendsto (fun M =>
      ∫ ω, |μ[(fun ω => g (ω 0)) | mSI] ω - μ[(fun ω => g_M M (ω 0)) | mSI] ω| ∂μ)
      atTop (𝓝 0) := by
    have h_bound : ∀ M, (∫ ω, |μ[(fun ω => g (ω 0)) | mSI] ω - μ[(fun ω => g_M M (ω 0)) | mSI] ω| ∂μ)
        ≤ ∫ ω, |g (ω 0) - g_M M (ω 0)| ∂μ := by
      intro M
      have h_integrable_diff : Integrable (fun ω => g (ω 0) - g_M M (ω 0)) μ := by
        have h_g_M_int : Integrable (fun ω => g_M M (ω 0)) μ := by
          obtain ⟨C, hC⟩ := hg_M_bd M
          refine Exchangeability.Probability.integrable_of_bounded ?_ ⟨C, fun ω => hC (ω 0)⟩
          exact (hg_M_meas M).comp (measurable_pi_apply 0)
        exact hg_int.sub h_g_M_int
      have h_ce_lin : μ[(fun ω => g (ω 0) - g_M M (ω 0)) | mSI] =ᵐ[μ]
          (fun ω => μ[(fun ω => g (ω 0)) | mSI] ω - μ[(fun ω => g_M M (ω 0)) | mSI] ω) := by
        have h_int_g : Integrable (fun ω => g (ω 0)) μ := hg_int
        have h_int_gM : Integrable (fun ω => g_M M (ω 0)) μ := by
          obtain ⟨C, hC⟩ := hg_M_bd M
          refine Exchangeability.Probability.integrable_of_bounded ?_ ⟨C, fun ω => hC (ω 0)⟩
          exact (hg_M_meas M).comp (measurable_pi_apply 0)
        exact condExp_sub h_int_g h_int_gM mSI
      calc ∫ ω, |μ[(fun ω => g (ω 0)) | mSI] ω - μ[(fun ω => g_M M (ω 0)) | mSI] ω| ∂μ
          = ∫ ω, |μ[(fun ω => g (ω 0) - g_M M (ω 0)) | mSI] ω| ∂μ := by
              refine integral_congr_ae ?_
              filter_upwards [h_ce_lin] with ω h
              simp [h]
        _ ≤ ∫ ω, |g (ω 0) - g_M M (ω 0)| ∂μ :=
              integral_abs_condExp_le (m := mSI) (fun ω => g (ω 0) - g_M M (ω 0))
    refine squeeze_zero (fun M => integral_nonneg (fun ω => abs_nonneg _)) h_bound ?_
    exact h_trunc_L1

  -- Step 7: ε/3 argument
  refine Metric.tendsto_atTop.mpr (fun ε hε => ?_)
  have h_third : 0 < ε / 3 := by linarith
  obtain ⟨M, hM_trunc⟩ := Metric.tendsto_atTop.mp h_trunc_L1 (ε / 3) h_third
  obtain ⟨M', hM'_ce⟩ := Metric.tendsto_atTop.mp h_ce_trunc_L1 (ε / 3) h_third
  let M₀ : ℕ := max M M'
  obtain ⟨N, hN_bdd⟩ := Metric.tendsto_atTop.mp (h_bdd M₀) (ε / 3) h_third
  use N
  intro n hn
  rw [Real.dist_eq, sub_zero]

  let A_M₀ : (ℕ → α) → ℝ := fun ω => (1 / ((n + 1) : ℝ)) * (Finset.range (n + 1)).sum (fun j => g_M M₀ (ω j))

  have h_tri_pointwise : ∀ ω, |A n ω - μ[(fun ω => g (ω 0)) | mSI] ω|
      ≤ |A n ω - A_M₀ ω|
        + |A_M₀ ω - μ[(fun ω => g_M M₀ (ω 0)) | mSI] ω|
        + |μ[(fun ω => g_M M₀ (ω 0)) | mSI] ω - μ[(fun ω => g (ω 0)) | mSI] ω| := by
    intro ω
    calc |A n ω - μ[(fun ω => g (ω 0)) | mSI] ω|
        ≤ |A n ω - A_M₀ ω| + |A_M₀ ω - μ[(fun ω => g (ω 0)) | mSI] ω| := abs_sub_le _ _ _
      _ ≤ |A n ω - A_M₀ ω|
          + |A_M₀ ω - μ[(fun ω => g_M M₀ (ω 0)) | mSI] ω|
          + |μ[(fun ω => g_M M₀ (ω 0)) | mSI] ω - μ[(fun ω => g (ω 0)) | mSI] ω| := by
            linarith [abs_sub_le (A_M₀ ω) (μ[(fun ω => g_M M₀ (ω 0)) | mSI] ω) (μ[(fun ω => g (ω 0)) | mSI] ω)]

  have h_nonneg : 0 ≤ ∫ ω, |A n ω - μ[(fun ω => g (ω 0)) | mSI] ω| ∂μ :=
    integral_nonneg (fun ω => abs_nonneg _)
  rw [abs_of_nonneg h_nonneg]

  -- Integrability facts
  have h_int_ce_g : Integrable (μ[(fun ω => g (ω 0)) | mSI]) μ := integrable_condExp
  have h_int_gM : Integrable (fun ω => g_M M₀ (ω 0)) μ := by
    obtain ⟨C, hC⟩ := hg_M_bd M₀
    refine Exchangeability.Probability.integrable_of_bounded ?_ ⟨C, fun ω => hC (ω 0)⟩
    exact (hg_M_meas M₀).comp (measurable_pi_apply 0)
  have h_int_ce_gM : Integrable (μ[(fun ω => g_M M₀ (ω 0)) | mSI]) μ := integrable_condExp

  have h_int_A : Integrable (A n) μ := by
    simp only [A]
    have h_int_sum : Integrable (fun ω => (Finset.range (n + 1)).sum (fun j => g (ω j))) μ := by
      have h_each_int : ∀ j ∈ Finset.range (n + 1), Integrable (fun ω => g (ω j)) μ := by
        intro j _
        have h_eq : (fun ω => g (ω j)) = (fun ω => g ((shift^[j] ω) 0)) := by
          simp [shift_iterate_apply_zero]
        rw [h_eq]
        have h_shiftj_pres : MeasurePreserving (shift^[j]) μ μ := hσ.iterate j
        exact h_shiftj_pres.integrable_comp_of_integrable hg_int
      exact integrable_finset_sum (Finset.range (n + 1)) h_each_int
    exact h_int_sum.const_mul (1 / ((n + 1) : ℝ))

  have h_int_AM : Integrable A_M₀ μ := by
    simp only [A_M₀]
    have h_int_sum : Integrable (fun ω => (Finset.range (n + 1)).sum (fun j => g_M M₀ (ω j))) μ := by
      have h_each_int : ∀ j ∈ Finset.range (n + 1), Integrable (fun ω => g_M M₀ (ω j)) μ := by
        intro j _
        obtain ⟨C, hC⟩ := hg_M_bd M₀
        refine Exchangeability.Probability.integrable_of_bounded ?_ ⟨C, fun ω => hC (ω j)⟩
        exact (hg_M_meas M₀).comp (measurable_pi_apply j)
      exact integrable_finset_sum (Finset.range (n + 1)) h_each_int
    exact h_int_sum.const_mul (1 / ((n + 1) : ℝ))

  have h_int_diff1 : Integrable (fun ω => |A n ω - A_M₀ ω|) μ := (h_int_A.sub h_int_AM).abs
  have h_int_diff2 : Integrable (fun ω => |A_M₀ ω - μ[(fun ω => g_M M₀ (ω 0)) | mSI] ω|) μ :=
    (h_int_AM.sub h_int_ce_gM).abs
  have h_int_diff3 : Integrable (fun ω => |μ[(fun ω => g_M M₀ (ω 0)) | mSI] ω - μ[(fun ω => g (ω 0)) | mSI] ω|) μ :=
    (h_int_ce_gM.sub h_int_ce_g).abs

  calc ∫ ω, |A n ω - μ[(fun ω => g (ω 0)) | mSI] ω| ∂μ
      ≤ ∫ ω, (|A n ω - A_M₀ ω|
            + |A_M₀ ω - μ[(fun ω => g_M M₀ (ω 0)) | mSI] ω|
            + |μ[(fun ω => g_M M₀ (ω 0)) | mSI] ω - μ[(fun ω => g (ω 0)) | mSI] ω|) ∂μ := by
        refine integral_mono_ae ?_ ?_ ?_
        · exact (h_int_A.sub h_int_ce_g).abs
        · exact ((h_int_A.sub h_int_AM).abs.add (h_int_AM.sub h_int_ce_gM).abs).add (h_int_ce_gM.sub h_int_ce_g).abs
        · filter_upwards with ω; exact h_tri_pointwise ω
    _ = (∫ ω, |A n ω - A_M₀ ω| ∂μ)
        + (∫ ω, |A_M₀ ω - μ[(fun ω => g_M M₀ (ω 0)) | mSI] ω| ∂μ)
        + (∫ ω, |μ[(fun ω => g_M M₀ (ω 0)) | mSI] ω - μ[(fun ω => g (ω 0)) | mSI] ω| ∂μ) := by
        rw [integral_add, integral_add]
        · exact h_int_diff1
        · exact h_int_diff2
        · exact h_int_diff1.add h_int_diff2
        · exact h_int_diff3
    _ < ε / 3 + ε / 3 + ε / 3 := by
        gcongr
        · -- Term 1: shift invariance argument
          have h_M₀_ge : M₀ ≥ M := le_max_left M M'
          have h_bound := hM_trunc M₀ h_M₀_ge
          rw [Real.dist_eq, sub_zero] at h_bound
          rw [abs_of_nonneg (integral_nonneg (fun ω => abs_nonneg _))] at h_bound
          calc ∫ ω, |A n ω - A_M₀ ω| ∂μ
              ≤ ∫ ω, (1 / (↑n + 1)) * (∑ j ∈ Finset.range (n + 1), |g (ω j) - g_M M₀ (ω j)|) ∂μ := by
                refine integral_mono_ae ?_ ?_ ?_
                · exact (h_int_A.sub h_int_AM).abs
                · have h_sum_int : Integrable (fun ω => ∑ j ∈ Finset.range (n + 1), |g (ω j) - g_M M₀ (ω j)|) μ := by
                    refine integrable_finset_sum _ (fun j _ => ?_)
                    have h_int_gj : Integrable (fun ω => g (ω j)) μ := by
                      have h_eq : (fun ω => g (ω j)) = (fun ω => g ((shift^[j] ω) 0)) := by
                        simp [shift_iterate_apply_zero]
                      rw [h_eq]
                      exact (hσ.iterate j).integrable_comp_of_integrable hg_int
                    have h_int_gMj : Integrable (fun ω => g_M M₀ (ω j)) μ := by
                      obtain ⟨C, hC⟩ := hg_M_bd M₀
                      refine Exchangeability.Probability.integrable_of_bounded ?_ ⟨C, fun ω => hC (ω j)⟩
                      exact (hg_M_meas M₀).comp (measurable_pi_apply j)
                    exact (h_int_gj.sub h_int_gMj).abs
                  exact h_sum_int.const_mul (1 / ((n + 1) : ℝ))
                · filter_upwards with ω
                  simp only [A, A_M₀]
                  rw [← mul_sub_left_distrib, ← Finset.sum_sub_distrib, abs_mul, abs_of_pos (by positivity : 0 < 1 / (↑n + 1 : ℝ))]
                  exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
            _ = (1 / (↑n + 1)) * ∑ j ∈ Finset.range (n + 1), ∫ ω, |g (ω j) - g_M M₀ (ω j)| ∂μ := by
                rw [integral_const_mul, integral_finset_sum]
                intro j _
                have h_int_gj : Integrable (fun ω => g (ω j)) μ := by
                  have h_eq : (fun ω => g (ω j)) = (fun ω => g ((shift^[j] ω) 0)) := by
                    simp [shift_iterate_apply_zero]
                  rw [h_eq]
                  exact (hσ.iterate j).integrable_comp_of_integrable hg_int
                have h_int_gMj : Integrable (fun ω => g_M M₀ (ω j)) μ := by
                  obtain ⟨C, hC⟩ := hg_M_bd M₀
                  refine Exchangeability.Probability.integrable_of_bounded ?_ ⟨C, fun ω => hC (ω j)⟩
                  exact (hg_M_meas M₀).comp (measurable_pi_apply j)
                exact (h_int_gj.sub h_int_gMj).abs
            _ = (1 / (↑n + 1)) * ∑ j ∈ Finset.range (n + 1), ∫ ω, |g (ω 0) - g_M M₀ (ω 0)| ∂μ := by
                congr 1
                refine Finset.sum_congr rfl fun j _hj => ?_
                have h_iter : MeasurePreserving (shift^[j]) μ μ := hσ.iterate j
                have h_smeas : StronglyMeasurable (fun ω : Ω[α] => |g (ω 0) - g_M M₀ (ω 0)|) :=
                  ((hg_meas.comp (measurable_pi_apply 0)).sub
                    ((hg_M_meas M₀).comp (measurable_pi_apply 0))).stronglyMeasurable.norm
                have h_eq : ∫ ω, |g (ω j) - g_M M₀ (ω j)| ∂μ =
                    ∫ ω, (fun ω' => |g (ω' 0) - g_M M₀ (ω' 0)|) (shift^[j] ω) ∂μ := by
                  congr 1; ext ω; exact congrArg₂ (fun a b => |g a - g_M M₀ b|) (shift_iterate_apply_zero j ω).symm (shift_iterate_apply_zero j ω).symm
                rw [h_eq, (integral_map_of_stronglyMeasurable h_iter.measurable h_smeas).symm, h_iter.map_eq]
            _ = (1 / (↑n + 1)) * ((n + 1) * ∫ ω, |g (ω 0) - g_M M₀ (ω 0)| ∂μ) := by
                congr 1
                rw [Finset.sum_const, Finset.card_range]
                ring
            _ = ∫ ω, |g (ω 0) - g_M M₀ (ω 0)| ∂μ := by field_simp
            _ < ε / 3 := h_bound
        · -- Term 2: bounded case
          have := hN_bdd n hn
          rw [Real.dist_eq, sub_zero] at this
          rw [abs_of_nonneg (integral_nonneg (fun ω => abs_nonneg _))] at this
          convert this using 2
          ext ω
          simp only [A_M₀]
          congr 1
          norm_cast
        · -- Term 3: CE truncation error
          have h_M₀_ge : M₀ ≥ M' := le_max_right M M'
          have := hM'_ce M₀ h_M₀_ge
          rw [Real.dist_eq, sub_zero] at this
          rw [abs_of_nonneg (integral_nonneg (fun ω => abs_nonneg _))] at this
          calc ∫ ω, |μ[(fun ω => g_M M₀ (ω 0)) | mSI] ω - μ[(fun ω => g (ω 0)) | mSI] ω| ∂μ
              = ∫ ω, |μ[(fun ω => g (ω 0)) | mSI] ω - μ[(fun ω => g_M M₀ (ω 0)) | mSI] ω| ∂μ := by
                  congr 1; ext ω; exact abs_sub_comm _ _
            _ < ε / 3 := this
    _ = ε := by ring

omit [StandardBorelSpace α] in
/-- **CE Lipschitz convergence**: Pull L¹ convergence through conditional expectation.

Given that `A_n → CE[g(ω₀) | mSI]` in L¹ and f is bounded,
proves that `CE[f·A_n | mSI] → CE[f·CE[g | mSI] | mSI]` in L¹. -/
lemma ce_lipschitz_convergence
    {μ : Measure (Ω[α])} [IsProbabilityMeasure μ] [StandardBorelSpace α]
    (f g : α → ℝ)
    (hf_meas : Measurable f) (hf_bd : ∃ Cf, ∀ x, |f x| ≤ Cf)
    (hg_meas : Measurable g) (hg_bd : ∃ Cg, ∀ x, |g x| ≤ Cg)
    (h_L1_An_to_CE :
      let A := fun n : ℕ => fun ω => (1 / ((n + 1) : ℝ)) * (Finset.range (n + 1)).sum (fun j => g (ω j))
      Tendsto (fun n =>
        ∫ ω, |A n ω - μ[(fun ω => g (ω 0)) | mSI] ω| ∂μ)
              atTop (𝓝 0)) :
    let A := fun n : ℕ => fun ω => (1 / ((n + 1) : ℝ)) * (Finset.range (n + 1)).sum (fun j => g (ω j))
    Tendsto (fun n =>
      ∫ ω, |μ[(fun ω' => f (ω' 0) * A n ω') | mSI] ω
           - μ[(fun ω' => f (ω' 0) * μ[(fun ω => g (ω 0)) | mSI] ω') | mSI] ω| ∂μ)
      atTop (𝓝 0) := by
  let A := fun n : ℕ => fun ω : Ω[α] => (1 / ((n + 1) : ℝ)) * (Finset.range (n + 1)).sum (fun j => g (ω j))
  set Y : Ω[α] → ℝ := fun ω => μ[(fun ω' => g (ω' 0)) | mSI] ω with hY_def
  obtain ⟨Cf, hCf⟩ := hf_bd
  obtain ⟨Cg, hCg⟩ := hg_bd

  have hA_int : ∀ n, Integrable (A n) μ := fun n =>
    (integrable_finset_sum (Finset.range (n + 1)) fun j _ =>
      integrable_of_bounded_measurable
        (hg_meas.comp (measurable_pi_apply j)) Cg fun ω => hCg (ω j)).smul (1 / ((n + 1) : ℝ))

  have hg0_int : Integrable (fun ω => g (ω 0)) μ :=
    integrable_of_bounded_measurable
      (hg_meas.comp (measurable_pi_apply 0)) Cg (fun ω => hCg (ω 0))

  have hZ_int : ∀ n, Integrable (fun ω => f (ω 0) * A n ω) μ := fun n =>
    integrable_mul_of_ae_bdd_left (hf_meas.comp (measurable_pi_apply 0))
      ⟨Cf, ae_of_all μ (fun ω => hCf (ω 0))⟩ (hA_int n)

  have hW_int : Integrable (fun ω => f (ω 0) * Y ω) μ :=
    integrable_mul_of_ae_bdd_left (hf_meas.comp (measurable_pi_apply 0))
      ⟨Cf, ae_of_all μ (fun ω => hCf (ω 0))⟩ integrable_condExp

  have h₁ : ∀ n, ∫ ω, |μ[(fun ω' => f (ω' 0) * A n ω') | mSI] ω
                     - μ[(fun ω' => f (ω' 0) * Y ω') | mSI] ω| ∂μ
               ≤ ∫ ω, |f (ω 0) * A n ω - f (ω 0) * Y ω| ∂μ := fun n =>
    Exchangeability.Probability.condExp_L1_lipschitz
      (μ := μ) (m := mSI) (hZ_int n) hW_int

  have h₂ : ∀ n, ∫ ω, |f (ω 0) * A n ω - f (ω 0) * Y ω| ∂μ
               ≤ Cf * ∫ ω, |A n ω - Y ω| ∂μ := fun n => by
    have h_eq : ∀ ω, |f (ω 0) * A n ω - f (ω 0) * Y ω| = |f (ω 0)| * |A n ω - Y ω| := fun ω => by
      rw [← mul_sub, abs_mul]
    have hpt : ∀ᵐ ω ∂μ, |f (ω 0)| * |A n ω - Y ω| ≤ Cf * |A n ω - Y ω| :=
      ae_of_all μ (fun ω => mul_le_mul_of_nonneg_right (hCf (ω 0)) (abs_nonneg _))
    have h_diff_int : Integrable (fun ω => A n ω - Y ω) μ := (hA_int n).sub integrable_condExp
    have hint_rhs : Integrable (fun ω => Cf * |A n ω - Y ω|) μ := h_diff_int.abs.const_mul Cf
    have hint_lhs : Integrable (fun ω => |f (ω 0)| * |A n ω - Y ω|) μ := by
      have h_bd_by_rhs : ∀ᵐ ω ∂μ, ‖|f (ω 0)| * |A n ω - Y ω|‖ ≤ Cf * |A n ω - Y ω| := by
        filter_upwards with ω
        rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_abs]
        exact mul_le_mul_of_nonneg_right (hCf (ω 0)) (abs_nonneg _)
      have h_asm : AEStronglyMeasurable (fun ω => |f (ω 0)| * |A n ω - Y ω|) μ :=
        (continuous_abs.measurable.comp (hf_meas.comp (measurable_pi_apply 0))).aestronglyMeasurable.mul
          (continuous_abs.comp_aestronglyMeasurable ((hA_int n).sub integrable_condExp).aestronglyMeasurable)
      exact Integrable.mono' hint_rhs h_asm h_bd_by_rhs
    calc ∫ ω, |f (ω 0) * A n ω - f (ω 0) * Y ω| ∂μ
        = ∫ ω, |f (ω 0)| * |A n ω - Y ω| ∂μ := by congr 1; ext ω; exact h_eq ω
      _ ≤ ∫ ω, Cf * |A n ω - Y ω| ∂μ := integral_mono_ae hint_lhs hint_rhs hpt
      _ = Cf * ∫ ω, |A n ω - Y ω| ∂μ := integral_const_mul Cf _

  have h_upper : ∀ n,
      ∫ ω, |μ[(fun ω' => f (ω' 0) * A n ω') | mSI] ω
           - μ[(fun ω' => f (ω' 0) * Y ω') | mSI] ω| ∂μ
      ≤ Cf * ∫ ω, |A n ω - μ[(fun ω => g (ω 0)) | mSI] ω| ∂μ := fun n =>
    le_trans (h₁ n) (h₂ n)

  have h_bound_to_zero : Tendsto (fun n =>
      Cf * ∫ ω, |A n ω - μ[(fun ω => g (ω 0)) | mSI] ω| ∂μ) atTop (𝓝 0) := by
    convert Tendsto.const_mul Cf h_L1_An_to_CE using 1
    simp

  have h_nonneg : ∀ n, 0 ≤ ∫ ω, |μ[(fun ω' => f (ω' 0) * A n ω') | mSI] ω
       - μ[(fun ω' => f (ω' 0) * Y ω') | mSI] ω| ∂μ := fun n =>
    integral_nonneg (fun ω => abs_nonneg _)

  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h_bound_to_zero h_nonneg h_upper

end CesaroL1Bounded

end Exchangeability.DeFinetti.ViaKoopman
