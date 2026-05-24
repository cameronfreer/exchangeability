/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Exchangeability.DeFinetti.ViaL2.AlphaIicCE
import Exchangeability.DeFinetti.ViaL2.CesaroConvergence.L1

/-!
# Endpoint limit at -∞ for `alphaIicCE`

L¹ and almost-everywhere pointwise convergence of `alphaIicCE` to 0 as `t → -∞`.

## Main result

* `alphaIicCE_ae_tendsto_zero_atBot`: For a.e. ω, `alphaIicCE X _ t ω → 0` as `t → -∞`.

The L¹ stepping stone `alphaIicCE_L1_tendsto_zero_atBot` is private to this file.

## References

* Kallenberg (2005), *Probabilistic Symmetries and Invariance Principles*,
  Chapter 1, "Second proof of Theorem 1.1"
-/

noncomputable section

namespace Exchangeability.DeFinetti.ViaL2

open MeasureTheory ProbabilityTheory BigOperators Filter Topology
open Exchangeability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- **L¹ endpoint limit at -∞**: As t → -∞, alphaIicCE → 0 in L¹.

**Proof strategy:**
- For t → -∞, the indicator `1_{(-∞,t]}(X_0 ω)` → 0 for each fixed ω
- By dominated convergence (bounded by 1), `‖1_{(-∞,t]} ∘ X_0‖₁ → 0`
- By L¹ contraction of conditional expectation:
  ```
  ‖alphaIicCE t - 0‖₁ = ‖μ[1_{(-∞,t]} ∘ X_0 | tailSigma] - μ[0 | tailSigma]‖₁
                      ≤ ‖1_{(-∞,t]} ∘ X_0 - 0‖₁ → 0
  ```
-/
private lemma alphaIicCE_L1_tendsto_zero_atBot
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ) :
    Tendsto (fun n : ℕ =>
      ∫ ω, |alphaIicCE X hX_contract hX_meas hX_L2 (-(n : ℝ)) ω| ∂μ)
      atTop (𝓝 0) := by
  -- Strategy: Use L¹ contraction property of conditional expectation
  -- ‖condExp m f‖₁ ≤ ‖f‖₁
  -- First show ‖(indIic (-(n:ℝ))) ∘ X 0‖₁ → 0 by dominated convergence

  -- Set up the tail σ-algebra Fact instance (needed for condExp)
  have hm_le : TailSigma.tailSigma X ≤ (inferInstance : MeasurableSpace Ω) :=
    TailSigma.tailSigma_le X hX_meas
  haveI : Fact (TailSigma.tailSigma X ≤ (inferInstance : MeasurableSpace Ω)) := ⟨hm_le⟩

  -- For each n, alphaIicCE (-(n:ℝ)) = μ[(indIic (-(n:ℝ))) ∘ X 0 | tailSigma]
  have h_def : ∀ n, alphaIicCE X hX_contract hX_meas hX_L2 (-(n : ℝ))
      = μ[(indIic (-(n : ℝ))) ∘ (X 0) | TailSigma.tailSigma X] := by
    intro n
    rfl

  -- Step 1: Show ∫ |(indIic (-(n:ℝ))) ∘ X 0| → 0
  -- Indicator integral = measure of set {X 0 ≤ -n} → 0 by continuity
  have h_indicator_tendsto : Tendsto (fun n : ℕ =>
      ∫ ω, |(indIic (-(n : ℝ))) (X 0 ω)| ∂μ) atTop (𝓝 0) := by
    -- Rewrite as integral = measure
    have h_eq : ∀ n : ℕ, ∫ ω, |(indIic (-(n : ℝ))) (X 0 ω)| ∂μ
        = (μ (X 0 ⁻¹' Set.Iic (-(n : ℝ)))).toReal := by
      intro n
      -- Indicator is nonnegative, so |indicator| = indicator
      have : (fun ω => |(indIic (-(n : ℝ))) (X 0 ω)|) = (indIic (-(n : ℝ))) ∘ (X 0) := by
        ext ω
        simp [indIic, Set.indicator]
        split_ifs <;> norm_num
      rw [this]
      -- Integral of indicator of measurable set = measure
      -- Rewrite composition as indicator on preimage
      have h_comp : (indIic (-(n : ℝ))) ∘ (X 0)
          = (X 0 ⁻¹' Set.Iic (-(n : ℝ))).indicator (fun _ => (1 : ℝ)) := by
        ext ω
        simp only [indIic, Function.comp_apply, Set.indicator_apply]
        rfl
      rw [h_comp, integral_indicator (measurableSet_preimage (hX_meas 0) measurableSet_Iic),
          setIntegral_one_eq_measureReal]
      rfl
    simp only [h_eq]
    -- The sets {X 0 ≤ -n} decrease to empty
    have h_antitone : Antitone (fun n : ℕ => X 0 ⁻¹' Set.Iic (-(n : ℝ))) := by
      intro n m hnm
      apply Set.preimage_mono
      intro x hx
      simp only [Set.mem_Iic] at hx ⊢
      calc x ≤ -(m : ℝ) := hx
           _ ≤ -(n : ℝ) := by simp [neg_le_neg_iff, Nat.cast_le, hnm]
    have h_empty : (⋂ (n : ℕ), X 0 ⁻¹' Set.Iic (-(n : ℝ))) = ∅ := by
      ext ω
      simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_Iic, Set.mem_empty_iff_false, iff_false]
      intro h
      -- For all n, X 0 ω ≤ -n, which means X 0 ω ≤ -n for arbitrarily large n
      -- This is impossible for any real number
      -- Use Archimedean property: exists n with -X 0 ω < n
      obtain ⟨n, hn⟩ := exists_nat_gt (-X 0 ω)
      -- This gives X 0 ω > -n, contradicting h n
      have h1 : X 0 ω > -(n : ℝ) := by linarith
      have h2 : X 0 ω ≤ -(n : ℝ) := h n
      linarith
    -- Apply tendsto_measure_iInter_atTop to get ENNReal convergence, then convert to Real
    have h_meas : ∀ (n : ℕ), NullMeasurableSet (X 0 ⁻¹' Set.Iic (-(n : ℝ))) μ := fun n =>
      (measurableSet_preimage (hX_meas 0) measurableSet_Iic).nullMeasurableSet
    have h_fin : ∃ (n : ℕ), μ (X 0 ⁻¹' Set.Iic (-(n : ℝ))) ≠ ⊤ := by
      use 0
      exact measure_ne_top μ _
    have h_tendsto_ennreal : Tendsto (fun (n : ℕ) => μ (X 0 ⁻¹' Set.Iic (-(n : ℝ)))) atTop (𝓝 0) := by
      have := tendsto_measure_iInter_atTop (μ := μ) h_meas h_antitone h_fin
      simp only [h_empty, measure_empty] at this
      simpa [Function.comp] using this
    -- Convert from ENNReal to Real using continuity of toReal at 0
    have h_ne_top : ∀ n, μ (X 0 ⁻¹' Set.Iic (-(n : ℝ))) ≠ ⊤ := fun n => measure_ne_top μ _
    have h_zero_ne_top : (0 : ENNReal) ≠ ⊤ := by norm_num
    rw [← ENNReal.toReal_zero]
    exact (ENNReal.continuousAt_toReal h_zero_ne_top).tendsto.comp h_tendsto_ennreal

  -- Step 2: L¹ contraction - ‖condExp f‖₁ ≤ ‖f‖₁
  have h_contraction : ∀ n : ℕ,
      ∫ ω, |alphaIicCE X hX_contract hX_meas hX_L2 (-(n : ℝ)) ω| ∂μ
      ≤ ∫ ω, |(indIic (-(n : ℝ))) (X 0 ω)| ∂μ := by
    intro n
    -- alphaIicCE is conditional expectation, so use integral_abs_condExp_le
    unfold alphaIicCE
    exact integral_abs_condExp_le (μ := μ) (m := TailSigma.tailSigma X) _

  -- Apply squeeze theorem: 0 ≤ ‖alphaIicCE‖₁ ≤ ‖indicator‖₁ → 0
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h_indicator_tendsto ?_ h_contraction
  intro n
  exact integral_nonneg (fun ω => abs_nonneg _)

/-- **A.e. pointwise endpoint limit at -∞**.

**Proof strategy:**
Combine monotonicity (from conditional expectation), boundedness (0 ≤ alphaIicCE ≤ 1),
and L¹ → 0 to conclude a.e. pointwise → 0 along integers. -/
lemma alphaIicCE_ae_tendsto_zero_atBot
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ =>
      alphaIicCE X hX_contract hX_meas hX_L2 (-(n : ℝ)) ω)
      atTop (𝓝 0) := by
  -- Strategy:
  -- 1. alphaIicCE is monotone decreasing in the sequence (-(n:ℝ))
  --    (since t ↦ alphaIicCE t is monotone increasing)
  -- 2. alphaIicCE ∈ [0,1] (bounded)
  -- 3. By monotone convergence, the sequence converges a.e. to some limit L
  -- 4. By L¹ convergence to 0, we have L = 0 a.e.

  -- Set up the tail σ-algebra (needed for conditional expectation)
  have hm_le : TailSigma.tailSigma X ≤ (inferInstance : MeasurableSpace Ω) :=
    TailSigma.tailSigma_le X hX_meas

  -- Step 1: Monotonicity - for each ω, alphaIicCE (-(m):ℝ) ω ≤ alphaIicCE (-(n):ℝ)) ω when n ≤ m
  have h_mono : ∀ᵐ ω ∂μ, ∀ n m : ℕ, n ≤ m →
      alphaIicCE X hX_contract hX_meas hX_L2 (-(m : ℝ)) ω
      ≤ alphaIicCE X hX_contract hX_meas hX_L2 (-(n : ℝ)) ω := by
    -- Use alphaIicCE_mono: s ≤ t implies alphaIicCE s ≤ alphaIicCE t a.e.
    -- When n ≤ m, we have -(m : ℝ) ≤ -(n : ℝ)
    -- Combine countably many ae statements using ae_all_iff
    rw [ae_all_iff]
    intro n
    rw [ae_all_iff]
    intro m
    by_cases hnm : n ≤ m
    · -- When n ≤ m, use alphaIicCE_mono with -(m:ℝ) ≤ -(n:ℝ)
      have h_le : -(m : ℝ) ≤ -(n : ℝ) := by
        simp [neg_le_neg_iff, Nat.cast_le, hnm]
      filter_upwards [alphaIicCE_mono X hX_contract hX_meas hX_L2 (-(m : ℝ)) (-(n : ℝ)) h_le] with ω hω
      intro _
      exact hω
    · -- When ¬(n ≤ m), the implication is vacuously true
      exact ae_of_all μ (fun ω h_contra => absurd h_contra hnm)

  -- Step 2: Boundedness - 0 ≤ alphaIicCE ≤ 1
  have h_bound : ∀ᵐ ω ∂μ, ∀ n : ℕ,
      0 ≤ alphaIicCE X hX_contract hX_meas hX_L2 (-(n : ℝ)) ω
      ∧ alphaIicCE X hX_contract hX_meas hX_L2 (-(n : ℝ)) ω ≤ 1 := by
    -- Use alphaIicCE_nonneg_le_one for each t, combine with ae_all_iff
    rw [ae_all_iff]
    intro n
    exact alphaIicCE_nonneg_le_one X hX_contract hX_meas hX_L2 (-(n : ℝ))

  -- Step 3: Monotone bounded sequences converge a.e.
  have h_ae_conv : ∀ᵐ ω ∂μ, ∃ L : ℝ, Tendsto (fun n : ℕ =>
      alphaIicCE X hX_contract hX_meas hX_L2 (-(n : ℝ)) ω) atTop (𝓝 L) := by
    -- Monotone decreasing bounded sequence converges (monotone convergence theorem)
    filter_upwards [h_mono, h_bound] with ω h_mono_ω h_bound_ω
    -- For this ω, the sequence is antitone and bounded, so it converges
    refine ⟨⨅ (n : ℕ), alphaIicCE X hX_contract hX_meas hX_L2 (-(n : ℝ)) ω, ?_⟩
    apply tendsto_atTop_ciInf
    · -- Antitone: n ≤ m implies f m ≤ f n
      intro n m hnm
      exact h_mono_ω n m hnm
    · -- Bounded below by 0
      refine ⟨0, ?_⟩
      rintro _ ⟨k, rfl⟩
      exact (h_bound_ω k).1

  -- Step 4: The limit is 0 by L¹ convergence
  -- Define the limit function L : Ω → ℝ
  -- For each ω in the convergence set, L(ω) = lim f_n(ω) = ⨅ n, f_n(ω)
  let L_fun : Ω → ℝ := fun ω => ⨅ (n : ℕ), alphaIicCE X hX_contract hX_meas hX_L2 (-(n : ℝ)) ω

  -- L_fun ≥ 0 a.e. (since each f_n ≥ 0 a.e.)
  have hL_nonneg : 0 ≤ᵐ[μ] L_fun := by
    filter_upwards [h_bound] with ω h_bound_ω
    apply le_ciInf
    intro n
    exact (h_bound_ω n).1

  -- From L¹ convergence ∫|f_n| → 0 and f_n ≥ 0, we get ∫ f_n → 0
  have h_L1_conv : Tendsto (fun n : ℕ =>
      ∫ ω, alphaIicCE X hX_contract hX_meas hX_L2 (-(n : ℝ)) ω ∂μ) atTop (𝓝 0) := by
    have h_abs := alphaIicCE_L1_tendsto_zero_atBot X hX_contract hX_meas hX_L2
    -- Since alphaIicCE ≥ 0 a.e., we have |alphaIicCE| = alphaIicCE a.e.
    -- Therefore ∫|f| = ∫ f
    refine h_abs.congr' ?_
    rw [EventuallyEq, eventually_atTop]
    use 0
    intro n _
    apply integral_congr_ae
    filter_upwards [alphaIicCE_nonneg_le_one X hX_contract hX_meas hX_L2 (-(n : ℝ))] with ω hω
    exact abs_of_nonneg hω.1

  -- By dominated convergence: ∫ L_fun = lim ∫ f_n = 0
  have hL_integral_zero : ∫ ω, L_fun ω ∂μ = 0 := by
    -- Use dominated convergence theorem with bound = 1 (constant function)
    have h_conv_ae : ∀ᵐ ω ∂μ, Tendsto (fun (n : ℕ) => alphaIicCE X hX_contract hX_meas hX_L2 (-(n : ℝ)) ω)
        atTop (𝓝 (L_fun ω)) := by
      filter_upwards [h_ae_conv, h_bound, h_mono] with ω ⟨L, hL⟩ h_bound_ω h_mono_ω
      have hL_is_inf : L = L_fun ω := by
        apply tendsto_nhds_unique hL
        apply tendsto_atTop_ciInf h_mono_ω
        exact ⟨0, fun y hy => by obtain ⟨k, hk⟩ := hy; rw [← hk]; exact (h_bound_ω k).1⟩
      rw [← hL_is_inf]
      exact hL
    have h_meas : ∀ (n : ℕ), AEStronglyMeasurable (fun ω => alphaIicCE X hX_contract hX_meas hX_L2 (-(n : ℝ)) ω) μ := by
      intro n
      -- alphaIicCE is conditional expectation μ[·|m], which is:
      -- 1. StronglyMeasurable[m] by stronglyMeasurable_condExp
      -- 2. AEStronglyMeasurable[m] by .aestronglyMeasurable
      -- 3. AEStronglyMeasurable[m₀] by .mono hm_le (where m ≤ m₀)
      unfold alphaIicCE
      exact stronglyMeasurable_condExp.aestronglyMeasurable.mono hm_le
    have h_bound_ae : ∀ (n : ℕ), ∀ᵐ ω ∂μ, ‖alphaIicCE X hX_contract hX_meas hX_L2 (-(n : ℝ)) ω‖ ≤ (1 : ℝ) := by
      intro n
      filter_upwards [alphaIicCE_nonneg_le_one X hX_contract hX_meas hX_L2 (-(n : ℝ))] with ω hω
      rw [Real.norm_eq_abs, abs_of_nonneg hω.1]
      exact hω.2
    have h_int : Integrable (fun _ : Ω => (1 : ℝ)) μ := integrable_const 1
    have h_lim := tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
      h_meas h_int h_bound_ae h_conv_ae
    rw [← tendsto_nhds_unique h_lim h_L1_conv]

  -- Since L_fun ≥ 0 a.e. and ∫ L_fun = 0, we have L_fun = 0 a.e.
  have hL_ae_zero : L_fun =ᵐ[μ] 0 := by
    -- Need to show L_fun is integrable first
    have hL_int : Integrable L_fun μ := by
      -- L_fun is bounded by 1 a.e., so it's integrable on a probability space
      have hL_bound : ∀ᵐ ω ∂μ, ‖L_fun ω‖ ≤ 1 := by
        filter_upwards [hL_nonneg, h_bound] with ω hω_nn h_bound_ω
        rw [Real.norm_eq_abs, abs_of_nonneg hω_nn]
        -- L_fun ω = ⨅ n, f(n) where each f(n) ≤ 1, so L_fun ω ≤ 1
        -- Use that infimum is ≤ any particular value
        calc L_fun ω
            = ⨅ (n : ℕ), alphaIicCE X hX_contract hX_meas hX_L2 (-(n : ℝ)) ω := rfl
          _ ≤ alphaIicCE X hX_contract hX_meas hX_L2 (-((0 : ℕ) : ℝ)) ω := by
              apply ciInf_le
              -- Bounded below by 0 (from alphaIicCE_nonneg_le_one)
              refine ⟨0, fun y hy => ?_⟩
              obtain ⟨k, hk⟩ := hy
              rw [← hk]
              exact (h_bound_ω k).1
          _ ≤ 1 := (h_bound_ω 0).2
      -- L_fun is AEStronglyMeasurable as the a.e. limit of measurable functions
      have hL_meas : AEStronglyMeasurable L_fun μ := by
        -- Each alphaIicCE (-(n:ℝ)) is AEStronglyMeasurable (conditional expectation)
        have h_meas_n : ∀ (n : ℕ), AEStronglyMeasurable (fun ω => alphaIicCE X hX_contract hX_meas hX_L2 (-(n : ℝ)) ω) μ := by
          intro n
          unfold alphaIicCE
          exact stronglyMeasurable_condExp.aestronglyMeasurable.mono hm_le
        -- They converge a.e. to L_fun (by monotone convergence)
        have h_conv_ae_n : ∀ᵐ ω ∂μ, Tendsto (fun (n : ℕ) => alphaIicCE X hX_contract hX_meas hX_L2 (-(n : ℝ)) ω)
            atTop (𝓝 (L_fun ω)) := by
          filter_upwards [h_ae_conv, h_bound, h_mono] with ω ⟨L, hL⟩ h_bound_ω h_mono_ω
          have hL_is_inf : L = L_fun ω := by
            apply tendsto_nhds_unique hL
            apply tendsto_atTop_ciInf h_mono_ω
            exact ⟨0, fun y hy => by obtain ⟨k, hk⟩ := hy; rw [← hk]; exact (h_bound_ω k).1⟩
          rw [← hL_is_inf]
          exact hL
        -- Apply aestronglyMeasurable_of_tendsto_ae
        exact aestronglyMeasurable_of_tendsto_ae atTop h_meas_n h_conv_ae_n
      exact Integrable.of_bound hL_meas 1 hL_bound
    -- Now apply integral_eq_zero_iff_of_nonneg_ae
    rw [← integral_eq_zero_iff_of_nonneg_ae hL_nonneg hL_int]
    exact hL_integral_zero

  -- Now show Tendsto f_n (𝓝 0) at a.e. ω
  filter_upwards [h_ae_conv, hL_ae_zero, h_bound, h_mono] with ω ⟨L, hL⟩ hL_zero h_bound_ω h_mono_ω
  -- At this ω, we have f_n → L and L_fun(ω) = 0
  have hL_eq : L = L_fun ω := by
    apply tendsto_nhds_unique hL
    apply tendsto_atTop_ciInf h_mono_ω
    exact ⟨0, fun y hy => by obtain ⟨k, hk⟩ := hy; rw [← hk]; exact (h_bound_ω k).1⟩
  rw [hL_eq, hL_zero] at hL
  exact hL


end Exchangeability.DeFinetti.ViaL2
