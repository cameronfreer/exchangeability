/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Exchangeability.DeFinetti.ViaL2.AlphaIicCE
import Exchangeability.DeFinetti.ViaL2.CesaroConvergence.L1
import Exchangeability.DeFinetti.ViaL2.AlphaConvergence.EndpointCommon

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
  have hm_le : Exchangeability.Tail.tailProcess X ≤ (inferInstance : MeasurableSpace Ω) :=
    Exchangeability.Tail.tailProcess_le_ambient X hX_meas
  haveI : Fact (Exchangeability.Tail.tailProcess X ≤ (inferInstance : MeasurableSpace Ω)) := ⟨hm_le⟩

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
    exact integral_abs_condExp_le (μ := μ) (m := Exchangeability.Tail.tailProcess X) _

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
  -- Strategy: the sequence is antitone (since `t ↦ alphaIicCE _ t` is monotone) and
  -- bounded in [0,1], so it converges pointwise a.e. to its infimum `L ω`. The L¹
  -- limit (from `alphaIicCE_L1_tendsto_zero_atBot`) is `0`, so the shared helper
  -- `ae_tendsto_const_of_ae_convergent_of_L1_const` identifies `L ω = 0` a.e.
  set f : ℕ → Ω → ℝ := fun n ω => alphaIicCE X hX_contract hX_meas hX_L2 (-(n : ℝ)) ω
    with hf_def
  set L : Ω → ℝ := fun ω => ⨅ (n : ℕ), f n ω with hL_def
  have hm_le : Exchangeability.Tail.tailProcess X ≤ (inferInstance : MeasurableSpace Ω) :=
    Exchangeability.Tail.tailProcess_le_ambient X hX_meas
  -- (1) Each f n is AEStronglyMeasurable (conditional expectation).
  have hf_meas : ∀ n, AEStronglyMeasurable (f n) μ := fun n => by
    show AEStronglyMeasurable (alphaIicCE X hX_contract hX_meas hX_L2 (-(n : ℝ))) μ
    unfold alphaIicCE
    exact stronglyMeasurable_condExp.aestronglyMeasurable.mono hm_le
  -- (2) Uniform bound ‖f n ω‖ ≤ 1.
  have hf_bound : ∀ n, ∀ᵐ ω ∂μ, ‖f n ω‖ ≤ (1 : ℝ) := fun n => by
    filter_upwards [alphaIicCE_nonneg_le_one X hX_contract hX_meas hX_L2 (-(n : ℝ))] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg hω.1]; exact hω.2
  -- (3) Pointwise a.e. convergence to L = ⨅ n, f n ·.
  have hf_ae : ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop (𝓝 (L ω)) := by
    have h_antitone : ∀ᵐ ω ∂μ, ∀ n m : ℕ, n ≤ m → f m ω ≤ f n ω := by
      rw [ae_all_iff]; intro n; rw [ae_all_iff]; intro m
      by_cases hnm : n ≤ m
      · have h_le : -(m : ℝ) ≤ -(n : ℝ) := by simp [neg_le_neg_iff, Nat.cast_le, hnm]
        filter_upwards [alphaIicCE_mono X hX_contract hX_meas hX_L2
          (-(m : ℝ)) (-(n : ℝ)) h_le] with ω hω
        intro _; exact hω
      · exact ae_of_all μ (fun _ h_contra => absurd h_contra hnm)
    have h_bound_pt : ∀ᵐ ω ∂μ, ∀ n : ℕ, 0 ≤ f n ω ∧ f n ω ≤ 1 := by
      rw [ae_all_iff]; intro n
      exact alphaIicCE_nonneg_le_one X hX_contract hX_meas hX_L2 (-(n : ℝ))
    filter_upwards [h_antitone, h_bound_pt] with ω h_anti h_bd
    refine tendsto_atTop_ciInf h_anti ⟨0, ?_⟩
    rintro _ ⟨k, rfl⟩; exact (h_bd k).1
  -- (4) L¹ convergence to 0 (the indicator absolute value matches |f - 0|).
  have hf_L1 : Tendsto (fun n => ∫ ω, |f n ω - 0| ∂μ) atTop (𝓝 0) := by
    simpa [sub_zero] using
      alphaIicCE_L1_tendsto_zero_atBot X hX_contract hX_meas hX_L2
  -- Apply the shared helper.
  exact ae_tendsto_const_of_ae_convergent_of_L1_const hf_meas hf_bound hf_ae hf_L1


end Exchangeability.DeFinetti.ViaL2
