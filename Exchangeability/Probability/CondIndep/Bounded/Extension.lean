/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Exchangeability.Probability.CondIndep.Indicator
import Exchangeability.Probability.CondIndep.Bounded.Approximation

/-!
# Conditional Independence - Bounded Measurable Extension

This file extends conditional independence from simple functions to bounded measurable
functions using L¹ approximation and convergence arguments.

## Main results

* `condIndep_simpleFunc_left`: Simple function → bounded measurable extension (left)
* `condIndep_bddMeas_extend_left`: Full bounded measurable extension (left)
* `condIndep_boundedMeasurable`: Conditional independence for bounded measurable functions
* `condIndep_of_rect_factorization`: Rectangle factorization implies conditional independence

## References

* Kallenberg (2005), *Probabilistic Symmetries and Invariance Principles*, Section 6.1
-/

open scoped Classical

noncomputable section
open scoped MeasureTheory ENNReal
open MeasureTheory ProbabilityTheory Set Exchangeability.Probability

variable {Ω α β γ : Type*}
variable [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

lemma condIndep_simpleFunc_left
    {Ω α β γ : Type*}
    {m₀ : MeasurableSpace Ω}  -- Explicit ambient space
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure Ω) [IsProbabilityMeasure μ]  -- μ explicit, instances after
    (Y : Ω → α) (Z : Ω → β) (W : Ω → γ)  -- Then plain parameters
    (hCI : @CondIndep Ω α β γ m₀ _ _ _ μ Y Z W)
    (φ : SimpleFunc α ℝ) {ψ : β → ℝ}
    (hY : @Measurable Ω α m₀ _ Y) (hZ : @Measurable Ω β m₀ _ Z) (hW : @Measurable Ω γ m₀ _ W)
    (hψ_meas : Measurable ψ)
    (Mψ : ℝ) (hψ_bdd : ∀ᵐ ω ∂μ, |ψ (Z ω)| ≤ Mψ) :
    μ[ (φ ∘ Y) * (ψ ∘ Z) | MeasurableSpace.comap W inferInstance ] =ᵐ[μ]
    μ[ φ ∘ Y | MeasurableSpace.comap W inferInstance ] *
    μ[ ψ ∘ Z | MeasurableSpace.comap W inferInstance ] := by
  classical
  -- Define mW := σ(W) for cleaner notation
  set mW := MeasurableSpace.comap W (inferInstance : MeasurableSpace γ) with hmW_def
  have hmW_le : mW ≤ m₀ := hW.comap_le

  -- Step 0: Build simple function approximation of ψ via eapprox_real_approx
  -- This provides: |sψ n b| ≤ |ψ b| and sψ n b → ψ b for all n, b
  obtain ⟨sψ, h_sψ_bdd, h_sψ_tendsto⟩ := eapprox_real_approx ψ hψ_meas

  -- Get bound for φ from simple function (finite range)
  -- Simple functions have finite range, so they're bounded
  -- Use the sum of absolute values as a safe upper bound
  have hMφ : ∃ Mφ : ℝ, 0 ≤ Mφ ∧ ∀ a, |φ a| ≤ Mφ := by
    use φ.range.sum (fun x => |x|)
    constructor
    · exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    · intro a
      have h_mem := φ.mem_range_self a
      calc |φ a| ≤ |φ a| + (φ.range.erase (φ a)).sum (fun x => |x|) := by
            exact le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => abs_nonneg _))
        _ = φ.range.sum (fun x => |x|) := by
            rw [← Finset.add_sum_erase _ _ h_mem]
  obtain ⟨Mφ, hMφ_nn, hφ_bdd⟩ := hMφ

  -- Step 1: For each n, apply condIndep_simpleFunc for (φ, sψ n)
  have h_rect_n : ∀ n,
      μ[ (φ ∘ Y) * ((sψ n) ∘ Z) | mW ]
        =ᵐ[μ]
      μ[ (φ ∘ Y) | mW ] * μ[ ((sψ n) ∘ Z) | mW ] := by
    intro n
    -- mW = MeasurableSpace.comap W inferInstance by definition
    have := @condIndep_simpleFunc Ω α β γ m₀ _ _ _ μ _ Y Z W hCI φ (sψ n) hY hZ
    convert this using 2

  -- Step 2: Prove set integrals are equal for all mW-measurable sets
  have hC_sets : ∀ C, MeasurableSet[mW] C →
      ∫ ω in C, ((φ ∘ Y) * (ψ ∘ Z)) ω ∂μ
        = ∫ ω in C, (μ[(φ ∘ Y) | mW] * μ[(ψ ∘ Z) | mW]) ω ∂μ := by
    intro C hC

    -- Integrate h_rect_n over C
    have h_int_n : ∀ n,
      ∫ ω in C, ((φ ∘ Y) * ((sψ n) ∘ Z)) ω ∂μ
        = ∫ ω in C, (μ[(φ ∘ Y) | mW] * μ[((sψ n) ∘ Z) | mW]) ω ∂μ := by
      intro n
      have hφ_int : Integrable (φ ∘ Y) μ := (SimpleFunc.integrable_of_isFiniteMeasure φ).comp_measurable hY
      have hsψn_int : Integrable ((sψ n) ∘ Z) μ := ((sψ n).integrable_of_isFiniteMeasure).comp_measurable hZ
      have hprod_int : Integrable ((φ ∘ Y) * ((sψ n) ∘ Z)) μ := by
        have h_eq : (φ ∘ Y) * ((sψ n) ∘ Z) = ((sψ n) ∘ Z) * (φ ∘ Y) := by
          ext ω; exact mul_comm _ _
        rw [h_eq]
        refine Integrable.bdd_mul' (c := Mψ) hφ_int ((sψ n).measurable.comp hZ).aestronglyMeasurable ?_
        filter_upwards [hψ_bdd] with ω hω
        calc ‖((sψ n) ∘ Z) ω‖
            = |sψ n (Z ω)| := by simp [Real.norm_eq_abs]
          _ ≤ |ψ (Z ω)| := h_sψ_bdd n (Z ω)
          _ ≤ Mψ := hω
      calc ∫ ω in C, ((φ ∘ Y) * ((sψ n) ∘ Z)) ω ∂μ
          = ∫ ω in C, μ[((φ ∘ Y) * ((sψ n) ∘ Z)) | mW] ω ∂μ := by
              exact (setIntegral_condExp hmW_le hprod_int hC).symm
        _ = ∫ ω in C, (μ[(φ ∘ Y) | mW] * μ[((sψ n) ∘ Z) | mW]) ω ∂μ := by
              exact setIntegral_congr_ae (hmW_le _ hC) (by filter_upwards [h_rect_n n] with x hx _; exact hx)

    -- Step 4: LHS convergence via DCT
    have hLHS :
      Filter.Tendsto (fun n => ∫ ω in C, ((φ ∘ Y) * ((sψ n) ∘ Z)) ω ∂μ)
              Filter.atTop
              (nhds (∫ ω in C, ((φ ∘ Y) * (ψ ∘ Z)) ω ∂μ)) := by
      have hψZ_int : Integrable (ψ ∘ Z) μ := by
        refine Integrable.of_mem_Icc (-Mψ) Mψ (hψ_meas.comp hZ).aemeasurable ?_
        filter_upwards [hψ_bdd] with ω hω
        simp only [Function.comp_apply, Set.mem_Icc]
        exact abs_le.mp hω

      refine tendsto_integral_filter_of_dominated_convergence
        (bound := fun ω => Mφ * ‖(ψ ∘ Z) ω‖) ?_ ?_ ?_ ?_

      · refine Filter.Eventually.of_forall (fun n => ?_)
        exact (φ.measurable.comp hY).aestronglyMeasurable.mul ((sψ n).measurable.comp hZ).aestronglyMeasurable

      · refine Filter.Eventually.of_forall (fun n => ?_)
        refine ae_restrict_of_ae ?_
        filter_upwards [hψ_bdd] with ω hω_ψ
        simp only [Function.comp_apply, Pi.mul_apply]
        calc ‖((φ ∘ Y) * ((sψ n) ∘ Z)) ω‖
            = ‖φ (Y ω)‖ * ‖(sψ n) (Z ω)‖ := norm_mul _ _
          _ = |φ (Y ω)| * |(sψ n) (Z ω)| := by rw [Real.norm_eq_abs, Real.norm_eq_abs]
          _ ≤ Mφ * |ψ (Z ω)| := by
              apply mul_le_mul (hφ_bdd (Y ω)) (h_sψ_bdd n (Z ω)) (abs_nonneg _) hMφ_nn
          _ ≤ Mφ * ‖(ψ ∘ Z) ω‖ := by rw [Real.norm_eq_abs]; exact le_refl _

      · exact (hψZ_int.norm.const_mul Mφ).integrableOn

      · refine ae_restrict_of_ae ?_
        filter_upwards [] with ω
        apply Filter.Tendsto.mul tendsto_const_nhds
        exact h_sψ_tendsto (Z ω)

    -- Step 5: RHS convergence via L¹ convergence
    have hRHS :
      Filter.Tendsto (fun n =>
          ∫ ω in C, (μ[(φ ∘ Y) | mW] * μ[((sψ n) ∘ Z) | mW]) ω ∂μ)
        Filter.atTop
        (nhds (∫ ω in C, (μ[(φ ∘ Y) | mW] * μ[(ψ ∘ Z) | mW]) ω ∂μ)) := by
      have hφY_ce_int : Integrable (μ[(φ ∘ Y) | mW]) μ := integrable_condExp

      -- L¹ convergence of conditional expectations
      have h_L1_conv : Filter.Tendsto (fun n => condExpL1 hmW_le μ ((sψ n) ∘ Z)) Filter.atTop
                                (nhds (condExpL1 hmW_le μ (ψ ∘ Z))) := by
        apply tendsto_condExpL1_of_dominated_convergence hmW_le (fun ω => Mψ)
        · intro n
          exact ((sψ n).measurable.comp hZ).aestronglyMeasurable
        · exact integrable_const Mψ
        · intro n
          filter_upwards [hψ_bdd] with ω hω
          calc ‖((sψ n) ∘ Z) ω‖
              = |(sψ n) (Z ω)| := by rw [Real.norm_eq_abs]; rfl
            _ ≤ |ψ (Z ω)| := h_sψ_bdd n (Z ω)
            _ ≤ Mψ := hω
        · filter_upwards [] with ω
          exact h_sψ_tendsto (Z ω)

      -- φY is essentially bounded
      have hφY_bdd : ∀ᵐ ω ∂μ, |μ[(φ ∘ Y) | mW] ω| ≤ Mφ := by
        have h_bdd : ∀ᵐ ω ∂μ, |(φ ∘ Y) ω| ≤ (⟨Mφ, hMφ_nn⟩ : NNReal) := by
          filter_upwards [] with ω
          simpa using hφ_bdd (Y ω)
        simpa [Real.norm_eq_abs] using
          ae_bdd_condExp_of_ae_bdd (m := mW) (R := ⟨Mφ, hMφ_nn⟩) h_bdd

      -- Step 5a: L¹ convergence of sψ n ∘ Z → ψ ∘ Z using helper lemma
      have hMψ_nn : 0 ≤ Mψ := by
        rcases hψ_bdd.exists with ⟨ω, hω⟩
        exact (abs_nonneg _).trans hω
      have hsψZ_int : ∀ n, Integrable ((sψ n) ∘ Z) μ := fun n =>
        ((sψ n).integrable_of_isFiniteMeasure).comp_measurable hZ
      have hψZ_int' : Integrable (ψ ∘ Z) μ := by
        refine Integrable.of_mem_Icc (-Mψ) Mψ (hψ_meas.comp hZ).aemeasurable ?_
        filter_upwards [hψ_bdd] with ω hω; simp only [Function.comp_apply, Set.mem_Icc]; exact abs_le.mp hω
      have h_bound : ∀ n, ∀ᵐ ω ∂μ, |((sψ n) ∘ Z) ω - (ψ ∘ Z) ω| ≤ 2 * Mψ := by
        intro n
        filter_upwards [hψ_bdd] with ω hω
        have h_tri := abs_add_le ((sψ n) (Z ω)) (-(ψ (Z ω)))
        simp only [abs_neg, ← sub_eq_add_neg, Function.comp_apply] at h_tri ⊢
        calc |(sψ n) (Z ω) - ψ (Z ω)|
            ≤ |(sψ n) (Z ω)| + |ψ (Z ω)| := h_tri
          _ ≤ |ψ (Z ω)| + |ψ (Z ω)| := by linarith [h_sψ_bdd n (Z ω)]
          _ ≤ 2 * Mψ := by linarith
      have h_tendsto' : ∀ᵐ ω ∂μ, Filter.Tendsto (fun n => ((sψ n) ∘ Z) ω) Filter.atTop (nhds ((ψ ∘ Z) ω)) :=
        ae_of_all μ (fun ω => h_sψ_tendsto (Z ω))
      have h_conv : Filter.Tendsto (fun n => ∫ ω, |((sψ n) ∘ Z) ω - (ψ ∘ Z) ω| ∂μ)
                      Filter.atTop (nhds 0) :=
        @tendsto_L1_of_pointwise_dominated Ω m₀ μ _ _ _ Mψ hMψ_nn hsψZ_int hψZ_int' h_bound h_tendsto'

      -- Step 5b: Push through conditional expectation
      have h_ce_conv : Filter.Tendsto
          (fun n => ∫ ω, |μ[((sψ n) ∘ Z) | mW] ω - μ[(ψ ∘ Z) | mW] ω| ∂μ)
          Filter.atTop (nhds 0) := by
        have hsψ_int : ∀ n, Integrable ((sψ n) ∘ Z) μ := fun n =>
          ((sψ n).integrable_of_isFiniteMeasure).comp_measurable hZ
        have hψ_int : Integrable (ψ ∘ Z) μ := by
          refine Integrable.of_mem_Icc (-Mψ) Mψ (hψ_meas.comp hZ).aemeasurable ?_
          filter_upwards [hψ_bdd] with ω hω
          simp only [Function.comp_apply, Set.mem_Icc]
          exact abs_le.mp hω
        exact tendsto_condexp_L1 μ mW hmW_le hsψ_int hψ_int h_conv

      -- Step 5c: Product L¹ convergence: φY bounded * (sψZ - ψZ) → 0
      have h_prod_L1 : Filter.Tendsto
          (fun n => ∫ ω, |(μ[(φ ∘ Y) | mW] ω) * (μ[((sψ n) ∘ Z) | mW] ω - μ[(ψ ∘ Z) | mW] ω)| ∂μ)
          Filter.atTop (nhds 0) := by
        let g : ℕ → ℝ := fun n => Mφ * ∫ ω, |μ[((sψ n) ∘ Z) | mW] ω - μ[(ψ ∘ Z) | mW] ω| ∂μ
        have hg_tendsto : Filter.Tendsto g Filter.atTop (nhds 0) := by
          simp only [g]
          have := Filter.Tendsto.const_mul Mφ h_ce_conv
          simp only [mul_zero] at this
          exact this
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hg_tendsto ?_ ?_
        · intro n; exact integral_nonneg (fun _ => abs_nonneg _)
        · intro n
          simp only [g]
          have h_bd : ∀ᵐ ω ∂μ,
              |(μ[(φ ∘ Y) | mW] ω) * (μ[((sψ n) ∘ Z) | mW] ω - μ[(ψ ∘ Z) | mW] ω)|
                ≤ Mφ * |μ[((sψ n) ∘ Z) | mW] ω - μ[(ψ ∘ Z) | mW] ω| := by
            filter_upwards [hφY_bdd] with ω hω
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_right hω (abs_nonneg _)
          have h_lhs_int : Integrable (fun ω =>
              |(μ[(φ ∘ Y) | mW] ω) * (μ[((sψ n) ∘ Z) | mW] ω - μ[(ψ ∘ Z) | mW] ω)|) μ := by
            have h_bdd_asm := (integrable_condExp (μ := μ) (m := mW) (f := φ ∘ Y)).aestronglyMeasurable
            have h_bdd_bound : ∀ᵐ ω ∂μ, ‖μ[(φ ∘ Y) | mW] ω‖ ≤ Mφ := by
              filter_upwards [hφY_bdd] with ω hω
              rw [Real.norm_eq_abs]
              exact hω
            have h_diff_int' : Integrable (μ[((sψ n) ∘ Z) | mW] - μ[(ψ ∘ Z) | mW]) μ :=
              integrable_condExp.sub integrable_condExp
            have h_prod : Integrable (fun ω => μ[(φ ∘ Y) | mW] ω * (μ[((sψ n) ∘ Z) | mW] ω - μ[(ψ ∘ Z) | mW] ω)) μ :=
              h_diff_int'.bdd_mul' h_bdd_asm h_bdd_bound
            exact h_prod.abs
          have h_rhs_int : Integrable (fun ω =>
              Mφ * |μ[((sψ n) ∘ Z) | mW] ω - μ[(ψ ∘ Z) | mW] ω|) μ := by
            exact (integrable_condExp.sub integrable_condExp).abs.const_mul Mφ
          calc ∫ ω, |(μ[(φ ∘ Y) | mW] ω) * (μ[((sψ n) ∘ Z) | mW] ω - μ[(ψ ∘ Z) | mW] ω)| ∂μ
              ≤ ∫ ω, Mφ * |μ[((sψ n) ∘ Z) | mW] ω - μ[(ψ ∘ Z) | mW] ω| ∂μ := by
                exact integral_mono_ae h_lhs_int h_rhs_int h_bd
            _ = Mφ * ∫ ω, |μ[((sψ n) ∘ Z) | mW] ω - μ[(ψ ∘ Z) | mW] ω| ∂μ := by
                rw [integral_const_mul]

      -- Step 5d: Set integral convergence from global L¹ convergence
      have h_rewrite : ∀ n ω,
          (μ[(φ ∘ Y) | mW] * μ[((sψ n) ∘ Z) | mW]) ω - (μ[(φ ∘ Y) | mW] * μ[(ψ ∘ Z) | mW]) ω
          = (μ[(φ ∘ Y) | mW] ω) * (μ[((sψ n) ∘ Z) | mW] ω - μ[(ψ ∘ Z) | mW] ω) := by
        intro n ω
        simp only [Pi.mul_apply]
        ring

      have h_int_prod : ∀ n, Integrable (μ[(φ ∘ Y) | mW] * μ[((sψ n) ∘ Z) | mW]) μ := by
        intro n
        -- bdd_mul' (c := Mφ) hg hf hf_bound gives Integrable (hf * hg)
        -- We want Integrable (μ[φY|mW] * μ[sψnZ|mW])
        -- So hf = μ[φY|mW] (bounded), hg = μ[sψnZ|mW] (integrable)
        refine Integrable.bdd_mul' (c := Mφ)
          (integrable_condExp (m := mW) (f := (sψ n) ∘ Z))
          (integrable_condExp (m := mW) (f := φ ∘ Y)).aestronglyMeasurable ?_
        filter_upwards [hφY_bdd] with ω hω
        rw [Real.norm_eq_abs]
        exact hω

      have h_int_prod_lim : Integrable (μ[(φ ∘ Y) | mW] * μ[(ψ ∘ Z) | mW]) μ := by
        refine Integrable.bdd_mul' (c := Mφ)
          (integrable_condExp (m := mW) (f := ψ ∘ Z))
          (integrable_condExp (m := mW) (f := φ ∘ Y)).aestronglyMeasurable ?_
        filter_upwards [hφY_bdd] with ω hω
        rw [Real.norm_eq_abs]
        exact hω

      have h_diff_L1_bochner : Filter.Tendsto
          (fun n => ∫ ω, |(μ[(φ ∘ Y) | mW] * μ[((sψ n) ∘ Z) | mW]) ω -
                         (μ[(φ ∘ Y) | mW] * μ[(ψ ∘ Z) | mW]) ω| ∂μ)
          Filter.atTop (nhds 0) := by
        convert h_prod_L1 using 1
        ext n
        congr 1
        ext ω
        exact congrArg abs (h_rewrite n ω)

      -- Direct proof of set integral convergence using L¹ convergence
      -- Key: |∫_C (fn - f)| ≤ ∫_Ω |fn - f| → 0
      rw [Metric.tendsto_atTop] at h_diff_L1_bochner ⊢
      intro ε hε
      obtain ⟨N, hN⟩ := h_diff_L1_bochner ε hε
      use N
      intro n hn
      have hN' := hN n hn
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg (fun _ => abs_nonneg _))] at hN'
      rw [Real.dist_eq]
      have hfn_int : Integrable (fun ω => (μ[(φ ∘ Y) | mW] * μ[((sψ n) ∘ Z) | mW]) ω)
          (μ.restrict C) := (h_int_prod n).restrict
      have hf_int : Integrable (fun ω => (μ[(φ ∘ Y) | mW] * μ[(ψ ∘ Z) | mW]) ω)
          (μ.restrict C) := h_int_prod_lim.restrict
      calc |∫ ω in C, (μ[(φ ∘ Y) | mW] * μ[((sψ n) ∘ Z) | mW]) ω ∂μ -
            ∫ ω in C, (μ[(φ ∘ Y) | mW] * μ[(ψ ∘ Z) | mW]) ω ∂μ|
          = |∫ ω in C, ((μ[(φ ∘ Y) | mW] * μ[((sψ n) ∘ Z) | mW]) ω -
                        (μ[(φ ∘ Y) | mW] * μ[(ψ ∘ Z) | mW]) ω) ∂μ| := by
            rw [← integral_sub hfn_int hf_int]
        _ ≤ ∫ ω in C, |(μ[(φ ∘ Y) | mW] * μ[((sψ n) ∘ Z) | mW]) ω -
                       (μ[(φ ∘ Y) | mW] * μ[(ψ ∘ Z) | mW]) ω| ∂μ :=
            abs_integral_le_integral_abs
        _ ≤ ∫ ω, |(μ[(φ ∘ Y) | mW] * μ[((sψ n) ∘ Z) | mW]) ω -
                  (μ[(φ ∘ Y) | mW] * μ[(ψ ∘ Z) | mW]) ω| ∂μ := by
            apply setIntegral_le_integral ((h_int_prod n).sub h_int_prod_lim).abs
            filter_upwards with ω; exact abs_nonneg _
        _ < ε := hN'

    -- Step 6: LHS = RHS by uniqueness of limits
    have h_eq_seq : ∀ n,
        ∫ ω in C, ((φ ∘ Y) * ((sψ n) ∘ Z)) ω ∂μ
          = ∫ ω in C, (μ[(φ ∘ Y) | mW] * μ[((sψ n) ∘ Z) | mW]) ω ∂μ :=
      h_int_n

    have h_lhs_lim := hLHS
    have h_rhs_lim := hRHS

    have h_seq_eq : ∀ n,
        ∫ ω in C, ((φ ∘ Y) * ((sψ n) ∘ Z)) ω ∂μ
          = ∫ ω in C, (μ[(φ ∘ Y) | mW] * μ[((sψ n) ∘ Z) | mW]) ω ∂μ := h_eq_seq

    -- Since both sequences converge and are equal term by term, their limits are equal
    have h_rhs_lim' : Filter.Tendsto (fun n => ∫ ω in C, ((φ ∘ Y) * ((sψ n) ∘ Z)) ω ∂μ)
                        Filter.atTop
                        (nhds (∫ ω in C, (μ[(φ ∘ Y) | mW] * μ[(ψ ∘ Z) | mW]) ω ∂μ)) := by
      convert h_rhs_lim using 1
      ext n
      exact h_seq_eq n
    exact tendsto_nhds_unique h_lhs_lim h_rhs_lim'

  -- Step 7: Use uniqueness of conditional expectation to conclude
  -- hC_sets proves: ∀ C mW-measurable, ∫_C (φY*ψZ) = ∫_C (μ[φY|mW] * μ[ψZ|mW])
  -- Apply ae_eq_condExp_of_forall_setIntegral_eq

  -- Integrability of product
  have hf_int : Integrable ((φ ∘ Y) * (ψ ∘ Z)) μ := by
    have hφ_int : Integrable (φ ∘ Y) μ := (SimpleFunc.integrable_of_isFiniteMeasure φ).comp_measurable hY
    have hψ_int : Integrable (ψ ∘ Z) μ := by
      refine Integrable.of_mem_Icc (-Mψ) Mψ (hψ_meas.comp hZ).aemeasurable ?_
      filter_upwards [hψ_bdd] with ω hω
      simp only [Function.comp_apply, Set.mem_Icc]
      exact abs_le.mp hω
    -- bdd_mul' (c := Mψ) hg hf bound gives Integrable (hf * hg)
    -- We want Integrable ((φ ∘ Y) * (ψ ∘ Z))
    -- So hf = φ ∘ Y, hg = ψ ∘ Z, but φ is simple (integrable), ψ is bounded
    -- Actually: ψ is bounded, φ is integrable, so use φ as hg, ψ as hf
    have h_prod : Integrable ((ψ ∘ Z) * (φ ∘ Y)) μ := by
      refine Integrable.bdd_mul' (c := Mψ) hφ_int (hψ_meas.comp hZ).aestronglyMeasurable ?_
      filter_upwards [hψ_bdd] with ω hω
      rw [Real.norm_eq_abs]
      exact hω
    convert h_prod using 1
    ext ω; exact mul_comm ((φ ∘ Y) ω) ((ψ ∘ Z) ω)

  refine (ae_eq_condExp_of_forall_setIntegral_eq hmW_le hf_int ?_ ?_ ?_).symm

  -- Hypothesis 1: IntegrableOn for g on finite mW-measurable sets
  · intro s hs hμs
    haveI : Fact (μ s < ∞) := ⟨hμs⟩
    have h1 : Integrable (μ[(φ ∘ Y) | mW]) μ := integrable_condExp
    have h2 : Integrable (μ[(ψ ∘ Z) | mW]) μ := integrable_condExp
    have hψZ_ce_bdd : ∀ᵐ ω ∂μ, |μ[(ψ ∘ Z) | mW] ω| ≤ Mψ := by
      have hMψ_nn : 0 ≤ Mψ := by
        rcases hψ_bdd.exists with ⟨ω, hω⟩
        exact (abs_nonneg _).trans hω
      have h_bdd : ∀ᵐ ω ∂μ, |(ψ ∘ Z) ω| ≤ (⟨Mψ, hMψ_nn⟩ : NNReal) := by
        filter_upwards [hψ_bdd] with ω hω
        simpa using hω
      simpa [Real.norm_eq_abs] using
        ae_bdd_condExp_of_ae_bdd (m := mW) (R := ⟨Mψ, hMψ_nn⟩) h_bdd
    have hprod : Integrable (μ[(φ ∘ Y) | mW] * μ[(ψ ∘ Z) | mW]) μ := by
      -- bdd_mul' (c := Mψ) hg hf_asm hf_bound gives Integrable (hf * hg)
      -- We want Integrable (μ[φY|mW] * μ[ψZ|mW])
      -- So hf = μ[φY|mW], hg = μ[ψZ|mW], but ψZ is bounded so use it as hf
      have h_prod : Integrable (μ[(ψ ∘ Z) | mW] * μ[(φ ∘ Y) | mW]) μ := by
        refine h1.bdd_mul' (c := Mψ) h2.aestronglyMeasurable ?_
        filter_upwards [hψZ_ce_bdd] with ω hω
        rw [Real.norm_eq_abs]
        exact hω
      convert h_prod using 1
      ext ω; exact mul_comm (μ[(φ ∘ Y) | mW] ω) (μ[(ψ ∘ Z) | mW] ω)
    exact hprod.integrableOn

  -- Hypothesis 2: Set integral equality (from hC_sets)
  · intro s hs hμs
    exact (hC_sets s hs).symm

  -- Hypothesis 3: AEStronglyMeasurable of g = μ[φ ∘ Y|mW] * μ[ψ ∘ Z|mW]
  · exact (stronglyMeasurable_condExp.mul stronglyMeasurable_condExp).aestronglyMeasurable

/-- **Extend factorization from simple φ to bounded measurable φ, keeping ψ fixed.**
Refactored to avoid instance pollution: works with σ(W) directly. -/
lemma condIndep_bddMeas_extend_left
    {Ω α β γ : Type*}
    {m₀ : MeasurableSpace Ω}  -- Explicit ambient space
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure Ω) [IsProbabilityMeasure μ]  -- μ explicit, instances after
    (Y : Ω → α) (Z : Ω → β) (W : Ω → γ)  -- Then plain parameters
    (hCI : @CondIndep Ω α β γ m₀ _ _ _ μ Y Z W)
    (hY : @Measurable Ω α m₀ _ Y) (hZ : @Measurable Ω β m₀ _ Z) (hW : @Measurable Ω γ m₀ _ W)
    {φ : α → ℝ} {ψ : β → ℝ}
    (hφ_meas : Measurable φ) (hψ_meas : Measurable ψ)
    (Mφ Mψ : ℝ)
    (hφ_bdd : ∀ᵐ ω ∂μ, |φ (Y ω)| ≤ Mφ)
    (hψ_bdd : ∀ᵐ ω ∂μ, |ψ (Z ω)| ≤ Mψ) :
    μ[ (φ ∘ Y) * (ψ ∘ Z) | MeasurableSpace.comap W inferInstance ] =ᵐ[μ]
    μ[ (φ ∘ Y) | MeasurableSpace.comap W inferInstance ] *
    μ[ (ψ ∘ Z) | MeasurableSpace.comap W inferInstance ] := by
  classical
  -- Define mW := σ(W) for cleaner notation
  set mW := MeasurableSpace.comap W (inferInstance : MeasurableSpace γ) with hmW_def
  have hmW_le : mW ≤ m₀ := hW.comap_le
  -- Step 0: Build simple function approximation of φ via eapprox_real_approx
  -- This provides: |sφ n a| ≤ |φ a| and sφ n a → φ a for all n, a
  obtain ⟨sφ, h_sφ_bdd, h_sφ_tendsto⟩ := eapprox_real_approx φ hφ_meas

  -- Step 1: reduce to equality of set integrals on σ(W)-sets C.

  have hC_sets :
    ∀ C, MeasurableSet[mW] C →
      ∫ ω in C, ((φ ∘ Y) * (ψ ∘ Z)) ω ∂μ
        = ∫ ω in C, (μ[(φ ∘ Y) | mW] * μ[(ψ ∘ Z) | mW]) ω ∂μ := by
    intro C hC

    -- For each n, simple φ-approximation: apply condIndep_simpleFunc
    have h_rect_n :
      ∀ n,
        μ[ ((sφ n) ∘ Y) * (ψ ∘ Z) | mW ]
          =ᵐ[μ]
        μ[ ((sφ n) ∘ Y) | mW ] * μ[ (ψ ∘ Z) | mW ] := by
      intro n
      -- Use the refactored lemma (now works directly with σ(W))
      -- mW is definitionally equal to MeasurableSpace.comap W inferInstance
      exact condIndep_simpleFunc_left μ Y Z W hCI (sφ n) hY hZ hW hψ_meas Mψ hψ_bdd

    -- Integrate both sides over C
    have h_int_n :
      ∀ n,
        ∫ ω in C, ((sφ n ∘ Y) * (ψ ∘ Z)) ω ∂μ
          = ∫ ω in C, (μ[(sφ n ∘ Y) | mW] * μ[(ψ ∘ Z) | mW]) ω ∂μ := by
      intro n
      -- First, need integrability
      have hsφn_int : Integrable ((sφ n) ∘ Y) μ := by
        refine Integrable.comp_measurable ?_ hY
        exact SimpleFunc.integrable_of_isFiniteMeasure (sφ n)
      have hψ_int : Integrable (ψ ∘ Z) μ := by
        refine Integrable.of_mem_Icc (-Mψ) Mψ (hψ_meas.comp hZ).aemeasurable ?_
        filter_upwards [hψ_bdd] with ω hω
        simp only [Function.comp_apply, Set.mem_Icc]
        exact abs_le.mp hω
      have hprod_int : Integrable (((sφ n) ∘ Y) * (ψ ∘ Z)) μ := by
        -- sφ n is bounded (simple function), ψ ∘ Z is integrable
        refine Integrable.bdd_mul' (c := Mφ) hψ_int ((sφ n).measurable.comp hY).aestronglyMeasurable ?_
        -- Need bound on sφ n ∘ Y: use that |sφ n| ≤ |φ| from h_sφ_bdd
        filter_upwards [hφ_bdd] with ω hω
        calc ‖((sφ n) ∘ Y) ω‖
            = |sφ n (Y ω)| := by simp [Real.norm_eq_abs]
          _ ≤ |φ (Y ω)| := h_sφ_bdd n (Y ω)
          _ ≤ Mφ := hω
      -- Use setIntegral_condExp followed by setIntegral_congr_ae
      calc ∫ ω in C, ((sφ n ∘ Y) * (ψ ∘ Z)) ω ∂μ
          = ∫ ω in C, μ[((sφ n ∘ Y) * (ψ ∘ Z)) | mW] ω ∂μ := by
              exact (setIntegral_condExp hmW_le hprod_int hC).symm
        _ = ∫ ω in C, (μ[(sφ n ∘ Y) | mW] * μ[(ψ ∘ Z) | mW]) ω ∂μ := by
              exact setIntegral_congr_ae (hmW_le _ hC) (by filter_upwards [h_rect_n n] with x hx _; exact hx)

    -- Limit passage n→∞ on both sides.
    -- LHS: DCT
    have hLHS :
      Filter.Tendsto (fun n => ∫ ω in C, ((sφ n ∘ Y) * (ψ ∘ Z)) ω ∂μ)
              Filter.atTop
              (nhds (∫ ω in C, ((φ ∘ Y) * (ψ ∘ Z)) ω ∂μ)) := by
      -- Apply DCT with bound Mφ * |ψ ∘ Z|
      have hψZ_int : Integrable (ψ ∘ Z) μ := by
        refine Integrable.of_mem_Icc (-Mψ) Mψ (hψ_meas.comp hZ).aemeasurable ?_
        filter_upwards [hψ_bdd] with ω hω
        simp only [Function.comp_apply, Set.mem_Icc]
        exact abs_le.mp hω

      -- Apply dominated convergence theorem with bound Mφ * ‖ψ ∘ Z‖
      refine tendsto_integral_filter_of_dominated_convergence
        (bound := fun ω => Mφ * ‖(ψ ∘ Z) ω‖) ?_ ?_ ?_ ?_

      -- Hypothesis 1: AEStronglyMeasurable for each n w.r.t. μ.restrict C
      · refine Filter.Eventually.of_forall (fun n => ?_)
        exact ((sφ n).measurable.comp hY).aestronglyMeasurable.mul (hψ_meas.comp hZ).aestronglyMeasurable

      -- Hypothesis 2: Dominated by bound a.e. w.r.t. μ.restrict C
      · refine Filter.Eventually.of_forall (fun n => ?_)
        refine ae_restrict_of_ae ?_
        filter_upwards [hφ_bdd] with ω hω_φ
        simp only [Function.comp_apply, Pi.mul_apply]
        calc ‖((sφ n ∘ Y) * (ψ ∘ Z)) ω‖
            = ‖(sφ n) (Y ω)‖ * ‖(ψ ∘ Z) ω‖ := norm_mul _ _
          _ = |(sφ n) (Y ω)| * ‖(ψ ∘ Z) ω‖ := by rw [Real.norm_eq_abs]
          _ ≤ |φ (Y ω)| * ‖(ψ ∘ Z) ω‖ := by apply mul_le_mul_of_nonneg_right (h_sφ_bdd n (Y ω)) (norm_nonneg _)
          _ ≤ Mφ * ‖(ψ ∘ Z) ω‖ := by apply mul_le_mul_of_nonneg_right hω_φ (norm_nonneg _)

      -- Hypothesis 3: Bound Mφ * ‖ψ ∘ Z‖ is integrable on C
      · exact (hψZ_int.norm.const_mul Mφ).integrableOn

      -- Hypothesis 4: Pointwise convergence a.e.
      · refine ae_restrict_of_ae ?_
        filter_upwards [] with ω
        apply Filter.Tendsto.mul
        · exact h_sφ_tendsto (Y ω)
        · exact tendsto_const_nhds

    -- RHS: convergence by dominated convergence theorem
    -- The conditional expectations μ[(sφ n ∘ Y) | mW] are uniformly bounded by Mφ,
    -- and μ[(ψ ∘ Z) | mW] is integrable, so DCT applies.
    have hRHS :
      Filter.Tendsto (fun n =>
          ∫ ω in C, (μ[(sφ n ∘ Y) | mW] * μ[(ψ ∘ Z) | mW]) ω ∂μ)
        Filter.atTop
        (nhds (∫ ω in C, (μ[(φ ∘ Y) | mW] * μ[(ψ ∘ Z) | mW]) ω ∂μ)) := by
      -- Integrability of μ[(ψ ∘ Z) | mW]
      have hψZ_ce_int : Integrable (μ[(ψ ∘ Z) | mW]) μ := integrable_condExp

      -- Key insight: h_int_n shows these two sequences are equal for all n.
      -- Since hLHS shows the LHS converges, the RHS must also converge (they're the same sequence!)
      -- We use L¹ convergence directly, without needing pointwise convergence.

      -- Step 1: Show L¹ convergence of conditional expectations
      have h_L1_conv : Filter.Tendsto (fun n => condExpL1 hmW_le μ ((sφ n) ∘ Y)) Filter.atTop
                                (nhds (condExpL1 hmW_le μ (φ ∘ Y))) := by
        apply tendsto_condExpL1_of_dominated_convergence hmW_le (fun ω => Mφ)
        · intro n
          exact ((sφ n).measurable.comp hY).aestronglyMeasurable
        · exact integrable_const Mφ
        · intro n
          filter_upwards [hφ_bdd] with ω hω
          calc ‖((sφ n) ∘ Y) ω‖
              = |(sφ n) (Y ω)| := by rw [Real.norm_eq_abs]; rfl
            _ ≤ |φ (Y ω)| := h_sφ_bdd n (Y ω)
            _ ≤ Mφ := hω
        · filter_upwards [] with ω
          exact h_sφ_tendsto (Y ω)

      -- Step 2: Show ψZ term is essentially bounded
      have hMψ_nn : 0 ≤ Mψ := by
        rcases hψ_bdd.exists with ⟨ω, hω⟩
        exact (abs_nonneg _).trans hω
      have hψZ_bdd : ∀ᵐ ω ∂μ, |μ[(ψ ∘ Z) | mW] ω| ≤ Mψ := by
        have h_bdd : ∀ᵐ ω ∂μ, |(ψ ∘ Z) ω| ≤ (⟨Mψ, hMψ_nn⟩ : NNReal) := by
          filter_upwards [hψ_bdd] with ω hω
          simpa using hω
        simpa [Real.norm_eq_abs] using
          ae_bdd_condExp_of_ae_bdd (m := mW) (R := ⟨Mψ, hMψ_nn⟩) h_bdd

      -- Step 2a: Show L¹ convergence of original functions: sφ n ∘ Y → φ ∘ Y
      have hsφ_int : ∀ n, Integrable ((sφ n) ∘ Y) μ := by
        intro n
        refine Integrable.comp_measurable ?_ hY
        exact SimpleFunc.integrable_of_isFiniteMeasure (sφ n)

      have hMφ_nn : 0 ≤ Mφ := by
        rcases hφ_bdd.exists with ⟨ω, hω⟩
        exact (abs_nonneg _).trans hω

      -- L¹ convergence of sφ n ∘ Y → φ ∘ Y using helper lemma
      have hφY_int : Integrable (φ ∘ Y) μ := by
        refine Integrable.of_mem_Icc (-Mφ) Mφ (hφ_meas.comp hY).aemeasurable ?_
        filter_upwards [hφ_bdd] with ω hω; simp only [Function.comp_apply, Set.mem_Icc]; exact abs_le.mp hω
      have h_bound_φ : ∀ n, ∀ᵐ ω ∂μ, |((sφ n) ∘ Y) ω - (φ ∘ Y) ω| ≤ 2 * Mφ := by
        intro n
        filter_upwards [hφ_bdd] with ω hω
        have h_tri := abs_add_le ((sφ n) (Y ω)) (-(φ (Y ω)))
        simp only [abs_neg, ← sub_eq_add_neg, Function.comp_apply] at h_tri ⊢
        calc |(sφ n) (Y ω) - φ (Y ω)|
            ≤ |(sφ n) (Y ω)| + |φ (Y ω)| := h_tri
          _ ≤ |φ (Y ω)| + |φ (Y ω)| := by linarith [h_sφ_bdd n (Y ω)]
          _ ≤ 2 * Mφ := by linarith
      have h_tendsto_φ : ∀ᵐ ω ∂μ, Filter.Tendsto (fun n => ((sφ n) ∘ Y) ω) Filter.atTop (nhds ((φ ∘ Y) ω)) :=
        ae_of_all μ (fun ω => h_sφ_tendsto (Y ω))
      have h_sφ_L1 : Filter.Tendsto (fun n => ∫ ω, |((sφ n) ∘ Y) ω - (φ ∘ Y) ω| ∂μ)
          Filter.atTop (nhds 0) :=
        @tendsto_L1_of_pointwise_dominated Ω m₀ μ _ _ _ Mφ hMφ_nn hsφ_int hφY_int h_bound_φ h_tendsto_φ

      -- Step 2b: Apply tendsto_condexp_L1 to get CE convergence in L¹
      have h_ce_L1 : Filter.Tendsto
          (fun n => ∫ ω, |μ[((sφ n) ∘ Y) | mW] ω - μ[(φ ∘ Y) | mW] ω| ∂μ)
          Filter.atTop (nhds 0) :=
        tendsto_condexp_L1 μ mW hmW_le hsφ_int hφY_int h_sφ_L1

      -- Step 2c: Product L¹ convergence via bounded factor
      -- |(CE[sφn] - CE[φ]) * CE[ψ]| ≤ |CE[sφn] - CE[φ]| * Mψ
      have h_prod_L1 : Filter.Tendsto
          (fun n => ∫ ω, |(μ[((sφ n) ∘ Y) | mW] ω - μ[(φ ∘ Y) | mW] ω) *
                         μ[(ψ ∘ Z) | mW] ω| ∂μ)
          Filter.atTop (nhds 0) := by
        -- Upper bound function: Mψ * ∫|CE[sφn] - CE[φ]|
        let g : ℕ → ℝ := fun n => Mψ * ∫ ω, |μ[((sφ n) ∘ Y) | mW] ω - μ[(φ ∘ Y) | mW] ω| ∂μ
        have h_g_tends : Filter.Tendsto g Filter.atTop (nhds 0) := by
          have := Filter.Tendsto.const_mul Mψ h_ce_L1
          simp only [mul_zero] at this
          exact this
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h_g_tends ?_ ?_
        · -- Lower bound is 0
          intro n
          exact integral_nonneg (fun _ => abs_nonneg _)
        · -- Pointwise upper bound via integral_mono_ae
          intro n
          have h_bd : ∀ᵐ ω ∂μ,
              |(μ[((sφ n) ∘ Y) | mW] ω - μ[(φ ∘ Y) | mW] ω) * μ[(ψ ∘ Z) | mW] ω|
              ≤ Mψ * |μ[((sφ n) ∘ Y) | mW] ω - μ[(φ ∘ Y) | mW] ω| := by
            filter_upwards [hψZ_bdd] with ω hω
            rw [abs_mul]
            calc |μ[((sφ n) ∘ Y) | mW] ω - μ[(φ ∘ Y) | mW] ω| * |μ[(ψ ∘ Z) | mW] ω|
                ≤ |μ[((sφ n) ∘ Y) | mW] ω - μ[(φ ∘ Y) | mW] ω| * Mψ := by
                  exact mul_le_mul_of_nonneg_left hω (abs_nonneg _)
              _ = Mψ * |μ[((sφ n) ∘ Y) | mW] ω - μ[(φ ∘ Y) | mW] ω| := by ring
          -- Integrate the a.e. inequality
          have h_lhs_int : Integrable (fun ω =>
              |(μ[((sφ n) ∘ Y) | mW] ω - μ[(φ ∘ Y) | mW] ω) * μ[(ψ ∘ Z) | mW] ω|) μ := by
            -- Product of difference (integrable) and bounded factor (CE[ψ])
            -- Use Integrable.bdd_mul': (bounded * integrable), then swap order
            have h_diff_int' : Integrable (μ[((sφ n) ∘ Y) | mW] - μ[(φ ∘ Y) | mW]) μ :=
              integrable_condExp.sub integrable_condExp
            have h_bdd_asm := (integrable_condExp (μ := μ) (m := mW) (f := ψ ∘ Z)).aestronglyMeasurable
            have h_bdd_bound : ∀ᵐ ω ∂μ, ‖μ[(ψ ∘ Z) | mW] ω‖ ≤ Mψ := by
              filter_upwards [hψZ_bdd] with ω hω
              rw [Real.norm_eq_abs]
              exact hω
            have h_prod : Integrable (fun ω => μ[(ψ ∘ Z) | mW] ω * (μ[((sφ n) ∘ Y) | mW] ω - μ[(φ ∘ Y) | mW] ω)) μ :=
              h_diff_int'.bdd_mul' h_bdd_asm h_bdd_bound
            -- Swap order using mul_comm, then take abs
            convert h_prod.abs using 1
            ext ω
            rw [abs_mul, abs_mul, mul_comm]
          have h_rhs_int : Integrable (fun ω =>
              Mψ * |μ[((sφ n) ∘ Y) | mW] ω - μ[(φ ∘ Y) | mW] ω|) μ := by
            exact (integrable_condExp.sub integrable_condExp).abs.const_mul Mψ
          calc ∫ ω, |(μ[((sφ n) ∘ Y) | mW] ω - μ[(φ ∘ Y) | mW] ω) * μ[(ψ ∘ Z) | mW] ω| ∂μ
              ≤ ∫ ω, Mψ * |μ[((sφ n) ∘ Y) | mW] ω - μ[(φ ∘ Y) | mW] ω| ∂μ := by
                exact integral_mono_ae h_lhs_int h_rhs_int h_bd
            _ = Mψ * ∫ ω, |μ[((sφ n) ∘ Y) | mW] ω - μ[(φ ∘ Y) | mW] ω| ∂μ := by
                rw [integral_const_mul]

      -- Step 2d: Set integral convergence from global L¹ convergence
      -- Rewrite as difference of products
      have h_rewrite : ∀ n ω,
          (μ[((sφ n) ∘ Y) | mW] * μ[(ψ ∘ Z) | mW]) ω - (μ[(φ ∘ Y) | mW] * μ[(ψ ∘ Z) | mW]) ω
          = (μ[((sφ n) ∘ Y) | mW] ω - μ[(φ ∘ Y) | mW] ω) * μ[(ψ ∘ Z) | mW] ω := by
        intro n ω
        simp only [Pi.mul_apply]
        ring

      -- The set integral of a function converges if the global L¹ norm tends to 0
      have h_diff_L1 : Filter.Tendsto
          (fun n => ∫ ω, |(μ[((sφ n) ∘ Y) | mW] * μ[(ψ ∘ Z) | mW]) ω -
                         (μ[(φ ∘ Y) | mW] * μ[(ψ ∘ Z) | mW]) ω| ∂μ)
          Filter.atTop (nhds 0) := by
        convert h_prod_L1 using 1
        ext n
        congr 1
        ext ω
        exact congrArg abs (h_rewrite n ω)

      -- Set integral converges by bounding: |∫_C f| ≤ ∫_C |f| ≤ ∫ |f|
      have h_int_prod : ∀ n, Integrable (μ[((sφ n) ∘ Y) | mW] * μ[(ψ ∘ Z) | mW]) μ := by
        intro n
        -- Use bdd_mul': f * g with f bounded and g integrable
        -- Here f = μ[(ψ ∘ Z)|mW] is bounded by Mψ, g = μ[(sφn ∘ Y)|mW] is integrable
        have h_prod : Integrable (μ[(ψ ∘ Z) | mW] * μ[((sφ n) ∘ Y) | mW]) μ := by
          refine Integrable.bdd_mul' (c := Mψ)
            (integrable_condExp (m := mW) (f := (sφ n) ∘ Y))
            (integrable_condExp (m := mW) (f := ψ ∘ Z)).aestronglyMeasurable ?_
          filter_upwards [hψZ_bdd] with ω hω
          rw [Real.norm_eq_abs]
          exact hω
        -- Swap the order
        simpa only [mul_comm] using h_prod
      have h_int_limit : Integrable (μ[(φ ∘ Y) | mW] * μ[(ψ ∘ Z) | mW]) μ := by
        have h_prod : Integrable (μ[(ψ ∘ Z) | mW] * μ[(φ ∘ Y) | mW]) μ := by
          refine Integrable.bdd_mul' (c := Mψ)
            (integrable_condExp (m := mW) (f := φ ∘ Y))
            (integrable_condExp (m := mW) (f := ψ ∘ Z)).aestronglyMeasurable ?_
          filter_upwards [hψZ_bdd] with ω hω
          rw [Real.norm_eq_abs]
          exact hω
        simpa only [mul_comm] using h_prod

      -- Use that |∫_C (fn - f)| ≤ ∫|fn - f| → 0
      refine Metric.tendsto_atTop.mpr (fun ε hε => ?_)
      obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp h_diff_L1 ε hε
      use N
      intro n hn
      rw [Real.dist_eq]
      calc |∫ ω in C, (μ[((sφ n) ∘ Y) | mW] * μ[(ψ ∘ Z) | mW]) ω ∂μ -
            ∫ ω in C, (μ[(φ ∘ Y) | mW] * μ[(ψ ∘ Z) | mW]) ω ∂μ|
          = |∫ ω in C, ((μ[((sφ n) ∘ Y) | mW] * μ[(ψ ∘ Z) | mW]) ω -
                        (μ[(φ ∘ Y) | mW] * μ[(ψ ∘ Z) | mW]) ω) ∂μ| := by
            rw [← integral_sub (h_int_prod n).integrableOn h_int_limit.integrableOn]
        _ ≤ ∫ ω in C, |(μ[((sφ n) ∘ Y) | mW] * μ[(ψ ∘ Z) | mW]) ω -
                       (μ[(φ ∘ Y) | mW] * μ[(ψ ∘ Z) | mW]) ω| ∂μ := abs_integral_le_integral_abs
        _ ≤ ∫ ω, |(μ[((sφ n) ∘ Y) | mW] * μ[(ψ ∘ Z) | mW]) ω -
                  (μ[(φ ∘ Y) | mW] * μ[(ψ ∘ Z) | mW]) ω| ∂μ := by
            refine setIntegral_le_integral ?_ ?_
            · exact ((h_int_prod n).sub h_int_limit).abs
            · filter_upwards with ω
              exact abs_nonneg _
        _ < ε := by
            have := hN n hn
            rw [Real.dist_eq] at this
            simp only [sub_zero] at this
            rwa [abs_of_nonneg (integral_nonneg (fun _ => abs_nonneg _))] at this

    -- h_eq shows LHS and RHS sequences are equal; uniqueness gives equal limits
    have h_eq : (fun n => ∫ ω in C, ((sφ n ∘ Y) * (ψ ∘ Z)) ω ∂μ) =
                (fun n => ∫ ω in C, (μ[(sφ n ∘ Y) | mW] * μ[(ψ ∘ Z) | mW]) ω ∂μ) := by
      ext n; exact h_int_n n
    rw [← h_eq] at hRHS
    exact tendsto_nhds_unique hLHS hRHS

  -- Step 2: uniqueness of versions from set-integral equality on σ(W)-sets.
  -- Now we have: ∀ C ∈ σ(W), ∫_C (φY * ψZ) = ∫_C (μ[φY|W] * μ[ψZ|W])
  -- By uniqueness, this implies μ[φY * ψZ|W] =ᵐ μ[φY|W] * μ[ψZ|W]

  -- Use ae_eq_condExp_of_forall_setIntegral_eq: if g is mW-measurable and
  -- ∫_C g = ∫_C f for all mW-measurable sets C, then g =ᵐ μ[f|mW]

  -- Apply ae_eq_condExp_of_forall_setIntegral_eq
  -- This lemma says: if g is mW-measurable and ∫_C g = ∫_C f for all mW-measurable C,
  -- then g =ᵐ μ[f|mW]
  --
  -- Here: f = φ ∘ Y * ψ ∘ Z, g = μ[φ ∘ Y|mW] * μ[ψ ∘ Z|mW]
  -- We have: hC_sets gives ∫_C f = ∫_C g for all mW-measurable C
  -- Conclusion: g =ᵐ μ[f|mW], i.e., μ[φ ∘ Y|mW] * μ[ψ ∘ Z|mW] =ᵐ μ[φ ∘ Y * ψ ∘ Z|mW]

  -- First, establish integrability of f = φ ∘ Y * ψ ∘ Z
  have hφY_int : Integrable (φ ∘ Y) μ := by
    refine Integrable.of_mem_Icc (-Mφ) Mφ (hφ_meas.comp hY).aemeasurable ?_
    filter_upwards [hφ_bdd] with ω hω
    simp only [Function.comp_apply, Set.mem_Icc]
    exact abs_le.mp hω

  have hψZ_int : Integrable (ψ ∘ Z) μ := by
    refine Integrable.of_mem_Icc (-Mψ) Mψ (hψ_meas.comp hZ).aemeasurable ?_
    filter_upwards [hψ_bdd] with ω hω
    simp only [Function.comp_apply, Set.mem_Icc]
    exact abs_le.mp hω

  have hf_int : Integrable ((φ ∘ Y) * (ψ ∘ Z)) μ := by
    -- Product of bounded integrable functions: φ ∘ Y bounded a.e., ψ ∘ Z integrable
    -- Use Integrable.bdd_mul': requires hg integrable, hf ae strongly measurable, hf bounded a.e.
    refine Integrable.bdd_mul' (c := Mφ) hψZ_int (hφ_meas.comp hY).aestronglyMeasurable ?_
    -- Need: ∀ᵐ ω ∂μ, ‖(φ ∘ Y) ω‖ ≤ Mφ
    filter_upwards [hφ_bdd] with ω hω
    simp only [Function.comp_apply]
    rw [Real.norm_eq_abs]
    exact hω

  -- Apply the uniqueness characterization lemma (gives g =ᵐ μ[f|m], need symm)
  refine (ae_eq_condExp_of_forall_setIntegral_eq hmW_le hf_int ?_ ?_ ?_).symm

  -- Hypothesis 1: IntegrableOn for g on finite mW-measurable sets
  · intro s hs hμs
    haveI : Fact (μ s < ∞) := ⟨hμs⟩
    -- Conditional expectations are integrable
    have h1 : Integrable (μ[(φ ∘ Y) | mW]) μ := integrable_condExp
    have h2 : Integrable (μ[(ψ ∘ Z) | mW]) μ := integrable_condExp
    -- Product of integrable functions is integrable on whole space (finite measure)
    have hprod : Integrable (μ[(φ ∘ Y) | mW] * μ[(ψ ∘ Z) | mW]) μ := by
      -- Use Integrable.bdd_mul': product of integrable and bounded ae functions is integrable
      -- First, establish that μ[φ ∘ Y|mW] is bounded ae by Mφ
      have hMφ_nn : 0 ≤ Mφ := by
        rcases hφ_bdd.exists with ⟨ω, hω⟩
        exact (abs_nonneg _).trans hω
      have hφY_ce_bdd : ∀ᵐ ω ∂μ, |μ[(φ ∘ Y) | mW] ω| ≤ Mφ := by
        have h_bdd : ∀ᵐ ω ∂μ, |(φ ∘ Y) ω| ≤ (⟨Mφ, hMφ_nn⟩ : NNReal) := by
          filter_upwards [hφ_bdd] with ω hω
          simpa using hω
        simpa [Real.norm_eq_abs] using
          ae_bdd_condExp_of_ae_bdd (m := mW) (R := ⟨Mφ, hMφ_nn⟩) h_bdd
      -- Apply Integrable.bdd_mul': g integrable, f ae strongly measurable and bounded
      -- Use h1.aestronglyMeasurable since h1 : Integrable (μ[(φ ∘ Y) | mW]) μ
      refine h2.bdd_mul' (c := Mφ) h1.aestronglyMeasurable ?_
      filter_upwards [hφY_ce_bdd] with ω hω
      rw [Real.norm_eq_abs]
      exact hω
    -- Product integrable on whole space implies integrable on subset
    exact hprod.integrableOn

  -- Hypothesis 2: Set integral equality (from hC_sets)
  · intro s hs hμs
    exact (hC_sets s hs).symm

  -- Hypothesis 3: g is mW-measurable
  · -- Product of conditional expectations is mW-measurable
    refine AEStronglyMeasurable.mul ?_ ?_
    · exact stronglyMeasurable_condExp.aestronglyMeasurable
    · exact stronglyMeasurable_condExp.aestronglyMeasurable

/-- **Conditional independence extends to bounded measurable functions (monotone class).**

If Y ⊥⊥_W Z for indicators, then by approximation the factorization extends to all
bounded measurable functions.

**Mathematical content:** For bounded measurable f(Y) and g(Z):
E[f(Y)·g(Z)|σ(W)] = E[f(Y)|σ(W)]·E[g(Z)|σ(W)]

**Proof strategy:** Use monotone class theorem:
1. Simple functions are dense in bounded measurables
2. Conditional expectation is continuous w.r.t. bounded convergence
3. Approximate f, g by simple functions fₙ, gₙ
4. Pass to limit using dominated convergence

This is the key extension that enables proving measurability properties.
-/
lemma condIndep_boundedMeasurable (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Ω → α) (Z : Ω → β) (W : Ω → γ)
    (hCI : CondIndep μ Y Z W)
    (hY : Measurable Y) (hZ : Measurable Z) (hW : Measurable W)
    {φ : α → ℝ} {ψ : β → ℝ}
    (hφ_meas : Measurable φ) (hψ_meas : Measurable ψ)
    (Mφ Mψ : ℝ)
    (hφ_bdd : ∀ᵐ ω ∂μ, |φ (Y ω)| ≤ Mφ)
    (hψ_bdd : ∀ᵐ ω ∂μ, |ψ (Z ω)| ≤ Mψ) :
    μ[ (φ ∘ Y) * (ψ ∘ Z) | MeasurableSpace.comap W (by infer_instance) ] =ᵐ[μ]
    μ[ φ ∘ Y | MeasurableSpace.comap W (by infer_instance) ] *
    μ[ ψ ∘ Z | MeasurableSpace.comap W (by infer_instance) ] := by
  -- Strategy: Apply the left-extension lemma twice
  -- Step 1: Extend in φ (keeping ψ fixed) - this is condIndep_bddMeas_extend_left
  -- Step 2: The result already has φ bounded measurable, so we're done
  -- (Alternatively: could extend in ψ by symmetric argument)

  -- Apply the left extension directly
  exact condIndep_bddMeas_extend_left μ Y Z W hCI hY hZ hW hφ_meas hψ_meas Mφ Mψ hφ_bdd hψ_bdd

/-!
## Wrapper: Rectangle factorization implies conditional independence
-/

/-- **Rectangle factorization implies conditional independence.**

This is essentially the identity, since `CondIndep` is defined as rectangle factorization.
This wrapper allows replacing axioms in ViaMartingale.lean with concrete proofs. -/
lemma condIndep_of_rect_factorization (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Ω → α) (Z : Ω → β) (W : Ω → γ)
    (hRect :
      ∀ ⦃A B⦄, MeasurableSet A → MeasurableSet B →
        μ[ (Y ⁻¹' A).indicator (fun _ => (1:ℝ)) *
           (Z ⁻¹' B).indicator (fun _ => (1:ℝ)) | MeasurableSpace.comap W (by infer_instance) ]
          =ᵐ[μ]
        μ[(Y ⁻¹' A).indicator (fun _ => (1:ℝ)) | MeasurableSpace.comap W (by infer_instance)] *
        μ[(Z ⁻¹' B).indicator (fun _ => (1:ℝ)) | MeasurableSpace.comap W (by infer_instance)]) :
  CondIndep μ Y Z W :=
  hRect  -- CondIndep is defined as exactly this property
