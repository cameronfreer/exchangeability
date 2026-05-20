/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Exchangeability.DeFinetti.ViaL2.DirectingMeasureBridge

/-!
# Directing Measure Integrals: Bridge Lemma and Conditional Expectation

This file establishes the bridge lemma connecting the directing measure to conditional
expectation: for bounded measurable `f`,

  ∫ f dν(ω) = E[f(X₀) | tail](ω)  a.e.

The proof routes through the kernel-level identification
`directing_measure_ae_eq_condExpKernel_map` plus mathlib's
`condExp_ae_eq_integral_condExpKernel`, so this file contains only the bridge lemma
itself and the L¹-uniqueness chain that downstream callers consume.

## Main results

* `directing_measure_integral_eq_condExp`: bridge lemma (now thin — routes through
  `DirectingMeasureBridge`).
* `directing_measure_integral_via_chain`: combines the bridge with the Cesàro / L¹
  identification chain to give the existence statement consumed by `MoreL2Helpers`.

## References

* Kallenberg (2005), *Probabilistic Symmetries and Invariance Principles*,
  Chapter 1, "Second proof of Theorem 1.1"
-/

noncomputable section

namespace Exchangeability.DeFinetti.ViaL2

open MeasureTheory ProbabilityTheory BigOperators Filter Topology
open Exchangeability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- **Bridge lemma:** For bounded measurable `f`,

`fun ω => ∫ x, f x ∂(directing_measure X … ω)` agrees a.e. with the conditional expectation
`μ[fun ω => f (X 0 ω) | tailSigma X]`.

The proof routes through the kernel-level bridge
`directing_measure_ae_eq_condExpKernel_map` and mathlib's
`condExp_ae_eq_integral_condExpKernel`, replacing what was previously a hand-built
monotone-class extension from `Iic` indicators.

The `[StandardBorelSpace Ω]` assumption comes from `condExpKernel`. -/
lemma directing_measure_integral_eq_condExp
    [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ)
    (f : ℝ → ℝ) (hf_meas : Measurable f) (hf_bdd : ∃ M, ∀ x, |f x| ≤ M) :
    (fun ω => ∫ x, f x ∂(directing_measure X hX_contract hX_meas hX_L2 ω))
      =ᵐ[μ] μ[fun ω => f (X 0 ω) | TailSigma.tailSigma X] := by
  have hm_le : TailSigma.tailSigma X ≤ (inferInstance : MeasurableSpace Ω) :=
    TailSigma.tailSigma_le X hX_meas
  obtain ⟨M, hM⟩ := hf_bdd
  -- `f ∘ X 0` is integrable on the probability space (bounded measurable).
  have hfX0_int : Integrable (fun ω => f (X 0 ω)) μ := by
    refine Integrable.mono' (integrable_const (max M 0)) ?_ ?_
    · exact (hf_meas.comp (hX_meas 0)).aestronglyMeasurable
    · filter_upwards with ω
      rw [Real.norm_eq_abs]
      exact (hM (X 0 ω)).trans (le_max_left _ _)
  -- Bridge: a.e. in ω, `directing_measure ω = (condExpKernel μ (tailSigma X) ω).map (X 0)`.
  have h_bridge := directing_measure_ae_eq_condExpKernel_map X hX_contract hX_meas hX_L2
  -- Hence the integral against `directing_measure ω` equals the integral of `f ∘ X 0`
  -- against the kernel at `ω`, by `integral_map`.
  have h_push : (fun ω => ∫ x, f x ∂(directing_measure X hX_contract hX_meas hX_L2 ω))
      =ᵐ[μ] fun ω => ∫ y, f (X 0 y)
          ∂(condExpKernel (μ := μ) (m := TailSigma.tailSigma X) ω) := by
    filter_upwards [h_bridge] with ω hω
    rw [hω]
    exact integral_map (hX_meas 0).aemeasurable hf_meas.aestronglyMeasurable
  -- The kernel integral identifies the conditional expectation.
  exact h_push.trans
    (condExp_ae_eq_integral_condExpKernel hm_le hfX0_int).symm

/-- **Simplified directing measure integral via identification chain.**

This lemma proves that the L¹ limit α equals ∫f dν a.e. using the Kallenberg identification chain:
1. α = E[f(X₀)|tail]  (from `cesaro_to_condexp_L2`)
2. E[f(X₀)|tail] = ∫f dν  (from `directing_measure_integral_eq_condExp`)
3. Therefore α = ∫f dν by transitivity

This approach bypasses the Ioc/step function decomposition entirely, giving a much simpler proof.

**Key insight:** By uniqueness of L¹ limits, the L¹ limit from `weighted_sums_converge_L1`
equals the L² limit from `cesaro_to_condexp_L2` (since L² convergence implies L¹ on prob spaces).
-/
lemma directing_measure_integral_via_chain
    [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ)
    (f : ℝ → ℝ) (hf_meas : Measurable f)
    (hf_bdd : ∃ M, ∀ x, |f x| ≤ M) :
    ∃ (alpha : Ω → ℝ),
      Measurable alpha ∧ MemLp alpha 1 μ ∧
      (∀ n, ∀ ε > 0, ∃ M : ℕ, ∀ m : ℕ, m ≥ M →
        ∫ ω, |(1/(m:ℝ)) * ∑ k : Fin m, f (X (n + k.val + 1) ω) - alpha ω| ∂μ < ε) ∧
      (∀ᵐ ω ∂μ, alpha ω = ∫ x, f x ∂(directing_measure X hX_contract hX_meas hX_L2 ω)) := by
  -- Get α from weighted_sums_converge_L1
  obtain ⟨alpha, hα_meas, hα_L1, hα_conv⟩ :=
    weighted_sums_converge_L1 X hX_contract hX_meas hX_L2 f hf_meas hf_bdd
  refine ⟨alpha, hα_meas, hα_L1, hα_conv, ?_⟩

  -- ═══════════════════════════════════════════════════════════════════════════════
  -- IDENTIFICATION CHAIN: α = E[f(X₀)|tail] = ∫f dν
  -- ═══════════════════════════════════════════════════════════════════════════════

  -- Step 1: Get α_f from cesaro_to_condexp_L2 with identification
  -- α_f =ᵐ E[f(X₀)|tail]
  -- Note: cesaro_to_condexp_L2 requires |f x| ≤ 1, so we need to rescale if M > 1
  obtain ⟨M, hM⟩ := hf_bdd
  by_cases hM_zero : M = 0
  · -- If M = 0, then f = 0, so both α and ∫f dν are 0 a.e.
    have hf_zero : ∀ x, f x = 0 := fun x => by
      have := hM x
      rw [hM_zero] at this
      exact abs_nonpos_iff.mp this

    -- Show ∫f dν = 0 for all ω (deterministic, not just a.e.)
    have h_integral_zero : ∀ ω, ∫ x, f x ∂(directing_measure X hX_contract hX_meas hX_L2 ω) = 0 := by
      intro ω
      simp only [hf_zero, integral_zero]

    -- Show alpha = 0 a.e. from L¹ convergence
    -- When f = 0, Cesàro averages are 0, so ∫|0 - alpha| < ε for all ε > 0
    -- This implies ∫|alpha| = 0, hence alpha = 0 a.e.
    have h_alpha_zero_ae : alpha =ᵐ[μ] 0 := by
      -- The Cesàro sum is 0 when f = 0
      have h_cesaro_zero : ∀ (n : ℕ) (m : ℕ) ω,
          (1/(m:ℝ)) * ∑ k : Fin m, f (X (n + k.val + 1) ω) = 0 := by
        intro n m ω
        simp only [hf_zero, Finset.sum_const_zero, mul_zero]
      -- From hα_conv with n = 0, ε = 1/k: ∫|0 - alpha| < 1/k for large m
      -- Taking limit: ∫|alpha| ≤ 0, so ∫|alpha| = 0
      have h_int_abs_alpha_eq_zero : ∫ ω, |alpha ω| ∂μ = 0 := by
        apply le_antisymm _ (integral_nonneg (fun _ => abs_nonneg _))
        -- For any ε > 0, ∫|alpha| < ε (using hα_conv with cesaro = 0)
        by_contra h_pos
        push Not at h_pos
        have hε : (0 : ℝ) < ∫ ω, |alpha ω| ∂μ := h_pos
        obtain ⟨M_idx, hM_idx⟩ := hα_conv 0 (∫ ω, |alpha ω| ∂μ) hε
        specialize hM_idx M_idx (le_refl _)
        have h_simp : ∀ ω', |(1 / (M_idx : ℝ)) * ∑ k : Fin M_idx, f (X (0 + k.val + 1) ω') - alpha ω'|
            = |alpha ω'| := by
          intro ω'
          rw [h_cesaro_zero 0 M_idx ω', zero_sub, abs_neg]
        simp_rw [h_simp] at hM_idx
        linarith
      -- ∫|alpha| = 0 implies alpha = 0 a.e.
      -- Use: integral_eq_zero_iff_of_nonneg_ae
      have h_abs_nonneg : (0 : Ω → ℝ) ≤ᵐ[μ] (fun ω => |alpha ω|) :=
        ae_of_all μ (fun ω => abs_nonneg (alpha ω))
      have h_abs_int : Integrable (fun ω => |alpha ω|) μ :=
        (memLp_one_iff_integrable.mp hα_L1).norm
      rw [integral_eq_zero_iff_of_nonneg_ae h_abs_nonneg h_abs_int] at h_int_abs_alpha_eq_zero
      exact h_int_abs_alpha_eq_zero.mono (fun ω hω => abs_eq_zero.mp hω)

    -- Combine: alpha = 0 = ∫f dν a.e.
    filter_upwards [h_alpha_zero_ae] with ω hω
    simp only [hω, h_integral_zero ω, Pi.zero_apply]

  · -- M > 0 case
    have hM_pos : 0 < M := lt_of_le_of_ne (abs_nonneg (f 0) |>.trans (hM 0)) (Ne.symm hM_zero)

    -- Rescale f to g = f/M so |g| ≤ 1
    let g : ℝ → ℝ := fun x => f x / M
    have hg_meas : Measurable g := hf_meas.div_const M
    have hg_bdd : ∀ x, |g x| ≤ 1 := fun x => by
      simp only [g, abs_div]
      have hM_abs : |M| = M := abs_of_pos hM_pos
      rw [hM_abs]
      calc |f x| / M ≤ M / M := div_le_div_of_nonneg_right (hM x) (le_of_lt hM_pos)
        _ = 1 := div_self (ne_of_gt hM_pos)

    -- Apply cesaro_to_condexp_L2 to g
    obtain ⟨α_g, hα_g_L2, hα_g_tail, hα_g_conv, hα_g_eq⟩ :=
      cesaro_to_condexp_L2 hX_contract hX_meas g hg_meas hg_bdd

    -- α_g = E[g(X₀)|tail] = E[(f/M)(X₀)|tail] = (1/M) * E[f(X₀)|tail]
    -- So: E[f(X₀)|tail] = M * α_g

    -- Chain:
    -- 1. alpha =ᵐ M * α_g  (by uniqueness of limits for f = M * g)
    -- 2. M * α_g =ᵐ M * E[g(X₀)|tail] = E[f(X₀)|tail]  (by linearity of condExp)
    -- 3. E[f(X₀)|tail] =ᵐ ∫f dν  (by directing_measure_integral_eq_condExp)

    -- Bridge lemma: E[f(X₀)|tail] =ᵐ ∫f dν
    have h_bridge : (fun ω => ∫ x, f x ∂(directing_measure X hX_contract hX_meas hX_L2 ω))
        =ᵐ[μ] μ[fun ω => f (X 0 ω) | TailSigma.tailSigma X] :=
      directing_measure_integral_eq_condExp X hX_contract hX_meas hX_L2 f hf_meas ⟨M, hM⟩

    -- ═══════════════════════════════════════════════════════════════════════════════
    -- KEY STEP: alpha =ᵐ E[f(X₀)|tail] via L¹ uniqueness
    -- ═══════════════════════════════════════════════════════════════════════════════
    --
    -- The identification chain connects three quantities a.e.:
    --   alpha = E[f(X₀)|tail] = ∫f dν
    --
    -- Direct approach: Both alpha and E[f|tail] are L¹ limits of shifted f-averages.
    -- - alpha → from hα_conv (L¹ limit of shifted f-averages at indices n+1,...,n+m)
    -- - E[f(X₀)|tail] → from cesaro_convergence_all_shifts (same averages)
    -- By L¹ uniqueness, alpha =ᵐ E[f(X₀)|tail].
    --
    -- Note: We use the rescaled function g = f/M with |g| ≤ 1 since
    -- cesaro_convergence_all_shifts requires the bound |g| ≤ 1.
    -- Then we scale back: M * (g-averages) = f-averages.

    -- Step 1: Show alpha =ᵐ E[f(X₀)|tail] using L¹ uniqueness directly
    -- Both limits are a.e. equal to the unique L¹ limit of shifted f-averages
    have h_alpha_eq_condExp : alpha =ᵐ[μ] μ[f ∘ X 0 | TailSigma.tailSigma X] := by
      -- PROOF: Use condExp_smul and the identification from cesaro_to_condexp_L2
      --
      -- We have from cesaro_to_condexp_L2:
      --   α_g =ᵐ μ[g ∘ X 0 | tail]    where g = f/M
      --
      -- By condExp_smul: μ[M • (g ∘ X 0) | tail] = M • μ[g ∘ X 0 | tail]
      -- Since f = M * g: μ[f ∘ X 0 | tail] = M * μ[g ∘ X 0 | tail] =ᵐ M * α_g
      --
      -- The L¹ uniqueness argument:
      -- - f-averages = M * g-averages (algebra)
      -- - g-averages → α_g in L² (from cesaro_to_condexp_L2, via L² convergence)
      -- - L² convergence ⟹ L¹ convergence on probability spaces
      -- - So M * g-averages = f-averages → M * α_g in L¹
      -- - But hα_conv says f-averages → alpha in L¹
      -- - By uniqueness of L¹ limits: alpha =ᵐ M * α_g
      --
      -- Conclusion: alpha =ᵐ M * α_g =ᵐ M * μ[g ∘ X 0 | tail] = μ[f ∘ X 0 | tail]

      -- Step 1a: Show μ[f ∘ X 0 | tail] = M * μ[g ∘ X 0 | tail]
      have hm_le := TailSigma.tailSigma_le X hX_meas
      have h_condExp_f_eq : μ[f ∘ X 0 | TailSigma.tailSigma X]
          =ᵐ[μ] fun ω => M * μ[g ∘ X 0 | TailSigma.tailSigma X] ω := by
        -- f x = M * g x (since g x = f x / M and M > 0)
        have h_f_eq_Mg : ∀ x, f x = M * g x := fun x => by
          simp only [g]
          field_simp [ne_of_gt hM_pos]
        -- f ∘ X 0 = (M • g) ∘ X 0 (pointwise)
        have h_comp_eq : (f ∘ X 0) = fun ω => M * g (X 0 ω) := by
          ext ω
          simp only [Function.comp_apply, h_f_eq_Mg]
        -- Use condExp linearity: E[M * h | m] = M * E[h | m]
        have h_ae : μ[fun ω => M * g (X 0 ω) | TailSigma.tailSigma X]
            =ᵐ[μ] fun ω => M * μ[g ∘ X 0 | TailSigma.tailSigma X] ω :=
          condExp_smul M (g ∘ X 0) (m := TailSigma.tailSigma X) (μ := μ)
        calc μ[f ∘ X 0 | TailSigma.tailSigma X]
            = μ[fun ω => M * g (X 0 ω) | TailSigma.tailSigma X] := by rw [h_comp_eq]
          _ =ᵐ[μ] fun ω => M * μ[g ∘ X 0 | TailSigma.tailSigma X] ω := h_ae

      -- Step 1b: Show alpha =ᵐ M * α_g by L¹ uniqueness
      -- Both are L¹ limits of f-averages (which equal M * g-averages)
      have h_alpha_eq_M_alpha_g : alpha =ᵐ[μ] fun ω => M * α_g ω := by
        -- Strategy: Both alpha and M * α_g are L¹ limits of the same sequence:
        --   A m ω := m⁻¹ * ∑ k : Fin m, f (X (k.val + 1) ω)
        -- The indices match:
        --   - hα_conv 0: uses X (0 + k.val + 1) = X (k.val + 1), indices 1, 2, ..., m
        --   - cesaro_convergence_all_shifts with n=1: uses X (1+k), indices 1, 2, ..., m
        -- By L¹ uniqueness, alpha =ᵐ M * α_g.

        -- Define the averaging sequence with matching indices
        let A : ℕ → Ω → ℝ := fun m ω => (1/(m:ℝ)) * ∑ k : Fin m, f (X (k.val + 1) ω)

        -- From hα_conv 0: A → alpha in L¹
        have hA_to_alpha : ∀ ε > 0, ∃ M_idx : ℕ, ∀ m ≥ M_idx,
            ∫ ω, |A m ω - alpha ω| ∂μ < ε := by
          intro ε hε
          obtain ⟨M_idx, hM_idx⟩ := hα_conv 0 ε hε
          use M_idx
          intro m hm
          convert hM_idx m hm using 2
          ext ω
          simp only [A, zero_add]

        -- From cesaro_convergence_all_shifts with n=1: g-averages → E[g∘X 0|tail] in L¹
        have hg_cesaro : ∀ ε > 0, ∃ M_idx : ℕ, ∀ m ≥ M_idx,
            ∫ ω, |(1/(m:ℝ)) * ∑ k : Fin m, g (X (1+k) ω) -
                 μ[g ∘ X 0 | TailSigma.tailSigma X] ω| ∂μ < ε := by
          intro ε hε
          exact cesaro_convergence_all_shifts X hX_contract hX_meas g hg_meas hg_bdd 1 ε hε

        -- Reindex: X(1+k) = X(k.val+1) for k : Fin m
        have hg_cesaro' : ∀ ε > 0, ∃ M_idx : ℕ, ∀ m ≥ M_idx,
            ∫ ω, |(1/(m:ℝ)) * ∑ k : Fin m, g (X (k.val+1) ω) -
                 μ[g ∘ X 0 | TailSigma.tailSigma X] ω| ∂μ < ε := by
          intro ε hε
          obtain ⟨M_idx, hM_idx⟩ := hg_cesaro ε hε
          use M_idx
          intro m hm
          convert hM_idx m hm using 3
          simp only [add_comm (1:ℕ)]

        -- Since α_g =ᵐ E[g∘X 0|tail], we have ∫ |α_g - E[g∘X 0|tail]| = 0
        have hα_g_diff_zero : ∫ ω, |α_g ω - μ[g ∘ X 0 | TailSigma.tailSigma X] ω| ∂μ = 0 := by
          have h_ae := hα_g_eq
          rw [integral_eq_zero_iff_of_nonneg_ae (ae_of_all μ (fun _ => abs_nonneg _))]
          · filter_upwards [h_ae] with ω hω
            simp only [hω, sub_self, abs_zero, Pi.zero_apply]
          · -- Integrability: α_g - condExp is in L¹
            have hα_g_int : Integrable α_g μ := hα_g_L2.integrable one_le_two
            fun_prop

        -- Triangle inequality: g-averages → α_g in L¹
        have hg_to_alpha_g : ∀ ε > 0, ∃ M_idx : ℕ, ∀ m ≥ M_idx,
            ∫ ω, |(1/(m:ℝ)) * ∑ k : Fin m, g (X (k.val+1) ω) - α_g ω| ∂μ < ε := by
          intro ε hε
          obtain ⟨M_idx, hM_idx⟩ := hg_cesaro' ε hε
          use M_idx
          intro m hm
          calc ∫ ω, |(1/(m:ℝ)) * ∑ k : Fin m, g (X (k.val+1) ω) - α_g ω| ∂μ
              ≤ ∫ ω, (|(1/(m:ℝ)) * ∑ k : Fin m, g (X (k.val+1) ω) -
                      μ[g ∘ X 0 | TailSigma.tailSigma X] ω| +
                     |μ[g ∘ X 0 | TailSigma.tailSigma X] ω - α_g ω|) ∂μ := by
                  apply integral_mono_of_nonneg (ae_of_all μ (fun _ => abs_nonneg _))
                  · apply Integrable.add
                    · have hg_avg_meas : Measurable (fun ω => (1/(m:ℝ)) * ∑ k : Fin m, g (X (k.val+1) ω)) := by
                        fun_prop
                      have hg_avg_bdd : ∀ ω, |(1/(m:ℝ)) * ∑ k : Fin m, g (X (k.val+1) ω)| ≤ 1 := by
                        intro ω
                        by_cases hm : m = 0
                        · simp [hm]
                        · calc |(1/(m:ℝ)) * ∑ k : Fin m, g (X (k.val+1) ω)|
                              ≤ (m:ℝ)⁻¹ * ∑ k : Fin m, |g (X (k.val+1) ω)| := by
                                rw [one_div, abs_mul, abs_of_pos (by positivity : (m:ℝ)⁻¹ > 0)]
                                gcongr; exact Finset.abs_sum_le_sum_abs _ _
                            _ ≤ (m:ℝ)⁻¹ * ∑ k : Fin m, (1:ℝ) := by
                                gcongr with k _; exact hg_bdd _
                            _ = 1 := by simp [Finset.sum_const, Finset.card_fin]; field_simp [hm]
                      have hg_avg_bdd' : ∀ᵐ ω ∂μ, ‖(1/(m:ℝ)) * ∑ k : Fin m, g (X (k.val+1) ω)‖ ≤ 1 := by
                        apply ae_of_all μ
                        intro ω
                        rw [Real.norm_eq_abs]
                        exact hg_avg_bdd ω
                      refine (Integrable.of_bound hg_avg_meas.aestronglyMeasurable 1 hg_avg_bdd').sub integrable_condExp |>.norm
                    · refine (integrable_condExp.sub (hα_g_L2.integrable one_le_two)).norm
                  · apply ae_of_all μ
                    intro ω
                    calc |(1/(m:ℝ)) * ∑ k : Fin m, g (X (k.val+1) ω) - α_g ω|
                        = |((1/(m:ℝ)) * ∑ k : Fin m, g (X (k.val+1) ω) -
                            μ[g ∘ X 0 | TailSigma.tailSigma X] ω) +
                           (μ[g ∘ X 0 | TailSigma.tailSigma X] ω - α_g ω)| := by ring_nf
                      _ ≤ _ := abs_add_le _ _
            _ = ∫ ω, |(1/(m:ℝ)) * ∑ k : Fin m, g (X (k.val+1) ω) -
                      μ[g ∘ X 0 | TailSigma.tailSigma X] ω| ∂μ +
                ∫ ω, |μ[g ∘ X 0 | TailSigma.tailSigma X] ω - α_g ω| ∂μ := by
                  apply integral_add
                  · have hg_avg_meas : Measurable (fun ω => (1/(m:ℝ)) * ∑ k : Fin m, g (X (k.val+1) ω)) := by
                      fun_prop
                    have hg_avg_bdd : ∀ ω, |(1/(m:ℝ)) * ∑ k : Fin m, g (X (k.val+1) ω)| ≤ 1 := by
                      intro ω
                      by_cases hm : m = 0
                      · simp [hm]
                      · calc |(1/(m:ℝ)) * ∑ k : Fin m, g (X (k.val+1) ω)|
                            ≤ (m:ℝ)⁻¹ * ∑ k : Fin m, |g (X (k.val+1) ω)| := by
                              rw [one_div, abs_mul, abs_of_pos (by positivity : (m:ℝ)⁻¹ > 0)]
                              gcongr; exact Finset.abs_sum_le_sum_abs _ _
                          _ ≤ (m:ℝ)⁻¹ * ∑ k : Fin m, (1:ℝ) := by
                              gcongr with k _; exact hg_bdd _
                          _ = 1 := by simp [Finset.sum_const, Finset.card_fin]; field_simp [hm]
                    have hg_avg_bdd' : ∀ᵐ ω ∂μ, ‖(1/(m:ℝ)) * ∑ k : Fin m, g (X (k.val+1) ω)‖ ≤ 1 := by
                      apply ae_of_all μ
                      intro ω
                      rw [Real.norm_eq_abs]
                      exact hg_avg_bdd ω
                    exact (Integrable.of_bound hg_avg_meas.aestronglyMeasurable 1 hg_avg_bdd').sub integrable_condExp |>.norm
                  · exact (integrable_condExp.sub (hα_g_L2.integrable one_le_two)).norm
            _ = ∫ ω, |(1/(m:ℝ)) * ∑ k : Fin m, g (X (k.val+1) ω) -
                      μ[g ∘ X 0 | TailSigma.tailSigma X] ω| ∂μ + 0 := by
                  congr 1
                  convert hα_g_diff_zero using 2
                  ext ω
                  rw [abs_sub_comm]
            _ < ε := by simp only [add_zero]; exact hM_idx m hm

        -- Scaling: f-averages = M * g-averages
        have hfg_scaling : ∀ m ω, A m ω = M * ((1/(m:ℝ)) * ∑ k : Fin m, g (X (k.val+1) ω)) := by
          intro m ω
          simp only [A, g]
          by_cases hm : m = 0
          · simp [hm]
          · have hM_ne : M ≠ 0 := ne_of_gt hM_pos
            have hm_ne : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
            -- LHS: 1/m * ∑ f(...)
            -- RHS: M * (1/m * ∑ (f(...)/M)) = 1/m * ∑ f(...)
            -- Direct algebra: M * (1/m * ∑ (f/M)) = 1/m * ∑ f
            have h_sum_eq : ∑ k : Fin m, f (X (k.val+1) ω) / M = (∑ k : Fin m, f (X (k.val+1) ω)) / M := by
              rw [Finset.sum_div]
            rw [h_sum_eq]
            field_simp [hM_ne, hm_ne]

        -- Therefore: A → M * α_g in L¹
        have hA_to_M_alpha_g : ∀ ε > 0, ∃ M_idx : ℕ, ∀ m ≥ M_idx,
            ∫ ω, |A m ω - M * α_g ω| ∂μ < ε := by
          intro ε hε
          have hε' : 0 < ε / (|M| + 1) := by positivity
          obtain ⟨M_idx, hM_idx⟩ := hg_to_alpha_g (ε / (|M| + 1)) hε'
          use M_idx
          intro m hm
          calc ∫ ω, |A m ω - M * α_g ω| ∂μ
              = ∫ ω, |M * ((1/(m:ℝ)) * ∑ k : Fin m, g (X (k.val+1) ω)) - M * α_g ω| ∂μ := by
                  congr 1; ext ω; rw [hfg_scaling]
            _ = ∫ ω, |M| * |(1/(m:ℝ)) * ∑ k : Fin m, g (X (k.val+1) ω) - α_g ω| ∂μ := by
                  congr 1; ext ω; rw [← mul_sub, abs_mul]
            _ = |M| * ∫ ω, |(1/(m:ℝ)) * ∑ k : Fin m, g (X (k.val+1) ω) - α_g ω| ∂μ := by
                  rw [integral_const_mul]
            _ < |M| * (ε / (|M| + 1)) := by
                  gcongr; exact hM_idx m hm
            _ < (|M| + 1) * (ε / (|M| + 1)) := by
                  gcongr; linarith
            _ = ε := by field_simp

        -- Convert to TendstoInMeasure and apply uniqueness
        -- Both A → alpha and A → M * α_g in L¹

        -- First convert L¹ convergence to eLpNorm convergence
        have hA_meas : ∀ m, Measurable (A m) := fun m => by fun_prop

        have hA_bdd : ∀ m ω, |A m ω| ≤ M := fun m ω => by
          simp only [A]
          by_cases hm : m = 0
          · simp [hm]; exact abs_nonneg _ |>.trans (hM 0)
          · calc |(1/(m:ℝ)) * ∑ k : Fin m, f (X (k.val+1) ω)|
                ≤ (m:ℝ)⁻¹ * ∑ k : Fin m, |f (X (k.val+1) ω)| := by
                    rw [one_div, abs_mul, abs_of_pos (by positivity : (m:ℝ)⁻¹ > 0)]
                    gcongr; exact Finset.abs_sum_le_sum_abs _ _
              _ ≤ (m:ℝ)⁻¹ * ∑ k : Fin m, M := by
                    gcongr with k _; exact hM _
              _ = M := by simp [Finset.sum_const, Finset.card_fin]; field_simp [hm]

        have hAalpha_integrable : ∀ m, Integrable (fun ω => A m ω - alpha ω) μ := fun m =>
          (Integrable.of_bound (hA_meas m).aestronglyMeasurable M (ae_of_all μ (hA_bdd m))).sub
            (hα_L1.integrable le_rfl)

        have hAMalpha_g_integrable : ∀ m, Integrable (fun ω => A m ω - M * α_g ω) μ := fun m =>
          (Integrable.of_bound (hA_meas m).aestronglyMeasurable M (ae_of_all μ (hA_bdd m))).sub
            ((hα_g_L2.integrable one_le_two).const_mul M)

        have hA_tendsto_alpha : Tendsto (fun m => ∫ ω, |A m ω - alpha ω| ∂μ) atTop (𝓝 0) := by
          rw [Metric.tendsto_atTop]
          intro ε hε
          obtain ⟨M_idx, hM_idx⟩ := hA_to_alpha ε hε
          use M_idx
          intro m hm
          rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg (fun ω => abs_nonneg _))]
          exact hM_idx m hm

        have hA_tendsto_M_alpha_g : Tendsto (fun m => ∫ ω, |A m ω - M * α_g ω| ∂μ) atTop (𝓝 0) := by
          rw [Metric.tendsto_atTop]
          intro ε hε
          obtain ⟨M_idx, hM_idx⟩ := hA_to_M_alpha_g ε hε
          use M_idx
          intro m hm
          rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg (fun ω => abs_nonneg _))]
          exact hM_idx m hm

        have halpha_eLpNorm : Tendsto (fun m => eLpNorm (fun ω => A m ω - alpha ω) 1 μ) atTop (𝓝 0) := by
          rw [ENNReal.tendsto_nhds_zero]
          intro ε hε
          rw [Metric.tendsto_atTop] at hA_tendsto_alpha
          by_cases h_top : ε = ⊤
          · simp [h_top]
          · have ε_pos : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' h_top
            obtain ⟨M_idx, hM_idx⟩ := hA_tendsto_alpha ε.toReal ε_pos
            refine Filter.eventually_atTop.mpr ⟨M_idx, fun m hm => ?_⟩
            rw [Exchangeability.Probability.IntegrationHelpers.eLpNorm_one_eq_integral_abs (hAalpha_integrable m)]
            rw [← ENNReal.ofReal_toReal h_top]
            rw [ENNReal.ofReal_le_ofReal_iff ε_pos.le]
            have := hM_idx m hm
            rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg (fun ω => abs_nonneg _))] at this
            exact this.le

        have hM_alpha_g_eLpNorm : Tendsto (fun m => eLpNorm (fun ω => A m ω - M * α_g ω) 1 μ) atTop (𝓝 0) := by
          rw [ENNReal.tendsto_nhds_zero]
          intro ε hε
          rw [Metric.tendsto_atTop] at hA_tendsto_M_alpha_g
          by_cases h_top : ε = ⊤
          · simp [h_top]
          · have ε_pos : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' h_top
            obtain ⟨M_idx, hM_idx⟩ := hA_tendsto_M_alpha_g ε.toReal ε_pos
            refine Filter.eventually_atTop.mpr ⟨M_idx, fun m hm => ?_⟩
            rw [Exchangeability.Probability.IntegrationHelpers.eLpNorm_one_eq_integral_abs (hAMalpha_g_integrable m)]
            rw [← ENNReal.ofReal_toReal h_top]
            rw [ENNReal.ofReal_le_ofReal_iff ε_pos.le]
            have := hM_idx m hm
            rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg (fun ω => abs_nonneg _))] at this
            exact this.le

        -- Convert to TendstoInMeasure
        have halpha_meas_conv : TendstoInMeasure μ A atTop alpha := by
          apply tendstoInMeasure_of_tendsto_eLpNorm (p := 1) one_ne_zero
          · intro m; exact (hA_meas m).aestronglyMeasurable
          · exact hα_meas.aestronglyMeasurable
          · exact halpha_eLpNorm

        have hM_alpha_g_meas_conv : TendstoInMeasure μ A atTop (fun ω => M * α_g ω) := by
          apply tendstoInMeasure_of_tendsto_eLpNorm (p := 1) one_ne_zero
          · intro m; exact (hA_meas m).aestronglyMeasurable
          · exact aestronglyMeasurable_const.mul hα_g_L2.aestronglyMeasurable
          · exact hM_alpha_g_eLpNorm

        -- Apply uniqueness
        exact tendstoInMeasure_ae_unique halpha_meas_conv hM_alpha_g_meas_conv

      -- Step 1c: Combine: alpha =ᵐ M * α_g =ᵐ M * μ[g|tail] = μ[f|tail]
      calc alpha =ᵐ[μ] fun ω => M * α_g ω := h_alpha_eq_M_alpha_g
        _ =ᵐ[μ] fun ω => M * μ[g ∘ X 0 | TailSigma.tailSigma X] ω := by
            filter_upwards [hα_g_eq] with ω hω
            simp only [hω]
        _ =ᵐ[μ] μ[f ∘ X 0 | TailSigma.tailSigma X] := h_condExp_f_eq.symm

    -- Step 2: Combine with bridge lemma: alpha =ᵐ ∫f dν
    exact h_alpha_eq_condExp.trans h_bridge.symm

end Exchangeability.DeFinetti.ViaL2
