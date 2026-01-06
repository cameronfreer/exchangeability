/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Exchangeability.DeFinetti.ViaKoopman.CesaroL1Bounded

/-! # Cesàro Pair Factorization via MET

This file proves the pair factorization lemma for conditional expectations
using Mean Ergodic Theorem (MET) and exchangeability.

**Main result:**
- `condexp_pair_factorization_MET`: For exchangeable measures, CE[f(ω₀)·g(ω₁)|ℐ]
  factors into CE[f(ω₀)|ℐ]·CE[g(ω₀)|ℐ].

**Proof strategy** (CORRECTED - avoids false k=0 lag constancy):
1. Apply tower property directly on g₁ (via Cesàro from index 1):
   CE[f(ω₀)·g(ω₁)|ℐ] = CE[f(ω₀)·CE[g(ω₀)|ℐ]|ℐ]
   (uses h_tower_of_lagConst_from_one which only needs k ≥ 1 lag constancy)
2. Apply pull-out property: CE[f(ω₀)·CE[g(ω₀)|ℐ]|ℐ] = CE[g(ω₀)|ℐ]·CE[f(ω₀)|ℐ]
   (CE[g(ω₀)|ℐ] is ℐ-measurable)

**Key insight**: This requires EXCHANGEABILITY (via `hExch`), not just stationarity.

**Split from**: CesaroConvergence.lean (lines 1561-2014)
-/

open Filter MeasureTheory

noncomputable section

namespace Exchangeability.DeFinetti.ViaKoopman

open MeasureTheory Filter Topology ProbabilityTheory
open Exchangeability.Ergodic
open Exchangeability.PathSpace
open scoped BigOperators RealInnerProductSpace

set_option linter.unusedSectionVars false

variable {α : Type*} [MeasurableSpace α]

/-! ### Local notation -/

/-- Abbreviation for shiftInvariantSigma for readability -/
local notation "mSI" => shiftInvariantSigma (α := α)

section OptionB_L1Convergence

/-- **Tower property from index 1** (avoids k=0 lag constancy).

This is the corrected version that proves:
  CE[f·g₁ | mSI] =ᵐ CE[f·CE[g₀|mSI] | mSI]

Key insight: We use Cesàro averages starting from index 1 (A'_n) to avoid the false k=0 case.
The proof structure:
1. CE[A'_n | mSI] = CE[g₀ | mSI] (shift invariance: CE[g_j|mSI] = CE[g₀|mSI])
2. CE[f·A'_n | mSI] = CE[f·g₁ | mSI] for all n (lag constancy with k ≥ 1 only)
3. A'_n → CE[g₀|mSI] in L¹ (MET)
4. CE Lipschitz: CE[f·A'_n] → CE[f·CE[g₀|mSI]]
5. Squeeze: constant sequence converges to 0 -/
private theorem h_tower_of_lagConst_from_one
    {μ : Measure (Ω[α])} [IsProbabilityMeasure μ] [StandardBorelSpace α]
    (hσ : MeasurePreserving shift μ μ)
    (hExch : ∀ π : Equiv.Perm ℕ, Measure.map (Exchangeability.reindex π) μ = μ)
    (f g : α → ℝ)
    (hf_meas : Measurable f) (hf_bd : ∃ Cf, ∀ x, |f x| ≤ Cf)
    (hg_meas : Measurable g) (hg_bd : ∃ Cg, ∀ x, |g x| ≤ Cg) :
    μ[(fun ω => f (ω 0) * g (ω 1)) | shiftInvariantSigma (α := α)]
      =ᵐ[μ]
    μ[(fun ω =>
        f (ω 0) * μ[(fun ω => g (ω 0)) | shiftInvariantSigma (α := α)] ω)
        | shiftInvariantSigma (α := α)] := by
  classical
  have hmSI := shiftInvariantSigma_le (α := α)

  -- Cesàro averages from index 1: A'_n = (1/n) * Σ_{j=1}^n g(ω_j)
  let A' : ℕ → Ω[α] → ℝ := fun n ω =>
    if n = 0 then 0 else (1 / (n : ℝ)) * (Finset.range n).sum (fun j => g (ω (j + 1)))
  set Y : Ω[α] → ℝ := fun ω => μ[(fun ω' => g (ω' 0)) | mSI] ω

  obtain ⟨Cf, hCf⟩ := hf_bd
  obtain ⟨Cg, hCg⟩ := hg_bd

  -- (1) CE[f·A'_n | mSI] = CE[f·g₁ | mSI] for all n ≥ 1
  have h_product_const : ∀ n, 0 < n →
      μ[(fun ω => f (ω 0) * A' n ω) | mSI]
        =ᵐ[μ]
      μ[(fun ω => f (ω 0) * g (ω 1)) | mSI] := by
    intro n hn
    have hA' : A' n = fun ω => (1 / (n : ℝ)) * (Finset.range n).sum (fun j => g (ω (j + 1))) := by
      ext ω
      simp only [A', if_neg (Nat.ne_of_gt hn)]
    rw [show (fun ω => f (ω 0) * A' n ω)
           = (fun ω => f (ω 0) * ((1 / (n : ℝ)) * (Finset.range n).sum (fun j => g (ω (j + 1))))) by
         ext ω; rw [hA']]
    exact product_ce_constant_of_lag_const_from_one hExch f g hf_meas ⟨Cf, hCf⟩ hg_meas ⟨Cg, hCg⟩ n hn

  -- (2) A'_n → Y in L¹ (MET via shift composition)
  -- A'_{n+1}(ω) = (1/(n+1)) * Σ_{j=0}^n g(shift(ω)_j) = A_n(shift(ω))
  -- Since shift preserves μ and A_n → Y in L¹, A'_{n+1} → Y in L¹
  have h_L1_A'_to_Y : Tendsto (fun n =>
      ∫ ω, |A' (n + 1) ω - Y ω| ∂μ) atTop (𝓝 0) := by
    -- A'_{n+1}(ω) = (1/(n+1)) * Σ_{j=0}^n g(ω_{j+1})
    -- But ω_{j+1} = (shift ω)_j, so A'_{n+1}(ω) = A_n(shift ω)
    -- Let A_n(ω) = (1/(n+1)) * Σ_{j=0}^n g(ω_j)
    let A : ℕ → Ω[α] → ℝ := fun n ω =>
      (1 / ((n + 1) : ℝ)) * (Finset.range (n + 1)).sum (fun j => g (ω j))
    -- By L1_cesaro_convergence: A_n → Y in L¹
    have hg_int : Integrable (fun ω => g (ω 0)) μ :=
      integrable_of_bounded_measurable
        (hg_meas.comp (measurable_pi_apply 0)) Cg (fun ω => hCg (ω 0))
    have h_A_to_Y := L1_cesaro_convergence hσ g hg_meas hg_int
    -- A'_{n+1}(ω) = A_n(shift ω)
    have h_eq : ∀ n ω, A' (n + 1) ω = A n (shift ω) := by
      intro n ω
      simp only [A', if_neg (Nat.succ_ne_zero n), A]
      -- LHS: (1/(n+1)) * Σ_{j < n+1} g(ω_{j+1})
      -- RHS: (1/(n+1)) * Σ_{j < n+1} g((shift ω)_j)
      -- These are equal since (shift ω)_j = ω_{j+1}
      simp only [Nat.cast_add, Nat.cast_one, shift_apply]
    -- Change of variables: ∫|A'_{n+1} - Y| = ∫|A_n ∘ shift - Y ∘ shift|
    -- But Y is shift-invariant! So Y ∘ shift =ᵐ Y
    have hY_inv : (fun ω => Y (shift ω)) =ᵐ[μ] Y := by
      -- Y = CE[g(ω_0)|mSI], and CE is mSI-measurable
      -- shift preserves mSI, so Y ∘ shift =ᵃᵉ Y
      -- Use the lemma from InvariantSigma.lean that says:
      -- AEStronglyMeasurable[mSI] f μ → (f ∘ shift =ᵃᵉ f)
      have hY_aesm : AEStronglyMeasurable[mSI] Y μ :=
        stronglyMeasurable_condExp.aestronglyMeasurable
      exact shiftInvariantSigma_aestronglyMeasurable_ae_shift_eq hσ hY_aesm
    -- Now use measure preservation
    have h_mp : ∀ n, ∫ ω, |A n (shift ω) - Y ω| ∂μ = ∫ ω, |A n ω - Y ω| ∂μ := by
      intro n
      have h1 : (fun ω => |A n (shift ω) - Y ω|)
                =ᵐ[μ] (fun ω => |A n (shift ω) - Y (shift ω)|) := by
        filter_upwards [hY_inv] with ω hω
        simp [hω]
      rw [integral_congr_ae h1]
      -- ∫ f ∘ shift dμ = ∫ f dμ by measure preservation
      -- Using integral_map: ∫ h d(μ.map shift) = ∫ (h ∘ shift) dμ
      -- Since hσ.map_eq : μ.map shift = μ, we get ∫ h dμ = ∫ (h ∘ shift) dμ
      have hh_asm : AEStronglyMeasurable (fun ω => |A n ω - Y ω|) μ := by
        have hA_meas : Measurable (A n) := by
          apply Measurable.mul
          · exact measurable_const
          · apply Finset.measurable_sum
            intro j _
            exact hg_meas.comp (measurable_pi_apply j)
        have h_diff : AEStronglyMeasurable (fun ω => A n ω - Y ω) μ :=
          hA_meas.aestronglyMeasurable.sub integrable_condExp.aestronglyMeasurable
        exact continuous_abs.comp_aestronglyMeasurable h_diff
      -- By integral_map: ∫ f d(μ.map g) = ∫ (f ∘ g) dμ (reversed is what we need)
      have hh_asm' : AEStronglyMeasurable (fun ω => |A n ω - Y ω|) (μ.map shift) := by
        rw [hσ.map_eq]; exact hh_asm
      have h_int_map := integral_map hσ.measurable.aemeasurable hh_asm'
      -- Rewrite: ∫ (h ∘ shift) dμ = ∫ h d(μ.map shift) = ∫ h dμ
      rw [h_int_map.symm, hσ.map_eq]
    -- Conclude
    simp_rw [h_eq, h_mp]
    exact h_A_to_Y

  -- (3) CE Lipschitz: CE[f·A'_n] → CE[f·Y]
  have h_L1_CE : Tendsto (fun n =>
      ∫ ω, |μ[(fun ω' => f (ω' 0) * A' (n + 1) ω') | mSI] ω
           - μ[(fun ω' => f (ω' 0) * Y ω') | mSI] ω| ∂μ) atTop (𝓝 0) := by
    -- Use ce_lipschitz_convergence with A' shifted by 1
    have h_int : Integrable (fun ω => g (ω 0)) μ :=
      integrable_of_bounded_measurable (hg_meas.comp (measurable_pi_apply 0)) Cg (fun ω => hCg (ω 0))
    -- A'_{n+1} has the form (1/(n+1)) * Σ_{j=0}^n g(shift ω)_j = A_n(shift ω)
    -- Need to relate to ce_lipschitz_convergence format
    -- ce_lipschitz_convergence needs: A_n defined as (1/(n+1)) * Σ g(ω_j)
    -- We have: A'_{n+1} = A_n ∘ shift
    -- Apply the bound: ∫|CE[f·A'_{n+1}] - CE[f·Y]| ≤ Cf · ∫|A'_{n+1} - Y|
    -- Since A'_{n+1} - Y → 0 in L¹, the conclusion follows
    have h_bd : ∀ n, ∫ ω, |μ[(fun ω' => f (ω' 0) * A' (n + 1) ω') | mSI] ω
                        - μ[(fun ω' => f (ω' 0) * Y ω') | mSI] ω| ∂μ
                  ≤ Cf * ∫ ω, |A' (n + 1) ω - Y ω| ∂μ := by
      intro n
      -- Integrability of f(ω_0) * A'_{n+1}
      have hA'_int : ∀ n, 0 < n → Integrable (A' n) μ := by
        intro m hm
        simp only [A', if_neg (Nat.ne_of_gt hm)]
        have h_sum : Integrable (fun ω => (Finset.range m).sum (fun j => g (ω (j + 1)))) μ :=
          integrable_finset_sum (Finset.range m) (fun j _ =>
            integrable_of_bounded_measurable
              (hg_meas.comp (measurable_pi_apply (j + 1))) Cg (fun ω => hCg (ω (j + 1))))
        exact h_sum.smul (1 / (m : ℝ))
      have hfA_int : Integrable (fun ω => f (ω 0) * A' (n + 1) ω) μ := by
        refine integrable_mul_of_ae_bdd_left ?_ ?_ (hA'_int (n + 1) (Nat.succ_pos n))
        · exact hf_meas.comp (measurable_pi_apply 0)
        · exact ⟨Cf, ae_of_all μ (fun ω => hCf (ω 0))⟩
      have hfY_int : Integrable (fun ω => f (ω 0) * Y ω) μ := by
        refine integrable_mul_of_ae_bdd_left ?_ ?_ integrable_condExp
        · exact hf_meas.comp (measurable_pi_apply 0)
        · exact ⟨Cf, ae_of_all μ (fun ω => hCf (ω 0))⟩
      -- CE Lipschitz
      have h1 : ∫ ω, |μ[(fun ω' => f (ω' 0) * A' (n + 1) ω') | mSI] ω
                    - μ[(fun ω' => f (ω' 0) * Y ω') | mSI] ω| ∂μ
              ≤ ∫ ω, |f (ω 0) * A' (n + 1) ω - f (ω 0) * Y ω| ∂μ :=
        condExp_L1_lipschitz hfA_int hfY_int
      -- Factor bound
      have h2 : ∫ ω, |f (ω 0) * A' (n + 1) ω - f (ω 0) * Y ω| ∂μ
              ≤ Cf * ∫ ω, |A' (n + 1) ω - Y ω| ∂μ := by
        have h_eq : ∀ ω, |f (ω 0) * A' (n + 1) ω - f (ω 0) * Y ω| = |f (ω 0)| * |A' (n + 1) ω - Y ω| := by
          intro ω; rw [← mul_sub, abs_mul]
        have hpt : ∀ᵐ ω ∂μ, |f (ω 0)| * |A' (n + 1) ω - Y ω| ≤ Cf * |A' (n + 1) ω - Y ω| :=
          ae_of_all μ (fun ω => mul_le_mul_of_nonneg_right (hCf (ω 0)) (abs_nonneg _))
        have hdiff_int : Integrable (fun ω => A' (n + 1) ω - Y ω) μ :=
          (hA'_int (n + 1) (Nat.succ_pos n)).sub integrable_condExp
        have hint_lhs : Integrable (fun ω => |f (ω 0)| * |A' (n + 1) ω - Y ω|) μ := by
          have h_asm : AEStronglyMeasurable (fun ω => |f (ω 0)| * |A' (n + 1) ω - Y ω|) μ := by
            apply AEStronglyMeasurable.mul
            · exact (continuous_abs.measurable.comp (hf_meas.comp (measurable_pi_apply 0))).aestronglyMeasurable
            · exact continuous_abs.comp_aestronglyMeasurable hdiff_int.aestronglyMeasurable
          -- Use norm = abs for real numbers, and |a * b| = |a| * |b| for a, b ≥ 0
          have hpt_norm : ∀ᵐ ω ∂μ, ‖|f (ω 0)| * |A' (n + 1) ω - Y ω|‖ ≤ Cf * |A' (n + 1) ω - Y ω| := by
            filter_upwards [hpt] with ω hω
            rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_abs]
            exact hω
          exact Integrable.mono' (hdiff_int.abs.const_mul Cf) h_asm hpt_norm
        have hint_rhs : Integrable (fun ω => Cf * |A' (n + 1) ω - Y ω|) μ :=
          hdiff_int.abs.const_mul Cf
        calc ∫ ω, |f (ω 0) * A' (n + 1) ω - f (ω 0) * Y ω| ∂μ
            = ∫ ω, |f (ω 0)| * |A' (n + 1) ω - Y ω| ∂μ := by congr 1; ext ω; exact h_eq ω
          _ ≤ ∫ ω, Cf * |A' (n + 1) ω - Y ω| ∂μ := integral_mono_ae hint_lhs hint_rhs hpt
          _ = Cf * ∫ ω, |A' (n + 1) ω - Y ω| ∂μ := integral_const_mul Cf _
      exact le_trans h1 h2
    -- Squeeze
    have h_bound_to_zero : Tendsto (fun n =>
        Cf * ∫ ω, |A' (n + 1) ω - Y ω| ∂μ) atTop (𝓝 0) := by
      convert Tendsto.const_mul Cf h_L1_A'_to_Y using 1
      simp
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h_bound_to_zero ?_ ?_
    · exact fun n => integral_nonneg (fun ω => abs_nonneg _)
    · exact h_bd

  -- (4) Squeeze: constant sequence (= CE[f·g₁]) with L¹ limit 0 implies a.e. equality
  have h_const_is_target : ∀ n, 0 < n →
      μ[(fun ω => f (ω 0) * A' n ω) | mSI]
        =ᵐ[μ]
      μ[(fun ω => f (ω 0) * g (ω 1)) | mSI] := h_product_const

  -- The L¹ integral of |CE[f·A'_{n+1}] - CE[f·Y]| → 0
  -- But CE[f·A'_{n+1}] =ᵃᵉ CE[f·g₁] for all n
  -- So the L¹ integral of |CE[f·g₁] - CE[f·Y]| → 0
  -- A constant sequence with limit 0 must be 0 a.e.
  have h_ae_eq : μ[(fun ω => f (ω 0) * g (ω 1)) | mSI]
                   =ᵐ[μ]
                 μ[(fun ω => f (ω 0) * Y ω) | mSI] := by
    -- Show ∫|CE[f·g₁] - CE[f·Y]| = 0
    have h_zero : ∫ ω, |μ[(fun ω' => f (ω' 0) * g (ω' 1)) | mSI] ω
                      - μ[(fun ω' => f (ω' 0) * Y ω') | mSI] ω| ∂μ = 0 := by
      -- The sequence ∫|CE[f·A'_{n+1}] - CE[f·Y]| → 0
      -- But each CE[f·A'_{n+1}] =ᵃᵉ CE[f·g₁]
      -- So ∫|CE[f·g₁] - CE[f·Y]| ≤ ∫|CE[f·A'_{n+1}] - CE[f·Y]| for each n (up to null sets)
      have h_eq_ae : ∀ n, ∫ ω, |μ[(fun ω' => f (ω' 0) * g (ω' 1)) | mSI] ω
                           - μ[(fun ω' => f (ω' 0) * Y ω') | mSI] ω| ∂μ
                       = ∫ ω, |μ[(fun ω' => f (ω' 0) * A' (n + 1) ω') | mSI] ω
                           - μ[(fun ω' => f (ω' 0) * Y ω') | mSI] ω| ∂μ := by
        intro n
        have h := h_const_is_target (n + 1) (Nat.succ_pos n)
        refine integral_congr_ae ?_
        filter_upwards [h] with ω hω
        simp [hω]
      -- The RHS → 0, so for any ε > 0, there exists N such that RHS < ε
      -- Since the LHS = RHS for all n, the LHS ≤ ε for all ε > 0, hence LHS = 0
      have h_le : ∀ ε > 0, ∫ ω, |μ[(fun ω' => f (ω' 0) * g (ω' 1)) | mSI] ω
                              - μ[(fun ω' => f (ω' 0) * Y ω') | mSI] ω| ∂μ < ε := by
        intro ε hε
        rw [Metric.tendsto_atTop] at h_L1_CE
        obtain ⟨N, hN⟩ := h_L1_CE ε hε
        specialize hN N le_rfl
        rw [Real.dist_0_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => abs_nonneg _))] at hN
        rw [h_eq_ae N]
        exact hN
      have h_nonneg : 0 ≤ ∫ ω, |μ[(fun ω' => f (ω' 0) * g (ω' 1)) | mSI] ω
                           - μ[(fun ω' => f (ω' 0) * Y ω') | mSI] ω| ∂μ :=
        integral_nonneg (fun _ => abs_nonneg _)
      -- 0 ≤ x and (∀ ε > 0, x < ε) implies x = 0
      exact le_antisymm (le_of_forall_pos_lt_add (fun ε hε => by linarith [h_le ε hε])) h_nonneg
    -- ∫|X - Y| = 0 implies X =ᵃᵉ Y for integrable X, Y
    have h_int1 : Integrable (μ[(fun ω' => f (ω' 0) * g (ω' 1)) | mSI]) μ := integrable_condExp
    have h_int2 : Integrable (μ[(fun ω' => f (ω' 0) * Y ω') | mSI]) μ := integrable_condExp
    have h_diff_int : Integrable (fun ω => μ[(fun ω' => f (ω' 0) * g (ω' 1)) | mSI] ω
                                         - μ[(fun ω' => f (ω' 0) * Y ω') | mSI] ω) μ :=
      h_int1.sub h_int2
    -- Use integral_eq_zero_iff_of_nonneg_ae: ∫|f| = 0 ↔ f =ᵃᵉ 0 (for nonneg f)
    have h_nonneg : (0 : Ω[α] → ℝ) ≤ᵐ[μ] fun ω => |μ[(fun ω' => f (ω' 0) * g (ω' 1)) | mSI] ω
                                            - μ[(fun ω' => f (ω' 0) * Y ω') | mSI] ω| :=
      ae_of_all μ (fun ω => abs_nonneg _)
    have h_abs_eq_zero : (fun ω => |μ[(fun ω' => f (ω' 0) * g (ω' 1)) | mSI] ω
                                   - μ[(fun ω' => f (ω' 0) * Y ω') | mSI] ω|) =ᵐ[μ] 0 :=
      (integral_eq_zero_iff_of_nonneg_ae h_nonneg h_diff_int.abs).mp h_zero
    -- |X - Y| =ᵃᵉ 0 implies X - Y =ᵃᵉ 0, hence X =ᵃᵉ Y
    filter_upwards [h_abs_eq_zero] with ω hω
    have : μ[(fun ω' => f (ω' 0) * g (ω' 1)) | mSI] ω
         - μ[(fun ω' => f (ω' 0) * Y ω') | mSI] ω = 0 := abs_eq_zero.mp hω
    linarith

  exact h_ae_eq

set_option maxHeartbeats 1000000

/-- **Pair factorization via MET + Exchangeability** (Kallenberg's approach).

For EXCHANGEABLE measures μ on path space, the conditional expectation of f(ω₀)·g(ω₁)
given the shift-invariant σ-algebra factors into the product of the individual
conditional expectations.

**Proof strategy** (CORRECTED - avoids false k=0 lag constancy):
1. Apply tower property directly on g₁ (via Cesàro from index 1):
   CE[f(ω₀)·g(ω₁)|ℐ] = CE[f(ω₀)·CE[g(ω₀)|ℐ]|ℐ]
   (uses h_tower_of_lagConst_from_one which only needs k ≥ 1 lag constancy)
2. Apply pull-out property: CE[f(ω₀)·CE[g(ω₀)|ℐ]|ℐ] = CE[g(ω₀)|ℐ]·CE[f(ω₀)|ℐ]
   (CE[g(ω₀)|ℐ] is ℐ-measurable)

**Key insight**: This requires EXCHANGEABILITY (via `hExch`), not just stationarity.
The original k=0 lag constancy approach was FALSE. See Infrastructure.lean for details.
-/
lemma condexp_pair_factorization_MET
    {μ : Measure (Ω[α])} [IsProbabilityMeasure μ] [StandardBorelSpace α] [Nonempty α]
    (hσ : MeasurePreserving shift μ μ)
    (hExch : ∀ π : Equiv.Perm ℕ, Measure.map (Exchangeability.reindex π) μ = μ)
    (f g : α → ℝ)
    (hf_meas : Measurable f) (hf_bd : ∃ C, ∀ x, |f x| ≤ C)
    (hg_meas : Measurable g) (hg_bd : ∃ C, ∀ x, |g x| ≤ C) :
  μ[(fun ω => f (ω 0) * g (ω 1)) | shiftInvariantSigma (α := α)]
    =ᵐ[μ]
  (fun ω => μ[fun ω => f (ω 0) | shiftInvariantSigma (α := α)] ω
          * μ[fun ω => g (ω 0) | shiftInvariantSigma (α := α)] ω) := by
  -- Note: mSI is already defined as a local notation for shiftInvariantSigma (α := α)
  -- Step 1: Tower property via Cesàro from index 1 (CORRECTED - avoids k=0!)
  -- CE[f(ω₀)·g(ω₁)|ℐ] = CE[f(ω₀)·CE[g(ω₀)|ℐ]|ℐ]
  -- Uses h_tower_of_lagConst_from_one which only requires k ≥ 1 lag constancy
  have h_tower : μ[(fun ω => f (ω 0) * g (ω 1)) | mSI]
      =ᵐ[μ] μ[(fun ω => f (ω 0) * μ[(fun ω => g (ω 0)) | mSI] ω) | mSI] :=
    h_tower_of_lagConst_from_one hσ hExch f g hf_meas hf_bd hg_meas hg_bd

  -- Step 2: Pull-out property (CE[g(ω₀)|ℐ] is ℐ-measurable)
  -- CE[f(ω₀)·CE[g(ω₀)|ℐ]|ℐ] = CE[g(ω₀)|ℐ]·CE[f(ω₀)|ℐ]
  have h_pullout : μ[(fun ω => f (ω 0) * μ[(fun ω => g (ω 0)) | mSI] ω) | mSI]
      =ᵐ[μ] (fun ω => μ[(fun ω => g (ω 0)) | mSI] ω * μ[(fun ω => f (ω 0)) | mSI] ω) := by
    set Z := μ[(fun ω => g (ω 0)) | mSI]
    have hZ_meas : Measurable[mSI] Z := stronglyMeasurable_condExp.measurable
    obtain ⟨Cg, hCg⟩ := hg_bd
    have hZ_bd : ∃ C, ∀ᵐ ω ∂μ, |Z ω| ≤ C := by
      use Cg
      have hg_int : Integrable (fun ω => g (ω 0)) μ := by
        constructor
        · exact (hg_meas.comp (measurable_pi_apply 0)).aestronglyMeasurable
        · exact HasFiniteIntegral.of_bounded (ae_of_all μ (fun ω => hCg (ω 0)))
      have hCg_nn : 0 ≤ Cg := le_trans (abs_nonneg _) (hCg (Classical.choice ‹Nonempty α›))
      have hCg_ae' : ∀ᵐ ω ∂μ, |g (ω 0)| ≤ Cg.toNNReal := by
        filter_upwards with ω
        rw [Real.coe_toNNReal _ hCg_nn]
        exact hCg (ω 0)
      have := ae_bdd_condExp_of_ae_bdd (m := mSI) hCg_ae'
      filter_upwards [this] with ω hω; rwa [Real.coe_toNNReal _ hCg_nn] at hω
    obtain ⟨Cf, hCf⟩ := hf_bd
    have hY_int : Integrable (fun ω => f (ω 0)) μ := by
      constructor
      · exact (hf_meas.comp (measurable_pi_apply 0)).aestronglyMeasurable
      · exact HasFiniteIntegral.of_bounded (ae_of_all μ (fun ω => hCf (ω 0)))
    have h := condExp_mul_pullout hZ_meas hZ_bd hY_int
    calc μ[(fun ω => f (ω 0) * Z ω) | mSI]
        =ᵐ[μ] μ[(fun ω => Z ω * f (ω 0)) | mSI] := by
          have : (fun ω => f (ω 0) * Z ω) = (fun ω => Z ω * f (ω 0)) := by ext ω; ring
          rw [this]
      _ =ᵐ[μ] (fun ω => Z ω * μ[(fun ω => f (ω 0)) | mSI] ω) := h

  -- Combine all steps
  calc μ[(fun ω => f (ω 0) * g (ω 1)) | mSI]
      =ᵐ[μ] μ[(fun ω => f (ω 0) * μ[(fun ω => g (ω 0)) | mSI] ω) | mSI] := h_tower
    _ =ᵐ[μ] (fun ω => μ[(fun ω => g (ω 0)) | mSI] ω * μ[(fun ω => f (ω 0)) | mSI] ω) := h_pullout
    _ =ᵐ[μ] (fun ω => μ[(fun ω => f (ω 0)) | mSI] ω * μ[(fun ω => g (ω 0)) | mSI] ω) := by
        filter_upwards with ω; ring

-- Kernel independence lemmas are in section "Filled proofs of kernel independence lemmas"
-- below, after coord_indicator_via_ν is defined. The lemmas are:
--   kernel_indep_pair_01, kernel_indep_pair, kernel_indep_finset

end OptionB_L1Convergence

end Exchangeability.DeFinetti.ViaKoopman
