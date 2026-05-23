/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Exchangeability.DeFinetti.ViaL2.BlockAverages
import Exchangeability.DeFinetti.L2Helpers
import Exchangeability.Contractability
import Exchangeability.ConditionallyIID
import Exchangeability.Probability.CondExp
import Exchangeability.Probability.IntegrationHelpers
import Exchangeability.Tail.TailSigma
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.AEEqFun
import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.Kernel.Disintegration.CondCDF
import Mathlib.Probability.Kernel.Disintegration.MeasurableStieltjes
import Mathlib.Probability.CDF

/-!
# Main Convergence Theorems via L² Approach

This file contains the main L¹ convergence theorem for the L² proof of de Finetti's
theorem. The directing measure itself and the packaging theorem
`directing_measure_satisfies_requirements` now live in `DirectingMeasureCore.lean`
and `MoreL2Helpers.lean` respectively.

## Main results

* `weighted_sums_converge_L1`: Weighted sums converge in L¹ for contractable sequences

## References

* Kallenberg (2005), *Probabilistic Symmetries and Invariance Principles*,
  Chapter 1, "Second proof of Theorem 1.1"
-/

noncomputable section

namespace Exchangeability.DeFinetti.ViaL2

open MeasureTheory ProbabilityTheory BigOperators Filter Topology
open Exchangeability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-!
## L¹ convergence via reverse martingale (main convergence theorem)
-/

/-- **Weighted sums converge in L¹ for contractable sequences.**

For a contractable sequence X and bounded measurable f, the Cesàro averages
`(1/m) * ∑_{i<m} f(X_{n+i+1})` converge in L¹ to a limit α : Ω → ℝ that does not depend on n.

This is the key convergence result needed for de Finetti's theorem via the L² approach.
The proof uses L² contractability bounds to show the averages form a Cauchy sequence in L¹. -/
theorem weighted_sums_converge_L1
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (_hX_L2 : ∀ i, MemLp (X i) 2 μ)
    (f : ℝ → ℝ) (hf_meas : Measurable f)
    (hf_bdd : ∃ M, ∀ x, |f x| ≤ M) :
    ∃ (alpha : Ω → ℝ),  -- SINGLE alpha, not a sequence!
      Measurable alpha ∧ MemLp alpha 1 μ ∧
      -- The weighted sums converge to alpha in L¹ (for ANY starting index n)
      (∀ n, ∀ ε > 0, ∃ M : ℕ, ∀ m : ℕ, m ≥ M →
        ∫ ω, |(1/(m:ℝ)) * ∑ k : Fin m, f (X (n + k.val + 1) ω) - alpha ω| ∂μ < ε) := by
  classical

  -- Define the moving averages A n m
  let A : ℕ → ℕ → Ω → ℝ :=
    fun n m ω => (1 / (m : ℝ)) * ∑ k : Fin m, f (X (n + k.val + 1) ω)

  -- A n m is measurable for all n, m
  have hA_meas : ∀ n m, Measurable (A n m) := by
    intro n m
    simp only [A]
    fun_prop

  -- A n m is in L¹ for all n, m (bounded measurable on probability space)
  have hA_memLp : ∀ n m, MemLp (A n m) 1 μ := by
    intro n m
    obtain ⟨M, hM⟩ := hf_bdd
    -- On probability spaces, the integral of |A n m| is bounded by M
    -- since |A n m ω| ≤ M for all ω and μ is a probability measure
    have hA_ae_bdd : ∀ᵐ ω ∂μ, ‖A n m ω‖ ≤ M := by
      filter_upwards with ω
      simp only [A, Real.norm_eq_abs]
      -- Average of values bounded by M is bounded by M
      calc |(1 / (m : ℝ)) * ∑ k : Fin m, f (X (n + k.val + 1) ω)|
          ≤ (1 / (m : ℝ)) * ∑ k : Fin m, |f (X (n + k.val + 1) ω)| := by
            classical
            by_cases hm : m = 0
            · simp [hm]
            · have hm_pos : 0 < (m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hm
              have h_inv_pos : 0 < 1 / (m : ℝ) := by
                exact div_pos (by norm_num) hm_pos
              have h_abs_sum :
                  |∑ k : Fin m, f (X (n + k.val + 1) ω)|
                    ≤ ∑ k : Fin m, |f (X (n + k.val + 1) ω)| :=
                Finset.abs_sum_le_sum_abs
                  (fun k : Fin m => f (X (n + k.val + 1) ω))
                  Finset.univ
              have h_inv_abs : |1 / (m : ℝ)| = 1 / (m : ℝ) :=
                abs_of_pos h_inv_pos
              calc
                |(1 / (m : ℝ)) * ∑ k : Fin m, f (X (n + k.val + 1) ω)|
                    = (1 / (m : ℝ)) *
                        |∑ k : Fin m, f (X (n + k.val + 1) ω)| := by
                      simp [abs_mul]
                _ ≤ (1 / (m : ℝ)) *
                        ∑ k : Fin m, |f (X (n + k.val + 1) ω)| := by
                      exact
                        (mul_le_mul_of_nonneg_left h_abs_sum
                          (le_of_lt h_inv_pos))
        _ ≤ (1 / (m : ℝ)) * ∑ k : Fin m, M := by
            classical
            by_cases hm : m = 0
            · simp [hm]
            · have h_inv_nonneg : 0 ≤ 1 / (m : ℝ) := by
                have hm_pos : 0 < (m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hm
                exact le_of_lt (div_pos (by norm_num) hm_pos)
              have h_sum_le :
                  ∑ k : Fin m, |f (X (n + k.val + 1) ω)|
                    ≤ ∑ k : Fin m, M := by
                refine Finset.sum_le_sum ?_
                intro k _
                exact hM _
              exact (mul_le_mul_of_nonneg_left h_sum_le h_inv_nonneg)
        _ ≤ M := by
            classical
            by_cases hm : m = 0
            · have hM_nonneg : 0 ≤ M :=
                (le_trans (abs_nonneg _) (hM 0))
              simp [hm, hM_nonneg]
            · have : (1 / (m : ℝ)) * ∑ k : Fin m, M = M := by
                simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
                field_simp [Nat.cast_ne_zero.mpr hm]
                ring
              rw [this]
    exact MemLp.of_bound (hA_meas n m).aestronglyMeasurable M hA_ae_bdd

  -- A n m is also in L² (bounded functions on probability spaces)
  have hA_memLp_two : ∀ n m, MemLp (A n m) 2 μ := by
    intro n m
    obtain ⟨M, hM⟩ := hf_bdd
    have hA_ae_bdd : ∀ᵐ ω ∂μ, ‖A n m ω‖ ≤ M := by
      filter_upwards with ω
      simp only [A, Real.norm_eq_abs]
      -- Same bound as L¹ case
      classical
      by_cases hm : m = 0
      · simp [hm]; exact le_trans (abs_nonneg _) (hM 0)
      · calc |(1 / (m : ℝ)) * ∑ k : Fin m, f (X (n + k.val + 1) ω)|
            ≤ (1 / (m : ℝ)) * ∑ k : Fin m, |f (X (n + k.val + 1) ω)| := by
              have hm_pos : 0 < (m : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm)
              rw [abs_mul, abs_of_pos (div_pos zero_lt_one hm_pos)]
              exact mul_le_mul_of_nonneg_left
                (Finset.abs_sum_le_sum_abs _ _) (le_of_lt (div_pos zero_lt_one hm_pos))
          _ ≤ (1 / (m : ℝ)) * ∑ k : Fin m, M := by
              gcongr; exact hM _
          _ = M := by
              simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
              field_simp [Nat.cast_ne_zero.mpr hm]
              ring
    exact MemLp.of_bound (hA_meas n m).aestronglyMeasurable M hA_ae_bdd

  -- **Phase 2: Compute covariance structure once and pass to both lemmas**
  -- This eliminates the need to prove Cf = Cf_tail (they're the same by construction!)
  obtain ⟨Cf, mf, σSqf, ρf, hCf_def, hCf_nonneg, hmean, hvar, hcov, hσSq_nn, hρ_bd1, hρ_bd2⟩ :=
    get_covariance_constant X hX_contract hX_meas f hf_meas hf_bdd

  -- Apply l2_bound_two_windows_uniform with the shared covariance structure
  have h_window_bound :=
    l2_bound_two_windows_uniform X hX_meas f hf_meas hf_bdd
      Cf mf σSqf ρf hCf_def hmean hvar hcov hσSq_nn ⟨hρ_bd1, hρ_bd2⟩

  let Y : ℕ → Ω → ℝ := fun t ω => f (X t ω)

  -- Long average vs tail average bound with the same constant Cf
  -- ✅ Both lemmas now use the SAME Cf by construction → no proof needed!
  have h_long_tail_bound :
      ∀ {n m k : ℕ}, 0 < k → k ≤ m →
        ∫ ω,
            ((1 / (m : ℝ)) * ∑ i : Fin m, f (X (n + i.val + 1) ω) -
             (1 / (k : ℝ)) *
               ∑ i : Fin k, f (X (n + (m - k) + i.val + 1) ω))^2 ∂μ
          ≤ Cf / k := by
    intro n m k hk hkm
    exact l2_bound_long_vs_tail X hX_meas f hf_meas hf_bdd
      Cf mf σSqf ρf hCf_def hmean hvar hcov hσSq_nn ⟨hρ_bd1, hρ_bd2⟩
      n m k hk hkm

  -- Step 1: For n=0, show (A 0 m)_m is Cauchy in L² hence L¹
  have hA_cauchy_L2_0 : ∀ ε > 0, ∃ N, ∀ m ℓ, m ≥ N → ℓ ≥ N →
      eLpNorm (fun ω => A 0 m ω - A 0 ℓ ω) 2 μ < ENNReal.ofReal ε := by
    intro ε hε

    -- 3-segment decomposition strategy:
    -- For m, ℓ ≥ 2N with k = N, decompose ‖A 0 m - A 0 ℓ‖₂ via triangle inequality:
    -- ‖A 0 m - A 0 ℓ‖₂ ≤ ‖A 0 m - A (m-k) k‖₂ + ‖A (m-k) k - A (ℓ-k) k‖₂ + ‖A (ℓ-k) k - A 0 ℓ‖₂
    --
    -- Each segment bounded by √(Cf/k):
    -- - Segments 1 & 3: h_long_tail_bound (long avg vs tail avg) → ∫ (...)² ≤ Cf/k
    -- - Segment 2: h_window_bound (two equal-size windows) → ∫ (...)² ≤ Cf/k
    --
    -- Total bound: 3√(Cf/k) < ε
    -- Required: k > 9Cf/ε²

    let k := Nat.ceil (9 * Cf / (ε ^ 2)) + 1
    have hk_pos : 0 < k := Nat.succ_pos _

    -- Require m, ℓ ≥ 2k to ensure k ≤ m and k ≤ ℓ
    refine ⟨2 * k, ?_⟩
    intro m ℓ hm hℓ

    have hk_le_m : k ≤ m := by omega
    have hk_le_ℓ : k ≤ ℓ := by omega

    -- Segment 1: ‖A 0 m - A (m-k) k‖₂² ≤ Cf/k
    have h1 : ∫ ω, (A 0 m ω - A (m - k) k ω)^2 ∂μ ≤ Cf / k := by
      have h := @h_long_tail_bound 0 m k hk_pos hk_le_m
      convert h using 2
      ext ω
      simp only [A]
      congr 2; congr 1; apply Finset.sum_congr rfl; intro i _; congr; omega

    -- Segment 2: ‖A (m-k) k - A (ℓ-k) k‖₂² ≤ Cf/k
    have h2 : ∫ ω, (A (m - k) k ω - A (ℓ - k) k ω)^2 ∂μ ≤ Cf / k := by
      simpa only [A] using @h_window_bound (m - k) (ℓ - k) k hk_pos

    -- Segment 3: ‖A (ℓ-k) k - A 0 ℓ‖₂² ≤ Cf/k
    have h3 : ∫ ω, (A (ℓ - k) k ω - A 0 ℓ ω)^2 ∂μ ≤ Cf / k := by
      have h_sq : ∫ ω, (A 0 ℓ ω - A (ℓ - k) k ω)^2 ∂μ ≤ Cf / k := by
        have h := @h_long_tail_bound 0 ℓ k hk_pos hk_le_ℓ
        convert h using 2
        ext ω
        simp only [A]
        congr 2; congr 1; apply Finset.sum_congr rfl; intro i _; congr; omega
      have : ∀ ω, (A (ℓ - k) k ω - A 0 ℓ ω)^2 = (A 0 ℓ ω - A (ℓ - k) k ω)^2 := by
        intro ω; ring
      simp_rw [this]; exact h_sq

    -- Convert to eLpNorm bounds
    have h1_norm : eLpNorm (fun ω => A 0 m ω - A (m - k) k ω) 2 μ
        ≤ ENNReal.ofReal (Real.sqrt (Cf / k)) := by
      apply L2Helpers.eLpNorm_two_from_integral_sq_le
      · exact (hA_memLp_two 0 m).sub (hA_memLp_two (m - k) k)
      · apply div_nonneg hCf_nonneg; exact Nat.cast_nonneg k
      · exact h1

    have h2_norm : eLpNorm (fun ω => A (m - k) k ω - A (ℓ - k) k ω) 2 μ
        ≤ ENNReal.ofReal (Real.sqrt (Cf / k)) := by
      apply L2Helpers.eLpNorm_two_from_integral_sq_le
      · exact (hA_memLp_two (m - k) k).sub (hA_memLp_two (ℓ - k) k)
      · apply div_nonneg hCf_nonneg; exact Nat.cast_nonneg k
      · exact h2

    have h3_norm : eLpNorm (fun ω => A (ℓ - k) k ω - A 0 ℓ ω) 2 μ
        ≤ ENNReal.ofReal (Real.sqrt (Cf / k)) := by
      apply L2Helpers.eLpNorm_two_from_integral_sq_le
      · exact (hA_memLp_two (ℓ - k) k).sub (hA_memLp_two 0 ℓ)
      · apply div_nonneg hCf_nonneg; exact Nat.cast_nonneg k
      · exact h3

    -- Apply triangle inequality and combine
    calc eLpNorm (fun ω => A 0 m ω - A 0 ℓ ω) 2 μ
        = eLpNorm (fun ω => (A 0 m ω - A (m - k) k ω) +
                            (A (m - k) k ω - A (ℓ - k) k ω) +
                            (A (ℓ - k) k ω - A 0 ℓ ω)) 2 μ := by
          congr 1; ext ω; ring
      _ ≤ eLpNorm (fun ω => A 0 m ω - A (m - k) k ω) 2 μ +
          eLpNorm (fun ω => A (m - k) k ω - A (ℓ - k) k ω) 2 μ +
          eLpNorm (fun ω => A (ℓ - k) k ω - A 0 ℓ ω) 2 μ := by
          -- Apply triangle inequality twice: ‖f + g + h‖ ≤ ‖f + g‖ + ‖h‖ ≤ ‖f‖ + ‖g‖ + ‖h‖
          have h_decomp : (fun ω => (A 0 m ω - A (m - k) k ω) +
                                     (A (m - k) k ω - A (ℓ - k) k ω) +
                                     (A (ℓ - k) k ω - A 0 ℓ ω)) =
              fun ω => ((A 0 m ω - A (m - k) k ω) +
                        (A (m - k) k ω - A (ℓ - k) k ω)) +
                       (A (ℓ - k) k ω - A 0 ℓ ω) := by
            ext ω; ring
          rw [h_decomp]
          calc eLpNorm (fun ω => ((A 0 m ω - A (m - k) k ω) +
                                  (A (m - k) k ω - A (ℓ - k) k ω)) +
                                 (A (ℓ - k) k ω - A 0 ℓ ω)) 2 μ
              ≤ eLpNorm (fun ω => (A 0 m ω - A (m - k) k ω) +
                                  (A (m - k) k ω - A (ℓ - k) k ω)) 2 μ +
                eLpNorm (fun ω => A (ℓ - k) k ω - A 0 ℓ ω) 2 μ := by
                  apply eLpNorm_add_le
                  · exact ((hA_meas 0 m).sub (hA_meas (m - k) k)).add
                          ((hA_meas (m - k) k).sub (hA_meas (ℓ - k) k)) |>.aestronglyMeasurable
                  · exact (hA_meas (ℓ - k) k).sub (hA_meas 0 ℓ) |>.aestronglyMeasurable
                  · norm_num
            _ ≤ eLpNorm (fun ω => A 0 m ω - A (m - k) k ω) 2 μ +
                eLpNorm (fun ω => A (m - k) k ω - A (ℓ - k) k ω) 2 μ +
                eLpNorm (fun ω => A (ℓ - k) k ω - A 0 ℓ ω) 2 μ := by
                  gcongr
                  apply eLpNorm_add_le
                  · exact (hA_meas 0 m).sub (hA_meas (m - k) k) |>.aestronglyMeasurable
                  · exact (hA_meas (m - k) k).sub (hA_meas (ℓ - k) k) |>.aestronglyMeasurable
                  · norm_num
      _ ≤ ENNReal.ofReal (3 * Real.sqrt (Cf / k)) := by
          -- Each term bounded by √(Cf/k), so sum bounded by 3√(Cf/k)
          calc eLpNorm (fun ω => A 0 m ω - A (m - k) k ω) 2 μ +
               eLpNorm (fun ω => A (m - k) k ω - A (ℓ - k) k ω) 2 μ +
               eLpNorm (fun ω => A (ℓ - k) k ω - A 0 ℓ ω) 2 μ
              ≤ ENNReal.ofReal (Real.sqrt (Cf / k)) +
                ENNReal.ofReal (Real.sqrt (Cf / k)) +
                ENNReal.ofReal (Real.sqrt (Cf / k)) := by
                  gcongr
            _ = ENNReal.ofReal (3 * Real.sqrt (Cf / k)) := by
                  set r : ℝ := Real.sqrt (Cf / k)
                  have hr_nonneg : 0 ≤ r := Real.sqrt_nonneg _
                  -- Add three ofReal r terms
                  calc ENNReal.ofReal r + ENNReal.ofReal r + ENNReal.ofReal r
                      = (ENNReal.ofReal r + ENNReal.ofReal r) + ENNReal.ofReal r := by
                          rfl
                    _ = ENNReal.ofReal (r + r) + ENNReal.ofReal r := by
                          rw [ENNReal.ofReal_add hr_nonneg hr_nonneg]
                    _ = ENNReal.ofReal ((r + r) + r) := by
                          have h2r : 0 ≤ r + r := by linarith
                          rw [ENNReal.ofReal_add h2r hr_nonneg]
                    _ = ENNReal.ofReal (3 * r) := by
                          congr 1; ring
      _ < ENNReal.ofReal ε := by
          -- Show 3√(Cf/k) < ε using k > 9Cf/ε²
          have hε_pos : 0 < ε := hε
          -- First establish k > 9Cf/ε²
          have h_k_large : 9 * Cf / ε ^ 2 < (k : ℝ) := by
            have h_ceil : 9 * Cf / ε ^ 2 ≤ Nat.ceil (9 * Cf / ε ^ 2) := Nat.le_ceil _
            have h_succ : (Nat.ceil (9 * Cf / ε ^ 2) : ℝ) < k := by
              simp only [k]
              norm_cast
              omega
            linarith
          -- Now show Cf/k < ε²/9
          have h_frac : Cf / k < ε ^ 2 / 9 := by
            have hk_pos_real : 0 < (k : ℝ) := Nat.cast_pos.mpr hk_pos
            have h_nine_pos : (0 : ℝ) < 9 := by norm_num
            by_cases hCf_zero : Cf = 0
            · rw [hCf_zero]
              simp only [zero_div]
              exact div_pos (sq_pos_of_pos hε_pos) h_nine_pos
            · have hCf_pos : 0 < Cf := by
                rcases hCf_nonneg.lt_or_eq with h | h
                · exact h
                · exact absurd h.symm hCf_zero
              have h_denom : 0 < 9 * Cf / ε ^ 2 := by
                apply div_pos
                · exact mul_pos h_nine_pos hCf_pos
                · exact sq_pos_of_pos hε_pos
              have h_eq : Cf / (9 * Cf / ε ^ 2) = ε ^ 2 / 9 := by field_simp
              calc Cf / k < Cf / (9 * Cf / ε ^ 2) := div_lt_div_of_pos_left hCf_pos h_denom h_k_large
                _ = ε ^ 2 / 9 := h_eq
          -- So √(Cf/k) < ε/3
          have h_sqrt : Real.sqrt (Cf / k) < ε / 3 := by
            have h_bound : Cf / k < (ε / 3) ^ 2 := by
              calc Cf / k < ε ^ 2 / 9 := h_frac
                _ = (ε / 3) ^ 2 := by ring
            have hε3_pos : 0 < ε / 3 := by linarith
            rw [← Real.sqrt_sq (le_of_lt hε3_pos)]
            exact Real.sqrt_lt_sqrt (div_nonneg hCf_nonneg (Nat.cast_nonneg k)) h_bound
          -- Therefore 3√(Cf/k) < ε
          have h_real : 3 * Real.sqrt (Cf / k) < ε := by
            calc 3 * Real.sqrt (Cf / k)
                < 3 * (ε / 3) := mul_lt_mul_of_pos_left h_sqrt (by norm_num : (0 : ℝ) < 3)
              _ = ε := by ring
          -- Lift to ENNReal
          exact ENNReal.ofReal_lt_ofReal_iff hε_pos |>.mpr h_real

  have hA_cauchy_L1_0 : ∀ ε > 0, ∃ N, ∀ m ℓ, m ≥ N → ℓ ≥ N →
      eLpNorm (fun ω => A 0 m ω - A 0 ℓ ω) 1 μ < ENNReal.ofReal ε := by
    intro ε hε
    rcases hA_cauchy_L2_0 ε hε with ⟨N, hN⟩
    refine ⟨N, fun m ℓ hm hℓ => ?_⟩
    calc eLpNorm (fun ω => A 0 m ω - A 0 ℓ ω) 1 μ
        ≤ eLpNorm (fun ω => A 0 m ω - A 0 ℓ ω) 2 μ := by
          apply eLpNorm_le_eLpNorm_of_exponent_le
          · norm_num
          · exact (hA_meas 0 m).sub (hA_meas 0 ℓ) |>.aestronglyMeasurable
      _ < ENNReal.ofReal ε := hN m ℓ hm hℓ

  -- Step 2: Completeness of L¹ gives α₀ as the limit of the base averages.
  have h_exist_alpha_0 :
      ∃ alpha_0 : Ω → ℝ, Measurable alpha_0 ∧ MemLp alpha_0 1 μ ∧
        (∀ ε > 0, ∃ M, ∀ m ≥ M,
          eLpNorm (fun ω => A 0 m ω - alpha_0 ω) 1 μ < ENNReal.ofReal ε) := by
    classical
    -- View the base averages as a sequence in L¹.
    let F : ℕ → Lp ℝ 1 μ := fun m => (hA_memLp 0 m).toLp (A 0 m)
    -- Show this sequence is Cauchy.
    have hCauchy : CauchySeq F := by
      rw [Metric.cauchySeq_iff]
      intro ε hε
      obtain ⟨N, hN⟩ := hA_cauchy_L1_0 ε hε
      refine ⟨N, fun m hm ℓ hℓ => ?_⟩
      have hdist :
          dist (F m) (F ℓ) =
            ENNReal.toReal (eLpNorm (fun ω => A 0 m ω - A 0 ℓ ω) 1 μ) := by
        simpa [F] using
          L2Helpers.dist_toLp_eq_eLpNorm_sub (hA_memLp 0 m) (hA_memLp 0 ℓ)
      have hfin :
          eLpNorm (fun ω => A 0 m ω - A 0 ℓ ω) 1 μ ≠ ⊤ :=
        (MemLp.sub (hA_memLp 0 m) (hA_memLp 0 ℓ)).eLpNorm_ne_top
      have hbound := hN m ℓ hm hℓ
      have hlt :
          ENNReal.toReal (eLpNorm (fun ω => A 0 m ω - A 0 ℓ ω) 1 μ) < ε :=
        L2Helpers.toReal_lt_of_lt_ofReal hfin (le_of_lt hε) hbound
      simpa [hdist]
    -- Since L¹ is complete, the sequence converges to some `G`.
    rcases CompleteSpace.complete (show Cauchy (atTop.map F) from hCauchy) with ⟨G, hG⟩
    have hG' : Tendsto F atTop (𝓝 G) := hG
    -- Choose a measurable representative of `G`.
    let alpha : Ω → ℝ := (Lp.aestronglyMeasurable G).mk G
    have h_alpha_ae : G =ᵐ[μ] alpha :=
      (Lp.aestronglyMeasurable G).ae_eq_mk
    have halpha_meas : Measurable alpha :=
      (Lp.aestronglyMeasurable G).measurable_mk
    have halpha_mem : MemLp alpha 1 μ :=
      MemLp.ae_eq h_alpha_ae (Lp.memLp G)
    refine ⟨alpha, halpha_meas, halpha_mem, ?_⟩
    -- Convert convergence in L¹ to convergence of raw functions.
    intro ε hε
    obtain ⟨M, hM⟩ := Metric.tendsto_atTop.mp hG' ε hε
    refine ⟨M, fun m hm => ?_⟩
    have hdist_lt : dist (F m) G < ε := hM m hm
    have hdist :
        dist (F m) G =
          ENNReal.toReal (eLpNorm (fun ω => A 0 m ω - G ω) 1 μ) := by
      simpa [F] using
        L2Helpers.dist_toLp_eq_eLpNorm_sub (hA_memLp 0 m) (Lp.memLp G)
    have hfin :
        eLpNorm (fun ω => A 0 m ω - G ω) 1 μ ≠ ⊤ :=
      (MemLp.sub (hA_memLp 0 m) (Lp.memLp G)).eLpNorm_ne_top
    have htoReal :
        ENNReal.toReal (eLpNorm (fun ω => A 0 m ω - G ω) 1 μ) < ε := by
      simpa [hdist] using hdist_lt
    -- Relate the difference with `alpha` via the a.e. equality.
    have h_sub :
        (fun ω => A 0 m ω - alpha ω) =ᵐ[μ]
          fun ω => A 0 m ω - G ω := by
      filter_upwards [h_alpha_ae] with ω hω
      simp [A, hω]
    have h_eq :
        eLpNorm (fun ω => A 0 m ω - alpha ω) 1 μ =
          eLpNorm (fun ω => A 0 m ω - G ω) 1 μ :=
      (eLpNorm_congr_ae h_sub).trans rfl
    -- Convert the real inequality to one in `ℝ≥0∞`.
    have h_lt :
        eLpNorm (fun ω => A 0 m ω - G ω) 1 μ
          < ENNReal.ofReal ε := by
      have h_ofReal :
          ENNReal.ofReal (ENNReal.toReal
            (eLpNorm (fun ω => A 0 m ω - G ω) 1 μ)) < ENNReal.ofReal ε :=
        ENNReal.ofReal_lt_ofReal_iff hε |>.mpr htoReal
      rw [ENNReal.ofReal_toReal hfin] at h_ofReal
      exact h_ofReal
    rw [h_eq]
    exact h_lt

  obtain ⟨alpha_0, halpha_0_meas, halpha_0_mem, halpha_0_conv⟩ := h_exist_alpha_0

  -- Step 3: KEY - Prove alpha_0 works for ALL starting indices n
  -- For any n, show A n m → alpha_0 using the uniform two-window bound
  have halpha_0_univ : ∀ n, ∀ ε > 0, ∃ M, ∀ m ≥ M,
      eLpNorm (fun ω => A n m ω - alpha_0 ω) 1 μ < ENNReal.ofReal ε := by
    intro n ε hε
    -- Triangle inequality: ‖A n m - alpha_0‖₁ ≤ ‖A n m - A 0 m‖₂ + ‖A 0 m - alpha_0‖₁
    -- Term 1: ‖A n m - A 0 m‖₂ bounded by l2_bound_two_windows, goes to 0 as m → ∞
    -- Term 2: ‖A 0 m - alpha_0‖₁ → 0 as m → ∞ by halpha_0_conv

    have hε2_pos : 0 < ε / 2 := by linarith

    -- Get M₁ such that ‖A 0 m - alpha_0‖₁ < ε/2 for m ≥ M₁
    rcases halpha_0_conv (ε / 2) hε2_pos with ⟨M₁, hM₁⟩

    -- Get uniform bound constant (already computed above, reuse it)
    -- Note: Cf, mf, σSqf, ρf are already in scope from line 2186

    -- Choose M₂ large enough that √(Cf/M₂) < ε/2
    -- This means Cf/M₂ < ε²/4, so M₂ > 4Cf/ε²
    have hε_sq_pos : 0 < (ε / 2) ^ 2 := pow_pos hε2_pos 2

    let M₂ := Nat.ceil (4 * Cf / (ε ^ 2)) + 1

    -- Define M as max of M₁, M₂, and 2*n+1 to ensure m is large
    -- For A n m vs A 0 m: we use indices {n+1,...,n+m} vs {1,...,m}
    -- These overlap when n < m, so we can't directly use disjoint windows
    -- Instead, wait for m large enough that we can use a different approach
    let M := max (max M₁ M₂) (2 * n + 1)

    use M
    intro m hm
    have hm₁ : M₁ ≤ m := by
      calc M₁ ≤ max M₁ M₂ := le_max_left M₁ M₂
           _ ≤ M := le_max_left _ _
           _ ≤ m := hm
    have hm₂ : M₂ ≤ m := by
      calc M₂ ≤ max M₁ M₂ := le_max_right M₁ M₂
           _ ≤ M := le_max_left _ _
           _ ≤ m := hm
    have hmn : n < m := by
      calc n < 2 * n + 1 := by omega
           _ ≤ M := le_max_right _ _
           _ ≤ m := hm

    -- Apply triangle inequality
    have h_triangle : eLpNorm (fun ω => A n m ω - alpha_0 ω) 1 μ ≤
        eLpNorm (fun ω => A n m ω - A 0 m ω) 1 μ +
        eLpNorm (fun ω => A 0 m ω - alpha_0 ω) 1 μ := by
      -- Use eLpNorm triangle: ‖f - h‖ ≤ ‖f - g‖ + ‖g - h‖
      -- This follows from the fact that (f - h) = (f - g) + (g - h)
      have h_decomp : (fun ω => A n m ω - alpha_0 ω) =
          fun ω => (A n m ω - A 0 m ω) + (A 0 m ω - alpha_0 ω) := by
        ext ω; ring
      rw [h_decomp]
      -- Apply eLpNorm_add_le from Mathlib
      apply eLpNorm_add_le
      · exact (hA_meas n m).sub (hA_meas 0 m) |>.aestronglyMeasurable
      · exact (hA_meas 0 m).sub halpha_0_meas |>.aestronglyMeasurable
      · norm_num

    -- Bound term 2
    have h_term2 : eLpNorm (fun ω => A 0 m ω - alpha_0 ω) 1 μ < ENNReal.ofReal (ε / 2) := by
      apply hM₁; exact hm₁

    -- Bound term 1 using L² → L¹ and l2_bound_two_windows
    have h_term1 : eLpNorm (fun ω => A n m ω - A 0 m ω) 1 μ < ENNReal.ofReal (ε / 2) := by
      -- Use l2_bound_two_windows to bound ∫ (A n m - A 0 m)² ≤ Cf / m
      by_cases hm_pos : 0 < m
      · -- Use the uniform two-window L² bound (valid even for overlapping windows)
        have h_bound_sq' : ∫ ω, (A n m ω - A 0 m ω)^2 ∂μ ≤ Cf / m := by
          simpa [A] using h_window_bound n 0 m hm_pos
        have h_L2 : eLpNorm (fun ω => A n m ω - A 0 m ω) 2 μ ≤
            ENNReal.ofReal (Real.sqrt (Cf / m)) := by
          apply L2Helpers.eLpNorm_two_from_integral_sq_le
          · exact (hA_memLp_two n m).sub (hA_memLp_two 0 m)
          · exact div_nonneg hCf_nonneg (Nat.cast_nonneg m)
          · exact h_bound_sq'
        -- Use L² → L¹
        calc eLpNorm (fun ω => A n m ω - A 0 m ω) 1 μ
            ≤ eLpNorm (fun ω => A n m ω - A 0 m ω) 2 μ := by
              apply eLpNorm_le_eLpNorm_of_exponent_le
              · norm_num
              · exact (hA_meas n m).sub (hA_meas 0 m) |>.aestronglyMeasurable
          _ ≤ ENNReal.ofReal (Real.sqrt (Cf / m)) := h_L2
          _ < ENNReal.ofReal (ε / 2) := by
              apply ENNReal.ofReal_lt_ofReal_iff hε2_pos |>.mpr
              apply L2Helpers.sqrt_div_lt_half_eps_of_nat hCf_nonneg hε
              exact hm₂
      · -- m = 0 case is trivial or doesn't occur
        simp at hm
        omega

    -- Combine
    calc eLpNorm (fun ω => A n m ω - alpha_0 ω) 1 μ
        ≤ eLpNorm (fun ω => A n m ω - A 0 m ω) 1 μ +
            eLpNorm (fun ω => A 0 m ω - alpha_0 ω) 1 μ := h_triangle
      _ < ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := by
            exact ENNReal.add_lt_add h_term1 h_term2
      _ = ENNReal.ofReal ε := by
            rw [← ENNReal.ofReal_add hε2_pos.le hε2_pos.le]; norm_num

  -- Step 4: Package the result - alpha_0 is our answer!
  refine ⟨alpha_0, halpha_0_meas, halpha_0_mem, ?_⟩

  -- Convert eLpNorm convergence to integral convergence
  intro n ε hε
  rcases halpha_0_univ n ε hε with ⟨M, hM⟩
  refine ⟨M, fun m hm => ?_⟩
  have h_elpnorm := hM m hm
  -- Convert eLpNorm 1 to integral
  have h_memLp : MemLp (fun ω => A n m ω - alpha_0 ω) 1 μ := by
    apply MemLp.sub
    · exact hA_memLp n m
    · exact halpha_0_mem
  rw [MemLp.eLpNorm_eq_integral_rpow_norm one_ne_zero ENNReal.coe_ne_top h_memLp] at h_elpnorm
  simp only [ENNReal.toReal_one, Real.rpow_one] at h_elpnorm
  norm_num at h_elpnorm
  rw [ENNReal.ofReal_lt_ofReal_iff hε] at h_elpnorm
  convert h_elpnorm using 1


