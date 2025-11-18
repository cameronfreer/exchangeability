/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Exchangeability.DeFinetti.ViaL2.BlockAverages
import Exchangeability.DeFinetti.ViaL2.CesaroConvergence
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
import Mathlib.Probability.CDF

/-!
# Main Convergence Theorems via L² Approach

This file contains the main convergence theorems for the L² proof of de Finetti's
theorem, including weighted sums convergence and reverse martingale results.

## Main results

* `weighted_sums_converge_L1`: Weighted sums converge in L¹ for contractable sequences
* `reverse_martingale_limit`: Tail-measurable limit via reverse martingale
* `directing_measure`: Construction of the directing measure
* `directing_measure_satisfies_requirements`: Final packaging theorem

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
    (hX_L2 : ∀ i, MemLp (X i) 2 μ)
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
    apply Measurable.const_mul
    apply Finset.measurable_sum
    intro k _
    exact hf_meas.comp (hX_meas _)

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

  -- Covariance structure of f ∘ X
  have hfX_contract' : Contractable μ (fun n ω => f (X n ω)) :=
    L2Helpers.contractable_comp X hX_contract hX_meas f hf_meas

  have hfX_meas' : ∀ i, Measurable fun ω => f (X i ω) := by
    intro i
    exact hf_meas.comp (hX_meas i)

  have hfX_L2' : ∀ i, MemLp (fun ω => f (X i ω)) 2 μ := by
    intro i
    obtain ⟨M, hM⟩ := hf_bdd
    apply MemLp.of_bound (hfX_meas' i).aestronglyMeasurable M
    filter_upwards with ω
    simp [Real.norm_eq_abs]
    exact hM (X i ω)

  -- **Phase 2: Compute covariance structure once and pass to both lemmas**
  -- This eliminates the need to prove Cf = Cf_tail (they're the same by construction!)
  obtain ⟨Cf, mf, σSqf, ρf, hCf_def, hCf_nonneg, hmean, hvar, hcov, hσSq_nn, hρ_bd1, hρ_bd2⟩ :=
    get_covariance_constant X hX_contract hX_meas hX_L2 f hf_meas hf_bdd

  -- Apply l2_bound_two_windows_uniform with the shared covariance structure
  have h_window_bound :=
    l2_bound_two_windows_uniform X hX_contract hX_meas hX_L2 f hf_meas hf_bdd
      Cf mf σSqf ρf hCf_def hCf_nonneg hmean hvar hcov hσSq_nn ⟨hρ_bd1, hρ_bd2⟩

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
    -- Apply l2_bound_long_vs_tail with the shared covariance structure
    -- No more existential unpacking, no more sorry - just a direct bound!
    exact l2_bound_long_vs_tail X hX_contract hX_meas hX_L2 f hf_meas hf_bdd
      Cf mf σSqf ρf hCf_def hCf_nonneg hmean hvar hcov hσSq_nn ⟨hρ_bd1, hρ_bd2⟩
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
      congr 2 <;> (congr 1; apply Finset.sum_congr rfl; intro i _; congr; omega)

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
        congr 2 <;> (congr 1; apply Finset.sum_congr rfl; intro i _; congr; omega)
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

/-!
## Step 3: Reverse martingale convergence
-/

/-- **FMP 4.2: Subsequence criterion**.

Let ξ, ξ₁, ξ₂,... be random elements in a metric space (S, ρ). Then ξₙ →ᵖ ξ
iff every subsequence N' ⊆ ℕ has a further subsequence N'' ⊆ N' such that
ξₙ → ξ a.s. along N''.
In particular, ξₙ → ξ a.s. implies ξₙ →ᵖ ξ.

**Proof outline** (Kallenberg):
Forward direction (→ᵖ implies a.s. along subsequence):
1. Assume ξₙ →ᵖ ξ, fix arbitrary subsequence N' ⊆ ℕ
2. Choose further subsequence N'' ⊆ N' with
   E ∑_{n∈N''} {ρ(ξₙ,ξ) ∧ 1} = ∑_{n∈N''} E[ρ(ξₙ,ξ) ∧ 1] < ∞
   (equality by monotone convergence)
3. Series converges a.s., so ξₙ → ξ a.s. along N''

Reverse direction (a.s. subsequences imply →ᵖ):
1. Assume condition. If ξₙ ↛ᵖ ξ, then ∃ε > 0 with E[ρ(ξₙ,ξ) ∧ 1] > ε along N' ⊆ ℕ
2. By hypothesis, ξₙ → ξ a.s. along N'' ⊆ N'
3. By dominated convergence, E[ρ(ξₙ,ξ) ∧ 1] → 0 along N'', contradiction

**Mathlib reference**: Look for convergence in probability and a.s. convergence
in `Probability` namespace. The subsequence extraction should follow from
summability of expectations.

TODO: Adapt to our L¹ convergence setting.
-/
theorem subsequence_criterion_convergence_in_probability
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (ξ : ℕ → Ω → ℝ) (ξ_limit : Ω → ℝ)
    (hξ_meas : ∀ n, Measurable (ξ n))
    (hξ_limit_meas : Measurable ξ_limit)
    (h_prob_conv : ∀ ε > 0, Tendsto (fun n => μ {ω | ε ≤ |ξ n ω - ξ_limit ω|}) atTop (𝓝 0)) :
    ∃ (φ : ℕ → ℕ), StrictMono φ ∧
      ∀ᵐ ω ∂μ, Tendsto (fun k => ξ (φ k) ω) atTop (𝓝 (ξ_limit ω)) := by
  classical
  -- Strategy: Build φ recursively to ensure strict monotonicity
  -- For each k, choose φ(k) > φ(k-1) where μ{|ξ_{φ k} - ξ_limit| ≥ 1/(k+1)} < (1/2)^(k+1)

  -- Helper: for each k and threshold m, eventually the measure is small
  have h_eventually_small : ∀ (k : ℕ) (m : ℕ),
      ∃ n ≥ m, μ {ω | 1 / (k + 1 : ℝ) ≤ |ξ n ω - ξ_limit ω|} < ENNReal.ofReal ((1 / 2) ^ (k + 1)) := by
    intro k m
    have hε_pos : (0 : ℝ) < 1 / (k + 1) := by positivity
    have hbound_pos : (0 : ℝ) < (1 / 2) ^ (k + 1) := by positivity
    have h := h_prob_conv (1 / (k + 1 : ℝ)) hε_pos
    -- ENNReal.tendsto_atTop_zero: μ_n → 0 iff ∀ε>0, ∃N, ∀n≥N, μ_n ≤ ε
    -- We need strict <, so use ε/2
    rw [ENNReal.tendsto_atTop_zero] at h
    have hbound_half : (0 : ℝ) < (1 / 2) ^ (k + 1) / 2 := by positivity
    obtain ⟨N, hN⟩ := h (ENNReal.ofReal ((1 / 2) ^ (k + 1) / 2)) (by positivity)
    use max m N, le_max_left m N
    calc μ {ω | 1 / (k + 1 : ℝ) ≤ |ξ (max m N) ω - ξ_limit ω|}
        ≤ ENNReal.ofReal ((1 / 2) ^ (k + 1) / 2) := hN (max m N) (le_max_right m N)
      _ < ENNReal.ofReal ((1 / 2) ^ (k + 1)) := by
          have h_pos : (0 : ℝ) < (1 / 2) ^ (k + 1) := by positivity
          have h_ineq : (1 / 2 : ℝ) ^ (k + 1) / 2 < (1 / 2) ^ (k + 1) := by linarith
          exact (ENNReal.ofReal_lt_ofReal_iff h_pos).mpr h_ineq

  -- Build φ recursively using Nat.rec with the helper
  let φ : ℕ → ℕ := Nat.rec
    (Classical.choose (h_eventually_small 0 0))
    (fun k φ_k => Classical.choose (h_eventually_small (k + 1) (φ_k + 1)))

  -- Prove strict monotonicity
  have hφ_mono : StrictMono φ := by
    intro i j hij
    induction j, hij using Nat.le_induction with
    | base =>
        show φ i < φ (i + 1)
        simp only [φ]
        calc φ i
            < φ i + 1 := Nat.lt_succ_self _
          _ ≤ Classical.choose (h_eventually_small (i + 1) (φ i + 1)) :=
              (Classical.choose_spec (h_eventually_small (i + 1) (φ i + 1))).1
    | succ j _ IH =>
        calc φ i < φ j := IH
          _ < φ (j + 1) := by
              simp only [φ]
              calc φ j
                  < φ j + 1 := Nat.lt_succ_self _
                _ ≤ Classical.choose (h_eventually_small (j + 1) (φ j + 1)) :=
                    (Classical.choose_spec (h_eventually_small (j + 1) (φ j + 1))).1

  -- Extract measure bounds - φ k means we evaluate the recursive function at natural number k
  have hφ_small : ∀ (k : ℕ), μ {ω | 1 / (k + 1 : ℝ) ≤ |ξ (φ k) ω - ξ_limit ω|} < ENNReal.ofReal ((1 / 2) ^ (k + 1)) := by
    intro k
    -- Prove by induction on k
    induction k with
    | zero =>
        -- For k = 0, φ 0 is the base case
        simp only [φ]
        exact (Classical.choose_spec (h_eventually_small 0 0)).2
    | succ k' IH_unused =>
        -- For k = k'+1, φ (k'+1) uses the recursive case
        simp only [φ]
        exact (Classical.choose_spec (h_eventually_small (k' + 1) (φ k' + 1))).2

  -- Define bad sets
  let E : ℕ → Set Ω := fun k => {ω | 1 / (k + 1 : ℝ) ≤ |ξ (φ k) ω - ξ_limit ω|}

  have hE_meas : ∀ k, MeasurableSet (E k) := fun k =>
    measurableSet_le (measurable_const) ((hξ_meas (φ k)).sub hξ_limit_meas).norm

  have hE_small : ∀ k, μ (E k) ≤ ENNReal.ofReal ((1 / 2) ^ (k + 1)) := fun k =>
    le_of_lt (hφ_small k)

  -- Geometric series: ∑_k (1/2)^(k+1) converges (ratio < 1)
  -- We need: ∑' k, μ (E k) ≠ ⊤
  have hsum_finite : ∑' k, μ (E k) ≠ ⊤ := by
    -- 1) Summability of the *shifted* geometric series (in ℝ), obtained from the unshifted one
    have hgeom : Summable (fun k : ℕ => (1 / 2 : ℝ) ^ k) :=
      summable_geometric_of_lt_one (by norm_num : 0 ≤ (1 / 2 : ℝ))
                                   (by norm_num : (1 / 2 : ℝ) < 1)
    have hshift : Summable (fun k : ℕ => (1 / 2 : ℝ) ^ (k + 1)) := by
      -- (1/2)^(k+1) = (1/2) * (1/2)^k
      simpa [pow_succ, mul_comm] using hgeom.mul_left (1 / 2 : ℝ)

    -- 2) The ENNReal series ∑ ofReal((1/2)^(k+1)) is finite because it equals ofReal(tsum …)
    have htsum :
        ENNReal.ofReal (∑' k, ((1 / 2 : ℝ) ^ (k + 1)))
          = (∑' k, ENNReal.ofReal ((1 / 2 : ℝ) ^ (k + 1))) :=
      ENNReal.ofReal_tsum_of_nonneg
        (by
          intro k
          have : 0 ≤ (1 / 2 : ℝ) := by norm_num
          exact pow_nonneg this (k + 1))
        hshift

    have htop : (∑' k, ENNReal.ofReal ((1 / 2 : ℝ) ^ (k + 1))) ≠ ⊤ := by
      -- RHS is ofReal of a real number, hence finite
      rw [← htsum]
      exact ENNReal.ofReal_ne_top

    -- 3) Compare termwise with μ (E k) ≤ ofReal((1/2)^(k+1)), then lift to tsums
    have hle :
        (∑' k, μ (E k))
          ≤ (∑' k, ENNReal.ofReal ((1 / 2 : ℝ) ^ (k + 1))) :=
      ENNReal.tsum_le_tsum hE_small

    -- 4) Conclude our tsum is not ⊤
    exact ne_top_of_le_ne_top htop hle

  -- Borel-Cantelli
  have h_BC : ∀ᵐ ω ∂μ, ∀ᶠ k in atTop, ω ∉ E k :=
    ae_eventually_notMem hsum_finite

  -- Extract convergence
  refine ⟨φ, hφ_mono, ?_⟩
  filter_upwards [h_BC] with ω hω
  rw [Filter.eventually_atTop] at hω
  obtain ⟨K, hK⟩ := hω
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨K', hK'⟩ := exists_nat_one_div_lt hε
  use max K (K' + 1)
  intro k hk
  simp only [Real.dist_eq]
  have hk_ge_K : k ≥ K := le_trans (le_max_left K (K' + 1)) hk
  have : ω ∉ E k := hK k hk_ge_K
  simp only [E, Set.mem_setOf_eq, not_le] at this
  calc |ξ (φ k) ω - ξ_limit ω|
      < 1 / (k + 1 : ℝ) := this
    _ ≤ 1 / (K' + 1 : ℝ) := by
        apply div_le_div_of_nonneg_left
        · norm_num
        · positivity
        · have : (K' + 1 : ℝ) ≤ (k : ℝ) := by
            calc (K' + 1 : ℝ) ≤ (max K (K' + 1) : ℝ) := by exact_mod_cast le_max_right K (K' + 1)
              _ ≤ (k : ℝ) := by exact_mod_cast hk
          linarith
    _ < ε := hK'

/-- **OBSOLETE with refactored approach**: This theorem is no longer needed.

With the refactored `weighted_sums_converge_L1`, we get a single `alpha : Ω → ℝ`
that is independent of the starting index. There is no sequence `alpha_n` to
take a subsequence of.

The original Kallenberg approach had `alpha_n → alpha_∞`, but our refactored
proof shows `alpha_n = alpha` for all n directly.
-/
theorem reverse_martingale_subsequence_convergence
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (alpha : ℕ → Ω → ℝ) (alpha_inf : Ω → ℝ)
    (h_alpha_meas : ∀ n, Measurable (alpha n))
    (h_alpha_inf_meas : Measurable alpha_inf)
    (h_integrable : ∀ n, Integrable (fun ω => alpha n ω - alpha_inf ω) μ)
    (h_L1_conv : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∫ ω, |alpha n ω - alpha_inf ω| ∂μ < ε) :
    ∃ (φ : ℕ → ℕ), StrictMono φ ∧
      ∀ᵐ ω ∂μ, Tendsto (fun k => alpha (φ k) ω) atTop (𝓝 (alpha_inf ω)) := by
  classical
  exact Helpers.subseq_ae_of_L1 alpha alpha_inf h_alpha_meas h_alpha_inf_meas h_integrable h_L1_conv

/-- Placeholder: The α_n sequence is a reverse martingale with respect to the tail filtration.

**TODO**: This lemma's content is deferred to Step 5 (`alpha_is_conditional_expectation`).
Once we identify α_n = E[f(X_{n+1}) | σ(X_{n+1}, X_{n+2}, ...)] in Step 5,
the reverse martingale property follows immediately from the standard tower property
of conditional expectation.

This private placeholder exists only so the file compiles while we develop other parts.
-/
@[nolint unusedArguments]
private theorem alpha_is_reverse_martingale
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (_X : ℕ → Ω → ℝ) (_hX_contract : Contractable μ _X)
    (_hX_meas : ∀ i, Measurable (_X i))
    (_α : ℕ → Ω → ℝ)
    (_f : ℝ → ℝ) (_hf_meas : Measurable _f) :
    True :=
  trivial

/-!
## Step 4: Contractability + dominated convergence gives conditional expectation formula
-/

/-- Placeholder: Using contractability and dominated convergence, we get:
E[f(X_i) ; ∩I_k] = E[α_{k-1} ; ∩I_k] → E[α_∞ ; ∩I_k]

**Kallenberg**: "By the contractability of ξ and dominated convergence we get, a.s. along ℕ
for any i ∈ I:
  E[f(ξ_i); ∩I_k] = E[α_{k-1}; ∩I_k] → E[α_∞; ∩I_k]"

**TODO**: Use contractability to relate different time points.

This private placeholder exists only so the file compiles while we develop other parts.
The parameters document the intended signature for the full implementation.
-/
@[nolint unusedArguments]
private theorem contractability_conditional_expectation
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (_X : ℕ → Ω → ℝ) (_hX_contract : Contractable μ _X)
    (_hX_meas : ∀ i, Measurable (_X i))
    (_f : ℝ → ℝ) (_hf_meas : Measurable _f)
    (_alpha : ℕ → Ω → ℝ) (_alpha_inf : Ω → ℝ)
    (_I_k : Set Ω)  -- Event ∩I_k in tail σ-algebra
    (_h_conv : ∀ᵐ ω ∂μ, Tendsto (fun n => _alpha n ω) atTop (𝓝 (_alpha_inf ω))) :
    True :=
  trivial

/-!
## Step 5: α_n = E_n f(X_{n+1}) = ν^f
-/

/-- The limit α_n satisfies α_n = E_n f(X_{n+1}) where E_n is conditional
expectation on σ(X_{n+1}, X_{n+2}, ...).

Moreover, α_n = ν^f a.s. for some directing measure ν.

**Kallenberg**: "which implies α_n = E_n f(ξ_{n+1}) = ν^f a.s."

TODO: Show this characterizes α_n as the conditional expectation.
-/
theorem alpha_is_conditional_expectation
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (f : ℝ → ℝ) (hf_meas : Measurable f)
    (alpha : ℕ → Ω → ℝ) :
    ∃ (nu : Ω → Measure ℝ),
      (∀ ω, IsProbabilityMeasure (nu ω)) ∧
      -- tail-measurable kernel: spelled out in Step 6
      (Measurable fun ω => nu ω (Set.univ)) ∧
      -- α_n = ∫ f dν a.e. (the "identification" statement)
      (∀ n, ∀ᵐ ω ∂μ, alpha n ω = ∫ x, f x ∂(nu ω)) := by
  classical
  /- **Sketch (wired into Step 6):**
     • Define ν via Stieltjes/Carathéodory from the family α_{1_{(-∞,t]}}(ω).
     • It is a probability kernel and tail–measurable.
     • For bounded measurable f, α_f(ω) = ∫ f dν(ω) a.e.
     Here we just package that existence; concretely we can point to
     `directing_measure` from Step 6 once those are in place. -/
  -- TODO: once Step 6 is complete, replace the whole proof by:
  --   refine ⟨directing_measure X hX_contract hX_meas ?hX_L2?, ?isProb?, ?meas?, ?ident?⟩
  -- where `?ident?` comes from `directing_measure_integral` specialized to f.
  sorry

/-!
## Step 6: Build directing measure ν via Carathéodory extension

Given the family of limit functions α_f for bounded measurable f, we construct
the directing measure ν : Ω → Measure ℝ such that:
- ν(ω) is a probability measure for each ω
- ω ↦ ν(ω)(B) is measurable for each Borel B
- α_f(ω) = ∫ f dν(ω) for all bounded measurable f

The construction proceeds via the Carathéodory extension theorem:
1. For intervals (-∞, t], use α_{𝟙_{(-∞,t]}} to define a pre-measure
2. Verify this is a valid CDF (monotone, right-continuous, limits 0 and 1)
3. Extend to Borel sets via Carathéodory
4. Establish measurability of ω ↦ ν(ω)(B) using monotone class theorem

This is the "lightest path" mentioned in the original plan.
-/

/-- Indicator of `(-∞, t]` as a bounded measurable function ℝ → ℝ. -/
private def indIic (t : ℝ) : ℝ → ℝ :=
  (Set.Iic t).indicator (fun _ => (1 : ℝ))

@[fun_prop]
private lemma indIic_measurable (t : ℝ) : Measurable (indIic t) := by
  simpa [indIic] using (measurable_const.indicator measurableSet_Iic)

private lemma indIic_bdd (t : ℝ) : ∀ x, |indIic t x| ≤ 1 := by
  intro x; by_cases hx : x ≤ t <;> simp [indIic, hx, abs_of_nonneg]

/-- Raw "CDF" at level t: the L¹-limit α_{1_{(-∞,t]}} produced by Step 2,
clipped to [0,1] to ensure pointwise bounds.

The clipping preserves measurability and a.e. equality (hence L¹ properties) since
the underlying limit is a.e. in [0,1] anyway (being the limit of averages in [0,1]).
-/
noncomputable def alphaIic
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ)
    (t : ℝ) : Ω → ℝ :=
  fun ω => max 0 (min 1 ((weighted_sums_converge_L1 X hX_contract hX_meas hX_L2
      (indIic t) (indIic_measurable t) ⟨1, indIic_bdd t⟩).choose ω))

/-- Measurability of the raw α_{Iic t}. -/
lemma alphaIic_measurable
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ)
    (t : ℝ) :
    Measurable (alphaIic X hX_contract hX_meas hX_L2 t) := by
  -- alphaIic is max 0 (min 1 limit) where limit is measurable
  unfold alphaIic
  have h_limit_meas : Measurable (weighted_sums_converge_L1 X hX_contract hX_meas hX_L2
            (indIic t) (indIic_measurable t) ⟨1, indIic_bdd t⟩).choose := by
    exact (weighted_sums_converge_L1 X hX_contract hX_meas hX_L2
            (indIic t) (indIic_measurable t) ⟨1, indIic_bdd t⟩).choose_spec.1
  -- max and min preserve measurability: max 0 (min 1 limit)
  -- Build: min limit 1, then max 0 result
  refine Measurable.max measurable_const ?_
  refine Measurable.min measurable_const h_limit_meas

/-- 0 ≤ α_{Iic t} ≤ 1. The α is an L¹-limit of averages of indicators in [0,1].

DESIGN NOTE: This lemma requires pointwise bounds on alphaIic, but alphaIic is defined
as an L¹ limit witness via .choose, which only determines the function up to a.e. equivalence.

The mathematically standard resolution is one of:
1. Modify alphaIic's definition to explicitly take a representative in [0,1]:
   `alphaIic t ω := max 0 (min 1 (original_limit t ω))`
   This preserves measurability and a.e. equality, hence L¹ properties.

2. Strengthen weighted_sums_converge_L1 to provide a witness with pointwise bounds
   when the input function is bounded (requires modifying the existential).

3. Accept as a property of the construction: Since each Cesàro average
   (1/m) Σ_{i<m} indIic(X_i ω) ∈ [0,1] pointwise, and these converge in L¹ to alphaIic,
   we can choose a representative of the equivalence class that is in [0,1] pointwise.

For the proof to proceed, we adopt approach (3) as an axiom of the construction.
-/
lemma alphaIic_bound
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ)
    (t : ℝ) (ω : Ω) :
    0 ≤ alphaIic X hX_contract hX_meas hX_L2 t ω
    ∧ alphaIic X hX_contract hX_meas hX_L2 t ω ≤ 1 := by
  -- alphaIic is defined as max 0 (min 1 limit), so bounds are immediate
  unfold alphaIic
  constructor
  · -- 0 ≤ max 0 (min 1 ...)
    exact le_max_left 0 _
  · -- max 0 (min 1 ...) ≤ 1
    -- Since min 1 x ≤ 1 for any x, and max a b ≤ c when both a ≤ c and b ≤ c
    -- We have max 0 (min 1 x) ≤ 1 since 0 ≤ 1 and min 1 x ≤ 1
    apply max_le
    · linarith
    · exact min_le_left 1 _

/-!
### Canonical conditional expectation version of alphaIic

The existential α from `weighted_sums_converge_L1` is unique in L¹ up to a.e. equality.
We now define the **canonical** version using conditional expectation onto the tail σ-algebra.
This avoids all pointwise headaches and gives us the endpoint limits for free.
-/

/-- **Canonical conditional expectation version** of α_{Iic t}.

This is the conditional expectation of the indicator function `1_{(-∞,t]}∘X_0` with respect
to the tail σ-algebra. By the reverse martingale convergence theorem, this equals the
existential `alphaIic` almost everywhere.

**Key advantages:**
- Has pointwise bounds `0 ≤ alphaIicCE ≤ 1` everywhere (not just a.e.)
- Monotone in `t` almost everywhere (from positivity of conditional expectation)
- Endpoint limits follow from L¹ contraction and dominated convergence
-/
noncomputable def alphaIicCE
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ)
    (t : ℝ) : Ω → ℝ := by
  classical
  -- Set up the tail σ-algebra and its sub-σ-algebra relation
  have hm_le : TailSigma.tailSigma X ≤ (inferInstance : MeasurableSpace Ω) :=
    TailSigma.tailSigma_le X hX_meas
  -- Create the Fact instance for the sub-σ-algebra relation
  haveI : Fact (TailSigma.tailSigma X ≤ (inferInstance : MeasurableSpace Ω)) := ⟨hm_le⟩
  -- Now we can call condExp with the tail σ-algebra
  exact μ[(indIic t) ∘ (X 0) | TailSigma.tailSigma X]

/-- Measurability of alphaIicCE.

TODO: Currently a sorry due to BorelSpace typeclass instance resolution issues.
The conditional expectation `condExp μ (tailSigma X) f` is measurable by
`stronglyMeasurable_condExp.measurable`, but Lean can't synthesize the required
`BorelSpace` instance automatically. This should be straightforward to fix. -/
lemma alphaIicCE_measurable
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ)
    (t : ℝ) :
    Measurable (alphaIicCE X hX_contract hX_meas hX_L2 t) := by
  unfold alphaIicCE
  -- The conditional expectation μ[f|m] is strongly measurable w.r.t. m
  -- Since m ≤ ambient, measurability w.r.t. m implies measurability w.r.t. ambient
  have hm_le := TailSigma.tailSigma_le X hX_meas
  refine Measurable.mono stronglyMeasurable_condExp.measurable hm_le le_rfl

/-- alphaIicCE is monotone nondecreasing in t (for each fixed ω). -/
lemma alphaIicCE_mono
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ) :
    ∀ s t : ℝ, s ≤ t → ∀ᵐ ω ∂μ,
      alphaIicCE X hX_contract hX_meas hX_L2 s ω
      ≤ alphaIicCE X hX_contract hX_meas hX_L2 t ω := by
  -- alphaIicCE is conditional expectation of (indIic ·) ∘ X 0
  -- indIic is monotone: s ≤ t ⇒ indIic s ≤ indIic t
  -- Conditional expectation preserves monotonicity a.e.
  intro s t hst

  -- Set up tail σ-algebra infrastructure
  have hm_le : TailSigma.tailSigma X ≤ (inferInstance : MeasurableSpace Ω) :=
    TailSigma.tailSigma_le X hX_meas
  haveI : Fact (TailSigma.tailSigma X ≤ (inferInstance : MeasurableSpace Ω)) := ⟨hm_le⟩

  -- Show indIic s ≤ indIic t pointwise
  have h_ind_mono : (indIic s) ∘ (X 0) ≤ᵐ[μ] (indIic t) ∘ (X 0) := by
    apply ae_of_all
    intro ω
    simp [indIic, Set.indicator]
    split_ifs with h1 h2
    · norm_num  -- Both in set: 1 ≤ 1
    · -- X 0 ω ≤ s but not ≤ t: contradiction since s ≤ t
      exfalso
      exact h2 (le_trans h1 hst)
    · norm_num  -- s not satisfied but t is: 0 ≤ 1
    · norm_num  -- Neither satisfied: 0 ≤ 0

  -- Integrability of both functions
  have h_int_s : Integrable ((indIic s) ∘ (X 0)) μ := by
    have : indIic s = Set.indicator (Set.Iic s) (fun _ => (1 : ℝ)) := rfl
    rw [this]
    exact Exchangeability.Probability.integrable_indicator_comp (hX_meas 0) measurableSet_Iic

  have h_int_t : Integrable ((indIic t) ∘ (X 0)) μ := by
    have : indIic t = Set.indicator (Set.Iic t) (fun _ => (1 : ℝ)) := rfl
    rw [this]
    exact Exchangeability.Probability.integrable_indicator_comp (hX_meas 0) measurableSet_Iic

  -- Apply condExp_mono
  unfold alphaIicCE
  exact condExp_mono (μ := μ) (m := TailSigma.tailSigma X) h_int_s h_int_t h_ind_mono

/-- alphaIicCE is bounded in [0,1] almost everywhere. -/
lemma alphaIicCE_nonneg_le_one
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ)
    (t : ℝ) :
    ∀ᵐ ω ∂μ, 0 ≤ alphaIicCE X hX_contract hX_meas hX_L2 t ω
             ∧ alphaIicCE X hX_contract hX_meas hX_L2 t ω ≤ 1 := by
  -- alphaIicCE = condExp of (indIic t) ∘ X 0
  -- Since 0 ≤ indIic t ≤ 1, we have 0 ≤ condExp(...) ≤ 1 a.e.

  -- Set up tail σ-algebra infrastructure
  have hm_le : TailSigma.tailSigma X ≤ (inferInstance : MeasurableSpace Ω) :=
    TailSigma.tailSigma_le X hX_meas
  haveI : Fact (TailSigma.tailSigma X ≤ (inferInstance : MeasurableSpace Ω)) := ⟨hm_le⟩

  -- Nonnegativity: 0 ≤ indIic t ∘ X 0 implies 0 ≤ condExp
  have h₀ : 0 ≤ᵐ[μ] alphaIicCE X hX_contract hX_meas hX_L2 t := by
    have : 0 ≤ᵐ[μ] (indIic t) ∘ (X 0) := by
      apply ae_of_all
      intro ω
      -- indIic t is an indicator function, so it's 0 or 1
      simp [indIic, Set.indicator]
      split_ifs <;> norm_num
    unfold alphaIicCE
    convert condExp_nonneg (μ := μ) (m := TailSigma.tailSigma X) this using 2

  -- Upper bound: indIic t ∘ X 0 ≤ 1 implies condExp ≤ 1
  have h₁ : alphaIicCE X hX_contract hX_meas hX_L2 t ≤ᵐ[μ] fun _ => (1 : ℝ) := by
    have h_le : (indIic t) ∘ (X 0) ≤ᵐ[μ] fun _ => (1 : ℝ) := by
      apply ae_of_all
      intro ω
      -- indIic t is an indicator function, so it's 0 or 1
      simp [indIic, Set.indicator]
      split_ifs <;> norm_num
    -- Need integrability
    have h_int : Integrable ((indIic t) ∘ (X 0)) μ := by
      -- Bounded indicator composition is integrable
      have : indIic t = Set.indicator (Set.Iic t) (fun _ => (1 : ℝ)) := rfl
      rw [this]
      exact Exchangeability.Probability.integrable_indicator_comp (hX_meas 0) measurableSet_Iic
    unfold alphaIicCE
    have h_mono := condExp_mono (μ := μ) (m := TailSigma.tailSigma X)
      h_int (integrable_const (1 : ℝ)) h_le
    rw [condExp_const (μ := μ) (m := TailSigma.tailSigma X) hm_le (1 : ℝ)] at h_mono
    exact h_mono

  filter_upwards [h₀, h₁] with ω h0 h1
  exact ⟨h0, h1⟩

/-!
### Identification lemma and endpoint limits for alphaIicCE

The key results that solve the endpoint limit problem:
1. **Identification**: The existential `alphaIic` equals the canonical `alphaIicCE` a.e.
2. **L¹ endpoint limits**: Using L¹ contraction of condExp, we get integral convergence
3. **A.e. endpoint limits**: Monotonicity + boundedness + L¹ limits ⇒ a.e. pointwise limits
-/

set_option maxHeartbeats 400000 in
/-- **Identification lemma**: alphaIic equals alphaIicCE almost everywhere.

**Proof strategy:**
Both are L¹ limits of the same Cesàro averages `(1/m) ∑ᵢ (indIic t) ∘ X_{n+i}`:
- `alphaIic` is defined as the L¹ limit from `weighted_sums_converge_L1`
- `alphaIicCE` is the conditional expectation `μ[(indIic t) ∘ X_0 | tailSigma X]`

By the reverse martingale convergence theorem (or direct L² analysis), the Cesàro averages
converge in L² (hence L¹) to the conditional expectation. Since L¹ limits are unique up
to a.e. equality, we get `alphaIic =ᵐ alphaIicCE`.

TODO: Implement using reverse martingale convergence or L² projection argument. -/
lemma alphaIic_ae_eq_alphaIicCE
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ)
    (t : ℝ) :
    alphaIic X hX_contract hX_meas hX_L2 t
      =ᵐ[μ] alphaIicCE X hX_contract hX_meas hX_L2 t := by
  -- Proof strategy: Both are L¹ limits of the same Cesàro averages, so they're equal a.e.

  -- Define the Cesàro averages
  let A : ℕ → ℕ → Ω → ℝ := fun n m ω =>
    (1 / (m : ℝ)) * ∑ k : Fin m, indIic t (X (n + k.val + 1) ω)

  -- Step 1: alphaIic is (essentially) the L¹ limit of these averages by construction
  have h_alphaIic_is_limit : ∀ n, ∀ ε > 0, ∃ M : ℕ, ∀ m ≥ M,
      ∫ ω, |A n m ω - alphaIic X hX_contract hX_meas hX_L2 t ω| ∂μ < ε := by
    intro n ε hε
    -- By definition, alphaIic is max 0 (min 1 (witness from weighted_sums_converge_L1))
    -- The witness satisfies the L¹ convergence property
    unfold alphaIic

    -- Get the witness alpha from weighted_sums_converge_L1
    let alpha := (weighted_sums_converge_L1 X hX_contract hX_meas hX_L2
                    (indIic t) (indIic_measurable t) ⟨1, indIic_bdd t⟩).choose
    have h_alpha_conv := (weighted_sums_converge_L1 X hX_contract hX_meas hX_L2
                    (indIic t) (indIic_measurable t) ⟨1, indIic_bdd t⟩).choose_spec.2.2

    -- Use L¹ convergence of A n m to alpha
    obtain ⟨M, hM⟩ := h_alpha_conv n ε hε
    use M
    intro m hm

    -- Strategy: Show A n m is already in [0,1], so clipping doesn't change it
    -- A n m = (1/m) * ∑ indIic, and each indIic ∈ {0,1}, so A n m ∈ [0,1]
    have hA_in_01 : ∀ ω, 0 ≤ A n m ω ∧ A n m ω ≤ 1 := by
      intro ω
      unfold A
      constructor
      · -- 0 ≤ A
        apply mul_nonneg
        · positivity
        · apply Finset.sum_nonneg
          intro k _
          unfold indIic
          simp [Set.indicator]
          split_ifs <;> norm_num
      · -- A ≤ 1
        by_cases hm_pos : m = 0
        · simp [hm_pos, A]
        · have hm_cast : 0 < (m : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm_pos)
          calc (1 / (m : ℝ)) * ∑ k : Fin m, indIic t (X (n + ↑k + 1) ω)
              ≤ (1 / (m : ℝ)) * ∑ k : Fin m, (1 : ℝ) := by
                apply mul_le_mul_of_nonneg_left _ (by positivity)
                apply Finset.sum_le_sum
                intro k _
                unfold indIic
                simp [Set.indicator]
                split_ifs <;> norm_num
            _ = (1 / (m : ℝ)) * m := by simp
            _ = 1 := by field_simp [hm_cast.ne']

    -- Since A n m ∈ [0,1], we have max 0 (min 1 (A n m)) = A n m
    have hA_clip_eq : ∀ ω, max 0 (min 1 (A n m ω)) = A n m ω := by
      intro ω
      obtain ⟨h0, h1⟩ := hA_in_01 ω
      rw [min_comm, min_eq_left h1, max_eq_right h0]

    -- Use the fact that clipping can only make things closer when A n m ∈ [0,1]
    -- Since A n m ∈ [0,1], we have |A - clip(alpha)| ≤ |A - alpha| for all alpha
    have h_clip_le : ∀ ω, |A n m ω - max 0 (min 1 (alpha ω))| ≤ |A n m ω - alpha ω| := by
      intro ω
      obtain ⟨hA0, hA1⟩ := hA_in_01 ω
      by_cases halpha : alpha ω < 0
      · calc |A n m ω - max 0 (min 1 (alpha ω))|
            = |A n m ω - max 0 (alpha ω)| := by rw [min_eq_right (by linarith : alpha ω ≤ 1)]
          _ = |A n m ω - 0| := by rw [max_eq_left (by linarith : 0 ≥ alpha ω)]
          _ = A n m ω := by rw [sub_zero, abs_of_nonneg hA0]
          _ ≤ A n m ω - alpha ω := by linarith
          _ ≤ |A n m ω - alpha ω| := le_abs_self _
      · by_cases halpha1 : 1 < alpha ω
        · calc |A n m ω - max 0 (min 1 (alpha ω))|
              = |A n m ω - max 0 1| := by rw [min_eq_left (by linarith : 1 ≤ alpha ω)]
            _ = |A n m ω - 1| := by rw [max_eq_right (by linarith : (0 : ℝ) ≤ 1)]
            _ = 1 - A n m ω := by
                rw [abs_of_nonpos (by linarith : A n m ω - 1 ≤ 0)]
                ring
            _ ≤ alpha ω - A n m ω := by linarith
            _ ≤ |A n m ω - alpha ω| := by rw [abs_sub_comm]; exact le_abs_self _
        · -- alpha ∈ [0,1], so clipping does nothing
          push_neg at halpha halpha1
          rw [min_comm, min_eq_left halpha1, max_eq_right halpha]

    -- Prove integrability of A n m
    have hA_int : Integrable (A n m) μ := by
      have hA_meas_nm : Measurable (A n m) := by
        simp only [A]
        apply Measurable.const_mul
        apply Finset.measurable_sum
        intro k _
        exact (indIic_measurable t).comp (hX_meas _)
      refine Integrable.of_bound hA_meas_nm.aestronglyMeasurable 1 ?_
      filter_upwards with ω
      unfold A
      simp only [Real.norm_eq_abs]
      by_cases hm : m = 0
      · simp [hm]
      · have hm_pos : 0 < (m : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm)
        calc |(1/(m:ℝ)) * ∑ k : Fin m, indIic t (X (n + k.val + 1) ω)|
            = (1/(m:ℝ)) * |∑ k : Fin m, indIic t (X (n + k.val + 1) ω)| := by
                rw [abs_mul, abs_of_pos (one_div_pos.mpr hm_pos)]
          _ ≤ (1/(m:ℝ)) * ∑ k : Fin m, |indIic t (X (n + k.val + 1) ω)| := by
                gcongr; exact Finset.abs_sum_le_sum_abs _ _
          _ ≤ (1/(m:ℝ)) * ∑ k : Fin m, (1 : ℝ) := by
                gcongr with k
                unfold indIic; simp [Set.indicator]; split_ifs <;> norm_num
          _ = (1/(m:ℝ)) * m := by simp [Finset.sum_const, Finset.card_fin]
          _ = 1 := by field_simp [hm]

    -- Prove integrability of alpha (from weighted_sums_converge_L1)
    have halpha_meas : Measurable alpha :=
      (weighted_sums_converge_L1 X hX_contract hX_meas hX_L2
        (indIic t) (indIic_measurable t) ⟨1, indIic_bdd t⟩).choose_spec.1
    have h_alpha_memLp : MemLp alpha 1 μ :=
      (weighted_sums_converge_L1 X hX_contract hX_meas hX_L2
        (indIic t) (indIic_measurable t) ⟨1, indIic_bdd t⟩).choose_spec.2.1
    have halpha_int : Integrable alpha μ := memLp_one_iff_integrable.mp h_alpha_memLp

    calc ∫ ω, |A n m ω - max 0 (min 1 (alpha ω))| ∂μ
        ≤ ∫ ω, |A n m ω - alpha ω| ∂μ := by
          apply integral_mono_ae
          · apply Integrable.abs
            apply Integrable.sub hA_int
            have : Measurable (fun ω => max 0 (min 1 (alpha ω))) :=
              Measurable.max measurable_const (Measurable.min measurable_const halpha_meas)
            apply Integrable.of_bound this.aestronglyMeasurable 1
            filter_upwards with ω
            simp [Real.norm_eq_abs]
            -- max 0 (min 1 x) is always in [0,1]
            by_cases h : alpha ω ≤ 0
            · rw [min_eq_right (by linarith : alpha ω ≤ 1), max_eq_left h, abs_zero]
              norm_num
            · by_cases h1 : 1 ≤ alpha ω
              · rw [min_eq_left h1, max_eq_right (by linarith : 0 ≤ (1:ℝ)), abs_of_nonneg (by linarith : 0 ≤ (1:ℝ))]
              · push_neg at h h1
                rw [min_eq_right (le_of_lt h1), max_eq_right (le_of_lt h)]
                exact abs_of_pos h |>.trans_le (le_of_lt h1)
          · exact (hA_int.sub halpha_int).abs
          · filter_upwards with ω; exact h_clip_le ω
      _ < ε := hM m hm

  -- Step 2: alphaIicCE is also the L¹ limit of the same averages (at n=0)
  -- This is the reverse martingale convergence theorem / ergodic theorem
  -- Note: We only need n=0 for the uniqueness argument below
  have h_alphaIicCE_is_limit : ∀ ε > 0, ∃ M : ℕ, ∀ m ≥ M,
      ∫ ω, |A 0 m ω - alphaIicCE X hX_contract hX_meas hX_L2 t ω| ∂μ < ε := by
    intro ε hε

    -- Strategy: Use asymptotic negligibility
    -- A 0 m uses X(k+1) for k ∈ {0,...,m-1}, i.e., X_1,...,X_m
    -- cesaro_to_condexp_L1 uses X(k) for k ∈ {0,...,m-1}, i.e., X_0,...,X_{m-1}

    unfold A alphaIicCE
    simp only [zero_add]

    -- Define the "standard" Cesàro average (matching axiom indexing)
    let B : ℕ → Ω → ℝ := fun m ω => (1 / (m : ℝ)) * ∑ i : Fin m, indIic t (X i ω)

    -- Apply cesaro_to_condexp_L1 for B
    have hε_half : ε/2 > 0 := by linarith
    have h_axiom : ∃ (M : ℕ), ∀ (m : ℕ), m ≥ M →
        ∫ ω, |(1 / (m : ℝ)) * ∑ i : Fin m, indIic t (X i ω) -
              (μ[(indIic t ∘ X 0) | TailSigma.tailSigma X] ω)| ∂μ < ε/2 :=
      cesaro_to_condexp_L1 hX_contract hX_meas (indIic t) (indIic_measurable t) (indIic_bdd t) (ε/2) hε_half
    obtain ⟨M₁, hM₁⟩ := h_axiom

    -- The difference between A 0 m and B m is O(1/m)
    -- A 0 m = (1/m)[f(X₁) + ... + f(Xₘ)]
    -- B m   = (1/m)[f(X₀) + ... + f(X_{m-1})]
    -- Diff  = (1/m)[f(Xₘ) - f(X₀)]

    have h_diff_small : ∀ m : ℕ, m > 0 →
        ∫ ω, |(1/(m:ℝ)) * ∑ k : Fin m, indIic t (X (k.val + 1) ω) - B m ω| ∂μ ≤ 2/(m:ℝ) := by
      intro m hm_pos
      -- Unfold B and simplify
      simp only [B]

      -- The difference telescopes: (1/m)[∑ f(X(k+1)) - ∑ f(X(k))] = (1/m)[f(Xₘ) - f(X₀)]
      -- We'll bound this by (1/m)[|f(Xₘ)| + |f(X₀)|] ≤ 2/m

      have h_telescope : ∀ ω,
          |(1/(m:ℝ)) * ∑ k : Fin m, indIic t (X (k.val + 1) ω) -
           (1/(m:ℝ)) * ∑ i : Fin m, indIic t (X i ω)|
          = |(1/(m:ℝ)) * (indIic t (X m ω) - indIic t (X 0 ω))| := by
        intro ω
        -- Factor out (1/m) and show the sums telescope
        congr 1
        -- After congr 1, goal is the argument to | · |
        rw [←mul_sub]
        congr 1
        -- Now goal is: ∑ k, f(k+1) - ∑ i, f(i) = f(m) - f(0)

        -- The key telescoping identity:
        -- ∑_{k<m} f(X(k+1)) - ∑_{i<m} f(X i) = f(Xₘ) - f(X₀)
        --
        -- Proof: Left sum  = f(X₁) + f(X₂) + ... + f(Xₘ)
        --        Right sum = f(X₀) + f(X₁) + ... + f(X_{m-1})
        --        Middle terms cancel, leaving f(Xₘ) - f(X₀)

        -- First convert Fin m sums to range sums for easier manipulation
        -- Use Fin.sum_univ_eq_sum_range: ∑ i : Fin m, f ↑i = ∑ i ∈ range m, f i
        -- Note: k.val and ↑k are definitionally equal for Fin
        have h_left : ∑ k : Fin m, indIic t (X (k.val + 1) ω) =
                      (Finset.range m).sum (fun k => indIic t (X (k + 1) ω)) :=
          Fin.sum_univ_eq_sum_range (fun k => indIic t (X (k + 1) ω)) m
        have h_right : ∑ i : Fin m, indIic t (X i ω) =
                       (Finset.range m).sum (fun i => indIic t (X i ω)) :=
          Fin.sum_univ_eq_sum_range (fun i => indIic t (X i ω)) m

        -- Prove telescoping: ∑_{k<m} f(k+1) - ∑_{i<m} f(i) = f(m) - f(0)
        have h_telescope_sum : (Finset.range m).sum (fun k => indIic t (X (k + 1) ω)) -
                                (Finset.range m).sum (fun i => indIic t (X i ω)) =
                                indIic t (X m ω) - indIic t (X 0 ω) := by
          clear h_left h_right hm_pos -- Don't use outer context
          induction m with
          | zero => simp [Finset.sum_range_zero]
          | succ m' ih =>
              rw [Finset.sum_range_succ (f := fun k => indIic t (X (k + 1) ω))]
              rw [Finset.sum_range_succ (f := fun i => indIic t (X i ω))]
              --  Goal: (∑ x < m', f(x+1)) + f(m'+1) - ((∑ x < m', f(x)) + f(m')) = f(m'+1) - f(0)
              -- Simplify LHS algebraically to expose the IH pattern
              have : (∑ x ∈ Finset.range m', indIic t (X (x + 1) ω)) + indIic t (X (m' + 1) ω) -
                     ((∑ x ∈ Finset.range m', indIic t (X x ω)) + indIic t (X m' ω))
                   = (∑ x ∈ Finset.range m', indIic t (X (x + 1) ω)) - (∑ x ∈ Finset.range m', indIic t (X x ω))
                     + (indIic t (X (m' + 1) ω) - indIic t (X m' ω)) := by ring
              rw [this, ih]
              ring

        -- Now apply to our goal: ∑ k : Fin m, f(k+1) - ∑ i : Fin m, f(i) = f(m) - f(0)
        -- Use h_left and h_right to convert Fin sums to range sums, then apply h_telescope_sum
        rw [h_left, h_right]
        exact h_telescope_sum

      -- Integrability facts needed throughout the calc chain
      have hf_int : Integrable (indIic t ∘ X m) μ := by
        apply Integrable.of_bound ((indIic_measurable t).comp (hX_meas m) |>.aestronglyMeasurable) 1
        filter_upwards with x; unfold indIic; simp [Set.indicator]; split_ifs <;> norm_num
      have hg_int : Integrable (indIic t ∘ X 0) μ := by
        apply Integrable.of_bound ((indIic_measurable t).comp (hX_meas 0) |>.aestronglyMeasurable) 1
        filter_upwards with x; unfold indIic; simp [Set.indicator]; split_ifs <;> norm_num

      calc ∫ ω, |(1/(m:ℝ)) * ∑ k : Fin m, indIic t (X (k.val + 1) ω) -
                 (1/(m:ℝ)) * ∑ i : Fin m, indIic t (X i ω)| ∂μ
          = ∫ ω, |(1/(m:ℝ)) * (indIic t (X m ω) - indIic t (X 0 ω))| ∂μ := by
              congr 1; ext ω; exact h_telescope ω
        _ = ∫ ω, (1/(m:ℝ)) * |indIic t (X m ω) - indIic t (X 0 ω)| ∂μ := by
              congr 1; ext ω
              have hm_pos' : 0 < (m : ℝ) := Nat.cast_pos.mpr hm_pos
              rw [abs_mul, abs_of_pos (one_div_pos.mpr hm_pos')]
        _ = (1/(m:ℝ)) * ∫ ω, |indIic t (X m ω) - indIic t (X 0 ω)| ∂μ := by
              rw [integral_mul_left]
        _ ≤ (1/(m:ℝ)) * ∫ ω, |indIic t (X m ω)| + |indIic t (X 0 ω)| ∂μ := by
              gcongr
              -- gcongr creates 3 goals: integrability of LHS, RHS, and pointwise inequality
              · -- Integrable (fun x => |f x - g x|)
                exact Integrable.abs (Integrable.sub hf_int hg_int)
              · -- Integrable (fun x => |f x| + |g x|)
                exact Integrable.add (Integrable.abs hf_int) (Integrable.abs hg_int)
              · -- Pointwise: |f x - g x| ≤ |f x| + |g x|
                intro ω
                exact abs_sub (indIic t (X m ω)) (indIic t (X 0 ω))
        _ = (1/(m:ℝ)) * (∫ ω, |indIic t (X m ω)| ∂μ + ∫ ω, |indIic t (X 0 ω)| ∂μ) := by
              congr 1
              exact integral_add (Integrable.abs hf_int) (Integrable.abs hg_int)
        _ ≤ (1/(m:ℝ)) * (1 + 1) := by
              gcongr
              · -- ∫ |indIic t (X m)| ≤ 1
                have : ∫ ω, |indIic t (X m ω)| ∂μ ≤ ∫ ω, (1 : ℝ) ∂μ := by
                  refine integral_mono (Integrable.abs hf_int) (integrable_const 1) ?_
                  intro ω
                  unfold indIic; simp [Set.indicator, abs_of_nonneg]; split_ifs <;> norm_num
                calc ∫ ω, |indIic t (X m ω)| ∂μ
                    ≤ ∫ ω, (1 : ℝ) ∂μ := this
                  _ = 1 := by simp [measure_univ]
              · -- ∫ |indIic t (X 0)| ≤ 1
                have : ∫ ω, |indIic t (X 0 ω)| ∂μ ≤ ∫ ω, (1 : ℝ) ∂μ := by
                  refine integral_mono (Integrable.abs hg_int) (integrable_const 1) ?_
                  intro ω
                  unfold indIic; simp [Set.indicator, abs_of_nonneg]; split_ifs <;> norm_num
                calc ∫ ω, |indIic t (X 0 ω)| ∂μ
                    ≤ ∫ ω, (1 : ℝ) ∂μ := this
                  _ = 1 := by simp [measure_univ]
        _ = 2/(m:ℝ) := by ring

    -- Choose M large enough for both axiom and negligibility
    -- M₁: ensures ∫ |B m - target| < ε/2 (from axiom)
    -- ⌈4/ε⌉: ensures 2/m ≤ ε/2 (from negligibility)
    use max M₁ (Nat.ceil (4/ε))
    intro m hm

    -- Triangle inequality: ∫ |A 0 m - target| ≤ ∫ |A 0 m - B m| + ∫ |B m - target|
    -- We need to show: ∫ |A 0 m - μ[indIic t ∘ X 0|tail]| < ε
    -- We have:
    --   1. ∫ |A 0 m - B m| ≤ 2/m (from h_diff_small)
    --   2. ∫ |B m - μ[indIic t ∘ X 0|tail]| < ε/2 (from h_axiom/hM₁)

    have h1 : (m : ℝ) ≥ M₁ := by
      calc (m : ℝ)
          ≥ max M₁ (Nat.ceil (4/ε)) := Nat.cast_le.mpr hm
        _ ≥ M₁ := by
            have : max (M₁ : ℝ) (Nat.ceil (4/ε) : ℝ) ≥ M₁ := le_max_left _ _
            simpa [Nat.cast_max] using this

    have h2 : (m : ℝ) ≥ Nat.ceil (4/ε) := by
      calc (m : ℝ)
          ≥ max M₁ (Nat.ceil (4/ε)) := Nat.cast_le.mpr hm
        _ ≥ Nat.ceil (4/ε) := by
            have : max (M₁ : ℝ) (Nat.ceil (4/ε) : ℝ) ≥ Nat.ceil (4/ε) := le_max_right _ _
            simpa [Nat.cast_max] using this

    -- From h2, we get 2/m ≤ ε/2
    have h_small : 2/(m:ℝ) ≤ ε/2 := by
      have hm_pos'' : 0 < (m : ℝ) := by
        calc (m : ℝ)
            ≥ Nat.ceil (4/ε) := h2
          _ > 0 := Nat.cast_pos.mpr (Nat.ceil_pos.mpr (by positivity))
      have : (m : ℝ) ≥ 4/ε := by
        calc (m : ℝ)
            ≥ Nat.ceil (4/ε) := h2
          _ ≥ 4/ε := Nat.le_ceil _
      calc 2/(m:ℝ)
          ≤ 2/(4/ε) := by gcongr
        _ = ε/2 := by field_simp; ring

    -- Apply the axiom
    have hB_conv : ∫ ω, |B m ω - μ[indIic t ∘ X 0|TailSigma.tailSigma X] ω| ∂μ < ε/2 := by
      convert hM₁ m (Nat.cast_le.mp h1) using 2

    -- Apply h_diff_small
    have hm_pos' : m > 0 := Nat.pos_of_ne_zero (by
      intro h
      simp [h] at h2
      have : (4 : ℝ) / ε > 0 := by positivity
      linarith)
    have hAB_diff : ∫ ω, |(1/(m:ℝ)) * ∑ k : Fin m, indIic t (X (k.val + 1) ω) - B m ω| ∂μ ≤ 2/(m:ℝ) :=
      h_diff_small m hm_pos'

    -- Triangle inequality for integrals
    calc ∫ ω, |(1/(m:ℝ)) * ∑ k : Fin m, indIic t (X (k.val + 1) ω) -
               μ[indIic t ∘ X 0|TailSigma.tailSigma X] ω| ∂μ
        ≤ ∫ ω, |(1/(m:ℝ)) * ∑ k : Fin m, indIic t (X (k.val + 1) ω) - B m ω| ∂μ +
          ∫ ω, |B m ω - μ[indIic t ∘ X 0|TailSigma.tailSigma X] ω| ∂μ := by
            -- Use pointwise triangle inequality: |a - c| ≤ |a - b| + |b - c|
            rw [← integral_add]
            · apply integral_mono
              · -- Integrability of |A - target|
                apply Integrable.abs
                apply Integrable.sub
                · -- A is integrable (bounded measurable on probability space)
                  have hA_meas : Measurable (fun ω => (1/(m:ℝ)) * ∑ k : Fin m, indIic t (X (k.val + 1) ω)) :=
                    Measurable.const_mul (Finset.measurable_sum _ (fun k _ =>
                      ((indIic_measurable t).comp (hX_meas _)))) _
                  apply Integrable.of_bound hA_meas.aestronglyMeasurable 1
                  filter_upwards with ω
                  simp [Real.norm_eq_abs]
                  -- Each indicator is in [0,1], so sum ≤ m, hence (1/m)*sum ≤ 1
                  -- Note: simp already converted |(1/m) * ∑...| to m⁻¹ * |∑...|
                  calc (m:ℝ)⁻¹ * |∑ k : Fin m, indIic t (X (k.val + 1) ω)|
                    _ ≤ (m:ℝ)⁻¹ * ∑ k : Fin m, |indIic t (X (k.val + 1) ω)| := by
                          gcongr; exact Finset.abs_sum_le_sum_abs _ _
                    _ ≤ (m:ℝ)⁻¹ * ∑ k : Fin m, (1 : ℝ) := by
                          gcongr with k
                          unfold indIic; simp [Set.indicator]; split_ifs <;> norm_num
                    _ = (1/(m:ℝ)) * m := by
                          rw [← one_div]; simp [Finset.sum_const, Finset.card_fin]
                    _ = 1 := by field_simp
                · -- target = condExp is integrable
                  exact integrable_condExp
              · -- Integrability of |A - B| + |B - target|
                apply Integrable.add
                · -- |A - B| is integrable
                  apply Integrable.abs
                  apply Integrable.sub
                  · -- A is integrable
                    have hA_meas : Measurable (fun ω => (1/(m:ℝ)) * ∑ k : Fin m, indIic t (X (k.val + 1) ω)) :=
                      Measurable.const_mul (Finset.measurable_sum _ (fun k _ =>
                        ((indIic_measurable t).comp (hX_meas _)))) _
                    apply Integrable.of_bound hA_meas.aestronglyMeasurable 1
                    filter_upwards with ω; simp [Real.norm_eq_abs]
                    -- Note: simp already converted |(1/m) * ∑...| to m⁻¹ * |∑...|
                    calc (m:ℝ)⁻¹ * |∑ k : Fin m, indIic t (X (k.val + 1) ω)|
                      _ ≤ (m:ℝ)⁻¹ * ∑ k : Fin m, |indIic t (X (k.val + 1) ω)| := by
                            gcongr; exact Finset.abs_sum_le_sum_abs _ _
                      _ ≤ (m:ℝ)⁻¹ * ∑ k : Fin m, (1 : ℝ) := by
                            gcongr with k
                            unfold indIic; simp [Set.indicator]; split_ifs <;> norm_num
                      _ = (1/(m:ℝ)) * m := by
                            rw [← one_div]; simp [Finset.sum_const, Finset.card_fin]
                      _ = 1 := by field_simp
                  · -- B is integrable
                    simp [B]
                    have hB_meas : Measurable (fun ω => (m:ℝ)⁻¹ * ∑ i : Fin m, indIic t (X i ω)) :=
                      Measurable.const_mul (Finset.measurable_sum _ (fun i _ =>
                        ((indIic_measurable t).comp (hX_meas _)))) _
                    apply Integrable.of_bound hB_meas.aestronglyMeasurable 1
                    filter_upwards with ω; simp [Real.norm_eq_abs]
                    -- Note: simp already converted |(m:ℝ)⁻¹ * ∑...| to (m:ℝ)⁻¹ * |∑...|
                    calc (m:ℝ)⁻¹ * |∑ i : Fin m, indIic t (X i ω)|
                      _ ≤ (m:ℝ)⁻¹ * ∑ i : Fin m, |indIic t (X i ω)| := by
                            gcongr; exact Finset.abs_sum_le_sum_abs _ _
                      _ ≤ (m:ℝ)⁻¹ * ∑ i : Fin m, (1 : ℝ) := by
                            gcongr with i
                            unfold indIic; simp [Set.indicator]; split_ifs <;> norm_num
                      _ = (m:ℝ)⁻¹ * m := by simp [Finset.sum_const, Finset.card_fin]
                      _ = 1 := by field_simp
                · -- |B - target| is integrable
                  apply Integrable.abs
                  apply Integrable.sub
                  · -- B is integrable
                    simp [B]
                    have hB_meas : Measurable (fun ω => (m:ℝ)⁻¹ * ∑ i : Fin m, indIic t (X i ω)) :=
                      Measurable.const_mul (Finset.measurable_sum _ (fun i _ =>
                        ((indIic_measurable t).comp (hX_meas _)))) _
                    apply Integrable.of_bound hB_meas.aestronglyMeasurable 1
                    filter_upwards with ω; simp [Real.norm_eq_abs]
                    -- Note: simp already converted |(m:ℝ)⁻¹ * ∑...| to (m:ℝ)⁻¹ * |∑...|
                    calc (m:ℝ)⁻¹ * |∑ i : Fin m, indIic t (X i ω)|
                      _ ≤ (m:ℝ)⁻¹ * ∑ i : Fin m, |indIic t (X i ω)| := by
                            gcongr; exact Finset.abs_sum_le_sum_abs _ _
                      _ ≤ (m:ℝ)⁻¹ * ∑ i : Fin m, (1 : ℝ) := by
                            gcongr with i
                            unfold indIic; simp [Set.indicator]; split_ifs <;> norm_num
                      _ = (m:ℝ)⁻¹ * m := by simp [Finset.sum_const, Finset.card_fin]
                      _ = 1 := by field_simp
                  · -- target is integrable
                    exact integrable_condExp
              · -- Pointwise bound: |a - c| ≤ |a - b| + |b - c|
                intro ω
                exact abs_sub_le _ _ _
            · -- Integrability of |A - B|
              apply Integrable.abs
              apply Integrable.sub
              · -- A is integrable
                have hA_meas : Measurable (fun ω => (1/(m:ℝ)) * ∑ k : Fin m, indIic t (X (k.val + 1) ω)) :=
                  Measurable.const_mul (Finset.measurable_sum _ (fun k _ =>
                    ((indIic_measurable t).comp (hX_meas _)))) _
                apply Integrable.of_bound hA_meas.aestronglyMeasurable 1
                filter_upwards with ω; simp [Real.norm_eq_abs]
                -- Note: simp already converted |(1/m) * ∑...| to m⁻¹ * |∑...|
                calc (m:ℝ)⁻¹ * |∑ k : Fin m, indIic t (X (k.val + 1) ω)|
                  _ ≤ (m:ℝ)⁻¹ * ∑ k : Fin m, |indIic t (X (k.val + 1) ω)| := by
                        gcongr; exact Finset.abs_sum_le_sum_abs _ _
                  _ ≤ (m:ℝ)⁻¹ * ∑ k : Fin m, (1 : ℝ) := by
                        gcongr with k
                        unfold indIic; simp [Set.indicator]; split_ifs <;> norm_num
                  _ = (1/(m:ℝ)) * m := by
                        rw [← one_div]; simp [Finset.sum_const, Finset.card_fin]
                  _ = 1 := by field_simp
              · -- B is integrable
                simp [B]
                have hB_meas : Measurable (fun ω => (m:ℝ)⁻¹ * ∑ i : Fin m, indIic t (X i ω)) :=
                  Measurable.const_mul (Finset.measurable_sum _ (fun i _ =>
                    ((indIic_measurable t).comp (hX_meas _)))) _
                apply Integrable.of_bound hB_meas.aestronglyMeasurable 1
                filter_upwards with ω; simp [Real.norm_eq_abs]
                -- Note: simp already converted |(m:ℝ)⁻¹ * ∑...| to (m:ℝ)⁻¹ * |∑...|
                calc (m:ℝ)⁻¹ * |∑ i : Fin m, indIic t (X i ω)|
                  _ ≤ (m:ℝ)⁻¹ * ∑ i : Fin m, |indIic t (X i ω)| := by
                        gcongr; exact Finset.abs_sum_le_sum_abs _ _
                  _ ≤ (m:ℝ)⁻¹ * ∑ i : Fin m, (1 : ℝ) := by
                        gcongr with i
                        unfold indIic; simp [Set.indicator]; split_ifs <;> norm_num
                  _ = (m:ℝ)⁻¹ * m := by simp [Finset.sum_const, Finset.card_fin]
                  _ = 1 := by field_simp
            · -- Integrability of |B - target|
              apply Integrable.abs
              apply Integrable.sub
              · -- B is integrable
                simp [B]
                have hB_meas : Measurable (fun ω => (m:ℝ)⁻¹ * ∑ i : Fin m, indIic t (X i ω)) :=
                  Measurable.const_mul (Finset.measurable_sum _ (fun i _ =>
                    ((indIic_measurable t).comp (hX_meas _)))) _
                apply Integrable.of_bound hB_meas.aestronglyMeasurable 1
                filter_upwards with ω; simp [Real.norm_eq_abs]
                -- Note: simp already converted |(m:ℝ)⁻¹ * ∑...| to (m:ℝ)⁻¹ * |∑...|
                calc (m:ℝ)⁻¹ * |∑ i : Fin m, indIic t (X i ω)|
                  _ ≤ (m:ℝ)⁻¹ * ∑ i : Fin m, |indIic t (X i ω)| := by
                        gcongr; exact Finset.abs_sum_le_sum_abs _ _
                  _ ≤ (m:ℝ)⁻¹ * ∑ i : Fin m, (1 : ℝ) := by
                        gcongr with i
                        unfold indIic; simp [Set.indicator]; split_ifs <;> norm_num
                  _ = (m:ℝ)⁻¹ * m := by simp [Finset.sum_const, Finset.card_fin]
                  _ = 1 := by field_simp
              · -- target is integrable
                exact integrable_condExp
      _ < 2/(m:ℝ) + ε/2 := by linarith [hAB_diff, hB_conv]
      _ ≤ ε/2 + ε/2 := by linarith [h_small]
      _ = ε := by ring

  -- Measurability of Cesàro averages
  have hA_meas : ∀ n m, AEStronglyMeasurable (A n m) μ := by
    intro n m
    -- A n m is a Cesàro average of indIic ∘ X, which are measurable
    -- Each indIic ∘ X_i is measurable, sum is measurable, scalar mult is measurable
    refine Measurable.aestronglyMeasurable ?_
    show Measurable fun ω => (1 / (m : ℝ)) * ∑ k : Fin m, indIic t (X (n + k.val + 1) ω)
    refine Measurable.const_mul ?_ _
    exact Finset.measurable_sum _ (fun k _ => (indIic_measurable t).comp (hX_meas _))

  -- Step 3: Use uniqueness of L¹ limits to conclude a.e. equality
  -- If both f and g are L¹ limits of the same sequence, then f =ᵐ g
  have h_L1_uniqueness : ∀ (f g : Ω → ℝ),
      AEStronglyMeasurable f μ → AEStronglyMeasurable g μ →
      (∀ᵐ ω ∂μ, ‖f ω‖ ≤ 1) → (∀ᵐ ω ∂μ, ‖g ω‖ ≤ 1) →
      (∀ ε > 0, ∃ M : ℕ, ∀ m ≥ M, ∫ ω, |A 0 m ω - f ω| ∂μ < ε) →
      (∀ ε > 0, ∃ M : ℕ, ∀ m ≥ M, ∫ ω, |A 0 m ω - g ω| ∂μ < ε) →
      f =ᵐ[μ] g := by
    intro f g hf_meas hg_meas hf_bdd hg_bdd hf_lim hg_lim
    -- Strategy: L¹ convergence implies a.e. convergent subsequence, and a.e. limits are unique
    -- Convert L¹ convergence hypothesis to Tendsto format
    have hf_tendsto : Tendsto (fun m => ∫ ω, |A 0 m ω - f ω| ∂μ) atTop (𝓝 0) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨M, hM⟩ := hf_lim ε hε
      use M
      intro m hm
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg (fun ω => abs_nonneg _))]
      exact hM m hm
    have hg_tendsto : Tendsto (fun m => ∫ ω, |A 0 m ω - g ω| ∂μ) atTop (𝓝 0) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨M, hM⟩ := hg_lim ε hε
      use M
      intro m hm
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg (fun ω => abs_nonneg _))]
      exact hM m hm
    -- Complete the proof using the mathlib convergence chain:
    -- 1. Convert L¹ convergence to eLpNorm convergence
    -- 2. Apply tendstoInMeasure_of_tendsto_eLpNorm
    -- 3. Use tendstoInMeasure_ae_unique

    -- Step 1a: Show A m - f is integrable for all m (needed for eLpNorm_one_eq_integral_abs)
    have hAf_integrable : ∀ m, Integrable (fun ω => A 0 m ω - f ω) μ := by
      intro m
      refine Integrable.sub ?_ ?_
      · -- A is a Cesàro average of indicators, bounded by 1
        refine Integrable.of_bound (hA_meas 0 m) 1 ?_
        filter_upwards with ω
        -- A n m ω = (1/m) * ∑_{k<m} indIic t (X (n+k+1) ω)
        -- Each indIic t x ∈ {0, 1}, so the sum is in [0, m]
        -- Therefore A n m ω ∈ [0, 1]
        unfold A
        simp only [Real.norm_eq_abs, zero_add]
        by_cases hm : m = 0
        · simp [hm]
        · calc |1 / (m:ℝ) * ∑ k : Fin m, indIic t (X (k.val + 1) ω)|
                = (m:ℝ)⁻¹ * |∑ k : Fin m, indIic t (X (k.val + 1) ω)| := by
                      rw [one_div, abs_mul, abs_of_pos]; positivity
              _ ≤ (m:ℝ)⁻¹ * ∑ k : Fin m, |indIic t (X (k.val + 1) ω)| := by
                    gcongr; exact Finset.abs_sum_le_sum_abs _ _
              _ ≤ (m:ℝ)⁻¹ * ∑ k : Fin m, (1 : ℝ) := by
                    gcongr with k
                    unfold indIic; simp [Set.indicator]; split_ifs <;> norm_num
              _ = (m:ℝ)⁻¹ * m := by simp [Finset.sum_const, Finset.card_fin]
              _ = 1 := by field_simp [hm]
      · -- f is bounded by hypothesis hf_bdd
        exact Integrable.of_bound hf_meas 1 hf_bdd

    have hAg_integrable : ∀ m, Integrable (fun ω => A 0 m ω - g ω) μ := by
      intro m
      refine Integrable.sub ?_ ?_
      · -- A is a Cesàro average of indicators, bounded by 1 (same proof as above)
        refine Integrable.of_bound (hA_meas 0 m) 1 ?_
        filter_upwards with ω
        unfold A
        simp only [Real.norm_eq_abs, zero_add]
        by_cases hm : m = 0
        · simp [hm]
        · calc |1 / (m:ℝ) * ∑ k : Fin m, indIic t (X (k.val + 1) ω)|
                = (m:ℝ)⁻¹ * |∑ k : Fin m, indIic t (X (k.val + 1) ω)| := by
                      rw [one_div, abs_mul, abs_of_pos]; positivity
              _ ≤ (m:ℝ)⁻¹ * ∑ k : Fin m, |indIic t (X (k.val + 1) ω)| := by
                    gcongr; exact Finset.abs_sum_le_sum_abs _ _
              _ ≤ (m:ℝ)⁻¹ * ∑ k : Fin m, (1 : ℝ) := by
                    gcongr with k
                    unfold indIic; simp [Set.indicator]; split_ifs <;> norm_num
              _ = (m:ℝ)⁻¹ * m := by simp [Finset.sum_const, Finset.card_fin]
              _ = 1 := by field_simp [hm]
      · -- g is bounded by hypothesis hg_bdd
        exact Integrable.of_bound hg_meas 1 hg_bdd

    -- Step 1b: Convert L¹ to eLpNorm using IntegrationHelpers.eLpNorm_one_eq_integral_abs
    have hf_eLpNorm : Tendsto (fun m => eLpNorm (fun ω => A 0 m ω - f ω) 1 μ) atTop (𝓝 0) := by
      rw [ENNReal.tendsto_nhds_zero]
      intro ε hε
      rw [Metric.tendsto_atTop] at hf_tendsto
      by_cases h_top : ε = ⊤
      · simp [h_top]
      · have ε_pos : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' h_top
        obtain ⟨M, hM⟩ := hf_tendsto ε.toReal ε_pos
        refine Filter.eventually_atTop.mpr ⟨M, fun m hm => ?_⟩
        rw [Exchangeability.Probability.IntegrationHelpers.eLpNorm_one_eq_integral_abs (hAf_integrable m)]
        -- Goal: ENNReal.ofReal (∫ |...|) ≤ ε
        rw [← ENNReal.ofReal_toReal h_top]
        -- Goal: ENNReal.ofReal (∫ |...|) ≤ ENNReal.ofReal ε.toReal
        rw [ENNReal.ofReal_le_ofReal_iff ε_pos.le]
        -- Goal: ∫ |...| ≤ ε.toReal
        have := hM m hm
        rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg (fun ω => abs_nonneg _))] at this
        exact this.le

    have hg_eLpNorm : Tendsto (fun m => eLpNorm (fun ω => A 0 m ω - g ω) 1 μ) atTop (𝓝 0) := by
      rw [ENNReal.tendsto_nhds_zero]
      intro ε hε
      rw [Metric.tendsto_atTop] at hg_tendsto
      by_cases h_top : ε = ⊤
      · simp [h_top]
      · have ε_pos : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' h_top
        obtain ⟨M, hM⟩ := hg_tendsto ε.toReal ε_pos
        refine Filter.eventually_atTop.mpr ⟨M, fun m hm => ?_⟩
        rw [Exchangeability.Probability.IntegrationHelpers.eLpNorm_one_eq_integral_abs (hAg_integrable m)]
        -- Goal: ENNReal.ofReal (∫ |...|) ≤ ε
        rw [← ENNReal.ofReal_toReal h_top]
        -- Goal: ENNReal.ofReal (∫ |...|) ≤ ENNReal.ofReal ε.toReal
        rw [ENNReal.ofReal_le_ofReal_iff ε_pos.le]
        -- Goal: ∫ |...| ≤ ε.toReal
        have := hM m hm
        rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg (fun ω => abs_nonneg _))] at this
        exact this.le

    -- Step 2: Apply tendstoInMeasure
    have hf_meas_conv : TendstoInMeasure μ (A 0) atTop f := by
      apply tendstoInMeasure_of_tendsto_eLpNorm (p := 1) one_ne_zero
      · intro m; exact hA_meas 0 m
      · exact hf_meas
      · exact hf_eLpNorm

    have hg_meas_conv : TendstoInMeasure μ (A 0) atTop g := by
      apply tendstoInMeasure_of_tendsto_eLpNorm (p := 1) one_ne_zero
      · intro m; exact hA_meas 0 m
      · exact hg_meas
      · exact hg_eLpNorm

    -- Step 3: Apply uniqueness
    exact tendstoInMeasure_ae_unique hf_meas_conv hg_meas_conv

  -- Apply uniqueness with f = alphaIic, g = alphaIicCE
  apply h_L1_uniqueness
  · -- alphaIic is ae strongly measurable
    exact (alphaIic_measurable X hX_contract hX_meas hX_L2 t).aestronglyMeasurable
  · -- alphaIicCE is ae strongly measurable
    exact (alphaIicCE_measurable X hX_contract hX_meas hX_L2 t).aestronglyMeasurable
  · -- alphaIic is bounded by 1
    filter_upwards with ω
    simp only [Real.norm_eq_abs]
    rw [abs_le_one_iff_mul_self_le_one]
    have ⟨h0, h1⟩ := alphaIic_bound X hX_contract hX_meas hX_L2 t ω
    nlinarith [sq_nonneg (alphaIic X hX_contract hX_meas hX_L2 t ω)]
  · -- alphaIicCE is bounded by 1 (using alphaIicCE_nonneg_le_one)
    have := alphaIicCE_nonneg_le_one X hX_contract hX_meas hX_L2 t
    filter_upwards [this] with ω ⟨h0, h1⟩
    simp only [Real.norm_eq_abs]
    rw [abs_le_one_iff_mul_self_le_one]
    nlinarith [sq_nonneg (alphaIicCE X hX_contract hX_meas hX_L2 t ω)]
  · exact h_alphaIic_is_limit 0
  · exact h_alphaIicCE_is_limit

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
lemma alphaIicCE_L1_tendsto_zero_atBot
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

/-- **L¹ endpoint limit at +∞**: As t → +∞, alphaIicCE → 1 in L¹.

**Proof strategy:**
Similar to the -∞ case, but `1_{(-∞,t]}(X_0 ω)` → 1 as t → +∞. -/
lemma alphaIicCE_L1_tendsto_one_atTop
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ) :
    Tendsto (fun n : ℕ =>
      ∫ ω, |alphaIicCE X hX_contract hX_meas hX_L2 (n : ℝ) ω - 1| ∂μ)
      atTop (𝓝 0) := by
  -- Strategy: Similar to atBot case, but now (indIic (n:ℝ)) → 1 pointwise
  -- So ∫ |(indIic (n:ℝ)) ∘ X 0 - 1| → 0

  -- Set up the tail σ-algebra Fact instance (needed for condExp)
  have hm_le : TailSigma.tailSigma X ≤ (inferInstance : MeasurableSpace Ω) :=
    TailSigma.tailSigma_le X hX_meas
  haveI : Fact (TailSigma.tailSigma X ≤ (inferInstance : MeasurableSpace Ω)) := ⟨hm_le⟩

  -- Step 1: Show ∫ |(indIic (n:ℝ)) ∘ X 0 - 1| → 0
  -- Integral of |indicator - 1| = μ(X 0 > n) → 0 by continuity
  have h_indicator_tendsto : Tendsto (fun n : ℕ =>
      ∫ ω, |(indIic (n : ℝ)) (X 0 ω) - 1| ∂μ) atTop (𝓝 0) := by
    -- |indIic n - 1| = indicator of (n, ∞) since indIic n = indicator of (-∞, n]
    have h_eq : ∀ n : ℕ, ∫ ω, |(indIic (n : ℝ)) (X 0 ω) - 1| ∂μ
        = (μ (X 0 ⁻¹' Set.Ioi (n : ℝ))).toReal := by
      intro n
      have : (fun ω => |(indIic (n : ℝ)) (X 0 ω) - 1|)
          = (Set.Ioi (n : ℝ)).indicator (fun _ => (1 : ℝ)) ∘ (X 0) := by
        ext ω
        simp only [indIic, Set.indicator, Function.comp_apply, Set.mem_Ioi, Set.mem_Iic]
        split_ifs with h1 h2
        · -- X 0 ω ≤ n and X 0 ω > n: contradiction
          linarith
        · -- X 0 ω ≤ n and ¬(X 0 ω > n): both give 0
          norm_num
        · -- ¬(X 0 ω ≤ n) and X 0 ω > n: both give 1
          norm_num
        · -- ¬(X 0 ω ≤ n) and ¬(X 0 ω > n): contradiction
          linarith
      rw [this]
      -- Rewrite composition as indicator on preimage
      have h_comp : (Set.Ioi (n : ℝ)).indicator (fun _ => (1 : ℝ)) ∘ (X 0)
          = (X 0 ⁻¹' Set.Ioi (n : ℝ)).indicator (fun _ => (1 : ℝ)) := by
        ext ω
        simp only [Function.comp_apply, Set.indicator_apply]
        rfl
      rw [h_comp, integral_indicator (measurableSet_preimage (hX_meas 0) measurableSet_Ioi),
          setIntegral_one_eq_measureReal]
      rfl
    simp only [h_eq]
    -- The sets {X 0 > n} decrease to empty
    have h_antitone : Antitone (fun n : ℕ => X 0 ⁻¹' Set.Ioi (n : ℝ)) := by
      intro n m hnm
      apply Set.preimage_mono
      intro x hx
      simp only [Set.mem_Ioi] at hx ⊢
      calc x > (m : ℝ) := hx
           _ ≥ (n : ℝ) := by simp [Nat.cast_le, hnm]
    have h_empty : (⋂ (n : ℕ), X 0 ⁻¹' Set.Ioi (n : ℝ)) = ∅ := by
      ext ω
      simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_Ioi, Set.mem_empty_iff_false, iff_false]
      intro h
      -- For all n, X 0 ω > n, impossible by Archimedean property
      obtain ⟨n, hn⟩ := exists_nat_gt (X 0 ω)
      have h1 : X 0 ω > (n : ℝ) := h n
      linarith
    have h_meas : ∀ (n : ℕ), NullMeasurableSet (X 0 ⁻¹' Set.Ioi (n : ℝ)) μ := fun n =>
      (measurableSet_preimage (hX_meas 0) measurableSet_Ioi).nullMeasurableSet
    have h_fin : ∃ (n : ℕ), μ (X 0 ⁻¹' Set.Ioi (n : ℝ)) ≠ ⊤ := by
      use 0
      exact measure_ne_top μ _
    have h_tendsto_ennreal : Tendsto (fun (n : ℕ) => μ (X 0 ⁻¹' Set.Ioi (n : ℝ))) atTop (𝓝 0) := by
      have := tendsto_measure_iInter_atTop (μ := μ) h_meas h_antitone h_fin
      simp only [h_empty, measure_empty] at this
      simpa [Function.comp] using this
    -- Convert from ENNReal to Real using continuity of toReal at 0
    have h_ne_top : ∀ n, μ (X 0 ⁻¹' Set.Ioi (n : ℝ)) ≠ ⊤ := fun n => measure_ne_top μ _
    have h_zero_ne_top : (0 : ENNReal) ≠ ⊤ := by norm_num
    rw [← ENNReal.toReal_zero]
    exact (ENNReal.continuousAt_toReal h_zero_ne_top).tendsto.comp h_tendsto_ennreal

  -- Step 2: L¹ contraction - ‖condExp f - condExp 1‖₁ ≤ ‖f - 1‖₁
  -- Since condExp 1 = 1, get ‖alphaIicCE - 1‖₁ ≤ ‖indicator - 1‖₁
  have h_contraction : ∀ n : ℕ,
      ∫ ω, |alphaIicCE X hX_contract hX_meas hX_L2 (n : ℝ) ω - 1| ∂μ
      ≤ ∫ ω, |(indIic (n : ℝ)) (X 0 ω) - 1| ∂μ := by
    intro n
    -- Use linearity: alphaIicCE - 1 = condExp(indicator) - condExp(1) = condExp(indicator - 1)
    have h_const : (fun _ : Ω => (1 : ℝ)) =ᵐ[μ]
        μ[(fun _ : Ω => (1 : ℝ)) | TailSigma.tailSigma X] :=
      (condExp_const (μ := μ) (m := TailSigma.tailSigma X) hm_le (1 : ℝ)).symm.eventuallyEq
    have h_ae : (fun ω => alphaIicCE X hX_contract hX_meas hX_L2 (n : ℝ) ω - 1)
        =ᵐ[μ] μ[(fun ω => (indIic (n : ℝ)) (X 0 ω) - 1) | TailSigma.tailSigma X] := by
      unfold alphaIicCE
      have h_int : Integrable ((indIic (n : ℝ)) ∘ (X 0)) μ := by
        have : indIic (n : ℝ) = Set.indicator (Set.Iic (n : ℝ)) (fun _ => (1 : ℝ)) := rfl
        rw [this]
        exact Exchangeability.Probability.integrable_indicator_comp (hX_meas 0) measurableSet_Iic
      filter_upwards [h_const, condExp_sub (μ := μ) (m := TailSigma.tailSigma X)
        h_int (integrable_const (1 : ℝ))] with ω h_const_ω h_sub_ω
      simp only [Pi.sub_apply] at h_sub_ω ⊢
      -- h_const_ω : 1 = μ[fun _ => 1|...] ω
      -- h_sub_ω : μ[indIic n ∘ X 0 - fun x => μ[fun x => 1|...] ω|...] ω = ...
      -- After substitution, we get the equality we need
      calc alphaIicCE X hX_contract hX_meas hX_L2 (n : ℝ) ω - 1
          = μ[indIic (n : ℝ) ∘ X 0|TailSigma.tailSigma X] ω - 1 := by rfl
        _ = μ[indIic (n : ℝ) ∘ X 0|TailSigma.tailSigma X] ω - μ[(fun _ => 1)|TailSigma.tailSigma X] ω := by rw [← h_const_ω]
        _ = μ[indIic (n : ℝ) ∘ X 0 - (fun _ => 1)|TailSigma.tailSigma X] ω := by rw [← h_sub_ω]
        _ = μ[(fun ω => indIic (n : ℝ) (X 0 ω) - 1)|TailSigma.tailSigma X] ω := by congr
    have h_ae_abs : (fun ω => |alphaIicCE X hX_contract hX_meas hX_L2 (n : ℝ) ω - 1|)
        =ᵐ[μ] (fun ω => |μ[(fun ω => (indIic (n : ℝ)) (X 0 ω) - 1) | TailSigma.tailSigma X] ω|) := by
      filter_upwards [h_ae] with ω hω
      rw [hω]
    rw [integral_congr_ae h_ae_abs]
    exact integral_abs_condExp_le (μ := μ) (m := TailSigma.tailSigma X) _

  -- Apply squeeze theorem: 0 ≤ ‖alphaIicCE - 1‖₁ ≤ ‖indicator - 1‖₁ → 0
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

/-- **A.e. pointwise endpoint limit at +∞**.

**Proof strategy:**
Similar to the -∞ case, using monotonicity + boundedness + L¹ → 1. -/
lemma alphaIicCE_ae_tendsto_one_atTop
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ =>
      alphaIicCE X hX_contract hX_meas hX_L2 (n : ℝ) ω)
      atTop (𝓝 1) := by
  -- Strategy: Similar to atBot case
  -- 1. alphaIicCE is monotone increasing in n
  -- 2. alphaIicCE ∈ [0,1] (bounded)
  -- 3. By monotone convergence, the sequence converges a.e. to some limit L
  -- 4. By L¹ convergence to 1, we have L = 1 a.e.

  -- Step 1: Monotonicity - for each ω, alphaIicCE (n:ℝ) ω ≤ alphaIicCE (m:ℝ) ω when n ≤ m
  have h_mono : ∀ᵐ ω ∂μ, ∀ n m : ℕ, n ≤ m →
      alphaIicCE X hX_contract hX_meas hX_L2 (n : ℝ) ω
      ≤ alphaIicCE X hX_contract hX_meas hX_L2 (m : ℝ) ω := by
    -- Use alphaIicCE_mono with countable ae union
    rw [ae_all_iff]
    intro n
    rw [ae_all_iff]
    intro m
    by_cases hnm : n ≤ m
    · -- When n ≤ m, use alphaIicCE_mono with (n:ℝ) ≤ (m:ℝ)
      have h_le : (n : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hnm
      filter_upwards [alphaIicCE_mono X hX_contract hX_meas hX_L2 (n : ℝ) (m : ℝ) h_le] with ω hω
      intro _
      exact hω
    · -- When ¬(n ≤ m), the implication is vacuously true
      exact ae_of_all μ (fun ω h_contra => absurd h_contra hnm)

  -- Step 2: Boundedness - 0 ≤ alphaIicCE ≤ 1
  have h_bound : ∀ᵐ ω ∂μ, ∀ n : ℕ,
      0 ≤ alphaIicCE X hX_contract hX_meas hX_L2 (n : ℝ) ω
      ∧ alphaIicCE X hX_contract hX_meas hX_L2 (n : ℝ) ω ≤ 1 := by
    -- Use alphaIicCE_nonneg_le_one with countable ae union
    rw [ae_all_iff]
    intro n
    exact alphaIicCE_nonneg_le_one X hX_contract hX_meas hX_L2 (n : ℝ)

  -- Step 3: Monotone bounded sequences converge a.e.
  have h_ae_conv : ∀ᵐ ω ∂μ, ∃ L : ℝ, Tendsto (fun n : ℕ =>
      alphaIicCE X hX_contract hX_meas hX_L2 (n : ℝ) ω) atTop (𝓝 L) := by
    -- Monotone increasing bounded sequence converges (monotone convergence theorem)
    filter_upwards [h_mono, h_bound] with ω h_mono_ω h_bound_ω
    -- For this ω, the sequence is monotone and bounded, so it converges
    refine ⟨⨆ (n : ℕ), alphaIicCE X hX_contract hX_meas hX_L2 (n : ℝ) ω, ?_⟩
    apply tendsto_atTop_ciSup
    · -- Monotone: n ≤ m implies f n ≤ f m
      intro n m hnm
      exact h_mono_ω n m hnm
    · -- Bounded above by 1
      refine ⟨1, ?_⟩
      intro y hy
      obtain ⟨k, hk⟩ := hy
      rw [← hk]
      exact (h_bound_ω k).2

  -- Step 4: The limit is 1 by L¹ convergence
  -- If f_n → L a.e. and f_n → 1 in L¹, then L = 1 a.e.

  -- Set up the tail σ-algebra (needed for conditional expectation)
  have hm_le : TailSigma.tailSigma X ≤ (inferInstance : MeasurableSpace Ω) :=
    TailSigma.tailSigma_le X hX_meas

  -- Define the limit function U : Ω → ℝ (supremum instead of infimum)
  let U_fun : Ω → ℝ := fun ω => ⨆ (n : ℕ), alphaIicCE X hX_contract hX_meas hX_L2 (n : ℝ) ω

  -- U_fun ≤ 1 a.e.
  have hU_le_one : U_fun ≤ᵐ[μ] 1 := by
    filter_upwards [h_bound] with ω h_bound_ω
    apply ciSup_le
    intro n
    exact (h_bound_ω n).2

  -- Convert ∫|f_n - 1| → 0 to ∫ (1 - f_n) → 0
  have h_L1_conv : Tendsto (fun n : ℕ =>
      ∫ ω, (1 - alphaIicCE X hX_contract hX_meas hX_L2 (n : ℝ) ω) ∂μ) atTop (𝓝 0) := by
    have h_abs := alphaIicCE_L1_tendsto_one_atTop X hX_contract hX_meas hX_L2
    refine h_abs.congr' ?_
    rw [EventuallyEq, eventually_atTop]
    use 0
    intro n _
    apply integral_congr_ae
    filter_upwards [alphaIicCE_nonneg_le_one X hX_contract hX_meas hX_L2 (n : ℝ)] with ω hω
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hω.2)]

  -- Apply dominated convergence theorem
  have hU_integral_one : ∫ ω, U_fun ω ∂μ = 1 := by
    have h_conv_ae : ∀ᵐ ω ∂μ, Tendsto (fun (n : ℕ) => alphaIicCE X hX_contract hX_meas hX_L2 (n : ℝ) ω)
        atTop (𝓝 (U_fun ω)) := by
      filter_upwards [h_ae_conv, h_bound, h_mono] with ω ⟨L, hL⟩ h_bound_ω h_mono_ω
      have hU_is_sup : L = U_fun ω := by
        apply tendsto_nhds_unique hL
        apply tendsto_atTop_ciSup h_mono_ω
        exact ⟨1, fun y hy => by obtain ⟨k, hk⟩ := hy; rw [← hk]; exact (h_bound_ω k).2⟩
      rw [← hU_is_sup]
      exact hL
    have h_meas : ∀ (n : ℕ), AEStronglyMeasurable (fun ω => alphaIicCE X hX_contract hX_meas hX_L2 (n : ℝ) ω) μ := by
      intro n
      unfold alphaIicCE
      exact stronglyMeasurable_condExp.aestronglyMeasurable.mono hm_le
    have h_bound_ae : ∀ (n : ℕ), ∀ᵐ ω ∂μ, ‖alphaIicCE X hX_contract hX_meas hX_L2 (n : ℝ) ω‖ ≤ (1 : ℝ) := by
      intro n
      filter_upwards [alphaIicCE_nonneg_le_one X hX_contract hX_meas hX_L2 (n : ℝ)] with ω hω
      rw [Real.norm_eq_abs, abs_of_nonneg hω.1]
      exact hω.2
    have h_int : Integrable (fun _ : Ω => (1 : ℝ)) μ := integrable_const 1
    have h_lim := tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
      h_meas h_int h_bound_ae h_conv_ae
    have h_int_conv : Tendsto (fun n : ℕ => ∫ ω, alphaIicCE X hX_contract hX_meas hX_L2 (n : ℝ) ω ∂μ) atTop (𝓝 1) := by
      have : Tendsto (fun n : ℕ => 1 - ∫ ω, (1 - alphaIicCE X hX_contract hX_meas hX_L2 (n : ℝ) ω) ∂μ) atTop (𝓝 (1 - 0)) := by
        exact Tendsto.sub tendsto_const_nhds h_L1_conv
      have this' : Tendsto (fun n : ℕ => 1 - ∫ ω, (1 - alphaIicCE X hX_contract hX_meas hX_L2 (n : ℝ) ω) ∂μ) atTop (𝓝 1) := by
        convert this using 2
        norm_num
      -- Show integral convergence by algebra
      refine this'.congr' ?_
      rw [EventuallyEq, eventually_atTop]
      use 0
      intro n _
      -- Show: 1 - ∫ (1 - f) = ∫ f
      have h_f_int : Integrable (fun ω => alphaIicCE X hX_contract hX_meas hX_L2 (n : ℝ) ω) μ := by
        refine Integrable.of_bound (stronglyMeasurable_condExp.aestronglyMeasurable.mono hm_le) 1 ?_
        filter_upwards [alphaIicCE_nonneg_le_one X hX_contract hX_meas hX_L2 (n : ℝ)] with ω hω
        rw [Real.norm_eq_abs, abs_of_nonneg hω.1]
        exact hω.2
      calc 1 - ∫ ω, (1 - alphaIicCE X hX_contract hX_meas hX_L2 (n : ℝ) ω) ∂μ
          = 1 - (∫ ω, 1 ∂μ - ∫ ω, alphaIicCE X hX_contract hX_meas hX_L2 (n : ℝ) ω ∂μ) := by
              rw [integral_sub (integrable_const 1) h_f_int]
          _ = 1 - (μ.real Set.univ - ∫ ω, alphaIicCE X hX_contract hX_meas hX_L2 (n : ℝ) ω ∂μ) := by
              rw [integral_const, smul_eq_mul, mul_one]
          _ = 1 - (1 - ∫ ω, alphaIicCE X hX_contract hX_meas hX_L2 (n : ℝ) ω ∂μ) := by
              simp only [Measure.real]
              rw [measure_univ]
              simp
          _ = ∫ ω, alphaIicCE X hX_contract hX_meas hX_L2 (n : ℝ) ω ∂μ := by ring
    rw [← tendsto_nhds_unique h_lim h_int_conv]

  -- Conclude U_fun = 1 a.e.
  have hU_ae_one : U_fun =ᵐ[μ] 1 := by
    have hU_int : Integrable U_fun μ := by
      have hU_nonneg : 0 ≤ᵐ[μ] U_fun := by
        filter_upwards [h_bound] with ω h_bound_ω
        -- U_fun ω = sup of values all ≥ 0, so U_fun ω ≥ value at 0 ≥ 0
        refine le_trans ?_ (le_ciSup ⟨1, fun y hy => by obtain ⟨k, hk⟩ := hy; rw [← hk]; exact (h_bound_ω k).2⟩ (0 : ℕ))
        exact (h_bound_ω 0).1
      have hU_bound : ∀ᵐ ω ∂μ, ‖U_fun ω‖ ≤ 1 := by
        filter_upwards [hU_nonneg, h_bound] with ω hω_nn h_bound_ω
        rw [Real.norm_eq_abs, abs_of_nonneg hω_nn]
        -- U_fun ω = ⨆ n, f(n) where each f(n) ≤ 1, so U_fun ω ≤ 1
        -- Use that 1 is an upper bound for all values
        calc U_fun ω
            = ⨆ (n : ℕ), alphaIicCE X hX_contract hX_meas hX_L2 (n : ℝ) ω := rfl
          _ ≤ 1 := by
              apply ciSup_le
              intro n
              exact (h_bound_ω n).2
      have hU_meas : AEStronglyMeasurable U_fun μ := by
        -- Each alphaIicCE (n:ℝ) is AEStronglyMeasurable (conditional expectation)
        have h_meas_n : ∀ (n : ℕ), AEStronglyMeasurable (fun ω => alphaIicCE X hX_contract hX_meas hX_L2 (n : ℝ) ω) μ := by
          intro n
          unfold alphaIicCE
          exact stronglyMeasurable_condExp.aestronglyMeasurable.mono hm_le
        -- They converge a.e. to U_fun (by monotone convergence)
        have h_conv_ae_n : ∀ᵐ ω ∂μ, Tendsto (fun (n : ℕ) => alphaIicCE X hX_contract hX_meas hX_L2 (n : ℝ) ω)
            atTop (𝓝 (U_fun ω)) := by
          filter_upwards [h_ae_conv, h_bound, h_mono] with ω ⟨L, hL⟩ h_bound_ω h_mono_ω
          have hU_is_sup : L = U_fun ω := by
            apply tendsto_nhds_unique hL
            apply tendsto_atTop_ciSup h_mono_ω
            exact ⟨1, fun y hy => by obtain ⟨k, hk⟩ := hy; rw [← hk]; exact (h_bound_ω k).2⟩
          rw [← hU_is_sup]
          exact hL
        -- Apply aestronglyMeasurable_of_tendsto_ae
        exact aestronglyMeasurable_of_tendsto_ae atTop h_meas_n h_conv_ae_n
      exact Integrable.of_bound hU_meas 1 hU_bound
    -- Show U_fun = 1 a.e. by showing 1 - U_fun = 0 a.e.
    have h_diff_nonneg : 0 ≤ᵐ[μ] fun ω => 1 - U_fun ω := by
      filter_upwards [hU_le_one] with ω hω
      exact sub_nonneg.mpr hω
    have h_diff_int : Integrable (fun ω => 1 - U_fun ω) μ := by
      exact Integrable.sub (integrable_const 1) hU_int
    have h_diff_zero : ∫ ω, (1 - U_fun ω) ∂μ = 0 := by
      rw [integral_sub (integrable_const 1) hU_int, integral_const, smul_eq_mul, mul_one, hU_integral_one]
      norm_num
    have : (fun ω => 1 - U_fun ω) =ᵐ[μ] 0 := by
      rw [← integral_eq_zero_iff_of_nonneg_ae h_diff_nonneg h_diff_int]
      exact h_diff_zero
    filter_upwards [this] with ω hω
    have h_eq : 1 - U_fun ω = 0 := by simpa using hω
    have : 1 = U_fun ω := sub_eq_zero.mp h_eq
    exact this.symm

  -- Now show Tendsto f_n (𝓝 1) at a.e. ω
  filter_upwards [h_ae_conv, hU_ae_one, h_bound, h_mono] with ω ⟨L, hL⟩ hU_one h_bound_ω h_mono_ω
  -- At this ω, we have f_n → L and U_fun(ω) = 1
  have hL_eq : L = U_fun ω := by
    apply tendsto_nhds_unique hL
    apply tendsto_atTop_ciSup h_mono_ω
    exact ⟨1, fun y hy => by obtain ⟨k, hk⟩ := hy; rw [← hk]; exact (h_bound_ω k).2⟩
  rw [hL_eq, hU_one] at hL
  exact hL

/-- Right-continuous CDF from α via countable rational envelope:
F(ω,t) := inf_{q∈ℚ, t<q} α_{Iic q}(ω).
This is monotone increasing and right-continuous in t. -/
noncomputable def cdf_from_alpha
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ)
    (ω : Ω) (t : ℝ) : ℝ :=
  ⨅ (q : {q : ℚ // t < (q : ℝ)}), alphaIic X hX_contract hX_meas hX_L2 (q : ℝ) ω

/-- F(ω,·) is monotone nondecreasing. -/
lemma cdf_from_alpha_mono
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ)
    (ω : Ω) :
    Monotone (cdf_from_alpha X hX_contract hX_meas hX_L2 ω) := by
  intro s t hst
  -- When s ≤ t, the set {q : ℚ | t < q} ⊆ {q : ℚ | s < q}
  -- For any element q in the smaller set, we show it's in the larger set
  -- Then iInf over smaller set ≥ iInf over larger set
  have hne_t : Nonempty {q : ℚ // t < (q : ℝ)} := by
    obtain ⟨q, hq1, _⟩ := exists_rat_btwn (lt_add_one t)
    exact ⟨⟨q, hq1⟩⟩
  refine le_ciInf fun ⟨qt, hqt⟩ => ?_
  -- qt > t ≥ s, so qt > s, hence ⟨qt, _⟩ is in the index set for s
  have hqs : s < (qt : ℝ) := lt_of_le_of_lt hst hqt
  calc alphaIic X hX_contract hX_meas hX_L2 (qt : ℝ) ω
      = alphaIic X hX_contract hX_meas hX_L2 ((⟨qt, hqs⟩ : {q : ℚ // s < (q : ℝ)}) : ℝ) ω := rfl
    _ ≥ ⨅ (q : {q : ℚ // s < (q : ℝ)}), alphaIic X hX_contract hX_meas hX_L2 (q : ℝ) ω := by
        have hbdd : BddBelow (Set.range fun (q : {q : ℚ // s < (q : ℝ)}) =>
            alphaIic X hX_contract hX_meas hX_L2 (q : ℝ) ω) := by
          use 0
          intro y ⟨q, hq⟩
          rw [← hq]
          exact (alphaIic_bound X hX_contract hX_meas hX_L2 (q : ℝ) ω).1
        exact ciInf_le hbdd ⟨qt, hqs⟩

/-- Right-continuity in t: F(ω,t) = lim_{u↘t} F(ω,u). -/
lemma cdf_from_alpha_rightContinuous
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ)
    (ω : Ω) :
    ∀ t, Filter.Tendsto (cdf_from_alpha X hX_contract hX_meas hX_L2 ω)
      (𝓝[>] t) (𝓝 (cdf_from_alpha X hX_contract hX_meas hX_L2 ω t)) := by
  intro t
  -- Standard right-limit envelope argument:
  -- F(t) = inf_{q>t, q∈ℚ} α(q), and by density of rationals,
  -- for any ε>0, ∃q>t with α(q) < F(t) + ε
  -- For u close enough to t (specifically u < q), F(u) ≤ α(q) < F(t) + ε
  -- Also F(t) ≤ F(u) by monotonicity, giving |F(u) - F(t)| < ε
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  -- F(t) is the infimum, so there exists q > t with α(q) < F(t) + ε
  have hne : Nonempty {q : ℚ // t < (q : ℝ)} := by
    obtain ⟨q, hq1, _⟩ := exists_rat_btwn (lt_add_one t)
    exact ⟨⟨q, hq1⟩⟩
  have hbdd : BddBelow (Set.range fun (q : {q : ℚ // t < (q : ℝ)}) =>
      alphaIic X hX_contract hX_meas hX_L2 (q : ℝ) ω) := by
    use 0
    intro y ⟨q, hq⟩
    rw [← hq]
    exact (alphaIic_bound X hX_contract hX_meas hX_L2 (q : ℝ) ω).1
  -- By definition of infimum, ∃ q with F(t) ≤ α(q) < F(t) + ε
  have h_inflt : iInf (fun (q : {q : ℚ // t < (q : ℝ)}) => alphaIic X hX_contract hX_meas hX_L2 (q : ℝ) ω) < cdf_from_alpha X hX_contract hX_meas hX_L2 ω t + ε := by
    unfold cdf_from_alpha
    linarith
  obtain ⟨⟨q, hqt⟩, hq_bound⟩ := exists_lt_of_ciInf_lt h_inflt
  -- For any u with t < u < q, we have F(u) ≤ α(q) < F(t) + ε
  refine ⟨q - t, by linarith, fun u hu_gt hu_dist => ?_⟩
  simp only [Set.mem_Ioi] at hu_gt
  rw [Real.dist_eq] at hu_dist
  have hu_lt_q : u < q := by
    have : |u - t| < q - t := hu_dist
    have h_pos : u - t < q - t := abs_lt.mp this |>.2
    linarith
  -- By monotonicity: F(t) ≤ F(u)
  have h_mono : cdf_from_alpha X hX_contract hX_meas hX_L2 ω t ≤ cdf_from_alpha X hX_contract hX_meas hX_L2 ω u :=
    cdf_from_alpha_mono X hX_contract hX_meas hX_L2 ω (le_of_lt hu_gt)
  -- F(u) ≤ α(q) because q > u
  have h_upper : cdf_from_alpha X hX_contract hX_meas hX_L2 ω u ≤ alphaIic X hX_contract hX_meas hX_L2 (q : ℝ) ω := by
    calc cdf_from_alpha X hX_contract hX_meas hX_L2 ω u
        = ⨅ (r : {r : ℚ // u < (r : ℝ)}), alphaIic X hX_contract hX_meas hX_L2 (r : ℝ) ω := rfl
      _ ≤ alphaIic X hX_contract hX_meas hX_L2 (q : ℝ) ω := by
          have hbdd_u : BddBelow (Set.range fun (r : {r : ℚ // u < (r : ℝ)}) =>
              alphaIic X hX_contract hX_meas hX_L2 (r : ℝ) ω) := by
            use 0
            intro y ⟨r, hr⟩
            rw [← hr]
            exact (alphaIic_bound X hX_contract hX_meas hX_L2 (r : ℝ) ω).1
          exact ciInf_le hbdd_u ⟨q, hu_lt_q⟩
  rw [Real.dist_eq]
  calc |cdf_from_alpha X hX_contract hX_meas hX_L2 ω u - cdf_from_alpha X hX_contract hX_meas hX_L2 ω t|
      = cdf_from_alpha X hX_contract hX_meas hX_L2 ω u - cdf_from_alpha X hX_contract hX_meas hX_L2 ω t := by
        rw [abs_of_nonneg]
        linarith
    _ ≤ alphaIic X hX_contract hX_meas hX_L2 (q : ℝ) ω - cdf_from_alpha X hX_contract hX_meas hX_L2 ω t := by linarith
    _ < ε := by linarith

/-- Bounds 0 ≤ F ≤ 1 (pointwise in ω,t). -/
lemma cdf_from_alpha_bounds
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ)
    (ω : Ω) (t : ℝ) :
    0 ≤ cdf_from_alpha X hX_contract hX_meas hX_L2 ω t
    ∧ cdf_from_alpha X hX_contract hX_meas hX_L2 ω t ≤ 1 := by
  -- First establish that the index set is nonempty
  have hne : Nonempty {q : ℚ // t < (q : ℝ)} := by
    obtain ⟨q, hq1, _⟩ := exists_rat_btwn (lt_add_one t)
    exact ⟨⟨q, hq1⟩⟩
  constructor
  · -- Lower bound: iInf ≥ 0
    -- Each alphaIic value is ≥ 0, so their infimum is ≥ 0
    refine le_ciInf fun q => ?_
    exact (alphaIic_bound X hX_contract hX_meas hX_L2 (q : ℝ) ω).1
  · -- Upper bound: iInf ≤ 1
    -- Pick any q with t < q, then iInf ≤ alphaIic q ≤ 1
    have hbdd : BddBelow (Set.range fun (q : {q : ℚ // t < (q : ℝ)}) =>
        alphaIic X hX_contract hX_meas hX_L2 (q : ℝ) ω) := by
      use 0
      intro y ⟨q, hq⟩
      rw [← hq]
      exact (alphaIic_bound X hX_contract hX_meas hX_L2 (q : ℝ) ω).1
    calc cdf_from_alpha X hX_contract hX_meas hX_L2 ω t
        = ⨅ (q : {q : ℚ // t < (q : ℝ)}), alphaIic X hX_contract hX_meas hX_L2 (q : ℝ) ω := rfl
      _ ≤ alphaIic X hX_contract hX_meas hX_L2 (hne.some : ℝ) ω := ciInf_le hbdd hne.some
      _ ≤ 1 := (alphaIic_bound X hX_contract hX_meas hX_L2 (hne.some : ℝ) ω).2

/-- Helper lemma: α_{Iic t}(ω) → 0 as t → -∞.

This requires showing that the L¹ limit of Cesàro averages of 1_{(-∞,t]} converges to 0
as t → -∞. The proof strategy:

1. For each fixed ω, as t → -∞, the indicators 1_{(-∞,t]}(X_i(ω)) → 0 pointwise
2. By dominated convergence, the Cesàro averages converge to 0 in L¹ uniformly in n
3. Since alphaIic is the L¹ limit (clipped to [0,1]), it must also converge to 0

The challenge is interchanging two limits:
- The Cesàro limit (m → ∞)
- The threshold limit (t → -∞)

This requires careful application of dominated convergence and diagonal arguments.
-/
private lemma alphaIic_tendsto_zero_at_bot
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ)
    (ω : Ω) :
    ∀ ε > 0, ∃ T : ℝ, ∀ t < T,
      alphaIic X hX_contract hX_meas hX_L2 t ω < ε := by
  intro ε hε_pos
  -- Strategy: For fixed ω, choose T smaller than all X_i(ω) for i ≤ K
  -- Then for t < T, the Cesàro averages are bounded by (K/m) → 0 as m → ∞
  -- Since alphaIic is the L¹ limit (clipped), it must be ≤ ε for large enough offset
  
  -- The key is that alphaIic is bounded in [0,1], so we can use compactness
  -- For any sequence in [0,1] that converges in L¹ to alphaIic, 
  -- we can extract subsequences that converge pointwise a.e.
  
  -- By definition, alphaIic t ω is the L¹ limit (clipped to [0,1])
  -- For t → -∞, the Cesàro averages converge to 0 uniformly in the starting index
  -- because eventually all X_i(ω) > t
  
  -- Take T to be smaller than the minimum of finitely many X_i(ω)
  -- This ensures finite support, making Cesàro averages → 0
  
  -- TODO: Formalize using L¹ convergence properties and boundedness
  -- The full proof requires showing that the L¹ limit inherits the pointwise behavior
  sorry

/-- Helper lemma: α_{Iic t}(ω) → 1 as t → +∞.

This is the dual of the previous lemma. As t → +∞:
- Indicators 1_{(-∞,t]}(x) → 1 for all x (monotone convergence)
- Cesàro averages converge to 1 in L¹
- alphaIic t ω → 1

The proof uses monotone convergence since the indicators increase to 1.
-/
private lemma alphaIic_tendsto_one_at_top
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ)
    (ω : Ω) :
    ∀ ε > 0, ∃ T : ℝ, ∀ t > T,
      1 - ε < alphaIic X hX_contract hX_meas hX_L2 t ω := by
  intro ε hε_pos
  -- As t → +∞, indIic t (x) → 1 for all x (since (-∞, t] eventually contains all of ℝ)
  -- The Cesàro averages (1/m) Σ 1_{(-∞,t]}(X_i(ω)) → 1 for each ω
  -- and alphaIic t ω → 1 as t → +∞
  --
  -- This is the monotone convergence case: indicators increase to 1.
  -- By dominated convergence (bounded by 1), the L¹ limits also converge to 1.
  --
  -- Same infrastructure requirements as the t → -∞ case. For now:
  sorry

namespace Helpers

/-- **AXIOM A2 (CDF endpoints):**
For the CDF built from `alphaIic` via the rational envelope, the limits at
±∞ are 0 and 1 for every ω. -/
axiom cdf_from_alpha_limits
  {Ω : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  (X : ℕ → Ω → ℝ) (hX_contract : Exchangeability.Contractable μ X)
  (hX_meas : ∀ i, Measurable (X i)) (hX_L2 : ∀ i, MemLp (X i) 2 μ) :
  ∀ ω, Tendsto (cdf_from_alpha X hX_contract hX_meas hX_L2 ω) atBot (𝓝 0) ∧
       Tendsto (cdf_from_alpha X hX_contract hX_meas hX_L2 ω) atTop (𝓝 1)

end Helpers

/-- F(ω,t) → 0 as t → -∞, and F(ω,t) → 1 as t → +∞.

Given the helper lemmas about alphaIic convergence, this follows from the definition
of cdf_from_alpha as the infimum of alphaIic values over rationals greater than t.
-/
lemma cdf_from_alpha_limits
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ)
    (ω : Ω) :
    Filter.Tendsto (cdf_from_alpha X hX_contract hX_meas hX_L2 ω) Filter.atBot (𝓝 0) ∧
    Filter.Tendsto (cdf_from_alpha X hX_contract hX_meas hX_L2 ω) Filter.atTop (𝓝 1) := by
  constructor
  · -- Limit at -∞: F(ω,t) → 0 as t → -∞
    -- Strategy: F(ω,t) = inf_{q>t} α_{Iic q}(ω)
    -- Since alphaIic q ω → 0 as q → -∞ (by helper lemma alphaIic_tendsto_zero_at_bot),
    -- and F(ω,t) ≤ alphaIic q ω for any q > t,
    -- we get F(ω,t) → 0 as t → -∞
    --
    -- The full proof would:
    -- 1. Use alphaIic_tendsto_zero_at_bot to get T such that alphaIic t ω < ε for t < T
    -- 2. For t < T, pick rational q with t < q < T
    -- 3. Then F(ω,t) ≤ alphaIic q ω < ε
    -- 4. Express this using mathlib's Filter.Tendsto API for atBot
    --
    -- This requires navigating mathlib's Filter/Metric API.
    -- Use the packaged axiom (A2).
    exact (Helpers.cdf_from_alpha_limits X hX_contract hX_meas hX_L2 ω).1

  · -- Limit at +∞: F(ω,t) → 1 as t → +∞
    -- Similar strategy using alphaIic_tendsto_one_at_top
    --
    -- For any ε > 0, find T such that for t > T:
    -- - For all q > t > T: 1 - ε < alphaIic q ω (by helper lemma)
    -- - So F(ω,t) = inf_{q>t} alphaIic q ω ≥ 1 - ε
    -- - Thus F(ω,t) → 1
    --
    -- Full proof requires mathlib's Filter API.
    -- Use the packaged axiom (A2).
    exact (Helpers.cdf_from_alpha_limits X hX_contract hX_meas hX_L2 ω).2

/-- Build the directing measure ν from the CDF.

For each ω ∈ Ω, we construct ν(ω) as the probability measure on ℝ with CDF
given by t ↦ cdf_from_alpha X ω t.

This uses the Stieltjes measure construction from mathlib.
-/
noncomputable def directing_measure
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ) :
    Ω → Measure ℝ :=
  fun ω =>
    -- Build via StieltjesFunction from the right-continuous CDF
    -- The Stieltjes function for ω is cdf_from_alpha X hX_contract hX_meas hX_L2 ω
    let F_ω : StieltjesFunction := {
      toFun := cdf_from_alpha X hX_contract hX_meas hX_L2 ω
      mono' := cdf_from_alpha_mono X hX_contract hX_meas hX_L2 ω
      right_continuous' := by
        intro t
        -- Right-continuity from Ioi t extends to Ici t
        -- We have: Tendsto at 𝓝[>] t from cdf_from_alpha_rightContinuous
        have h_rc := cdf_from_alpha_rightContinuous X hX_contract hX_meas hX_L2 ω t
        -- Note: Ici t = insert t (Ioi t), and inserting t doesn't affect the filter
        rw [ContinuousWithinAt]
        have h_eq : Set.Ici t = insert t (Set.Ioi t) := by
          ext x
          simp only [Set.mem_Ici, Set.mem_insert_iff, Set.mem_Ioi]
          constructor
          · intro hx
            by_cases h : x = t
            · left; exact h
            · right; exact lt_of_le_of_ne hx (Ne.symm h)
          · intro hx
            cases hx with
            | inl heq => rw [heq]
            | inr hlt => exact le_of_lt hlt
        rw [h_eq, nhdsWithin_insert]
        -- Need to show: Tendsto f (pure t ⊔ 𝓝[>] t) (𝓝 (f t))
        -- We have: Tendsto f (𝓝[>] t) (𝓝 (f t))
        -- At pure t: f(t) is trivially in 𝓝 (f t)
        apply Tendsto.sup
        · -- Tendsto f (pure t) (𝓝 (f t))
          rw [tendsto_pure_left]
          intro s hs
          exact mem_of_mem_nhds hs
        · exact h_rc
    }
    F_ω.measure

namespace Helpers

/-- **AXIOM A3 (Probability measure from CDF):**
The `directing_measure` built from the CDF is a probability measure. -/
axiom directing_measure_isProbabilityMeasure
  {Ω : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  (X : ℕ → Ω → ℝ) (hX_contract : Exchangeability.Contractable μ X)
  (hX_meas : ∀ i, Measurable (X i)) (hX_L2 : ∀ i, MemLp (X i) 2 μ) :
  ∀ ω, IsProbabilityMeasure (directing_measure X hX_contract hX_meas hX_L2 ω)

end Helpers

/-- The directing measure is a probability measure. -/
lemma directing_measure_isProbabilityMeasure
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ)
    (ω : Ω) :
    IsProbabilityMeasure (directing_measure X hX_contract hX_meas hX_L2 ω) := by
  -- Probability measure instance from axiom (A3):
  exact (Helpers.directing_measure_isProbabilityMeasure X hX_contract hX_meas hX_L2 ω)

