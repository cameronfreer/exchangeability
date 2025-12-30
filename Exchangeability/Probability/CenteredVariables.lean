/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Exchangeability.DeFinetti.L2Helpers
import Exchangeability.Probability.IntegrationHelpers
import Exchangeability.Probability.LpNormHelpers
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Centered Variable Infrastructure for L² Proofs

This file provides infrastructure for working with centered random variables in the context
of exchangeable/contractable sequences. The key result is that centering preserves the
uniform covariance structure needed for L² convergence proofs.

## Main results

* `centered_uniform_covariance`: Centered variables from a contractable sequence have
  uniform variance and covariance structure
* `centered_variable_bounded`: Centered variables from bounded functions are bounded
* `correlation_coefficient_bounded`: Correlation coefficient is bounded by 1 via Cauchy-Schwarz

## References

* Kallenberg (2005), *Probabilistic Symmetries and Invariance Principles*, Chapter 1
-/

noncomputable section

namespace Exchangeability.Probability.CenteredVariables

open MeasureTheory ProbabilityTheory BigOperators

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Helper lemma: Uniform covariance structure of centered variables.

Given contractable sequence X and function f, the centered variables Z_i = f(X_i) - m
have uniform covariance structure:
- Z is contractable
- Uniform variance: E[Z_i²] = E[Z_0²] for all i
- Zero mean: E[Z_i] = 0 for all i
- Uniform covariance: E[Z_i Z_j] = E[Z_0 Z_1] for all i ≠ j

This is the key infrastructure for applying l2_contractability_bound. -/
lemma centered_uniform_covariance
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (f : ℝ → ℝ) (hf_meas : Measurable f) (hf_bdd : ∀ x, |f x| ≤ 1)
    (m : ℝ) (hm_def : m = ∫ ω, f (X 0 ω) ∂μ)
    (Z : ℕ → Ω → ℝ) (hZ_def : ∀ i ω, Z i ω = f (X i ω) - m) :
    (∀ i, Measurable (Z i)) ∧ Contractable μ Z ∧
    (∀ i, ∫ ω, (Z i ω)^2 ∂μ = ∫ ω, (Z 0 ω)^2 ∂μ) ∧
    (∀ i, ∫ ω, Z i ω ∂μ = 0) ∧
    (∀ i j, i ≠ j → ∫ ω, Z i ω * Z j ω ∂μ = ∫ ω, Z 0 ω * Z 1 ω ∂μ) := by

  -- Step 1: Z is measurable
  have hZ_meas : ∀ i, Measurable (Z i) := by
    intro i
    rw [show Z i = fun ω => f (X i ω) - m by ext ω; exact hZ_def i ω]
    exact (hf_meas.comp (hX_meas i)).sub measurable_const

  -- Step 2: Show Z is contractable
  -- Z = f ∘ X - m, and contractability is preserved under composition + constant shift
  have hZ_contract : Contractable μ Z := by
    -- First show f ∘ X is contractable using contractable_comp
    have hfX_contract : Contractable μ (fun i ω => f (X i ω)) :=
      Exchangeability.DeFinetti.L2Helpers.contractable_comp (X := X) hX_contract hX_meas f hf_meas
    -- Subtracting a constant preserves contractability
    intro n k hk
    -- Need: map (fun ω i => Z (k i) ω) μ = map (fun ω i => Z i ω) μ
    simp only [hZ_def]
    -- This equals: map (fun ω i => f(X(k i) ω) - m) μ = map (fun ω i => f(X i ω) - m) μ

    -- From hfX_contract: map (fun ω i => f(X(k i) ω)) μ = map (fun ω i => f(X i ω)) μ
    -- Subtracting m from each coordinate gives the same measure equality
    have h_eq := hfX_contract n k hk

    -- The subtraction by m is the same measurable transformation on both sides
    -- Strategy: Transform h_eq using coordinatewise subtraction

    -- Define coordinatewise subtraction
    let h : (Fin n → ℝ) → (Fin n → ℝ) := fun g i => g i - m

    -- h is measurable
    have h_meas : Measurable h := by
      apply measurable_pi_iff.mpr
      intro i
      exact (measurable_pi_apply i).sub measurable_const

    -- Input functions are measurable
    have hL_meas : Measurable (fun ω (i : Fin n) => f (X (k i) ω)) :=
      measurable_pi_iff.mpr (fun i => hf_meas.comp (hX_meas (k i)))
    have hR_meas : Measurable (fun ω (i : Fin n) => f (X (↑i) ω)) :=
      measurable_pi_iff.mpr (fun i => hf_meas.comp (hX_meas i))

    -- Apply map_map: map (h ∘ g) μ = map h (map g μ)
    calc Measure.map (fun ω i => f (X (k i) ω) - m) μ
        = Measure.map (h ∘ (fun ω i => f (X (k i) ω))) μ := by congr
      _ = Measure.map h (Measure.map (fun ω i => f (X (k i) ω)) μ) := by
            exact (Measure.map_map h_meas hL_meas).symm
      _ = Measure.map h (Measure.map (fun ω i => f (X (↑i) ω)) μ) := by
            rw [h_eq]
      _ = Measure.map (h ∘ (fun ω i => f (X (↑i) ω))) μ := by
            exact Measure.map_map h_meas hR_meas
      _ = Measure.map (fun ω (i : Fin n) => f (X (↑i) ω) - m) μ := by congr

  -- Step 3: Show uniform variance via contractability
  -- E[Z_i²] = E[Z_0²] for all i
  have hZ_var_uniform : ∀ i, ∫ ω, (Z i ω)^2 ∂μ = ∫ ω, (Z 0 ω)^2 ∂μ := by
    intro i
    -- From contractability: map (Z i) μ = map (Z 0) μ
    have h_map_eq : Measure.map (Z i) μ = Measure.map (Z 0) μ :=
      Exchangeability.DeFinetti.L2Helpers.contractable_map_single (X := Z) hZ_contract hZ_meas (i := i)

    -- Strategy: Use integral_map to rewrite both sides
    -- ∫ (Z i ω)² dμ = ∫ x² d(map (Z i) μ) [by integral_map]
    --               = ∫ x² d(map (Z 0) μ) [by h_map_eq]
    --               = ∫ (Z 0 ω)² dμ     [by integral_map]

    -- Z i is measurable, so we can apply integral_map
    have hZi_meas : AEMeasurable (Z i) μ := (hZ_meas i).aemeasurable
    have hZ0_meas : AEMeasurable (Z 0) μ := (hZ_meas 0).aemeasurable

    -- Apply integral_map on both sides and use measure equality
    -- The function x ↦ x² is continuous, hence strongly measurable
    rw [← integral_map hZi_meas (continuous_pow 2).aestronglyMeasurable]
    rw [← integral_map hZ0_meas (continuous_pow 2).aestronglyMeasurable]
    rw [h_map_eq]

  -- Step 4: Show mean of Z is zero
  have hZ_mean_zero : ∀ i, ∫ ω, Z i ω ∂μ = 0 := by
    intro i
    simp only [show Z i = fun ω => f (X i ω) - m by ext ω; exact hZ_def i ω]
    -- E[Z_i] = E[f(X_i) - m] = E[f(X_i)] - m
    -- By contractability: E[f(X_i)] = E[f(X_0)] = m
    -- Therefore: E[Z_i] = m - m = 0

    -- f is bounded, so f ∘ X i is integrable
    have hfX_int : Integrable (fun ω => f (X i ω)) μ := by
      apply Integrable.of_bound
      · exact (hf_meas.comp (hX_meas i)).aestronglyMeasurable
      · filter_upwards [] with ω
        exact hf_bdd (X i ω)

    rw [integral_sub hfX_int (integrable_const m)]
    -- Now show ∫ f(X i) = m, so that ∫ f(X i) - m = m - m = 0

    -- Strategy: contractable_map_single gives map (X i) μ = map (X 0) μ
    -- Then integral_map gives: ∫ f(X i) dμ = ∫ f d(map (X i) μ) = ∫ f d(map (X 0) μ) = ∫ f(X 0) dμ = m

    -- Use contractability to get measure equality
    have h_map_eq : Measure.map (X i) μ = Measure.map (X 0) μ :=
      Exchangeability.DeFinetti.L2Helpers.contractable_map_single (X := X) hX_contract hX_meas (i := i)

    -- f is measurable and bounded, so we can apply integral_map
    have hXi_meas : AEMeasurable (X i) μ := (hX_meas i).aemeasurable
    have hX0_meas : AEMeasurable (X 0) μ := (hX_meas 0).aemeasurable

    -- Apply integral_map to show ∫ f(X i) = ∫ f(X 0)
    have h_int_eq : ∫ ω, f (X i ω) ∂μ = ∫ ω, f (X 0 ω) ∂μ := by
      rw [← integral_map hXi_meas hf_meas.aestronglyMeasurable]
      rw [← integral_map hX0_meas hf_meas.aestronglyMeasurable]
      rw [h_map_eq]

    -- From h_int_eq: ∫ f(X i) = ∫ f(X 0) = m
    -- So ∫ f(X i) - m = m - m = 0
    rw [h_int_eq, hm_def, integral_const]
    simp [measure_univ]

  -- Step 5: Show uniform covariance via contractability
  -- For i ≠ j, E[Z_i Z_j] = E[Z_0 Z_1]
  have hZ_cov_uniform : ∀ i j, i ≠ j →
      ∫ ω, Z i ω * Z j ω ∂μ = ∫ ω, Z 0 ω * Z 1 ω ∂μ := by
    intro i j hij
    -- Strategy: If i < j, use contractable_map_pair directly
    --           If i > j, use contractable_map_pair on (j,i) + symmetry of multiplication
    by_cases h_lt : i < j
    · -- Case i < j: use contractable_map_pair directly
      have h_map_eq : Measure.map (fun ω => (Z i ω, Z j ω)) μ =
          Measure.map (fun ω => (Z 0 ω, Z 1 ω)) μ :=
        Exchangeability.DeFinetti.L2Helpers.contractable_map_pair (X := Z) hZ_contract hZ_meas h_lt

      -- The function (x, y) ↦ x * y is continuous, hence measurable
      have h_mul_meas : Measurable (fun p : ℝ × ℝ => p.1 * p.2) :=
        (continuous_fst.mul continuous_snd).measurable

      -- Z i and Z j are measurable
      have hZi_meas : AEMeasurable (Z i) μ := (hZ_meas i).aemeasurable
      have hZj_meas : AEMeasurable (Z j) μ := (hZ_meas j).aemeasurable
      have hZ0_meas : AEMeasurable (Z 0) μ := (hZ_meas 0).aemeasurable
      have hZ1_meas : AEMeasurable (Z 1) μ := (hZ_meas 1).aemeasurable

      -- Product measurability
      have h_prod_ij : AEMeasurable (fun ω => (Z i ω, Z j ω)) μ :=
        hZi_meas.prod_mk hZj_meas
      have h_prod_01 : AEMeasurable (fun ω => (Z 0 ω, Z 1 ω)) μ :=
        hZ0_meas.prod_mk hZ1_meas

      -- Apply integral_map
      rw [← integral_map h_prod_ij h_mul_meas.aestronglyMeasurable]
      rw [← integral_map h_prod_01 h_mul_meas.aestronglyMeasurable]
      rw [h_map_eq]

    · -- Case i > j: use contractable_map_pair on (j,i) + symmetry
      have hji : j < i := Nat.lt_of_le_of_ne (Nat.le_of_not_lt h_lt) (hij.symm)

      -- Symmetry of multiplication: Z i * Z j = Z j * Z i
      have h_sym_ij : ∫ ω, Z i ω * Z j ω ∂μ = ∫ ω, Z j ω * Z i ω ∂μ := by
        congr 1
        ext ω
        ring

      -- Now use contractable_map_pair on (j, i)
      have h_map_eq : Measure.map (fun ω => (Z j ω, Z i ω)) μ =
          Measure.map (fun ω => (Z 0 ω, Z 1 ω)) μ :=
        Exchangeability.DeFinetti.L2Helpers.contractable_map_pair (X := Z) hZ_contract hZ_meas hji

      -- The function (x, y) ↦ x * y is continuous, hence measurable
      have h_mul_meas : Measurable (fun p : ℝ × ℝ => p.1 * p.2) :=
        (continuous_fst.mul continuous_snd).measurable

      -- Measurability
      have hZi_meas : AEMeasurable (Z i) μ := (hZ_meas i).aemeasurable
      have hZj_meas : AEMeasurable (Z j) μ := (hZ_meas j).aemeasurable
      have hZ0_meas : AEMeasurable (Z 0) μ := (hZ_meas 0).aemeasurable
      have hZ1_meas : AEMeasurable (Z 1) μ := (hZ_meas 1).aemeasurable

      -- Product measurability
      have h_prod_ji : AEMeasurable (fun ω => (Z j ω, Z i ω)) μ :=
        hZj_meas.prod_mk hZi_meas
      have h_prod_01 : AEMeasurable (fun ω => (Z 0 ω, Z 1 ω)) μ :=
        hZ0_meas.prod_mk hZ1_meas

      -- Apply integral_map and symmetry
      rw [h_sym_ij]
      rw [← integral_map h_prod_ji h_mul_meas.aestronglyMeasurable]
      rw [← integral_map h_prod_01 h_mul_meas.aestronglyMeasurable]
      rw [h_map_eq]

  -- Combine all results
  exact ⟨hZ_meas, hZ_contract, hZ_var_uniform, hZ_mean_zero, hZ_cov_uniform⟩

/-- Helper lemma: Centered variables Z = f(X) - m are bounded by 2.

When |f| ≤ 1 and m = E[f(X_0)], then |Z i ω| = |f(X i ω) - m| ≤ 2. -/
lemma centered_variable_bounded
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} (hX_meas : ∀ i, Measurable (X i))
    (f : ℝ → ℝ) (hf_meas : Measurable f) (hf_bdd : ∀ x, |f x| ≤ 1)
    (m : ℝ) (hm_def : m = ∫ ω, f (X 0 ω) ∂μ)
    (Z : ℕ → Ω → ℝ) (hZ_def : ∀ i ω, Z i ω = f (X i ω) - m) :
    ∀ i ω, |Z i ω| ≤ 2 := by
  intro i ω
  simp only [hZ_def]
  calc |f (X i ω) - m|
      ≤ |f (X i ω)| + |m| := abs_sub _ _
    _ ≤ 1 + 1 := by
        have h1 : |f (X i ω)| ≤ 1 := hf_bdd (X i ω)
        have h2 : |m| ≤ 1 := by
          have hfX_int : Integrable (fun ω => f (X 0 ω)) μ := by
            apply Integrable.of_bound
            · exact (hf_meas.comp (hX_meas 0)).aestronglyMeasurable
            · filter_upwards [] with ω; exact hf_bdd (X 0 ω)
          calc |m|
              = |∫ ω, f (X 0 ω) ∂μ| := by rw [hm_def]
            _ ≤ ∫ ω, |f (X 0 ω)| ∂μ := abs_integral_le_integral_abs
            _ ≤ ∫ ω, 1 ∂μ := by
                apply integral_mono_ae hfX_int.abs (integrable_const 1)
                filter_upwards [] with ω; exact hf_bdd (X 0 ω)
            _ = 1 := by simp
        linarith
    _ = 2 := by norm_num

/-- Helper lemma: Correlation coefficient is bounded by 1 via Cauchy-Schwarz.

Given variables Z with uniform variance σSq > 0 and bound |Z i ω| ≤ M,
proves |ρ| ≤ 1 where ρ = cov(Z_0,Z_1)/σSq. -/
lemma correlation_coefficient_bounded
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (Z : ℕ → Ω → ℝ) (hZ_meas : ∀ i, Measurable (Z i))
    (M : ℝ) (hZ_bdd : ∀ i ω, |Z i ω| ≤ M)
    (σSq : ℝ) (hσ_pos : σSq > 0) (h_σSq_def : σSq = ∫ ω, (Z 0 ω)^2 ∂μ)
    (covZ : ℝ) (h_covZ_def : covZ = ∫ ω, Z 0 ω * Z 1 ω ∂μ)
    (ρ : ℝ) (h_ρ_def : ρ = covZ / σSq)
    (hZ_var_uniform : ∀ i, ∫ ω, (Z i ω)^2 ∂μ = ∫ ω, (Z 0 ω)^2 ∂μ) :
    -1 ≤ ρ ∧ ρ ≤ 1 := by
  -- Z 0 and Z 1 are in L²(μ) since they are bounded by M
  have hZ0_L2 : MemLp (Z 0) 2 μ := by
    apply memLp_two_of_bounded (hZ_meas 0)
    exact hZ_bdd 0

  have hZ1_L2 : MemLp (Z 1) 2 μ := by
    apply memLp_two_of_bounded (hZ_meas 1)
    exact hZ_bdd 1

  -- Apply Cauchy-Schwarz: |∫ Z₀·Z₁| ≤ sqrt(∫ Z₀²)·sqrt(∫ Z₁²)
  have h_CS := Exchangeability.Probability.IntegrationHelpers.abs_integral_mul_le_L2 hZ0_L2 hZ1_L2

  -- By uniform variance: ∫ Z₁² = ∫ Z₀² = σSq
  have h_Z1_var : ∫ ω, (Z 1 ω) ^ 2 ∂μ = σSq := by
    rw [hZ_var_uniform 1, h_σSq_def]

  -- So Cauchy-Schwarz gives: |covZ| ≤ sqrt(σSq)·sqrt(σSq) = σSq
  have h_covZ_bd : |covZ| ≤ σSq := by
    simp only [h_covZ_def, h_σSq_def]
    calc |∫ ω, Z 0 ω * Z 1 ω ∂μ|
        ≤ (∫ ω, (Z 0 ω) ^ 2 ∂μ) ^ (1/2 : ℝ) * (∫ ω, (Z 1 ω) ^ 2 ∂μ) ^ (1/2 : ℝ) := h_CS
      _ = (∫ ω, (Z 0 ω) ^ 2 ∂μ) ^ (1/2 : ℝ) * (∫ ω, (Z 0 ω) ^ 2 ∂μ) ^ (1/2 : ℝ) := by rw [h_Z1_var, h_σSq_def]
      _ = (∫ ω, (Z 0 ω) ^ 2 ∂μ) := by
          rw [← Real.rpow_add_of_nonneg (integral_nonneg (fun ω => sq_nonneg _))]
          <;> norm_num

  -- Therefore |ρ| ≤ 1, which gives -1 ≤ ρ ≤ 1
  have h_ρ_abs : |ρ| ≤ 1 := by
    simp only [h_ρ_def]
    rw [abs_div, abs_of_pos hσ_pos]
    exact div_le_one_of_le₀ h_covZ_bd hσ_pos.le

  constructor
  · linarith [abs_le.mp h_ρ_abs]
  · exact (abs_le.mp h_ρ_abs).2

end Exchangeability.Probability.CenteredVariables
