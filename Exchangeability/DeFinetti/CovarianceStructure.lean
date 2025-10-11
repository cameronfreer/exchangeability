/-
Copyright (c) 2025 The Exchangeability Contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer, Your Name
-/
import Exchangeability.DeFinetti.ViaL2
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Covariance Structure of Contractable Sequences

This file contains auxiliary results about the covariance structure of contractable sequences.
While these results are not strictly necessary for the main de Finetti convergence proof,
they may be useful for other applications and provide additional insight into the properties
of contractable sequences.

## Main results

* `contractable_covariance_structure`: A contractable L² sequence has uniform mean m,
  variance σ², and correlation ρ ∈ [-1,1] across all variables and pairs.

## Implementation notes

The proofs use Cauchy-Schwarz inequality via Hölder's inequality (p=q=2 case) from mathlib.
The key insight is that contractability forces all single-variable marginals to be identical,
and all two-variable marginals to be identical, which implies the uniform covariance structure.
-/

noncomputable section

open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Finset

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

namespace Exchangeability.DeFinetti

/-!
### Covariance structure lemma

This result characterizes the complete second-moment structure of contractable sequences.
It's included here for potential future applications, though it's not currently used
in the main convergence proof (which takes a more direct L² approach).
-/

/-- **Uniform covariance structure for contractable L² sequences.**

A contractable sequence X in L²(μ) has uniform second-moment structure:
- All X_i have the same mean m
- All X_i have the same variance σ²
- All distinct pairs (X_i, X_j) have the same covariance σ²·ρ
- The correlation coefficient satisfies |ρ| ≤ 1

This is proved using the Cauchy-Schwarz inequality and the fact that contractability
forces all marginals of the same dimension to have identical distributions.

While this result provides a complete characterization of the covariance structure,
the main de Finetti convergence proof uses more direct L² contractability bounds
and doesn't require this full characterization. We include it here as it may be
useful for other applications involving contractable sequences.
-/
lemma contractable_covariance_structure
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ) :
    ∃ (m σSq ρ : ℝ),
      (∀ k, ∫ ω, X k ω ∂μ = m) ∧
      (∀ k, ∫ ω, (X k ω - m)^2 ∂μ = σSq) ∧
      (∀ i j, i ≠ j → ∫ ω, (X i ω - m) * (X j ω - m) ∂μ = σSq * ρ) ∧
      0 ≤ σSq ∧ -1 ≤ ρ ∧ ρ ≤ 1 := by
  -- Strategy: Use contractability to show all marginals of same size have same distribution
  -- This implies all X_i have the same mean and variance, and all pairs have same covariance

  -- Define m as the mean of X_0 (all X_i have the same distribution by contractability)
  let m := ∫ ω, X 0 ω ∂μ

  -- All X_i have the same mean by contractability (single-variable marginal)
  have hmean : ∀ k, ∫ ω, X k ω ∂μ = m := by
    intro k
    -- Use contractable_single_marginal_eq to show X_k has same distribution as X_0
    have h_eq_dist := ViaL2.contractable_single_marginal_eq (X := X) hX_contract hX_meas k
    -- Transfer integral via equal distributions
    -- The key fact: if X_k and X_0 have the same distribution, their expectations are equal
    -- This follows from ∫ X_k dμ = ∫ id d(X_k#μ) = ∫ id d(X_0#μ) = ∫ X_0 dμ
    have h_int_k : ∫ ω, X k ω ∂μ = ∫ x, x ∂(Measure.map (X k) μ) := by
      have h_ae : AEStronglyMeasurable (id : ℝ → ℝ) (Measure.map (X k) μ) :=
        aestronglyMeasurable_id
      exact (integral_map (hX_meas k).aemeasurable h_ae).symm
    have h_int_0 : ∫ ω, X 0 ω ∂μ = ∫ x, x ∂(Measure.map (X 0) μ) := by
      have h_ae : AEStronglyMeasurable (id : ℝ → ℝ) (Measure.map (X 0) μ) :=
        aestronglyMeasurable_id
      exact (integral_map (hX_meas 0).aemeasurable h_ae).symm
    rw [h_int_k, h_eq_dist, ← h_int_0]

  -- Define σSq as the variance of X_0
  let σSq := ∫ ω, (X 0 ω - m)^2 ∂μ

  -- All X_i have the same variance
  have hvar : ∀ k, ∫ ω, (X k ω - m)^2 ∂μ = σSq := by
    intro k
    -- Use equal distribution to transfer the variance integral
    have h_eq_dist := ViaL2.contractable_single_marginal_eq (X := X) hX_contract hX_meas k
    have hmean_k := hmean k
    -- The variance with k's mean equals variance with m (since they're equal)
    show ∫ ω, (X k ω - m)^2 ∂μ = σSq
    -- Transform X_k integral to X_0 integral via measure map
    have h_int_k : ∫ ω, (X k ω - m)^2 ∂μ = ∫ x, (x - m)^2 ∂(Measure.map (X k) μ) := by
      have h_ae : AEStronglyMeasurable (fun x : ℝ => (x - m)^2) (Measure.map (X k) μ) := by
        exact (continuous_id.sub continuous_const).pow 2 |>.aestronglyMeasurable
      exact (integral_map (hX_meas k).aemeasurable h_ae).symm
    have h_int_0 : ∫ ω, (X 0 ω - m)^2 ∂μ = ∫ x, (x - m)^2 ∂(Measure.map (X 0) μ) := by
      have h_ae : AEStronglyMeasurable (fun x : ℝ => (x - m)^2) (Measure.map (X 0) μ) := by
        exact (continuous_id.sub continuous_const).pow 2 |>.aestronglyMeasurable
      exact (integral_map (hX_meas 0).aemeasurable h_ae).symm
    rw [h_int_k, h_eq_dist, ← h_int_0]

  -- Define ρ from the covariance of (X_0, X_1)
  have hσSq_nonneg : 0 ≤ σSq := by
    apply integral_nonneg
    intro ω
    exact sq_nonneg _

  by_cases hσSq_pos : 0 < σSq
  · -- Case: positive variance
    let ρ := (∫ ω, (X 0 ω - m) * (X 1 ω - m) ∂μ) / σSq

    -- All pairs have the same covariance
    have hcov : ∀ i j, i ≠ j → ∫ ω, (X i ω - m) * (X j ω - m) ∂μ = σSq * ρ := by
      intro i j hij
      -- Apply contractability to get equal distributions for pairs
      by_cases h_ord : i < j
      · -- Case i < j: use contractable_map_pair directly
        have h_eq_dist := ViaL2.contractable_map_pair (X := X) hX_contract hX_meas h_ord
        -- Transfer the covariance integral via measure map
        have h_int_ij : ∫ ω, (X i ω - m) * (X j ω - m) ∂μ
            = ∫ p : ℝ × ℝ, (p.1 - m) * (p.2 - m) ∂(Measure.map (fun ω => (X i ω, X j ω)) μ) := by
          have h_ae : AEStronglyMeasurable (fun p : ℝ × ℝ => (p.1 - m) * (p.2 - m))
              (Measure.map (fun ω => (X i ω, X j ω)) μ) := by
            exact ((continuous_fst.sub continuous_const).mul
              (continuous_snd.sub continuous_const)).aestronglyMeasurable
          have h_comp : (fun ω => (X i ω - m) * (X j ω - m))
              = (fun p : ℝ × ℝ => (p.1 - m) * (p.2 - m)) ∘ (fun ω => (X i ω, X j ω)) := rfl
          rw [h_comp]
          exact (integral_map ((hX_meas i).prodMk (hX_meas j)).aemeasurable h_ae).symm
        have h_int_01 : ∫ ω, (X 0 ω - m) * (X 1 ω - m) ∂μ
            = ∫ p : ℝ × ℝ, (p.1 - m) * (p.2 - m) ∂(Measure.map (fun ω => (X 0 ω, X 1 ω)) μ) := by
          have h_ae : AEStronglyMeasurable (fun p : ℝ × ℝ => (p.1 - m) * (p.2 - m))
              (Measure.map (fun ω => (X 0 ω, X 1 ω)) μ) := by
            exact ((continuous_fst.sub continuous_const).mul
              (continuous_snd.sub continuous_const)).aestronglyMeasurable
          have h_comp : (fun ω => (X 0 ω - m) * (X 1 ω - m))
              = (fun p : ℝ × ℝ => (p.1 - m) * (p.2 - m)) ∘ (fun ω => (X 0 ω, X 1 ω)) := rfl
          rw [h_comp]
          exact (integral_map ((hX_meas 0).prodMk (hX_meas 1)).aemeasurable h_ae).symm
        rw [h_int_ij, h_eq_dist, ← h_int_01]
        -- Now need to show: ∫ (X 0 ω - m) * (X 1 ω - m) ∂μ = σSq * ρ
        -- This follows from the definition of ρ
        have hρ_def : ρ = (∫ ω, (X 0 ω - m) * (X 1 ω - m) ∂μ) / σSq := rfl
        rw [hρ_def]
        field_simp [ne_of_gt hσSq_pos]
      · -- Case j < i: use symmetry
        push_neg at h_ord
        have h_ji : j < i := Nat.lt_of_le_of_ne h_ord (Ne.symm hij)
        have h_eq_dist := ViaL2.contractable_map_pair (X := X) hX_contract hX_meas h_ji
        have h_int_ji : ∫ ω, (X j ω - m) * (X i ω - m) ∂μ
            = ∫ p : ℝ × ℝ, (p.1 - m) * (p.2 - m) ∂(Measure.map (fun ω => (X j ω, X i ω)) μ) := by
          have h_ae : AEStronglyMeasurable (fun p : ℝ × ℝ => (p.1 - m) * (p.2 - m))
              (Measure.map (fun ω => (X j ω, X i ω)) μ) := by
            exact ((continuous_fst.sub continuous_const).mul
              (continuous_snd.sub continuous_const)).aestronglyMeasurable
          have h_comp : (fun ω => (X j ω - m) * (X i ω - m))
              = (fun p : ℝ × ℝ => (p.1 - m) * (p.2 - m)) ∘ (fun ω => (X j ω, X i ω)) := rfl
          rw [h_comp]
          exact (integral_map ((hX_meas j).prodMk (hX_meas i)).aemeasurable h_ae).symm
        have h_int_01 : ∫ ω, (X 0 ω - m) * (X 1 ω - m) ∂μ
            = ∫ p : ℝ × ℝ, (p.1 - m) * (p.2 - m) ∂(Measure.map (fun ω => (X 0 ω, X 1 ω)) μ) := by
          have h_ae : AEStronglyMeasurable (fun p : ℝ × ℝ => (p.1 - m) * (p.2 - m))
              (Measure.map (fun ω => (X 0 ω, X 1 ω)) μ) := by
            exact ((continuous_fst.sub continuous_const).mul
              (continuous_snd.sub continuous_const)).aestronglyMeasurable
          have h_comp : (fun ω => (X 0 ω - m) * (X 1 ω - m))
              = (fun p : ℝ × ℝ => (p.1 - m) * (p.2 - m)) ∘ (fun ω => (X 0 ω, X 1 ω)) := rfl
          rw [h_comp]
          exact (integral_map ((hX_meas 0).prodMk (hX_meas 1)).aemeasurable h_ae).symm
        have h_symm : ∫ ω, (X i ω - m) * (X j ω - m) ∂μ = ∫ ω, (X j ω - m) * (X i ω - m) ∂μ := by
          congr 1; ext ω; ring
        rw [h_symm, h_int_ji, h_eq_dist, ← h_int_01]
        -- Now need to show: ∫ (X 0 ω - m) * (X 1 ω - m) ∂μ = σSq * ρ
        -- This follows from the definition of ρ
        have hρ_def : ρ = (∫ ω, (X 0 ω - m) * (X 1 ω - m) ∂μ) / σSq := rfl
        rw [hρ_def]
        field_simp [ne_of_gt hσSq_pos]

    -- Bound on ρ from Cauchy-Schwarz
    have hρ_bd : -1 ≤ ρ ∧ ρ ≤ 1 := by
      -- By Cauchy-Schwarz: |E[(X-m)(Y-m)]|² ≤ E[(X-m)²] · E[(Y-m)²]
      -- For X_0, X_1: |Cov|² ≤ σ² · σ² = σ⁴
      -- So |Cov| ≤ σ², and thus |ρ| = |Cov/σ²| ≤ 1

      -- The centered variables are in L²
      have hf₀ : MemLp (fun ω => X 0 ω - m) 2 μ := (hX_L2 0).sub (memLp_const m)
      have hf₁ : MemLp (fun ω => X 1 ω - m) 2 μ := (hX_L2 1).sub (memLp_const m)

      -- Their product is integrable
      have h_int : Integrable (fun ω => (X 0 ω - m) * (X 1 ω - m)) μ := hf₀.integrable_mul hf₁

      -- Apply Cauchy-Schwarz: |∫ f·g| ≤ √(∫ f²) · √(∫ g²)
      have h_cs : |∫ ω, (X 0 ω - m) * (X 1 ω - m) ∂μ|
          ≤ Real.sqrt (∫ ω, (X 0 ω - m)^2 ∂μ) * Real.sqrt (∫ ω, (X 1 ω - m)^2 ∂μ) := by
        -- Apply Hölder's inequality directly to the integrand
        -- Step 1: |∫ f·g| ≤ ∫ |f·g|
        have h_tri : |∫ ω, (X 0 ω - m) * (X 1 ω - m) ∂μ| ≤ ∫ ω, |(X 0 ω - m) * (X 1 ω - m)| ∂μ :=
          MeasureTheory.norm_integral_le_integral_norm (fun ω => (X 0 ω - m) * (X 1 ω - m))
        -- Step 2: ∫ |f·g| = ∫ |f|·|g|
        have h_abs_mul : ∫ ω, |(X 0 ω - m) * (X 1 ω - m)| ∂μ = ∫ ω, |X 0 ω - m| * |X 1 ω - m| ∂μ := by
          congr 1
          funext ω
          exact abs_mul (X 0 ω - m) (X 1 ω - m)
        -- Step 3: Hölder inequality
        have h_holder : ∫ ω, |X 0 ω - m| * |X 1 ω - m| ∂μ
            ≤ (∫ ω, |X 0 ω - m| ^ 2 ∂μ) ^ (1/2 : ℝ) * (∫ ω, |X 1 ω - m| ^ 2 ∂μ) ^ (1/2 : ℝ) := by
          -- Apply Hölder's inequality (Cauchy-Schwarz)
          -- We have f, g in L²
          -- Convert the goal to use snorm
          have h_nonneg₀ : ∀ᵐ ω ∂μ, 0 ≤ |X 0 ω - m| := ae_of_all μ (fun ω => abs_nonneg _)
          have h_nonneg₁ : ∀ᵐ ω ∂μ, 0 ≤ |X 1 ω - m| := ae_of_all μ (fun ω => abs_nonneg _)
          -- Apply Hölder: ∫ |f||g| ≤ (∫ |f|^p)^(1/p) * (∫ |g|^q)^(1/q) with p=q=2
          have h_key : ∫ ω, |X 0 ω - m| * |X 1 ω - m| ∂μ
              ≤ (∫ ω, |X 0 ω - m| ^ (2:ℝ) ∂μ) ^ ((2:ℝ)⁻¹) * (∫ ω, |X 1 ω - m| ^ (2:ℝ) ∂μ) ^ ((2:ℝ)⁻¹) := by
            -- HölderConjugate for p = q = 2
            have hpq : (2:ℝ).HolderConjugate 2 := by
              constructor
              · norm_num
              · norm_num
              · norm_num
            -- MemLp for |f| and |g| with ENNReal exponents
            -- Use that for ℝ, MemLp f p μ is defined via snorm which uses ‖f ω‖
            -- So MemLp (X 0 · - m) means ‖X 0 ω - m‖ which equals |X 0 ω - m|
            have hf₀' : MemLp (fun ω => |X 0 ω - m|) (ENNReal.ofReal 2) μ := by
              have h2 : (ENNReal.ofReal 2 : ENNReal) = (2 : ENNReal) := by norm_num
              rw [h2]
              -- hf₀ says MemLp (fun ω => X 0 ω - m), which by definition uses snorm of ‖·‖
              -- So this is the same as MemLp (fun ω => ‖X 0 ω - m‖)
              have : MemLp (fun ω => ‖X 0 ω - m‖) 2 μ := hf₀.norm
              -- Now ‖X 0 ω - m‖ = |X 0 ω - m| for reals
              have h_eq : (fun ω => ‖X 0 ω - m‖) =ᵐ[μ] (fun ω => |X 0 ω - m|) := by
                filter_upwards with ω
                exact Real.norm_eq_abs _
              exact MemLp.ae_eq h_eq this
            have hf₁' : MemLp (fun ω => |X 1 ω - m|) (ENNReal.ofReal 2) μ := by
              have h2 : (ENNReal.ofReal 2 : ENNReal) = (2 : ENNReal) := by norm_num
              rw [h2]
              -- hf₁ says MemLp (fun ω => X 1 ω - m), which by definition uses snorm of ‖·‖
              -- So this is the same as MemLp (fun ω => ‖X 1 ω - m‖)
              have : MemLp (fun ω => ‖X 1 ω - m‖) 2 μ := hf₁.norm
              -- Now ‖X 1 ω - m‖ = |X 1 ω - m| for reals
              have h_eq : (fun ω => ‖X 1 ω - m‖) =ᵐ[μ] (fun ω => |X 1 ω - m|) := by
                filter_upwards with ω
                exact Real.norm_eq_abs _
              exact MemLp.ae_eq h_eq this
            -- Apply integral_mul_le_Lp_mul_Lq_of_nonneg
            have := MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg hpq h_nonneg₀ h_nonneg₁ hf₀' hf₁'
            convert this using 2 <;> norm_num
          convert h_key using 2
          · norm_num
          · norm_num
        -- Step 4: Convert rpow to sqrt and |x|^2 to x^2
        have h_sqrt_conv : (∫ ω, |X 0 ω - m| ^ 2 ∂μ) ^ (1/2 : ℝ) * (∫ ω, |X 1 ω - m| ^ 2 ∂μ) ^ (1/2 : ℝ)
            = Real.sqrt (∫ ω, (X 0 ω - m)^2 ∂μ) * Real.sqrt (∫ ω, (X 1 ω - m)^2 ∂μ) := by
          have h4 : (∫ ω, |X 0 ω - m| ^ 2 ∂μ) ^ (1/2 : ℝ) = Real.sqrt (∫ ω, (X 0 ω - m)^2 ∂μ) := by
            rw [Real.sqrt_eq_rpow]
            congr 1
            congr 1
            funext ω
            rw [sq_abs]
          have h5 : (∫ ω, |X 1 ω - m| ^ 2 ∂μ) ^ (1/2 : ℝ) = Real.sqrt (∫ ω, (X 1 ω - m)^2 ∂μ) := by
            rw [Real.sqrt_eq_rpow]
            congr 1
            congr 1
            funext ω
            rw [sq_abs]
          rw [h4, h5]
        -- Combine all steps
        calc |∫ ω, (X 0 ω - m) * (X 1 ω - m) ∂μ|
            ≤ ∫ ω, |(X 0 ω - m) * (X 1 ω - m)| ∂μ := h_tri
          _ = ∫ ω, |X 0 ω - m| * |X 1 ω - m| ∂μ := h_abs_mul
          _ ≤ (∫ ω, |X 0 ω - m| ^ 2 ∂μ) ^ (1/2 : ℝ) * (∫ ω, |X 1 ω - m| ^ 2 ∂μ) ^ (1/2 : ℝ) := h_holder
          _ = Real.sqrt (∫ ω, (X 0 ω - m)^2 ∂μ) * Real.sqrt (∫ ω, (X 1 ω - m)^2 ∂μ) := h_sqrt_conv

      -- Substitute the variances
      rw [hvar 0, hvar 1] at h_cs
      have h_sqrt_sq : Real.sqrt σSq * Real.sqrt σSq = σSq := by
        have : σSq * σSq = σSq ^ 2 := (sq σSq).symm
        rw [← Real.sqrt_mul hσSq_nonneg, this, Real.sqrt_sq hσSq_nonneg]
      rw [h_sqrt_sq] at h_cs

      -- The covariance equals σSq * ρ by definition
      have h_cov_eq : ∫ ω, (X 0 ω - m) * (X 1 ω - m) ∂μ = σSq * ρ := by
        have : ρ = (∫ ω, (X 0 ω - m) * (X 1 ω - m) ∂μ) / σSq := rfl
        rw [this]; field_simp [ne_of_gt hσSq_pos]
      rw [h_cov_eq] at h_cs

      -- Now |σSq * ρ| ≤ σSq
      rw [abs_mul, abs_of_pos hσSq_pos, mul_comm] at h_cs
      have h_ρ_bd : |ρ| * σSq ≤ σSq := h_cs
      have : |ρ| ≤ 1 := (mul_le_iff_le_one_left hσSq_pos).mp h_ρ_bd
      exact abs_le.mp this

    exact ⟨m, σSq, ρ, hmean, hvar, hcov, hσSq_nonneg, hρ_bd⟩

  · -- Case: zero variance (all X_i are constant a.s.)
    push_neg at hσSq_pos
    have hσSq_zero : σSq = 0 := le_antisymm hσSq_pos hσSq_nonneg

    -- When variance is 0, all X_i = m almost surely
    have hX_const : ∀ i, ∀ᵐ ω ∂μ, X i ω = m := by
      intro i
      -- Use the fact that variance of X_i is 0
      have h_var_i : ∫ ω, (X i ω - m)^2 ∂μ = 0 := by
        rw [hvar i, hσSq_zero]
      -- When ∫ f² = 0 for a nonnegative function, f = 0 a.e.
      have h_ae_zero : ∀ᵐ ω ∂μ, (X i ω - m)^2 = 0 := by
        have h_nonneg : ∀ ω, 0 ≤ (X i ω - m)^2 := fun ω => sq_nonneg _
        have h_integrable : Integrable (fun ω => (X i ω - m)^2) μ := by
          have : MemLp (fun ω => X i ω - m) 2 μ := (hX_L2 i).sub (memLp_const m)
          exact this.integrable_sq
        exact integral_eq_zero_iff_of_nonneg_ae (ae_of_all _ h_nonneg) h_integrable |>.mp h_var_i
      -- Square equals zero iff the value equals zero
      filter_upwards [h_ae_zero] with ω h
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp h)

    -- Covariance is 0
    have hcov : ∀ i j, i ≠ j → ∫ ω, (X i ω - m) * (X j ω - m) ∂μ = 0 := by
      intro i j _
      -- Use the fact that X_i = m and X_j = m almost everywhere
      have h_ae_prod : ∀ᵐ ω ∂μ, (X i ω - m) * (X j ω - m) = 0 := by
        filter_upwards [hX_const i, hX_const j] with ω hi hj
        rw [hi, hj]
        ring
      -- Integral of a.e. zero function is zero
      have h_integrable : Integrable (fun ω => (X i ω - m) * (X j ω - m)) μ := by
        have h_i : MemLp (fun ω => X i ω - m) 2 μ := (hX_L2 i).sub (memLp_const m)
        have h_j : MemLp (fun ω => X j ω - m) 2 μ := (hX_L2 j).sub (memLp_const m)
        exact h_i.integrable_mul h_j
      exact integral_eq_zero_of_ae h_ae_prod

    -- ρ = 0 works
    use m, σSq, 0
    refine ⟨hmean, hvar, ?_, hσSq_nonneg, ?_⟩
    · intro i j hij
      rw [hcov i j hij, hσSq_zero]
      ring
    · norm_num

end Exchangeability.DeFinetti
