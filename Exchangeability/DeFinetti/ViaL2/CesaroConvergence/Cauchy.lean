/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Exchangeability.DeFinetti.ViaL2.BlockAvgDef
import Exchangeability.Probability.CenteredVariables
import Exchangeability.Util.FinsetHelpers

/-!
# Cesàro Cauchy Property: `blockAvg_cauchy_in_L2`

Block Cesàro averages of a contractable sequence form a Cauchy sequence in L².
This is the L²-side conclusion of Kallenberg's "second proof" — proved here via
`l2_contractability_bound` (from `L2Helpers.lean`), avoiding the circular use of
full exchangeability that `kallenberg_L2_bound` would require.

## Main results

* `blockAvg_cauchy_in_L2`: Block averages form a Cauchy sequence in L²
  (used by `CesaroConvergence.L2.cesaro_to_condexp_L2`)
* `blockAvgFrozen`: Block average with a "frozen" denominator (helper for the
  Cauchy proof)

## References

* Kallenberg (2005), *Probabilistic Symmetries and Invariance Principles*,
  Chapter 1, "Second proof of Theorem 1.1"
-/

noncomputable section

namespace Exchangeability.DeFinetti.ViaL2

open MeasureTheory ProbabilityTheory BigOperators Filter Topology
open Exchangeability
open Exchangeability.DeFinetti.L2Helpers
open Exchangeability.Probability.CenteredVariables

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

open scoped BigOperators

private lemma cesaro_cauchy_rho_lt
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} (_hX_contract : Exchangeability.Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (f : ℝ → ℝ) (hf_meas : Measurable f) (hf_bdd : ∀ x, |f x| ≤ 1)
    (m_mean : ℝ) (hm_mean : m_mean = ∫ ω, f (X 0 ω) ∂μ)
    (Z : ℕ → Ω → ℝ) (hZ_def : ∀ i ω, Z i ω = f (X i ω) - m_mean)
    (hZ_meas : ∀ i, Measurable (Z i))
    (_hZ_contract : Exchangeability.Contractable μ Z)
    (hZ_var_uniform : ∀ i, ∫ ω, (Z i ω)^2 ∂μ = ∫ ω, (Z 0 ω)^2 ∂μ)
    (hZ_mean_zero : ∀ i, ∫ ω, Z i ω ∂μ = 0)
    (hZ_cov_uniform : ∀ i j, i ≠ j → ∫ ω, Z i ω * Z j ω ∂μ = ∫ ω, Z 0 ω * Z 1 ω ∂μ)
    (σSq : ℝ) (hσ_pos : σSq > 0) (hσSq_def : σSq = ∫ ω, (Z 0 ω)^2 ∂μ)
    (ρ : ℝ) (hρ_bd : -1 ≤ ρ ∧ ρ ≤ 1) (hρ_def : ρ = (∫ ω, Z 0 ω * Z 1 ω ∂μ) / σSq)
    (hρ_lt : ρ < 1)
    (Cf : ℝ) (hCf_def : Cf = 2 * σSq * (1 - ρ))
    (ε : ENNReal) (hε : ε > 0) :
    ∃ N, ∀ {n n'}, n ≥ N → n' ≥ N →
      eLpNorm (blockAvg f X 0 n - blockAvg f X 0 n') 2 μ < ε := by
  -- Step 7c: Choose N via Archimedean property
  -- We want Cf / N < (ε.toReal)²
  -- Equivalently: N > Cf / (ε.toReal)²
  -- If ε = ⊤, the property is trivial (take any N); otherwise use Archimedean property
  by_cases hε_top : ε = ⊤
  · -- Case ε = ⊤: any N works (e.g. 0); the difference is in L² so its eLpNorm is finite.
    refine ⟨0, ?_⟩
    intro n n' _ _
    have h_mem : MemLp (fun ω => blockAvg f X 0 n ω - blockAvg f X 0 n' ω) 2 μ :=
      (blockAvg_memLp_two_of_abs_le_one f X hf_meas hX_meas hf_bdd 0 n).sub
        (blockAvg_memLp_two_of_abs_le_one f X hf_meas hX_meas hf_bdd 0 n')
    rw [hε_top]
    exact MemLp.eLpNorm_lt_top h_mem

  -- Case ε < ⊤: use Archimedean property to find N
  have hε_lt_top : ε < ⊤ := lt_top_iff_ne_top.mpr hε_top
  have hε_pos : 0 < ε.toReal := by
    rw [ENNReal.toReal_pos_iff]
    exact ⟨hε, hε_lt_top⟩
  have hε_sq_pos : 0 < (ε.toReal) ^ 2 := sq_pos_of_pos hε_pos

  have hCf_nonneg : 0 ≤ Cf := by
    rw [hCf_def]
    have h_one_sub_ρ_pos : 0 < 1 - ρ := by linarith
    positivity

  have hCf_pos : 0 < Cf := by
    rw [hCf_def]
    have h_one_sub_ρ_pos : 0 < 1 - ρ := by linarith
    positivity

  -- Find N using Archimedean property
  obtain ⟨N', hN'⟩ := exists_nat_gt (Cf / (ε.toReal) ^ 2)
  use max 1 (N' + 1)
  intros n n' hn_ge hn'_ge

  -- Step 7d: Apply l2_contractability_bound

  -- Work with a common finite prefix m = max(n, n')
  let m := max n n'
  let ξ : Fin m → Ω → ℝ := fun i ω => Z i.val ω

  -- Define weight distributions: p for blockAvg n, q for blockAvg n'
  let p : Fin m → ℝ := fun i => if i.val < n then (n : ℝ)⁻¹ else 0
  let q : Fin m → ℝ := fun i => if i.val < n' then (n' : ℝ)⁻¹ else 0

  -- Step 1: Show p and q are probability distributions
  -- First derive that n > 0 from hn_ge
  have hn_pos : n > 0 := by
    calc n ≥ max 1 (N' + 1) := hn_ge
      _ ≥ 1 := le_max_left 1 (N' + 1)
      _ > 0 := Nat.one_pos

  have hp_prob : ∑ i : Fin m, p i = 1 ∧ ∀ i, 0 ≤ p i := by
    constructor
    · -- Sum equals 1
      -- p i = 1/n for i < n, and 0 otherwise
      -- So ∑ p i = ∑_{i<n} (1/n) = n * (1/n) = 1
      calc ∑ i : Fin m, p i
          = ∑ i : Fin m, if i.val < n then (n : ℝ)⁻¹ else 0 := rfl
        _ = ∑ i ∈ Finset.univ.filter (fun i : Fin m => i.val < n), (n : ℝ)⁻¹ := by
            rw [Finset.sum_ite]
            simp only [Finset.sum_const_zero, add_zero]
        _ = (Finset.filter (fun i : Fin m => i.val < n) Finset.univ).card • (n : ℝ)⁻¹ := by
            rw [Finset.sum_const]
        _ = n • (n : ℝ)⁻¹ := by
            congr 1
            exact Finset.filter_val_lt_card (le_max_left n n')
        _ = 1 := by
            rw [nsmul_eq_mul]
            field_simp [Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hn_pos)]
    · -- All weights are non-negative
      intro i
      simp only [p]
      split_ifs
      · exact inv_nonneg.mpr (Nat.cast_nonneg n)
      · exact le_refl 0

  -- Similarly for n'
  have hn'_pos : n' > 0 := by
    calc n' ≥ max 1 (N' + 1) := hn'_ge
      _ ≥ 1 := le_max_left 1 (N' + 1)
      _ > 0 := Nat.one_pos

  have hq_prob : ∑ i : Fin m, q i = 1 ∧ ∀ i, 0 ≤ q i := by
    constructor
    · -- Sum equals 1
      calc ∑ i : Fin m, q i
          = ∑ i : Fin m, if i.val < n' then (n' : ℝ)⁻¹ else 0 := rfl
        _ = ∑ i ∈ Finset.univ.filter (fun i : Fin m => i.val < n'), (n' : ℝ)⁻¹ := by
            rw [Finset.sum_ite]
            simp only [Finset.sum_const_zero, add_zero]
        _ = (Finset.filter (fun i : Fin m => i.val < n') Finset.univ).card • (n' : ℝ)⁻¹ := by
            rw [Finset.sum_const]
        _ = n' • (n' : ℝ)⁻¹ := by
            congr 1
            exact Finset.filter_val_lt_card (le_max_right n n')
        _ = 1 := by
            rw [nsmul_eq_mul]
            field_simp [Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hn'_pos)]
    · -- All weights are non-negative
      intro i
      simp only [q]
      split_ifs
      · exact inv_nonneg.mpr (Nat.cast_nonneg n')
      · exact le_refl 0

  -- Step 2: Define σ and prove hypotheses for l2_contractability_bound

  -- Define σ := sqrt(σSq), the standard deviation
  let σ := Real.sqrt σSq

  -- Prove mean of ξ is 0
  have hmean_ξ : ∀ k : Fin m, ∫ ω, ξ k ω ∂μ = 0 := by
    intro k
    simp only [ξ]
    exact hZ_mean_zero k.val

  -- Prove ξ is in L²
  have hL2_ξ : ∀ k : Fin m, MemLp (fun ω => ξ k ω - 0) 2 μ := by
    intro k
    simp only [sub_zero, ξ]
    -- Z k.val is bounded, hence in L²
    -- Same proof as for Z 0: |Z k.val| ≤ |f| + |m| ≤ 1 + 1 = 2
    apply memLp_two_of_bounded (hZ_meas k.val)
    intro ω
    -- Unfold ξ and Z to show |f(X k.val ω) - m| ≤ 2
    have h1 : |f (X k.val ω)| ≤ 1 := hf_bdd (X k.val ω)
    have h2 : |∫ ω', f (X 0 ω') ∂μ| ≤ 1 := by
      -- |∫ f(X 0)| ≤ ∫ |f(X 0)| ≤ ∫ 1 = 1
      have hfX_int : Integrable (fun ω => f (X 0 ω)) μ := by
        apply Integrable.of_bound
        · exact (hf_meas.comp (hX_meas 0)).aestronglyMeasurable
        · filter_upwards [] with ω
          exact hf_bdd (X 0 ω)
      calc |∫ ω', f (X 0 ω') ∂μ|
          ≤ ∫ ω', |f (X 0 ω')| ∂μ := abs_integral_le_integral_abs
        _ ≤ ∫ ω', 1 ∂μ := by
            apply integral_mono_ae
            · exact hfX_int.abs
            · exact integrable_const 1
            · filter_upwards [] with ω'
              exact hf_bdd (X 0 ω')
        _ = 1 := by simp
    -- Show |Z k.val ω| ≤ 2 using hZ_def and triangle inequality
    rw [hZ_def k.val ω]
    calc |f (X k.val ω) - m_mean|
        ≤ |f (X k.val ω)| + |m_mean| := abs_sub _ _
      _ = |f (X k.val ω)| + |∫ ω', f (X 0 ω') ∂μ| := by rw [hm_mean]
      _ ≤ 1 + 1 := by linarith
      _ = 2 := by norm_num

  -- Prove uniform variance: ∫ ξ_k² = σ²
  have hvar_ξ : ∀ k : Fin m, ∫ ω, (ξ k ω - 0)^2 ∂μ = σ ^ 2 := by
    intro k
    simp only [sub_zero, ξ]
    -- From hZ_var_uniform: ∫ (Z k.val)² = ∫ (Z 0)² = σSq
    -- And σ² = (sqrt σSq)² = σSq (when σSq ≥ 0)
    calc ∫ ω, (Z k.val ω) ^ 2 ∂μ
        = ∫ ω, (Z 0 ω) ^ 2 ∂μ := hZ_var_uniform k.val
      _ = σSq := hσSq_def.symm
      _ = (Real.sqrt σSq) ^ 2 := by
          -- σSq = ∫ (Z 0)² ≥ 0, so sqrt(σSq)² = σSq
          have hσSq_nonneg : 0 ≤ σSq := by
            rw [hσSq_def]
            exact integral_nonneg fun ω => sq_nonneg _
          exact (Real.sq_sqrt hσSq_nonneg).symm
      _ = σ ^ 2 := rfl

  -- Define covZ from hρ_def
  let covZ := ∫ ω, Z 0 ω * Z 1 ω ∂μ
  have hρ_eq : ρ = covZ / σSq := hρ_def

  -- Prove uniform covariance: ∫ ξ_i * ξ_j = σ² * ρ for i ≠ j
  have hcov_ξ : ∀ i j : Fin m, i ≠ j →
      ∫ ω, (ξ i ω - 0) * (ξ j ω - 0) ∂μ = σ ^ 2 * ρ := by
    intros i j hij
    simp only [sub_zero, ξ]
    -- Need to show: ∫ Z i.val * Z j.val = σ² * ρ
    -- From hZ_cov_uniform: ∫ Z i.val * Z j.val = ∫ Z 0 * Z 1 = covZ (when i.val ≠ j.val)
    -- And σ² * ρ = σSq * (covZ / σSq) = covZ

    -- First show i.val ≠ j.val from i ≠ j
    have hij_val : i.val ≠ j.val := by
      intro h_eq
      apply hij
      exact Fin.ext h_eq

    -- Apply hZ_cov_uniform
    have h_cov_eq : ∫ ω, Z i.val ω * Z j.val ω ∂μ = covZ :=
      hZ_cov_uniform i.val j.val hij_val

    -- Show σ² * ρ = covZ
    have h_rhs : σ ^ 2 * ρ = covZ := by
      -- σ² = σSq and ρ = covZ / σSq, so σ² * ρ = σSq * (covZ / σSq) = covZ
      have hσSq_nonneg : 0 ≤ σSq := by positivity
      rw [hρ_eq]
      simp only [σ]
      rw [Real.sq_sqrt hσSq_nonneg]
      field_simp [hσ_pos.ne']

    rw [h_cov_eq, h_rhs]

  -- Step 3: Rewrite blockAvg difference as weighted sum
  -- blockAvg f X 0 n = (1/n) ∑_{i<n} f(X_i) = (1/n) ∑_{i<n} (Z_i + m) = (1/n) ∑_{i<n} Z_i + m
  -- So: blockAvg_n - blockAvg_n' = ∑ i, p i * Z_i - ∑ i, q i * Z_i

  have h_blockAvg_eq : ∀ᵐ ω ∂μ,
      blockAvg f X 0 n ω - blockAvg f X 0 n' ω =
      ∑ i : Fin m, p i * ξ i ω - ∑ i : Fin m, q i * ξ i ω := by
    -- This is true for all ω, not just a.e.
    apply ae_of_all
    intro ω
    -- Step 1: Unfold blockAvg definition
    simp only [blockAvg, zero_add]
    -- Now have: (n : ℝ)⁻¹ * ∑ k ∈ range n, f (X k ω) - (n' : ℝ)⁻¹ * ∑ k ∈ range n', f (X k ω)
    -- Step 2: Rewrite f (X k ω) = Z k ω + m_mean using hZ_def
    have h1 : ∑ k ∈ Finset.range n, f (X k ω) = ∑ k ∈ Finset.range n, (m_mean + Z k ω) := by
      congr 1 with k
      rw [hZ_def]
      ring
    have h2 : ∑ k ∈ Finset.range n', f (X k ω) = ∑ k ∈ Finset.range n', (m_mean + Z k ω) := by
      congr 1 with k
      rw [hZ_def]
      ring
    rw [h1, h2]
    -- Now have: (n : ℝ)⁻¹ * ∑ k ∈ range n, (m_mean + Z k ω) - (n' : ℝ)⁻¹ * ∑ k ∈ range n', (m_mean + Z k ω)
    -- Step 3: Distribute sums: ∑(a + b) = ∑a + ∑b
    simp only [Finset.sum_add_distrib]
    -- Now: (n : ℝ)⁻¹ * (∑ k ∈ range n, m_mean + ∑ k ∈ range n, Z k ω)
    --      - (n' : ℝ)⁻¹ * (∑ k ∈ range n', m_mean + ∑ k ∈ range n', Z k ω)
    -- Step 4: Simplify ∑ k ∈ range n, m_mean = n * m_mean
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    -- Now: (n : ℝ)⁻¹ * ((n : ℝ) * m_mean + ∑ k ∈ range n, Z k ω)
    --      - (n' : ℝ)⁻¹ * ((n' : ℝ) * m_mean + ∑ k ∈ range n', Z k ω)
    -- Step 5: Distribute multiplication
    ring_nf
    -- The m_mean terms cancel: (n : ℝ)⁻¹ * (n : ℝ) * m_mean = m_mean
    have hn_ne_zero : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hn_pos)
    have hn'_ne_zero : (n' : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hn'_pos)
    field_simp [hn_ne_zero, hn'_ne_zero]
    -- Convert both sides to sums over `Fin m` with indicators, then simplify.
    -- Goal: `(∑ k ∈ range n, Z k ω) / n - (∑ k ∈ range n', Z k ω) / n' =`
    --   `∑ i : Fin m, p i * ξ i ω - ∑ i : Fin m, q i * ξ i ω`
    -- where `p i = if i < n then 1/n else 0`, `q i = if i < n' then 1/n' else 0`,
    -- `ξ i = Z i.val`.
    simp only [ξ, p, q]
    -- Expand LHS: (n * m_mean + ∑_{i<n} Z_i) * n' + n * (-(m_mean * n') - ∑_{j<n'} Z_j)
    -- Should simplify to: n' * ∑_{i<n} Z_i - n * ∑_{j<n'} Z_j
    -- Expand RHS: n * n' * (∑ (if i<n then n⁻¹ else 0) * Z_i - ∑ (if j<n' then n'⁻¹ else 0) * Z_j)
    -- Using n * n' * n⁻¹ = n' and indicator sums
    calc ↑n' * (↑n * m_mean + ∑ x ∈ Finset.range n, Z x ω - ↑n * m_mean) -
          ↑n * ∑ x ∈ Finset.range n', Z x ω
        = ↑n' * ∑ x ∈ Finset.range n, Z x ω - ↑n * ∑ x ∈ Finset.range n', Z x ω := by ring
      _ = ↑n * ↑n' * (∑ x : Fin m, (if ↑x < n then (↑n)⁻¹ else 0) * Z (↑x) ω -
                      ∑ x : Fin m, (if ↑x < n' then (↑n')⁻¹ else 0) * Z (↑x) ω) := by
        -- RHS: distribute n * n' and simplify conditionals
        rw [mul_sub]
        -- Simplify: n * n' * n⁻¹ = n' and n * n' * n'⁻¹ = n
        have h1 : ↑n * ↑n' * (∑ x : Fin m, (if ↑x < n then (↑n)⁻¹ else 0) * Z (↑x) ω) =
                  ↑n' * ∑ x ∈ Finset.range n, Z x ω := by
          -- Pull n⁻¹ out and simplify n * n' * n⁻¹ = n'
          calc ↑n * ↑n' * (∑ x : Fin m, (if ↑x < n then (↑n)⁻¹ else 0) * Z (↑x) ω)
              = ∑ x : Fin m, ↑n * ↑n' * ((if ↑x < n then (↑n)⁻¹ else 0) * Z (↑x) ω) := by
                rw [Finset.mul_sum]
            _ = ∑ x : Fin m, (if ↑x < n then ↑n * ↑n' * (↑n)⁻¹ * Z (↑x) ω else 0) := by
                congr 1 with x; split_ifs with h <;> ring
            _ = ∑ x : Fin m, (if ↑x < n then ↑n' * Z (↑x) ω else 0) := by
                congr 1 with x; split_ifs with h
                · field_simp [hn_ne_zero]
                · rfl
            _ = ∑ x ∈ Finset.univ.filter (fun x : Fin m => ↑x < n), ↑n' * Z (↑x) ω := by
                rw [Finset.sum_ite]
                simp only [Finset.sum_const_zero, add_zero]
            _ = ∑ x ∈ Finset.range n, ↑n' * Z x ω := by
                -- Establish bijection between filtered Fin m and Finset.range n
                refine Finset.sum_nbij Fin.val ?hi ?i_inj ?i_surj ?h
                · -- Show x.val ∈ Finset.range n when x ∈ filter
                  intros a ha
                  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
                  exact Finset.mem_range.mpr ha
                · -- Injectivity on filtered set
                  intros a ha b hb hab
                  exact Fin.ext hab
                · -- Surjectivity onto Finset.range n
                  intros b hb
                  have hb' := Finset.mem_range.mp hb
                  refine ⟨⟨b, Nat.lt_of_lt_of_le hb' (le_max_left n n')⟩, ?_, rfl⟩
                  simp [hb']
                · -- Show functions agree
                  intros a ha
                  rfl
            _ = ↑n' * ∑ x ∈ Finset.range n, Z x ω := by rw [← Finset.mul_sum]
        have h2 : ↑n * ↑n' * (∑ x : Fin m, (if ↑x < n' then (↑n')⁻¹ else 0) * Z (↑x) ω) =
                  ↑n * ∑ x ∈ Finset.range n', Z x ω := by
          calc ↑n * ↑n' * (∑ x : Fin m, (if ↑x < n' then (↑n')⁻¹ else 0) * Z (↑x) ω)
              = ∑ x : Fin m, ↑n * ↑n' * ((if ↑x < n' then (↑n')⁻¹ else 0) * Z (↑x) ω) := by
                rw [Finset.mul_sum]
            _ = ∑ x : Fin m, (if ↑x < n' then ↑n * ↑n' * (↑n')⁻¹ * Z (↑x) ω else 0) := by
                congr 1 with x; split_ifs with h <;> ring
            _ = ∑ x : Fin m, (if ↑x < n' then ↑n * Z (↑x) ω else 0) := by
                congr 1 with x; split_ifs with h
                · field_simp [hn'_ne_zero]
                · rfl
            _ = ∑ x ∈ Finset.univ.filter (fun x : Fin m => ↑x < n'), ↑n * Z (↑x) ω := by
                rw [Finset.sum_ite]
                simp only [Finset.sum_const_zero, add_zero]
            _ = ∑ x ∈ Finset.range n', ↑n * Z x ω := by
                -- Establish bijection between filtered Fin m and Finset.range n'
                refine Finset.sum_nbij Fin.val ?hi2 ?i_inj2 ?i_surj2 ?h2
                · -- Show x.val ∈ Finset.range n' when x ∈ filter
                  intros a ha
                  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
                  exact Finset.mem_range.mpr ha
                · -- Injectivity on filtered set
                  intros a ha b hb hab
                  exact Fin.ext hab
                · -- Surjectivity onto Finset.range n'
                  intros b hb
                  have hb' := Finset.mem_range.mp hb
                  refine ⟨⟨b, Nat.lt_of_lt_of_le hb' (le_max_right n n')⟩, ?_, rfl⟩
                  simp [hb']
                · -- Show functions agree
                  intros a ha
                  rfl
            _ = ↑n * ∑ x ∈ Finset.range n', Z x ω := by rw [← Finset.mul_sum]
        rw [h1, h2]

  -- Step 4: Apply l2_contractability_bound
  have h_bound : ∫ ω, (∑ i : Fin m, p i * ξ i ω - ∑ i : Fin m, q i * ξ i ω) ^ 2 ∂μ ≤
      2 * σ ^ 2 * (1 - ρ) * (⨆ i : Fin m, |p i - q i|) :=
    L2Approach.l2_contractability_bound ξ 0 σ ρ hρ_bd hmean_ξ hL2_ξ hvar_ξ hcov_ξ p q hp_prob hq_prob

  -- Step 5: Bound ⨆ i, |p i - q i| ≤ max(1/n, 1/n')
  have h_sup_bound : (⨆ i : Fin m, |p i - q i|) ≤ max (1 / (n : ℝ)) (1 / (n' : ℝ)) := by
    -- m = max n n' ≥ max 1 1 = 1, so Fin m is nonempty
    have hm_pos : 0 < m := by
      simp only [m]
      calc 0 < 1 := Nat.one_pos
        _ ≤ n := hn_pos
        _ ≤ max n n' := le_max_left n n'
    haveI : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp hm_pos
    -- Show each |p i - q i| ≤ max(1/n, 1/n'), then take supremum
    apply ciSup_le
    intro i
    simp only [p, q]
    -- Case analysis on whether i.val < n and i.val < n'
    by_cases hi_n : i.val < n <;> by_cases hi_n' : i.val < n'
    · -- Case 1: i.val < n ∧ i.val < n'
      simp only [hi_n, hi_n', ite_true, one_div]
      -- Now have: |(n:ℝ)⁻¹ - (n':ℝ)⁻¹| ≤ max (n:ℝ)⁻¹ (n':ℝ)⁻¹
      by_cases h : (n : ℝ)⁻¹ ≤ (n' : ℝ)⁻¹
      · -- Case: n⁻¹ ≤ n'⁻¹, so max = n'⁻¹
        rw [abs_sub_comm, abs_of_nonneg (sub_nonneg_of_le h), max_eq_right h]
        exact sub_le_self _ (inv_nonneg.mpr (Nat.cast_nonneg n))
      · -- Case: n⁻¹ > n'⁻¹, so max = n⁻¹
        push Not at h
        rw [abs_of_nonneg (sub_nonneg_of_le (le_of_lt h)), max_eq_left (le_of_lt h)]
        exact sub_le_self _ (inv_nonneg.mpr (Nat.cast_nonneg n'))
    · -- Case 2: i.val < n ∧ i.val ≥ n'
      simp only [hi_n, hi_n', ite_true, ite_false, sub_zero, one_div]
      rw [abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n))]
      exact le_max_left _ _
    · -- Case 3: i.val ≥ n ∧ i.val < n'
      simp only [hi_n, hi_n', ite_false, ite_true, zero_sub, one_div]
      rw [abs_neg, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n'))]
      exact le_max_right _ _
    · -- Case 4: i.val ≥ n ∧ i.val ≥ n'
      simp only [hi_n, hi_n', ite_false, sub_self, abs_zero]
      positivity

  -- Step 6: Combine to get integral bound
  have h_integral_bound : ∫ ω, (blockAvg f X 0 n ω - blockAvg f X 0 n' ω) ^ 2 ∂μ ≤
      2 * σ ^ 2 * (1 - ρ) * max (1 / (n : ℝ)) (1 / (n' : ℝ)) := by
    -- Use h_blockAvg_eq to rewrite, then apply h_bound and h_sup_bound
    calc ∫ ω, (blockAvg f X 0 n ω - blockAvg f X 0 n' ω) ^ 2 ∂μ
        = ∫ ω, (∑ i : Fin m, p i * ξ i ω - ∑ i : Fin m, q i * ξ i ω) ^ 2 ∂μ := by
            -- Use h_blockAvg_eq to rewrite integrand a.e.
            apply integral_congr_ae
            filter_upwards [h_blockAvg_eq] with ω hω
            rw [hω]
      _ ≤ 2 * σ ^ 2 * (1 - ρ) * (⨆ i : Fin m, |p i - q i|) := h_bound
      _ ≤ 2 * σ ^ 2 * (1 - ρ) * max (1 / (n : ℝ)) (1 / (n' : ℝ)) := by
            apply mul_le_mul_of_nonneg_left h_sup_bound
            -- Need to show 0 ≤ 2 * σ ^ 2 * (1 - ρ)
            -- We know Cf = 2 * σSq * (1 - ρ) and σ ^ 2 = σSq
            have hσ_sq_eq : σ ^ 2 = σSq := by
              simp only [σ]
              have hσSq_nonneg : 0 ≤ σSq := by positivity
              exact Real.sq_sqrt hσSq_nonneg
            calc 0 ≤ Cf := hCf_nonneg
              _ = 2 * σSq * (1 - ρ) := hCf_def
              _ = 2 * σ ^ 2 * (1 - ρ) := by rw [← hσ_sq_eq]

  -- Step 7: Use Archimedean bound to show integral < ε²
  have h_integral_lt_ε_sq : ∫ ω, (blockAvg f X 0 n ω - blockAvg f X 0 n' ω) ^ 2 ∂μ < (ε.toReal) ^ 2 := by
    -- Strategy: Show 2*σ²*(1-ρ)*max(1/n,1/n') < ε²
    -- We have Cf = 2*σSq*(1-ρ) = 2*σ²*(1-ρ) and N' > Cf/ε²

    -- First show σ² = σSq
    have hσ_sq_eq : σ ^ 2 = σSq := by
      simp only [σ]
      have hσSq_nonneg : 0 ≤ σSq := by positivity
      exact Real.sq_sqrt hσSq_nonneg

    -- So our coefficient equals Cf
    have h_coeff_eq : 2 * σ ^ 2 * (1 - ρ) = Cf := by
      rw [hσ_sq_eq, hCf_def]

    -- Show that min (n:ℝ) (n':ℝ) = ↑(min n n')
    have h_min_cast : min (n : ℝ) (n' : ℝ) = ↑(min n n') := by
      simp only [Nat.cast_min]

    -- Bound max(1/n, 1/n') by 1/min(n,n')
    have h_max_bound : max (1 / (n : ℝ)) (1 / (n' : ℝ)) ≤ 1 / (min n n' : ℝ) := by
      -- Strategy: 1/n ≤ 1/min(n,n') and 1/n' ≤ 1/min(n,n') since min is smaller
      have hn_pos_real : (0 : ℝ) < n := Nat.cast_pos.mpr hn_pos
      have hn'_pos_real : (0 : ℝ) < n' := Nat.cast_pos.mpr hn'_pos
      rw [h_min_cast]
      have h_min_pos : (0 : ℝ) < ↑(min n n') := by
        simp only [Nat.cast_pos]
        -- min n n' > 0 since both n > 0 and n' > 0
        omega
      apply max_le
      · -- 1/n ≤ 1/min(n,n')
        apply div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1)
        · exact h_min_pos
        · exact Nat.cast_le.mpr (Nat.min_le_left n n')
      · -- 1/n' ≤ 1/min(n,n')
        apply div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1)
        · exact h_min_pos
        · exact Nat.cast_le.mpr (Nat.min_le_right n n')

    -- min(n,n') ≥ max 1 (N'+1) > N'
    have h_min_ge : min (n : ℝ) (n' : ℝ) > (N' : ℝ) := by
      have h1 : min n n' ≥ max 1 (N' + 1) := Nat.le_min.mpr ⟨hn_ge, hn'_ge⟩
      have h2 : max 1 (N' + 1) ≥ N' + 1 := Nat.le_max_right 1 (N' + 1)
      have h3 : min n n' ≥ N' + 1 := Nat.le_trans h2 h1
      rw [h_min_cast]
      have : N' < N' + 1 := Nat.lt_succ_self N'
      have : N' < min n n' := Nat.lt_of_lt_of_le this h3
      exact Nat.cast_lt.mpr this

    -- Therefore 1/min(n,n') < 1/N'
    have h_inv_bound : 1 / (min n n' : ℝ) < 1 / (N' : ℝ) := by
      -- For 0 < b < a, we have 1/a < 1/b
      have hN'_pos_nat : 0 < N' := by
        have h1 : (0 : ℝ) < Cf / (ε.toReal) ^ 2 := by positivity
        have h2 : Cf / (ε.toReal) ^ 2 < (N' : ℝ) := hN'
        exact Nat.cast_pos.mp (h1.trans h2)
      have hN'_pos : (0 : ℝ) < N' := Nat.cast_pos.mpr hN'_pos_nat
      -- Use h_min_ge which states min (n:ℝ) (n':ℝ) > N'
      exact div_lt_div_of_pos_left (by norm_num : (0 : ℝ) < 1) hN'_pos h_min_ge

    -- Combine to get the final bound
    calc ∫ ω, (blockAvg f X 0 n ω - blockAvg f X 0 n' ω) ^ 2 ∂μ
        ≤ 2 * σ ^ 2 * (1 - ρ) * max (1 / (n : ℝ)) (1 / (n' : ℝ)) := h_integral_bound
      _ = Cf * max (1 / (n : ℝ)) (1 / (n' : ℝ)) := by rw [h_coeff_eq]
      _ ≤ Cf * (1 / (min n n' : ℝ)) := by
          apply mul_le_mul_of_nonneg_left h_max_bound
          exact hCf_nonneg
      _ < Cf * (1 / (N' : ℝ)) := by
          apply mul_lt_mul_of_pos_left h_inv_bound hCf_pos
      _ = Cf / (N' : ℝ) := by ring
      _ < Cf / (Cf / (ε.toReal) ^ 2) := by
          apply div_lt_div_of_pos_left hCf_pos (by positivity)
          exact hN'
      _ = (ε.toReal) ^ 2 := by
          field_simp [hCf_pos.ne']

  -- Step 8: Convert integral bound to eLpNorm bound
  -- Goal: eLpNorm (blockAvg f X 0 n - blockAvg f X 0 n') 2 μ < ε

  -- First show blockAvg difference is in L².
  have h_diff_memLp : MemLp (fun ω => blockAvg f X 0 n ω - blockAvg f X 0 n' ω) 2 μ :=
    (blockAvg_memLp_two_of_abs_le_one f X hf_meas hX_meas hf_bdd 0 n).sub
      (blockAvg_memLp_two_of_abs_le_one f X hf_meas hX_meas hf_bdd 0 n')

  -- Now apply the conversion: eLpNorm² → integral
  -- From h_integral_lt_ε_sq: ∫ diff² < ε²
  -- Want: eLpNorm diff 2 < ε

  -- Apply eLpNorm_lt_of_integral_sq_lt from LpNormHelpers
  have h_bound : eLpNorm (fun ω => blockAvg f X 0 n ω - blockAvg f X 0 n' ω) 2 μ <
                 ENNReal.ofReal ε.toReal :=
    eLpNorm_lt_of_integral_sq_lt h_diff_memLp hε_pos h_integral_lt_ε_sq
  -- Convert result: ENNReal.ofReal ε.toReal = ε (since ε < ⊤)
  rw [ENNReal.ofReal_toReal (ne_of_lt hε_lt_top)] at h_bound
  -- Eta-reduce: (fun ω => blockAvg f X 0 n ω - blockAvg f X 0 n' ω) = blockAvg f X 0 n - blockAvg f X 0 n'
  exact h_bound

/-! ### Performance wrappers to stop unfolding `blockAvg` inside `eLpNorm` -/

/-- Frozen alias for `blockAvg f X 0 n`. Regular def (not `@[irreducible]`)
    but we provide helper lemmas to avoid unfolding in timeout-prone contexts.

    This wrapper prevents expensive elaboration timeouts when `blockAvg` appears
    inside `eLpNorm` goals, by using pre-proved lemmas instead of unfolding. -/
private def blockAvgFrozen {Ω : Type*} (f : ℝ → ℝ) (X : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω => blockAvg f X 0 n ω

private lemma blockAvgFrozen_def {Ω : Type*} (f : ℝ → ℝ) (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    blockAvgFrozen f X n ω = blockAvg f X 0 n ω :=
  rfl


/-- Internal version of `blockAvg_cauchy_in_L2` stated against `blockAvgFrozen`
to keep the elaborator from unfolding `blockAvg` inside `eLpNorm` during the
covariance bookkeeping. The public statement below restates the same fact in
terms of `blockAvg` directly. -/
private lemma blockAvgFrozen_cauchy_in_L2
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (f : ℝ → ℝ) (hf_meas : Measurable f) (hf_bdd : ∀ x, |f x| ≤ 1) :
    ∀ ε > 0, ∃ N, ∀ {n n'}, n ≥ N → n' ≥ N →
      eLpNorm (fun ω => blockAvgFrozen f X n ω - blockAvgFrozen f X n' ω) 2 μ < ε := by
  intro ε hε

  -- Define centered variables Z_i = f(X_i) - E[f(X_0)]
  let m := ∫ ω, f (X 0 ω) ∂μ
  let Z := fun i ω => f (X i ω) - m

  -- Establish uniform covariance structure
  have hZ_def : ∀ i ω, Z i ω = f (X i ω) - m := fun i ω => rfl
  have ⟨hZ_meas, hZ_contract, hZ_var_uniform, hZ_mean_zero, hZ_cov_uniform⟩ :=
    centered_uniform_covariance hX_contract hX_meas f hf_meas hf_bdd m rfl Z hZ_def

  -- Define variance and correlation
  let σSq := ∫ ω, (Z 0 ω)^2 ∂μ
  let covZ := ∫ ω, Z 0 ω * Z 1 ω ∂μ

  -- Case split on variance
  by_cases hσ_pos : σSq > 0
  · -- Non-degenerate case
    let ρ := covZ / σSq

    -- Bound |ρ| ≤ 1 using helpers
    have hZ_bdd := centered_variable_bounded hX_meas f hf_meas hf_bdd m rfl Z hZ_def
    have hρ_bd := correlation_coefficient_bounded Z hZ_meas 2 hZ_bdd
        σSq hσ_pos rfl covZ rfl ρ rfl hZ_var_uniform

    by_cases hρ_lt : ρ < 1
    · -- Standard case: ρ < 1
      exact cesaro_cauchy_rho_lt hX_contract hX_meas f hf_meas hf_bdd
        m rfl Z hZ_def hZ_meas hZ_contract hZ_var_uniform hZ_mean_zero hZ_cov_uniform
        σSq hσ_pos rfl ρ hρ_bd rfl hρ_lt (2 * σSq * (1 - ρ)) rfl ε hε

    · -- Edge case: ρ = 1 (perfect correlation) → blockAvg values are ae-equal
      have hρ_eq : ρ = 1 := le_antisymm hρ_bd.2 (not_lt.mp hρ_lt)
      -- When ρ = 1, Z_i = Z_0 a.e., so blockAvg values are equal a.e.
      -- Note: We only prove this for n, n' > 0, which suffices since we use N = 1 below.
      -- (The general case for all n, n' ∈ ℕ is also true, but not needed.)
      have h_ae_eq : ∀ n n', n > 0 → n' > 0 → ∀ᵐ ω ∂μ, blockAvg f X 0 n ω = blockAvg f X 0 n' ω := by
        -- Strategy: Show E[(Z_i - Z_j)²] = 0 when ρ = 1, implying Z_i = Z_j a.e.
        -- Step 1: Prove Z_i = Z_0 a.e. for all i
        have hZi_eq_Z0 : ∀ i, Z i =ᵐ[μ] Z 0 := by
          intro i
          -- Expand E[(Z_i - Z_0)²] = E[Z_i²] - 2*E[Z_i*Z_0] + E[Z_0²]
          have h_diff_sq : ∫ ω, (Z i ω - Z 0 ω) ^ 2 ∂μ = 0 := by
            by_cases hi : i = 0
            · -- Case i = 0: Z_0 - Z_0 = 0
              simp [hi]
            · -- Case i ≠ 0: Use ρ = 1
              -- E[(Z_i - Z_0)²] = E[Z_i²] + E[Z_0²] - 2*E[Z_i*Z_0]
              --                = σ² + σ² - 2*E[Z_i*Z_0]

              -- Expand (Z_i - Z_0)² = Z_i² + Z_0² - 2*Z_i*Z_0 in expectation
              -- Expand (a - b)² = a² + b² - 2ab using algebra and linearity of integral
              have h_expand : ∫ ω, (Z i ω - Z 0 ω) ^ 2 ∂μ =
                  ∫ ω, (Z i ω) ^ 2 ∂μ + ∫ ω, (Z 0 ω) ^ 2 ∂μ - 2 * ∫ ω, Z i ω * Z 0 ω ∂μ := by
                -- (a - b)² = a² - 2ab + b²
                have h_alg : ∀ a b : ℝ, (a - b) ^ 2 = a ^ 2 - 2 * a * b + b ^ 2 := by
                  intro a b; ring
                -- Rewrite the integrand
                have : (fun ω => (Z i ω - Z 0 ω) ^ 2) = fun ω => (Z i ω) ^ 2 - 2 * Z i ω * Z 0 ω + (Z 0 ω) ^ 2 := by
                  ext ω; exact h_alg (Z i ω) (Z 0 ω)
                rw [this]
                -- Define integrability proofs inline
                have hZ_bdd : ∀ j ω, |Z j ω| ≤ 2 :=
                  centered_variable_bounded hX_meas f hf_meas hf_bdd m rfl Z hZ_def
                have h_int_i : Integrable (Z i) μ := show Integrable (Z i) μ from ⟨
                  (hZ_meas i).aestronglyMeasurable,
                  HasFiniteIntegral.of_bounded (by
                    filter_upwards [] with ω
                    exact hZ_bdd i ω)⟩
                have h_int_0 : Integrable (Z 0) μ := show Integrable (Z 0) μ from ⟨
                  (hZ_meas 0).aestronglyMeasurable,
                  HasFiniteIntegral.of_bounded (by
                    filter_upwards [] with ω
                    exact hZ_bdd 0 ω)⟩
                -- Need integrability of Z i ^ 2, Z 0 ^ 2, and Z i * Z 0
                -- These follow from boundedness (bounded functions on finite measure are integrable)
                have h_int_i_sq : Integrable (fun ω => (Z i ω) ^ 2) μ := ⟨
                  (hZ_meas i).pow_const 2 |>.aestronglyMeasurable,
                  HasFiniteIntegral.of_bounded (by
                    filter_upwards [] with ω
                    have : |Z i ω| ≤ 2 := hZ_bdd i ω
                    calc ‖(Z i ω) ^ 2‖
                        = |(Z i ω) ^ 2| := by simp [Real.norm_eq_abs]
                      _ = (Z i ω) ^ 2 := abs_sq (Z i ω)
                      _ = |Z i ω| ^ 2 := by rw [sq_abs]
                      _ ≤ 2 ^ 2 := by gcongr
                      _ = 4 := by norm_num)⟩
                have h_int_0_sq : Integrable (fun ω => (Z 0 ω) ^ 2) μ := ⟨
                  (hZ_meas 0).pow_const 2 |>.aestronglyMeasurable,
                  HasFiniteIntegral.of_bounded (by
                    filter_upwards [] with ω
                    have : |Z 0 ω| ≤ 2 := hZ_bdd 0 ω
                    calc ‖(Z 0 ω) ^ 2‖
                        = |(Z 0 ω) ^ 2| := by simp [Real.norm_eq_abs]
                      _ = (Z 0 ω) ^ 2 := abs_sq (Z 0 ω)
                      _ = |Z 0 ω| ^ 2 := by rw [sq_abs]
                      _ ≤ 2 ^ 2 := by gcongr
                      _ = 4 := by norm_num)⟩
                have h_int_prod : Integrable (fun ω => Z i ω * Z 0 ω) μ := ⟨
                  (hZ_meas i).mul (hZ_meas 0) |>.aestronglyMeasurable,
                  HasFiniteIntegral.of_bounded (by
                    filter_upwards [] with ω
                    have hi : |Z i ω| ≤ 2 := hZ_bdd i ω
                    have h0 : |Z 0 ω| ≤ 2 := hZ_bdd 0 ω
                    calc ‖Z i ω * Z 0 ω‖
                        = |Z i ω * Z 0 ω| := by simp [Real.norm_eq_abs]
                      _ = |Z i ω| * |Z 0 ω| := abs_mul (Z i ω) (Z 0 ω)
                      _ ≤ 2 * 2 := mul_le_mul hi h0 (abs_nonneg _) (by norm_num)
                      _ = 4 := by norm_num)⟩
                -- ∫ (a² - 2ab + b²) = ∫ a² + ∫ b² - 2 * ∫ ab by linearity
                have h_rearrange : (fun ω => Z i ω ^ 2 - 2 * Z i ω * Z 0 ω + Z 0 ω ^ 2)
                                 = (fun ω => Z i ω ^ 2 + Z 0 ω ^ 2 - 2 * (Z i ω * Z 0 ω)) := by
                  ext ω; ring
                calc ∫ ω, Z i ω ^ 2 - 2 * Z i ω * Z 0 ω + Z 0 ω ^ 2 ∂μ
                    = ∫ ω, Z i ω ^ 2 + Z 0 ω ^ 2 - 2 * (Z i ω * Z 0 ω) ∂μ := by rw [h_rearrange]
                  _ = ∫ ω, (Z i ω ^ 2 + Z 0 ω ^ 2) ∂μ - ∫ ω, 2 * (Z i ω * Z 0 ω) ∂μ :=
                      integral_sub (h_int_i_sq.add h_int_0_sq) (h_int_prod.const_mul 2)
                  _ = ∫ ω, Z i ω ^ 2 ∂μ + ∫ ω, Z 0 ω ^ 2 ∂μ - ∫ ω, 2 * (Z i ω * Z 0 ω) ∂μ :=
                      by rw [integral_add h_int_i_sq h_int_0_sq]
                  _ = ∫ ω, Z i ω ^ 2 ∂μ + ∫ ω, Z 0 ω ^ 2 ∂μ - 2 * ∫ ω, Z i ω * Z 0 ω ∂μ :=
                      by simp_rw [integral_const_mul]

              -- Now substitute known values
              have h_var_i : ∫ ω, (Z i ω) ^ 2 ∂μ = σSq := by
                calc ∫ ω, (Z i ω) ^ 2 ∂μ
                    = ∫ ω, (Z 0 ω) ^ 2 ∂μ := hZ_var_uniform i
                  _ = σSq := rfl

              have h_var_0 : ∫ ω, (Z 0 ω) ^ 2 ∂μ = σSq := rfl

              have h_cov : ∫ ω, Z i ω * Z 0 ω ∂μ = σSq * ρ := by
                calc ∫ ω, Z i ω * Z 0 ω ∂μ
                    = ∫ ω, Z 0 ω * Z 1 ω ∂μ := by
                      by_cases hi1 : i = 1
                      · simp [hi1]
                        congr 1 with ω
                        ring
                      · -- Use hZ_cov_uniform for i ≠ 0, i ≠ 1
                        -- Use hZ_cov_uniform: ∫ Z 0 * Z i = ∫ Z 0 * Z 1 (then use commutativity)
                        have h_swap : ∫ ω, Z i ω * Z 0 ω ∂μ = ∫ ω, Z 0 ω * Z i ω ∂μ := by
                          congr 1 with ω; ring
                        calc ∫ ω, Z i ω * Z 0 ω ∂μ
                            = ∫ ω, Z 0 ω * Z i ω ∂μ := h_swap
                          _ = ∫ ω, Z 0 ω * Z 1 ω ∂μ := hZ_cov_uniform 0 i (Ne.symm hi)
                  _ = covZ := rfl
                  _ = σSq * ρ := by
                      rw [hρ_eq]
                      -- ρ is defined as covZ / σSq, so covZ = ρ * σSq
                      show covZ = σSq * 1
                      calc covZ = ρ * σSq := by unfold ρ; field_simp [hσ_pos.ne']
                        _ = σSq * ρ := mul_comm _ _
                        _ = σSq * 1 := by rw [hρ_eq]

              calc ∫ ω, (Z i ω - Z 0 ω) ^ 2 ∂μ
                  = σSq + σSq - 2 * (σSq * ρ) := by rw [h_expand, h_var_i, h_var_0, h_cov]
                _ = 2 * σSq - 2 * σSq * ρ := by ring
                _ = 2 * σSq * (1 - ρ) := by ring
                _ = 2 * σSq * (1 - 1) := by rw [hρ_eq]
                _ = 0 := by ring

          -- From E[(Z_i - Z_0)²] = 0, derive Z_i - Z_0 = 0 a.e.
          have h_diff_sq_ae : (fun ω => (Z i ω - Z 0 ω) ^ 2) =ᵐ[μ] 0 := by
            rw [← integral_eq_zero_iff_of_nonneg_ae]
            · exact h_diff_sq
            · apply ae_of_all; intro ω; exact sq_nonneg _
            · -- (Z i - Z 0)² is bounded by (2+2)² = 16
              apply Integrable.of_bound
              · exact ((hZ_meas i).sub (hZ_meas 0)).pow_const 2 |>.aestronglyMeasurable
              · filter_upwards [] with ω
                have hZ_bdd : ∀ j ω, |Z j ω| ≤ 2 :=
                  centered_variable_bounded hX_meas f hf_meas hf_bdd m rfl Z hZ_def
                -- |(Z i - Z 0)²| ≤ |Z i - Z 0|² ≤ (|Z i| + |Z 0|)² ≤ 4² = 16
                calc |(Z i ω - Z 0 ω) ^ 2|
                    = (Z i ω - Z 0 ω) ^ 2 := abs_sq (Z i ω - Z 0 ω)
                  _ = |Z i ω - Z 0 ω| ^ 2 := by rw [← sq_abs]
                  _ ≤ (|Z i ω| + |Z 0 ω|) ^ 2 := by
                      gcongr
                      exact abs_sub (Z i ω) (Z 0 ω)
                  _ ≤ (2 + 2) ^ 2 := by
                      gcongr
                      · exact hZ_bdd i ω
                      · exact hZ_bdd 0 ω
                  _ = 16 := by norm_num

          filter_upwards [h_diff_sq_ae] with ω hω
          have : (Z i ω - Z 0 ω) ^ 2 = 0 := hω
          have : Z i ω - Z 0 ω = 0 := sq_eq_zero_iff.mp this
          linarith

        -- Step 2: Use Z_i = Z_0 a.e. to show blockAvg n and blockAvg n' are both equal to f(X 0) a.e.
        intro n n' hn_pos hn'_pos
        -- Helper: blockAvg equals f(X 0) when all Z_k = Z_0
        have hBlockAvg_eq_fX0 : ∀ m_val, m_val > 0 → ∀ᵐ ω ∂μ, blockAvg f X 0 m_val ω = f (X 0 ω) := by
          intro m_val hm_pos
          -- When Z_k = Z_0 ae for all k, we have f(X_k) = f(X_0) ae for all k
          -- So blockAvg = (1/m) * ∑ f(X_0) = f(X_0)

          -- Collect ae equalities for all indices in range m_val
          have h_ae_all : ∀ᵐ ω ∂μ, ∀ k ∈ Finset.range m_val, f (X k ω) = f (X 0 ω) := by
            -- Since Z k = f(X k) - m and Z k = Z 0 = f(X 0) - m, we have f(X k) = f(X 0)
            apply MeasureTheory.ae_all_iff.mpr
            intro k
            filter_upwards [hZi_eq_Z0 k] with ω hω
            intro _hk
            -- Z k ω = Z 0 ω means f (X k ω) - m = f (X 0 ω) - m
            linarith

          filter_upwards [h_ae_all] with ω hω
          unfold blockAvg
          -- blockAvg f X 0 m_val ω = (m_val)⁻¹ * ∑ k in range m_val, f (X (0 + k) ω)
          -- Since f (X k ω) = f (X 0 ω) for all k, this equals f (X 0 ω)
          have : (Finset.range m_val).sum (fun k => f (X (0 + k) ω)) = (Finset.range m_val).sum (fun _ => f (X 0 ω)) := by
            apply Finset.sum_congr rfl
            intro k hk
            simp only [zero_add]
            exact hω k hk
          rw [this, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          field_simp [Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hm_pos)]

        -- Both n, n' > 0, so we can use the helper
        filter_upwards [hBlockAvg_eq_fX0 n hn_pos, hBlockAvg_eq_fX0 n' hn'_pos] with ω hn_eq hn'_eq
        rw [hn_eq, hn'_eq]
      -- Trivial Cauchy: if values are ae-equal, eLpNorm of difference is 0 < ε
      use 1
      intros n n' hn_ge hn'_ge
      -- Since n ≥ 1 and n' ≥ 1, we have n > 0 and n' > 0
      have hn_pos : n > 0 := Nat.lt_of_lt_of_le Nat.one_pos hn_ge
      have hn'_pos : n' > 0 := Nat.lt_of_lt_of_le Nat.one_pos hn'_ge
      -- Convert to blockAvgFrozen and show eLpNorm = 0
      show eLpNorm (fun ω => blockAvgFrozen f X n ω - blockAvgFrozen f X n' ω) 2 μ < ε
      have h_ae : ∀ᵐ ω ∂μ, blockAvgFrozen f X n ω = blockAvgFrozen f X n' ω := by
        filter_upwards [h_ae_eq n n' hn_pos hn'_pos] with ω hω
        simp only [blockAvgFrozen_def, hω]
      have h_norm_zero : eLpNorm (fun ω => blockAvgFrozen f X n ω - blockAvgFrozen f X n' ω) 2 μ = 0 := by
        have h_ae_zero : (fun ω => blockAvgFrozen f X n ω - blockAvgFrozen f X n' ω) =ᵐ[μ] 0 := by
          filter_upwards [h_ae] with ω hω
          simp [hω]
        rw [eLpNorm_congr_ae h_ae_zero, eLpNorm_zero]
      rw [h_norm_zero]
      exact hε

  · -- Degenerate case: σSq = 0 → Z is constant a.e. → blockAvg constant a.e.
    push Not at hσ_pos
    have hσSq_zero : σSq = 0 := by
      have hσSq_nonneg : 0 ≤ σSq := by
        simp only [σSq]
        apply integral_nonneg
        intro ω
        exact sq_nonneg _
      linarith
    -- When σSq = 0, Z_0 = 0 a.e., so blockAvg values are equal a.e. (for n, n' > 0)
    have h_ae_eq : ∀ n n', n > 0 → n' > 0 → ∀ᵐ ω ∂μ, blockAvg f X 0 n ω = blockAvg f X 0 n' ω := by
      -- Step 1: Show (Z 0)² =ᵐ 0 using integral_eq_zero_iff_of_nonneg_ae
      have hZ0_sq_ae_zero : (fun ω => (Z 0 ω) ^ 2) =ᵐ[μ] 0 := by
        rw [← integral_eq_zero_iff_of_nonneg_ae]
        · exact hσSq_zero
        · -- Show (Z 0)² ≥ 0 a.e.
          apply ae_of_all
          intro ω
          exact sq_nonneg _
        · -- Show (Z 0)² is integrable: bounded by 4
          apply Integrable.of_bound
          · exact (hZ_meas 0).pow_const 2 |>.aestronglyMeasurable
          · filter_upwards [] with ω
            have hZ_bdd : ∀ j ω, |Z j ω| ≤ 2 :=
              centered_variable_bounded hX_meas f hf_meas hf_bdd m rfl Z hZ_def
            calc |(Z 0 ω) ^ 2|
                = (Z 0 ω) ^ 2 := abs_sq (Z 0 ω)
              _ = |Z 0 ω| ^ 2 := by rw [← sq_abs]
              _ ≤ 2 ^ 2 := by
                  gcongr
                  exact hZ_bdd 0 ω
              _ = 4 := by norm_num

      -- Step 2: From (Z 0)² =ᵐ 0, derive Z 0 =ᵐ 0
      have hZ0_ae_zero : Z 0 =ᵐ[μ] 0 := by
        filter_upwards [hZ0_sq_ae_zero] with ω hω
        have : (Z 0 ω) ^ 2 = 0 := hω
        exact sq_eq_zero_iff.mp this

      -- Step 3: By uniform variance and integral_eq_zero, all Z i =ᵐ 0
      have hZi_ae_zero : ∀ i, Z i =ᵐ[μ] 0 := by
        intro i
        -- ∫ (Z i)² = ∫ (Z 0)² = 0, so by same argument Z i =ᵐ 0
        have hZi_sq_integral_zero : ∫ ω, (Z i ω) ^ 2 ∂μ = 0 := by
          calc ∫ ω, (Z i ω) ^ 2 ∂μ
              = ∫ ω, (Z 0 ω) ^ 2 ∂μ := hZ_var_uniform i
            _ = σSq := rfl  -- σSq is defined as ∫ (Z 0)² via let
            _ = 0 := hσSq_zero
        have hZi_sq_ae_zero : (fun ω => (Z i ω) ^ 2) =ᵐ[μ] 0 := by
          rw [← integral_eq_zero_iff_of_nonneg_ae]
          · exact hZi_sq_integral_zero
          · apply ae_of_all; intro ω; exact sq_nonneg _
          · -- Show (Z i)² is integrable: bounded by 4
            apply Integrable.of_bound
            · exact (hZ_meas i).pow_const 2 |>.aestronglyMeasurable
            · filter_upwards [] with ω
              have hZ_bdd : ∀ j ω, |Z j ω| ≤ 2 :=
                centered_variable_bounded hX_meas f hf_meas hf_bdd m rfl Z hZ_def
              calc |(Z i ω) ^ 2|
                  = (Z i ω) ^ 2 := abs_sq (Z i ω)
                _ = |Z i ω| ^ 2 := by rw [← sq_abs]
                _ ≤ 2 ^ 2 := by
                    gcongr
                    exact hZ_bdd i ω
                _ = 4 := by norm_num
        filter_upwards [hZi_sq_ae_zero] with ω hω
        exact sq_eq_zero_iff.mp hω

      -- Step 4: Show blockAvg f X 0 n =ᵐ m for n, n' > 0
      intro n n' hn_pos hn'_pos
      have hBlockAvg_n : blockAvg f X 0 n =ᵐ[μ] (fun _ => m) := by
        -- n > 0 case: use the fact that f(X i) = m a.e.
        have h_ae_all : ∀ᵐ ω ∂μ, ∀ k < n, f (X k ω) = m := by
          apply MeasureTheory.ae_all_iff.mpr
          intro k
          have hZk_zero : Z k =ᵐ[μ] 0 := hZi_ae_zero k
          filter_upwards [hZk_zero] with ω hω
          intro _hk
          -- hω : Z k ω = 0, which means f (X k ω) - m = 0
          have : f (X k ω) - m = 0 := hω
          linarith
        filter_upwards [h_ae_all] with ω hω
        unfold blockAvg
        have : (Finset.range n).sum (fun k => f (X (0 + k) ω)) = (Finset.range n).sum (fun _ => m) := by
          apply Finset.sum_congr rfl
          intro k hk
          simp only [zero_add, Finset.mem_range] at hk ⊢
          exact hω k hk
        rw [this, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        field_simp [Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hn_pos)]

      have hBlockAvg_n' : blockAvg f X 0 n' =ᵐ[μ] (fun _ => m) := by
        have h_ae_all : ∀ᵐ ω ∂μ, ∀ k < n', f (X k ω) = m := by
          apply MeasureTheory.ae_all_iff.mpr
          intro k
          have hZk_zero : Z k =ᵐ[μ] 0 := hZi_ae_zero k
          filter_upwards [hZk_zero] with ω hω
          intro _hk
          -- hω : Z k ω = 0, which means f (X k ω) - m = 0
          have : f (X k ω) - m = 0 := hω
          linarith
        filter_upwards [h_ae_all] with ω hω
        unfold blockAvg
        have : (Finset.range n').sum (fun k => f (X (0 + k) ω)) = (Finset.range n').sum (fun _ => m) := by
          apply Finset.sum_congr rfl
          intro k hk
          simp only [zero_add, Finset.mem_range] at hk ⊢
          exact hω k hk
        rw [this, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        field_simp [Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hn'_pos)]

      -- Step 5: Combine to show blockAvg n =ᵐ blockAvg n'
      filter_upwards [hBlockAvg_n, hBlockAvg_n'] with ω hn hn'
      rw [hn, hn']
    -- Trivial Cauchy: if values are ae-equal, eLpNorm of difference is 0 < ε
    use 1
    intros n n' hn_ge hn'_ge
    -- Since n ≥ 1 and n' ≥ 1, we have n > 0 and n' > 0
    have hn_pos : n > 0 := Nat.lt_of_lt_of_le Nat.one_pos hn_ge
    have hn'_pos : n' > 0 := Nat.lt_of_lt_of_le Nat.one_pos hn'_ge
    -- Convert to blockAvgFrozen and show eLpNorm = 0
    show eLpNorm (fun ω => blockAvgFrozen f X n ω - blockAvgFrozen f X n' ω) 2 μ < ε
    have h_ae : ∀ᵐ ω ∂μ, blockAvgFrozen f X n ω = blockAvgFrozen f X n' ω := by
      filter_upwards [h_ae_eq n n' hn_pos hn'_pos] with ω hω
      simp only [blockAvgFrozen_def, hω]
    have h_norm_zero : eLpNorm (fun ω => blockAvgFrozen f X n ω - blockAvgFrozen f X n' ω) 2 μ = 0 := by
      have h_ae_zero : (fun ω => blockAvgFrozen f X n ω - blockAvgFrozen f X n' ω) =ᵐ[μ] 0 := by
        filter_upwards [h_ae] with ω hω
        simp [hω]
      rw [eLpNorm_congr_ae h_ae_zero, eLpNorm_zero]
    rw [h_norm_zero]
    exact hε

/-- **Block averages form a Cauchy sequence in L².**

Given contractable `X` and bounded `f`, the block Cesàro averages
`blockAvg f X 0 n` form a Cauchy sequence in L²(μ). The proof goes through
the L² contractability bound (no full exchangeability assumed). -/
lemma blockAvg_cauchy_in_L2
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (f : ℝ → ℝ) (hf_meas : Measurable f) (hf_bdd : ∀ x, |f x| ≤ 1) :
    ∀ ε > 0, ∃ N, ∀ {n n'}, n ≥ N → n' ≥ N →
      eLpNorm (fun ω => blockAvg f X 0 n ω - blockAvg f X 0 n' ω) 2 μ < ε :=
  blockAvgFrozen_cauchy_in_L2 hX_contract hX_meas f hf_meas hf_bdd

end Exchangeability.DeFinetti.ViaL2
