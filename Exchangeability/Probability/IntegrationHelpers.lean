/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Integration Helper Lemmas

Convenience wrappers around mathlib's integration theory, providing specialized
lemmas for common patterns in the de Finetti proofs.

## Main Results

* `abs_integral_mul_le_L2`: Cauchy-Schwarz inequality for L² functions
* `eLpNorm_one_eq_integral_abs`: Connection between L¹ integral and eLpNorm
* `L2_tendsto_implies_L1_tendsto_of_bounded`: L² → L¹ convergence for bounded functions
* `integral_pushforward_id`: Integral of identity under pushforward measure
* `integral_pushforward_sq_diff`: Integral of squared difference under pushforward

These lemmas eliminate boilerplate by wrapping mathlib's general theorems.

## Implementation Notes

The file has no project dependencies - imports only mathlib.
-/

noncomputable section

namespace Exchangeability.Probability.IntegrationHelpers

open MeasureTheory Filter Topology

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Cauchy-Schwarz Inequality -/

omit [MeasurableSpace Ω] in
/-- **Cauchy-Schwarz inequality for L² real-valued functions.**

For integrable functions f, g in L²(μ):
  |∫ f·g dμ| ≤ (∫ f² dμ)^(1/2) · (∫ g² dμ)^(1/2)

This is Hölder's inequality specialized to p = q = 2. We derive it from the
nonnegative version by observing that |∫ f·g| ≤ ∫ |f|·|g| and |f|² = f². -/
@[nolint unusedArguments]
lemma abs_integral_mul_le_L2
    [IsFiniteMeasure μ] {f g : Ω → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |∫ ω, f ω * g ω ∂μ|
      ≤ (∫ ω, (f ω) ^ 2 ∂μ) ^ (1/2 : ℝ) * (∫ ω, (g ω) ^ 2 ∂μ) ^ (1/2 : ℝ) := by
  -- Reduce to nonnegative case using |f·g| = |f|·|g| and |f|² = f²
  have hf_abs : MemLp (fun ω => |f ω|) (ENNReal.ofReal 2) μ := by
    convert hf.abs; norm_num
  have hg_abs : MemLp (fun ω => |g ω|) (ENNReal.ofReal 2) μ := by
    convert hg.abs; norm_num
  have h_conj : (2 : ℝ).HolderConjugate 2 := by
    constructor <;> norm_num
  calc |∫ ω, f ω * g ω ∂μ|
      ≤ ∫ ω, |f ω * g ω| ∂μ := by
        have : |∫ ω, f ω * g ω ∂μ| = ‖∫ ω, f ω * g ω ∂μ‖ := Real.norm_eq_abs _
        rw [this]; exact norm_integral_le_integral_norm _
    _ = ∫ ω, |f ω| * |g ω| ∂μ := by
        congr 1 with ω; exact abs_mul (f ω) (g ω)
    _ ≤ (∫ ω, |f ω| ^ 2 ∂μ) ^ (1/2 : ℝ) * (∫ ω, |g ω| ^ 2 ∂μ) ^ (1/2 : ℝ) := by
        convert integral_mul_le_Lp_mul_Lq_of_nonneg h_conj ?_ ?_ hf_abs hg_abs using 2 <;> norm_num
        · apply ae_of_all; intro; positivity
        · apply ae_of_all; intro; positivity
    _ = (∫ ω, (f ω) ^ 2 ∂μ) ^ (1/2 : ℝ) * (∫ ω, (g ω) ^ 2 ∂μ) ^ (1/2 : ℝ) := by
        simp only [sq_abs]

/-! ### Lp Norm Connections and Convergence -/

/-- **Connection between L¹ Bochner integral and eLpNorm.**

For integrable real-valued functions, the L¹ norm (eLpNorm with p=1) equals
the ENNReal coercion of the integral of absolute value.

This bridges the gap between Real-valued integrals (∫ |f| ∂μ : ℝ) and
ENNReal-valued Lp norms (eLpNorm f 1 μ : ℝ≥0∞), which is essential for
applying mathlib's convergence in measure machinery. -/
@[nolint unusedArguments]
lemma eLpNorm_one_eq_integral_abs
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {f : Ω → ℝ} (hf : Integrable f μ) :
    eLpNorm f 1 μ = ENNReal.ofReal (∫ ω, |f ω| ∂μ) := by
  simp only [eLpNorm_one_eq_lintegral_enorm, ← ofReal_integral_norm_eq_lintegral_enorm hf,
    Real.norm_eq_abs]

/-- **L² convergence implies L¹ convergence for uniformly bounded functions.**

On a probability space, if fₙ → g in L² and the functions are uniformly bounded,
then fₙ → g in L¹.

This follows from Cauchy-Schwarz: ∫|f - g| ≤ (∫(f-g)²)^(1/2) · (∫ 1)^(1/2) = (∫(f-g)²)^(1/2)

This lemma provides the key bridge between the Mean Ergodic Theorem (which gives
L² convergence) and applications requiring L¹ convergence (such as ViaL2's
Cesàro average convergence). -/
lemma L2_tendsto_implies_L1_tendsto_of_bounded
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (f : ℕ → Ω → ℝ) (g : Ω → ℝ)
    (hf_meas : ∀ n, Measurable (f n))
    (hf_bdd : ∃ M, ∀ n ω, |f n ω| ≤ M)
    (hg_memLp : MemLp g 2 μ)  -- Explicit hypothesis: g ∈ L² (implied by L² convergence)
    (hL2 : Tendsto (fun n => ∫ ω, (f n ω - g ω)^2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, |f n ω - g ω| ∂μ) atTop (𝓝 0) := by
  -- Strategy: Use Cauchy-Schwarz to bound L¹ by L² on probability spaces
  -- ∫|f-g| ≤ (∫(f-g)²)^(1/2) · (∫ 1)^(1/2) = (∫(f-g)²)^(1/2)
  -- Apply squeeze theorem: 0 ≤ ∫|f-g| ≤ (∫(f-g)²)^(1/2) → 0

  -- Step 1: Get convergence of the square root
  have hL2_sqrt : Tendsto (fun n => (∫ ω, (f n ω - g ω)^2 ∂μ) ^ (1/2 : ℝ)) atTop (𝓝 0) := by
    have : (0 : ℝ) ^ (1/2 : ℝ) = 0 := by norm_num
    rw [← this]
    exact Tendsto.rpow hL2 tendsto_const_nhds (Or.inr (by norm_num : 0 < (1/2 : ℝ)))

  -- Step 2: Bound ∫|f-g| by (∫(f-g)²)^(1/2) using Cauchy-Schwarz
  have hbound : ∀ n, ∫ ω, |f n ω - g ω| ∂μ ≤ (∫ ω, (f n ω - g ω)^2 ∂μ) ^ (1/2 : ℝ) := by
    intro n
    -- Use Cauchy-Schwarz: ∫|h| = ∫(|h|·1) ≤ (∫|h|²)^(1/2) · (∫1²)^(1/2) = (∫h²)^(1/2) on probability spaces

    -- Apply abs_integral_mul_le_L2 with f = f n - g and g = 1
    have h_memLp : MemLp (fun ω => f n ω - g ω) 2 μ := by
      -- f_n ∈ L² (bounded on finite measure) and g ∈ L² (hypothesis)
      -- → f_n - g ∈ L²
      obtain ⟨M, hM⟩ := hf_bdd
      have hf_memLp : MemLp (f n) 2 μ := by
        apply MemLp.of_bound (hf_meas n).aestronglyMeasurable M
        exact ae_of_all μ (fun ω => (Real.norm_eq_abs _).le.trans (hM n ω))
      exact hf_memLp.sub hg_memLp

    have one_memLp : MemLp (fun ω => (1 : ℝ)) 2 μ := by
      refine memLp_const 1

    -- We'll apply cs to |f n - g| and 1, but cs is for general f, g
    -- So we need a version where we plug in |f n - g| for the first argument
    have h_abs_memLp : MemLp (fun ω => |f n ω - g ω|) 2 μ := by
      convert h_memLp.abs using 1

    have cs_abs := abs_integral_mul_le_L2 h_abs_memLp one_memLp

    -- Simplify: ∫|h|·1 = ∫|h|, and |h|² = h², and ∫1² = 1 on probability spaces
    calc ∫ ω, |f n ω - g ω| ∂μ
        = ∫ ω, |f n ω - g ω| * 1 ∂μ := by simp only [mul_one]
      _ = |∫ ω, |f n ω - g ω| * 1 ∂μ| := by
          symm; exact abs_of_nonneg (integral_nonneg (fun ω => by positivity))
      _ ≤ (∫ ω, (|f n ω - g ω|) ^ 2 ∂μ) ^ (1/2 : ℝ) * (∫ ω, (1 : ℝ) ^ 2 ∂μ) ^ (1/2 : ℝ) := cs_abs
      _ = (∫ ω, (f n ω - g ω) ^ 2 ∂μ) ^ (1/2 : ℝ) * (∫ ω, (1 : ℝ) ^ 2 ∂μ) ^ (1/2 : ℝ) := by
          congr 1
          apply congr_arg (· ^ (1/2 : ℝ))
          apply integral_congr_ae
          filter_upwards with ω
          exact sq_abs _
      _ = (∫ ω, (f n ω - g ω) ^ 2 ∂μ) ^ (1/2 : ℝ) * 1 := by
          congr 2
          -- Show (∫ 1² ∂μ)^(1/2) = 1 for probability measure
          have : ∫ ω, (1 : ℝ) ^ 2 ∂μ = 1 := by
            simp only [one_pow, integral_const, smul_eq_mul, mul_one]
            rw [Measure.real]
            simp [measure_univ]
          rw [this]
          norm_num
      _ = (∫ ω, (f n ω - g ω) ^ 2 ∂μ) ^ (1/2 : ℝ) := by ring

  -- Step 3: Apply squeeze theorem
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hL2_sqrt ?_ ?_
  · exact Filter.Eventually.of_forall fun n => integral_nonneg (fun ω => abs_nonneg _)
  · exact Filter.Eventually.of_forall hbound

/-! ### Pushforward Measure Integrals -/

/-- **Integral of identity function under pushforward measure.**

For measurable f:  ∫ x, x d(f₊μ) = ∫ ω, f ω dμ

Eliminates boilerplate of proving `AEStronglyMeasurable id`. -/
lemma integral_pushforward_id
    {μ : Measure Ω} {f : Ω → ℝ} (hf : Measurable f) :
    ∫ x, x ∂(Measure.map f μ) = ∫ ω, f ω ∂μ :=
  integral_map hf.aemeasurable aestronglyMeasurable_id

/-- **Integral of squared difference under pushforward measure.**

For measurable f and constant c:
  ∫ x, (x - c)² d(f₊μ) = ∫ ω, (f ω - c)² dμ -/
lemma integral_pushforward_sq_diff
    {μ : Measure Ω} {f : Ω → ℝ} (hf : Measurable f) (c : ℝ) :
    ∫ x, (x - c) ^ 2 ∂(Measure.map f μ) = ∫ ω, (f ω - c) ^ 2 ∂μ := by
  rw [integral_map hf.aemeasurable]
  exact (continuous_id.sub continuous_const).pow 2 |>.aestronglyMeasurable

end Exchangeability.Probability.IntegrationHelpers
