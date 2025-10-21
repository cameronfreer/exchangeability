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
    (hf_meas : ∀ n, Measurable (f n)) (hg_meas : Measurable g)
    (hf_bdd : ∃ M, ∀ n ω, |f n ω| ≤ M)
    (hL2 : Tendsto (fun n => ∫ ω, (f n ω - g ω)^2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, |f n ω - g ω| ∂μ) atTop (𝓝 0) := by
  -- **Proof strategy:** On probability spaces, Hölder inequality gives:
  --   ∫|f - g| ≤ (∫(f-g)²)^(1/2)
  --
  -- Key steps:
  -- 1. Apply `eLpNorm_le_eLpNorm_mul_rpow_measure_univ` with p=1, q=2
  -- 2. On probability spaces: eLpNorm f 1 ≤ eLpNorm f 2 (using μ(Ω) = 1)
  -- 3. Convert: ∫|f| = (eLpNorm f 1).toReal and (∫f²)^(1/2) = (eLpNorm f 2).toReal
  -- 4. Use lintegral_rpow_enorm_eq_rpow_eLpNorm' to connect eLpNorm 2 to integral
  -- 5. Apply squeeze theorem: 0 ≤ ∫|f n - g| ≤ (∫(f n - g)²)^(1/2) → 0
  --
  -- **Technical details:**
  -- - Need to convert between ‖·‖ (norm) and |·| (abs) for real numbers
  -- - Need to show eLpNorm f 2 < ∞ using finiteness of ∫f² from hL2
  -- - Need ofReal_integral_eq_lintegral_ofReal for connecting lintegral to integral
  --
  -- This is a standard argument, see reference proof in CesaroToCondExp.lean:225-287
  sorry

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

/-- **Integral of continuous function under pushforward.**

For measurable f and continuous g:
  ∫ x, g x d(f₊μ) = ∫ ω, g (f ω) dμ -/
lemma integral_pushforward_continuous
    {μ : Measure Ω} {f : Ω → ℝ} {g : ℝ → ℝ}
    (hf : Measurable f) (hg : Continuous g) :
    ∫ x, g x ∂(Measure.map f μ) = ∫ ω, g (f ω) ∂μ := by
  rw [integral_map hf.aemeasurable]
  exact hg.aestronglyMeasurable

end Exchangeability.Probability.IntegrationHelpers
