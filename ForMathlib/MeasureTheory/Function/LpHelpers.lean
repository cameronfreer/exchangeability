/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Lp Norm Helper Lemmas

This file contains helper lemmas about Lp norms and their relationship to integrals,
suitable for contribution to mathlib.

## Main Results

### L² Norm and Integral Relationship
* `eLpNorm_two_sq_eq_integral_sq`: For real functions in L², eLpNorm² equals integral of square
* `eLpNorm_lt_of_integral_sq_lt`: If ∫ f² < r², then eLpNorm f 2 < r

### Membership in Lp Spaces
* `memLp_of_abs_le_const`: Bounded functions are in Lp on finite measures
* `memLp_two_of_bounded`: Bounded functions are in L² on probability spaces

### L² Inner Product Bounds
* `setIntegral_le_eLpNorm_mul_measure`: |∫_A g| ≤ ‖g‖₂ · √(μ A) (Cauchy-Schwarz)

### Cauchy-Schwarz and Convergence
* `abs_integral_mul_le_L2`: Cauchy-Schwarz inequality for L² real-valued functions
* `L2_tendsto_implies_L1_tendsto_of_bounded`: L² → L¹ convergence for bounded functions

These lemmas bridge the gap between the ENNReal-valued eLpNorm and Real-valued integrals,
which is essential for applying analysis results in probability theory.

## Suggested Mathlib Location

`Mathlib.MeasureTheory.Function.L2Space` or `Mathlib.MeasureTheory.Function.LpSeminorm.Basic`

## References

* Kallenberg (2005), *Probabilistic Symmetries and Invariance Principles*
* Williams (1991), *Probability with Martingales*
-/

noncomputable section

namespace MeasureTheory

open ENNReal Filter Topology

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ### L² Norm and Integral Relationship -/

/-- **L² norm squared equals integral of square for real functions.**

For a real-valued function f in L²(μ), the square of its L² norm equals
the integral of f²:

  (eLpNorm f 2 μ)² = ∫ f² dμ

This is a fundamental relationship used throughout probability theory, bridging
the gap between ENNReal-valued Lp norms and Real-valued integrals. -/
lemma eLpNorm_two_sq_eq_integral_sq [IsFiniteMeasure μ] {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    (eLpNorm f 2 μ).toReal ^ 2 = ∫ ω, (f ω) ^ 2 ∂μ := by
  have h_norm_eq : ∀ ω, ‖f ω‖ ^ 2 = (f ω) ^ 2 := fun ω => by rw [Real.norm_eq_abs, sq_abs]
  rw [eLpNorm_eq_lintegral_rpow_enorm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ∞)]
  simp only [ENNReal.toReal_ofNat]
  conv_lhs => rw [← ENNReal.toReal_rpow]
  rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul ENNReal.toReal_nonneg]
  norm_num
  have h_enorm_conv : ∫⁻ (x : Ω), ‖f x‖ₑ ^ 2 ∂μ = ∫⁻ (x : Ω), ENNReal.ofReal (‖f x‖ ^ 2) ∂μ := by
    congr 1; ext ω
    calc ‖f ω‖ₑ ^ 2
        = (↑‖f ω‖₊ : ℝ≥0∞) ^ 2 := by rw [enorm_eq_nnnorm]
      _ = ↑(‖f ω‖₊ ^ 2) := by rw [← ENNReal.coe_pow]
      _ = ENNReal.ofReal (↑(‖f ω‖₊ ^ 2) : ℝ) := by rw [ENNReal.ofReal_coe_nnreal]
      _ = ENNReal.ofReal ((↑‖f ω‖₊ : ℝ) ^ 2) := by rw [NNReal.coe_pow]
      _ = ENNReal.ofReal (‖f ω‖ ^ 2) := by rw [coe_nnnorm]
  rw [h_enorm_conv, ← integral_eq_lintegral_of_nonneg_ae]
  · congr 1; ext ω; exact h_norm_eq ω
  · exact ae_of_all _ fun _ => sq_nonneg _
  · exact (AEStronglyMeasurable.pow hf.1.norm 2).congr (ae_of_all _ fun _ => rfl)

/-- **L² norm bound from integral bound.**

If the integral of f² is less than r², then the L² norm of f is less than r. -/
lemma eLpNorm_lt_of_integral_sq_lt [IsFiniteMeasure μ] {f : Ω → ℝ} {r : ℝ} (hf : MemLp f 2 μ)
    (hr : 0 < r) (h : ∫ ω, (f ω) ^ 2 ∂μ < r ^ 2) : eLpNorm f 2 μ < ENNReal.ofReal r := by
  have h_eq : (eLpNorm f 2 μ).toReal ^ 2 = ∫ ω, (f ω) ^ 2 ∂μ := eLpNorm_two_sq_eq_integral_sq hf
  have h_toReal_sq_lt : (eLpNorm f 2 μ).toReal ^ 2 < r ^ 2 := by rw [h_eq]; exact h
  have h_toReal_lt : (eLpNorm f 2 μ).toReal < r := by
    have := abs_lt_of_sq_lt_sq h_toReal_sq_lt (le_of_lt hr)
    rwa [abs_of_nonneg ENNReal.toReal_nonneg] at this
  have h_lt_top : eLpNorm f 2 μ < ∞ := hf.2
  rw [← ENNReal.ofReal_toReal (ne_of_lt h_lt_top)]
  exact ENNReal.ofReal_lt_ofReal_iff hr |>.mpr h_toReal_lt

/-! ### Membership in Lp Spaces -/

/-- **Functions bounded by a constant are in Lp.**

If |f| ≤ M almost everywhere, then f ∈ Lp for any p ∈ [1, ∞) on a finite measure space. -/
lemma memLp_of_abs_le_const [IsFiniteMeasure μ] {f : Ω → ℝ} {M : ℝ} (hf_meas : Measurable f)
    (hf_bdd : ∀ᵐ ω ∂μ, |f ω| ≤ M) (p : ℝ≥0∞) : MemLp f p μ :=
  MemLp.of_bound hf_meas.aestronglyMeasurable M
    (hf_bdd.mono fun _ hω => (Real.norm_eq_abs _).le.trans hω)

/-- **Block average of bounded function is in L².**

Special case: If f is bounded by M, then f is in L² on a probability space. -/
lemma memLp_two_of_bounded [IsProbabilityMeasure μ] {f : Ω → ℝ} {M : ℝ} (hf_meas : Measurable f)
    (hf_bdd : ∀ ω, |f ω| ≤ M) : MemLp f 2 μ :=
  memLp_of_abs_le_const hf_meas (ae_of_all μ hf_bdd) 2

/-! ### L² Inner Product Bounds -/

/-- **Cauchy-Schwarz on set integrals (probability measure).**

For a set A and function g ∈ L²(μ), the absolute value of ∫_A g is bounded
by the L² norm of g times √(μ A).

On probability spaces with μ A ≤ 1, this simplifies to |∫_A g| ≤ ‖g‖₂. -/
lemma setIntegral_le_eLpNorm_mul_measure [IsProbabilityMeasure μ] (A : Set Ω)
    (hA : MeasurableSet A) {g : Ω → ℝ} (hg : MemLp g 2 μ) :
    |∫ x in A, g x ∂μ| ≤ (eLpNorm g 2 μ).toReal * (μ A).toReal ^ (1/2 : ℝ) := by
  have hμA : μ A ≠ ∞ := (measure_lt_top μ A).ne
  let g_Lp : Lp ℝ 2 μ := hg.toLp g
  let indicator_Lp := indicatorConstLp 2 hA hμA (1 : ℝ)
  have h_inner : ∫ x in A, g x ∂μ = @inner ℝ (Lp ℝ 2 μ) _ indicator_Lp g_Lp := by
    rw [L2.inner_indicatorConstLp_one hA hμA g_Lp]
    exact setIntegral_congr_ae hA (hg.coeFn_toLp.mono fun x hx _ => hx.symm)
  have h_norm_g : ‖g_Lp‖ = (eLpNorm g 2 μ).toReal := Lp.norm_toLp g hg
  have h_norm_ind : ‖indicator_Lp‖ = (μ A).toReal ^ (1/2 : ℝ) := by
    rw [norm_indicatorConstLp (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞)]
    simp only [norm_one, one_mul, ENNReal.toReal_ofNat, one_div, measureReal_def]
  calc |∫ x in A, g x ∂μ|
      = |@inner ℝ (Lp ℝ 2 μ) _ indicator_Lp g_Lp| := by rw [h_inner]
    _ ≤ ‖indicator_Lp‖ * ‖g_Lp‖ := abs_real_inner_le_norm _ _
    _ = (μ A).toReal ^ (1/2 : ℝ) * (eLpNorm g 2 μ).toReal := by rw [h_norm_ind, h_norm_g]
    _ = (eLpNorm g 2 μ).toReal * (μ A).toReal ^ (1/2 : ℝ) := mul_comm _ _

/-! ### Cauchy-Schwarz Inequality -/

/-- **Cauchy-Schwarz inequality for L² real-valued functions.**

For integrable functions f, g in L²(μ):
  |∫ f·g dμ| ≤ (∫ f² dμ)^(1/2) · (∫ g² dμ)^(1/2) -/
lemma abs_integral_mul_le_L2 [IsFiniteMeasure μ] {f g : Ω → ℝ} (hf : MemLp f 2 μ)
    (hg : MemLp g 2 μ) : |∫ ω, f ω * g ω ∂μ|
      ≤ (∫ ω, (f ω) ^ 2 ∂μ) ^ (1/2 : ℝ) * (∫ ω, (g ω) ^ 2 ∂μ) ^ (1/2 : ℝ) := by
  have hf_abs : MemLp (fun ω => |f ω|) (ENNReal.ofReal 2) μ := by convert hf.abs; norm_num
  have hg_abs : MemLp (fun ω => |g ω|) (ENNReal.ofReal 2) μ := by convert hg.abs; norm_num
  have h_conj : (2 : ℝ).HolderConjugate 2 := by constructor <;> norm_num
  calc |∫ ω, f ω * g ω ∂μ|
      ≤ ∫ ω, |f ω * g ω| ∂μ := by
        have : |∫ ω, f ω * g ω ∂μ| = ‖∫ ω, f ω * g ω ∂μ‖ := Real.norm_eq_abs _
        rw [this]; exact norm_integral_le_integral_norm _
    _ = ∫ ω, |f ω| * |g ω| ∂μ := by congr 1 with ω; exact abs_mul (f ω) (g ω)
    _ ≤ (∫ ω, |f ω| ^ 2 ∂μ) ^ (1/2 : ℝ) * (∫ ω, |g ω| ^ 2 ∂μ) ^ (1/2 : ℝ) := by
        convert integral_mul_le_Lp_mul_Lq_of_nonneg h_conj ?_ ?_ hf_abs hg_abs using 2 <;> norm_num
        · apply ae_of_all; intro; positivity
        · apply ae_of_all; intro; positivity
    _ = (∫ ω, (f ω) ^ 2 ∂μ) ^ (1/2 : ℝ) * (∫ ω, (g ω) ^ 2 ∂μ) ^ (1/2 : ℝ) := by simp only [sq_abs]

/-! ### L² to L¹ Convergence -/

/-- **L² convergence implies L¹ convergence for uniformly bounded functions.**

On a probability space, if fₙ → g in L² and the functions are uniformly bounded,
then fₙ → g in L¹.

This follows from Cauchy-Schwarz: ∫|f - g| ≤ (∫(f-g)²)^(1/2) · (∫ 1)^(1/2) = (∫(f-g)²)^(1/2) -/
lemma L2_tendsto_implies_L1_tendsto_of_bounded [IsProbabilityMeasure μ] (f : ℕ → Ω → ℝ)
    (g : Ω → ℝ) (hf_meas : ∀ n, Measurable (f n)) (hf_bdd : ∃ M, ∀ n ω, |f n ω| ≤ M)
    (hg_memLp : MemLp g 2 μ) (hL2 : Tendsto (fun n => ∫ ω, (f n ω - g ω)^2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, |f n ω - g ω| ∂μ) atTop (𝓝 0) := by
  have hL2_sqrt : Tendsto (fun n => (∫ ω, (f n ω - g ω)^2 ∂μ) ^ (1/2 : ℝ)) atTop (𝓝 0) := by
    have : (0 : ℝ) ^ (1/2 : ℝ) = 0 := by norm_num
    rw [← this]
    exact Tendsto.rpow hL2 tendsto_const_nhds (Or.inr (by norm_num : 0 < (1/2 : ℝ)))
  have hbound : ∀ n, ∫ ω, |f n ω - g ω| ∂μ ≤ (∫ ω, (f n ω - g ω)^2 ∂μ) ^ (1/2 : ℝ) := by
    intro n
    have h_memLp : MemLp (fun ω => f n ω - g ω) 2 μ := by
      obtain ⟨M, hM⟩ := hf_bdd
      have hf_memLp : MemLp (f n) 2 μ := MemLp.of_bound (hf_meas n).aestronglyMeasurable M
        (ae_of_all μ (fun ω => (Real.norm_eq_abs _).le.trans (hM n ω)))
      exact hf_memLp.sub hg_memLp
    have one_memLp : MemLp (fun _ => (1 : ℝ)) 2 μ := memLp_const 1
    have h_abs_memLp : MemLp (fun ω => |f n ω - g ω|) 2 μ := by convert h_memLp.abs using 1
    have cs_abs := abs_integral_mul_le_L2 h_abs_memLp one_memLp
    calc ∫ ω, |f n ω - g ω| ∂μ
        = ∫ ω, |f n ω - g ω| * 1 ∂μ := by simp only [mul_one]
      _ = |∫ ω, |f n ω - g ω| * 1 ∂μ| := by
          symm; exact abs_of_nonneg (integral_nonneg (fun ω => by positivity))
      _ ≤ (∫ ω, (|f n ω - g ω|) ^ 2 ∂μ) ^ (1/2 : ℝ) * (∫ ω, (1 : ℝ) ^ 2 ∂μ) ^ (1/2 : ℝ) := cs_abs
      _ = (∫ ω, (f n ω - g ω) ^ 2 ∂μ) ^ (1/2 : ℝ) * (∫ ω, (1 : ℝ) ^ 2 ∂μ) ^ (1/2 : ℝ) := by
          congr 1; apply congr_arg (· ^ (1/2 : ℝ))
          exact integral_congr_ae (ae_of_all _ fun _ => sq_abs _)
      _ = (∫ ω, (f n ω - g ω) ^ 2 ∂μ) ^ (1/2 : ℝ) * 1 := by
          congr 2
          have : ∫ ω, (1 : ℝ) ^ 2 ∂μ = 1 := by
            simp only [one_pow, integral_const, smul_eq_mul, mul_one, Measure.real]
            simp [measure_univ]
          rw [this]; norm_num
      _ = (∫ ω, (f n ω - g ω) ^ 2 ∂μ) ^ (1/2 : ℝ) := by ring
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hL2_sqrt
    (Eventually.of_forall fun n => integral_nonneg fun _ => abs_nonneg _)
    (Eventually.of_forall hbound)

/-! ### Pushforward Measure Integrals -/

/-- **Integral of identity function under pushforward measure.**

For measurable f:  ∫ x, x d(f₊μ) = ∫ ω, f ω dμ -/
lemma integral_pushforward_id {f : Ω → ℝ} (hf : Measurable f) :
    ∫ x, x ∂(Measure.map f μ) = ∫ ω, f ω ∂μ :=
  integral_map hf.aemeasurable aestronglyMeasurable_id

/-- **Integral of squared difference under pushforward measure.**

For measurable f and constant c:
  ∫ x, (x - c)² d(f₊μ) = ∫ ω, (f ω - c)² dμ -/
lemma integral_pushforward_sq_diff {f : Ω → ℝ} (hf : Measurable f) (c : ℝ) :
    ∫ x, (x - c) ^ 2 ∂(Measure.map f μ) = ∫ ω, (f ω - c) ^ 2 ∂μ := by
  rw [integral_map hf.aemeasurable]
  exact (continuous_id.sub continuous_const).pow 2 |>.aestronglyMeasurable

/-- **Integral of continuous function under pushforward.**

For measurable f and continuous g:
  ∫ x, g x d(f₊μ) = ∫ ω, g (f ω) dμ -/
lemma integral_pushforward_continuous {f : Ω → ℝ} {g : ℝ → ℝ}
    (hf : Measurable f) (hg : Continuous g) :
    ∫ x, g x ∂(Measure.map f μ) = ∫ ω, g (f ω) ∂μ := by
  rw [integral_map hf.aemeasurable]
  exact hg.aestronglyMeasurable

end MeasureTheory
