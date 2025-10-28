/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer, Claude (Anthropic)
-/
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Lp Norm Helper Lemmas

This file contains helper lemmas about Lp norms and their relationship to integrals,
suitable for contribution to mathlib. All lemmas are self-contained with minimal
dependencies.

## Main Results

* `eLpNorm_two_sq_eq_integral_sq`: For real functions in L², eLpNorm² equals integral of square
* `eLpNorm_lt_of_integral_sq_lt`: If ∫ f² < r², then eLpNorm f 2 < r
* `memLp_of_abs_le_const`: Bounded functions are in Lp on finite measures

These lemmas bridge the gap between the ENNReal-valued eLpNorm and Real-valued integrals,
which is essential for applying analysis results in probability theory.

## Notes

These results are standard in probability theory but not currently in mathlib in this
exact form. They eliminate boilerplate in proofs involving L² convergence.
-/

noncomputable section

namespace MeasureTheory

open ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ### L² Norm and Integral Relationship -/

/-- **L² norm squared equals integral of square for real functions.**

For a real-valued function f in L²(μ), the square of its L² norm equals
the integral of f²:

  (eLpNorm f 2 μ)² = ∫ f² dμ

This is a fundamental relationship used throughout probability theory, bridging
the gap between ENNReal-valued Lp norms and Real-valued integrals.

**Proof strategy**: Use the definition of eLpNorm for p = 2, which involves
lintegral of ‖f‖^2, and convert via toReal. -/
lemma eLpNorm_two_sq_eq_integral_sq
    [IsFiniteMeasure μ] {f : Ω → ℝ}
    (hf : MemLp f 2 μ) :
    (eLpNorm f 2 μ).toReal ^ 2 = ∫ ω, (f ω) ^ 2 ∂μ := by
  -- Strategy:
  -- 1. Use eLpNorm definition: eLpNorm f 2 μ = (∫⁻ ‖f‖²)^(1/2)
  -- 2. Square both sides: (eLpNorm f 2 μ)² = ∫⁻ ‖f‖²
  -- 3. Convert lintegral to integral: ∫⁻ ‖f‖² = ↑(∫ |f|²) = ↑(∫ f²)

  -- For real functions, ‖f‖² = |f|² = f²
  have h_norm_eq : ∀ ω, ‖f ω‖ ^ 2 = (f ω) ^ 2 := by
    intro ω
    rw [Real.norm_eq_abs, sq_abs]

  -- Use the fundamental relationship for p = 2
  -- eLpNorm f p μ ^ p = ∫⁻ ‖f‖^p when p ≠ 0, ∞
  rw [eLpNorm_eq_lintegral_rpow_enorm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ∞)]

  -- Simplify: ENNReal.toReal 2 = 2, so we have ((∫⁻ ‖f‖² )^(1/2)).toReal²
  simp only [ENNReal.toReal_ofNat]

  -- Main strategy: Show (∫⁻ ‖f‖²).toReal = ∫ f²
  -- Then use (a^(1/2))² = a to simplify the LHS

  -- Step 1: Rewrite LHS using ENNReal.toReal_rpow (backwards)
  -- We have ((∫⁻ ...)^(1/2)).toReal ^ 2 and want (∫⁻ ...).toReal
  conv_lhs => rw [← ENNReal.toReal_rpow]

  -- Step 2: Simplify (x^(1/2))^2 = x
  rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul ENNReal.toReal_nonneg]
  norm_num

  -- Step 3: Convert lintegral to integral for nonnegative functions
  -- Key: ‖f ω‖ₑ = ↑‖f ω‖₊ where ‖·‖₊ is the nnnorm
  -- First rewrite the lintegral in terms of ofReal
  have h_enorm_conv : ∫⁻ (x : Ω), ‖f x‖ₑ ^ 2 ∂μ = ∫⁻ (x : Ω), ENNReal.ofReal (‖f x‖ ^ 2) ∂μ := by
    congr 1
    ext ω
    -- Show ‖f ω‖ₑ ^ 2 = ENNReal.ofReal (‖f ω‖ ^ 2)
    calc ‖f ω‖ₑ ^ 2
        = (↑‖f ω‖₊ : ℝ≥0∞) ^ 2 := by rw [enorm_eq_nnnorm]
      _ = ↑(‖f ω‖₊ ^ 2) := by rw [← ENNReal.coe_pow]
      _ = ENNReal.ofReal (↑(‖f ω‖₊ ^ 2) : ℝ) := by rw [ENNReal.ofReal_coe_nnreal]
      _ = ENNReal.ofReal ((↑‖f ω‖₊ : ℝ) ^ 2) := by rw [NNReal.coe_pow]
      _ = ENNReal.ofReal (‖f ω‖ ^ 2) := by rw [coe_nnnorm]
  rw [h_enorm_conv]
  -- Now use the fundamental relationship: (∫⁻ ofReal g).toReal = ∫ g for nonnegative g
  rw [← integral_eq_lintegral_of_nonneg_ae]
  · congr 1
    ext ω
    exact h_norm_eq ω
  · -- Nonnegativity: ‖f ω‖ ^ 2 ≥ 0
    apply ae_of_all
    intro ω
    exact sq_nonneg _
  · -- AE measurability
    apply AEStronglyMeasurable.pow
    exact hf.1.norm

/-- **L² norm bound from integral bound.**

If the integral of f² is less than r², then the L² norm of f is less than r.
This is the standard way to convert integral bounds to Lp norm bounds.

**Application**: Used when we have ∫ f² < ε² and want eLpNorm f 2 < ε. -/
lemma eLpNorm_lt_of_integral_sq_lt
    [IsFiniteMeasure μ] {f : Ω → ℝ} {r : ℝ}
    (hf : MemLp f 2 μ) (hr : 0 < r)
    (h : ∫ ω, (f ω) ^ 2 ∂μ < r ^ 2) :
    eLpNorm f 2 μ < ENNReal.ofReal r := by
  -- Strategy: Use eLpNorm² = ∫ f² and take square roots
  -- eLpNorm f 2 μ < r  ⟺  (eLpNorm f 2 μ)² < r²  ⟺  ∫ f² < r²

  have h_eq : (eLpNorm f 2 μ).toReal ^ 2 = ∫ ω, (f ω) ^ 2 ∂μ :=
    eLpNorm_two_sq_eq_integral_sq hf

  -- From ∫ f² < r², get (eLpNorm f 2 μ).toReal² < r²
  have h_toReal_sq_lt : (eLpNorm f 2 μ).toReal ^ 2 < r ^ 2 := by
    rw [h_eq]; exact h

  -- Take square roots: (eLpNorm f 2 μ).toReal < r
  have h_toReal_lt : (eLpNorm f 2 μ).toReal < r := by
    -- Use abs_lt_of_sq_lt_sq: x² < r² and 0 ≤ r → |x| < r
    have := abs_lt_of_sq_lt_sq h_toReal_sq_lt (le_of_lt hr)
    rwa [abs_of_nonneg ENNReal.toReal_nonneg] at this

  -- Convert back to ENNReal
  -- Use that eLpNorm f 2 μ < ∞ (since f ∈ MemLp), so toReal is order-preserving
  have h_lt_top : eLpNorm f 2 μ < ∞ := hf.2
  rw [← ENNReal.ofReal_toReal (ne_of_lt h_lt_top)]
  exact ENNReal.ofReal_lt_ofReal_iff hr |>.mpr h_toReal_lt

/-! ### Membership in Lp Spaces -/

/-- **Functions bounded by a constant are in Lp.**

If |f| ≤ M almost everywhere, then f ∈ Lp for any p ∈ [1, ∞) on a finite measure space.

This is a standard result used to show block averages of bounded functions are in L². -/
lemma memLp_of_abs_le_const
    [IsFiniteMeasure μ] {f : Ω → ℝ} {M : ℝ}
    (hf_meas : Measurable f)
    (hf_bdd : ∀ᵐ ω ∂μ, |f ω| ≤ M)
    (p : ℝ≥0∞) (_ : 1 ≤ p) (_ : p ≠ ∞) :
    MemLp f p μ := by
  -- Use MemLp.of_bound from mathlib
  apply MemLp.of_bound hf_meas.aestronglyMeasurable M
  apply Filter.Eventually.mono hf_bdd
  intro ω hω
  exact (Real.norm_eq_abs _).le.trans hω

/-- **Block average of bounded function is in L².**

Special case: If f is bounded by M, then f is in L² on a probability space.
This is used repeatedly in Cesàro convergence proofs. -/
lemma memLp_two_of_bounded
    [IsProbabilityMeasure μ] {f : Ω → ℝ} {M : ℝ}
    (hf_meas : Measurable f)
    (hf_bdd : ∀ ω, |f ω| ≤ M) :
    MemLp f 2 μ := by
  apply memLp_of_abs_le_const (M := M) hf_meas
  · filter_upwards []
    exact hf_bdd
  · norm_num
  · norm_num

end MeasureTheory

