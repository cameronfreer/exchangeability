/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# Conditional Expectation and Lp Helper Lemmas

This file contains utility lemmas for conditional expectation and Lp norm manipulation.

## Main Definitions

None - this file only contains helper lemmas.

## Main Results

* `condExp_const_mul`: Scalar linearity of conditional expectation
* `condExp_sum_finset`: Finite sum linearity of conditional expectation
* `integrable_of_bounded_measurable`: Bounded measurable functions are integrable on finite measure spaces
* `eLpNorm_one_le_eLpNorm_two_toReal`: L¹ norm bounded by L² norm on probability spaces
-/

open MeasureTheory Filter
open scoped Topology

noncomputable section

/-! ### Lp norm placeholder -/

/-! ### Lp seminorm: use mathlib's `eLpNorm` -/

/-! ### Conditional expectation linearity helpers -/

/-- Scalar linearity of conditional expectation.
**Mathematical content**: CE[c·f| mSI] = c·CE[f| mSI]
**Mathlib source**: `MeasureTheory.condexp_smul` for scalar multiplication. -/
lemma condExp_const_mul
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {m : MeasurableSpace Ω} (_hm : m ≤ mΩ)
    (c : ℝ) (f : Ω → ℝ) :
    μ[(fun ω => c * f ω) | m] =ᵐ[μ] (fun ω => c * μ[f | m] ω) := by
  -- `condExp_smul` in mathlib takes m as explicit positional parameter
  simpa [Pi.mul_apply, smul_eq_mul] using
    (MeasureTheory.condExp_smul c f m)

/-- Finite sum linearity of conditional expectation.
**Mathematical content**: CE[Σᵢfᵢ| mSI] = ΣᵢCE[fᵢ| mSI]
**Mathlib source**: Direct application of `MeasureTheory.condExp_finset_sum`.
NOTE: Uses η-expansion to work around notation elaboration issues with `∑ i ∈ s, f i` vs `fun ω => ∑ i ∈ s, f i ω`. -/
lemma condExp_sum_finset
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {m : MeasurableSpace Ω} (_hm : m ≤ mΩ)
    {ι : Type*} (s : Finset ι) (f : ι → Ω → ℝ)
    (hint : ∀ i ∈ s, Integrable (f i) μ) :
    μ[(fun ω => s.sum (fun i => f i ω)) | m]
      =ᵐ[μ] (fun ω => s.sum (fun i => μ[f i | m] ω)) := by
  classical
  -- Rewrite using η-reduction: (fun ω => ∑ i ∈ s, f i ω) = ∑ i ∈ s, f i
  have h_sum_eta : (fun ω => ∑ i ∈ s, f i ω) = ∑ i ∈ s, f i := by
    funext ω
    simp only [Finset.sum_apply]
  have h_ce_sum_eta : (fun ω => ∑ i ∈ s, μ[f i | m] ω) = ∑ i ∈ s, μ[f i | m] := by
    funext ω
    simp only [Finset.sum_apply]
  -- Rewrite goal using η-reduction
  rw [h_sum_eta, h_ce_sum_eta]
  -- Apply condExp_finset_sum
  exact condExp_finset_sum hint m

/-- On a finite measure space, a bounded measurable real function is integrable. -/
lemma integrable_of_bounded_measurable
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {f : Ω → ℝ} (hf_meas : Measurable f) (C : ℝ) (hf_bd : ∀ ω, |f ω| ≤ C) :
    Integrable f μ :=
  ⟨hf_meas.aestronglyMeasurable, HasFiniteIntegral.of_bounded (by
    filter_upwards with ω; simpa [Real.norm_eq_abs] using hf_bd ω)⟩

/-- On a probability space, `‖f‖₁ ≤ ‖f‖₂`. Version with real integral on the left.
We assume `MemLp f 2 μ` so the right-hand side is finite; this matches all uses below
where the function is bounded (hence in L²).

**Proof strategy** (from user's specification):
- Use `snorm_mono_exponent` or `memℒp_one_of_memℒp_two` to get `MemLp f 1 μ` from `MemLp f 2 μ`
- Show both `eLpNorm f 1 μ` and `eLpNorm f 2 μ` are finite
- Apply exponent monotonicity: `eLpNorm f 1 μ ≤ eLpNorm f 2 μ` on probability spaces
- Convert `∫|f|` to `(eLpNorm f 1 μ).toReal` and apply `ENNReal.toReal_le_toReal`
-/
lemma eLpNorm_one_le_eLpNorm_two_toReal
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (f : Ω → ℝ) (hL1 : Integrable f μ) (hL2 : MemLp f 2 μ) :
    (∫ ω, |f ω| ∂μ) ≤ (eLpNorm f 2 μ).toReal := by
  -- Step 1: Connect ∫|f| to eLpNorm f 1 μ using norm
  have h_eq : ENNReal.ofReal (∫ ω, |f ω| ∂μ) = eLpNorm f 1 μ := by
    have h_norm : ∫ ω, |f ω| ∂μ = ∫ ω, ‖f ω‖ ∂μ := integral_congr_ae (ae_of_all μ (fun ω => (Real.norm_eq_abs (f ω)).symm))
    rw [h_norm, ofReal_integral_norm_eq_lintegral_enorm hL1]
    exact eLpNorm_one_eq_lintegral_enorm.symm

  -- Step 2: eLpNorm f 1 μ ≤ eLpNorm f 2 μ on probability spaces
  have h_mono : eLpNorm f 1 μ ≤ eLpNorm f 2 μ := by
    have h_ae : AEStronglyMeasurable f μ := hL1.aestronglyMeasurable
    refine eLpNorm_le_eLpNorm_of_exponent_le ?_ h_ae
    norm_num

  -- Step 3: Convert to toReal inequality
  have h_fin : eLpNorm f 2 μ ≠ ⊤ := hL2.eLpNorm_ne_top
  have h_nonneg : 0 ≤ ∫ ω, |f ω| ∂μ := integral_nonneg (fun ω => abs_nonneg _)
  calc (∫ ω, |f ω| ∂μ)
      = (ENNReal.ofReal (∫ ω, |f ω| ∂μ)).toReal := by
          rw [ENNReal.toReal_ofReal h_nonneg]
    _ = (eLpNorm f 1 μ).toReal := by rw [h_eq]
    _ ≤ (eLpNorm f 2 μ).toReal := ENNReal.toReal_mono h_fin h_mono

