/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.SimpleFunc
import Mathlib.MeasureTheory.Function.SimpleFuncDense

/-!
# Approximation Infrastructure for Bounded Measurable Extension

This file provides the L¹ convergence lemmas and simple function approximation
infrastructure needed for extending conditional independence results from
simple functions to bounded measurable functions.

## Main results

* `tendsto_condexp_L1` - L¹ convergence of conditional expectations (continuity)
* `approx_bounded_measurable` - Approximate bounded measurable by simple functions

## References

* Kallenberg (2005), *Probabilistic Symmetries and Invariance Principles*, Section 6.1
-/

open scoped Classical

noncomputable section
open scoped MeasureTheory ENNReal
open MeasureTheory ProbabilityTheory Set

variable {Ω α β γ : Type*}
variable [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

/-!
## Helper lemmas for bounded measurable extension
-/

/-- **CE is continuous from L¹ to L¹ (wrapper around mathlib's lemma).**

Note: This lemma uses pointwise/product topology on `Ω → ℝ` for the output convergence.
For proper L¹ convergence of conditional expectations, the mathlib approach is to use
`condExpL1CLM` (conditional expectation as a continuous linear map on L¹ spaces).

The proof strategy is:
1. **L¹ contraction**: condExp is an L¹ contraction, i.e., `eLpNorm (μ[g|m]) 1 μ ≤ eLpNorm g 1 μ`
   - In mathlib: `eLpNorm_one_condExp_le_eLpNorm` (in Real.lean)
2. **Linearity**: `μ[fn n - f | m] =ᵐ[μ] μ[fn n | m] - μ[f | m]` (by `condExp_sub`)
3. **Apply contraction**: `eLpNorm (μ[fn n | m] - μ[f | m]) 1 μ ≤ eLpNorm (fn n - f) 1 μ → 0`
4. **Convert norms**: The hypothesis uses lintegral of nnnorm, which equals eLpNorm with exponent 1

The conclusion as stated uses pointwise topology, but the natural convergence mode is L¹.
For applications, L¹ convergence of condExp is typically what's needed. -/
lemma tendsto_condexp_L1 {mΩ : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m : MeasurableSpace Ω) (_hm : m ≤ mΩ)
    {fn : ℕ → Ω → ℝ} {f : Ω → ℝ}
    (h_int : ∀ n, Integrable (fn n) μ) (hf : Integrable f μ)
    (hL1 : Filter.Tendsto (fun n => ∫ ω, |fn n ω - f ω| ∂μ) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => ∫ ω, |μ[fn n | m] ω - μ[f | m] ω| ∂μ) Filter.atTop (nhds 0) := by
  -- Use squeeze theorem: 0 ≤ ∫|CE[fn]-CE[f]| ≤ ∫|fn-f| → 0
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hL1 ?_ ?_
  · -- Lower bound: 0 ≤ ∫|CE[fn]-CE[f]|
    intro n
    exact integral_nonneg (fun ω => abs_nonneg _)
  · -- Upper bound: ∫|CE[fn]-CE[f]| ≤ ∫|fn-f|
    intro n
    -- Step 1: CE[fn - f] =ᵐ CE[fn] - CE[f]
    have h_sub : μ[fn n - f | m] =ᵐ[μ] μ[fn n | m] - μ[f | m] :=
      condExp_sub (h_int n) hf m
    -- Step 2: Rewrite and apply L¹ contraction
    calc ∫ ω, |μ[fn n | m] ω - μ[f | m] ω| ∂μ
        = ∫ ω, |μ[fn n - f | m] ω| ∂μ := by
            refine integral_congr_ae ?_
            filter_upwards [h_sub] with ω hω
            simp [hω]
      _ ≤ ∫ ω, |fn n ω - f ω| ∂μ := integral_abs_condExp_le (fn n - f)

/-- **Helper: approximate bounded measurable function by simple functions.** -/
lemma approx_bounded_measurable (μ : Measure α) [IsProbabilityMeasure μ]
    {f : α → ℝ} (M : ℝ) (hf_meas : Measurable f)
    (hf_bdd : ∀ᵐ x ∂μ, |f x| ≤ M) :
    ∃ (fn : ℕ → SimpleFunc α ℝ),
      (∀ n, ∀ᵐ x ∂μ, |fn n x| ≤ M) ∧
      (∀ᵐ x ∂μ, Filter.Tendsto (fun n => (fn n) x) Filter.atTop (nhds (f x))) ∧
      (Filter.Tendsto (fun n => ∫⁻ x, ‖(fn n) x - f x‖₊ ∂μ) Filter.atTop (nhds 0)) := by
  -- Use StronglyMeasurable.approxBounded which creates bounded simple function approximations
  --
  -- PROOF STRATEGY:
  -- 1. Convert Measurable f to StronglyMeasurable f using hf_meas.stronglyMeasurable
  -- 2. Use hf_sm.approxBounded M n as the approximating simple functions
  -- 3. The bound property follows from StronglyMeasurable.norm_approxBounded_le
  -- 4. Pointwise ae convergence from StronglyMeasurable.tendsto_approxBounded_ae
  -- 5. L1 convergence via tendsto_lintegral_of_dominated_convergence:
  --    - Dominating function: constant 2*M (integrable on probability space)
  --    - Bound: ‖fn n x - f x‖ ≤ ‖fn n x‖ + ‖f x‖ ≤ M + M = 2M
  --    - ae limit is 0 from pointwise convergence
  --
  -- IMPLEMENTATION NOTE: The proof is straightforward but requires careful handling
  -- of ENNReal/NNReal/Real conversions. The key mathlib lemmas are:
  -- - StronglyMeasurable.approxBounded
  -- - StronglyMeasurable.norm_approxBounded_le
  -- - StronglyMeasurable.tendsto_approxBounded_ae
  -- - tendsto_lintegral_of_dominated_convergence
  -- Step 1: Get StronglyMeasurable f from Measurable f
  have hf_sm : StronglyMeasurable f := hf_meas.stronglyMeasurable
  -- Handle case where M < 0: this forces f = 0 ae, so use trivial approximation
  by_cases hM_nonneg : 0 ≤ M
  · -- Case M ≥ 0: Use approxBounded with M directly
    have hf_bdd' : ∀ᵐ x ∂μ, ‖f x‖ ≤ M := by
      filter_upwards [hf_bdd] with x hx
      rw [Real.norm_eq_abs]; exact hx
    -- Define approximating sequence using approxBounded
    refine ⟨fun n => hf_sm.approxBounded M n, ?_, ?_, ?_⟩
    -- Property 1: Each fn is bounded by M
    · intro n
      filter_upwards with x
      have h := hf_sm.norm_approxBounded_le hM_nonneg n x
      rw [Real.norm_eq_abs] at h; exact h
    -- Property 2: Pointwise ae convergence
    · exact hf_sm.tendsto_approxBounded_ae hf_bdd'
    -- Property 3: L¹ convergence via dominated convergence
    --
    -- PROOF STRATEGY using tendsto_lintegral_of_dominated_convergence:
    -- - F n x := ‖approxBounded M n x - f x‖₊ (as ℝ≥0∞)
    -- - Limit function: 0 (from pointwise ae convergence via tendsto_approxBounded_ae)
    -- - Dominator: constant 2*M (since ‖fn - f‖ ≤ ‖fn‖ + ‖f‖ ≤ M + M)
    -- - Dominator integrable: ∫ 2M dμ = 2M * μ(univ) = 2M < ∞ on probability space
    --
    -- Then tendsto_lintegral_of_dominated_convergence gives:
    --   ∫⁻ ‖fn - f‖₊ → ∫⁻ 0 = 0
    --
    -- Key lemmas:
    -- - hf_sm.tendsto_approxBounded_ae hf_bdd': fn → f pointwise ae
    -- - hf_sm.norm_approxBounded_le hM_nonneg: ‖fn x‖ ≤ M
    --
    -- IMPLEMENTATION NOTE: Requires careful handling of ℝ ↔ ℝ≥0 ↔ ℝ≥0∞ coercions.
    --
    -- The proof structure is:
    -- 1. h_ptwise := hf_sm.tendsto_approxBounded_ae hf_bdd' gives fn → f pointwise ae
    -- 2. h_norm_bdd : ‖fn x‖ ≤ M from norm_approxBounded_le
    -- 3. h_diff_bdd : ‖fn x - f x‖ ≤ 2M from triangle inequality
    -- 4. Apply tendsto_lintegral_of_dominated_convergence with:
    --    - F n x := ENNReal.ofReal ‖fn x - f x‖
    --    - Limit: 0
    --    - Dominator: ENNReal.ofReal (2 * M)
    --    - h_fin: ∫⁻ 2M dμ = 2M < ⊤ (probability measure)
    --    - h_lim: ae convergence from h_ptwise
    -- 5. Convert from ENNReal.ofReal ‖·‖ to ‖·‖₊ using ENNReal.coe_toNNNorm
    · -- Get pointwise ae convergence
      have h_ptwise : ∀ᵐ x ∂μ, Filter.Tendsto (fun n => (hf_sm.approxBounded M n) x)
          Filter.atTop (nhds (f x)) := hf_sm.tendsto_approxBounded_ae hf_bdd'
      -- Get bound: ‖fn x - f x‖ ≤ 2M
      have h_bdd_diff : ∀ n, ∀ᵐ x ∂μ, ‖(hf_sm.approxBounded M n) x - f x‖ ≤ 2 * M := by
        intro n
        filter_upwards [hf_bdd'] with x hfx
        calc ‖(hf_sm.approxBounded M n) x - f x‖
            ≤ ‖(hf_sm.approxBounded M n) x‖ + ‖f x‖ := norm_sub_le _ _
          _ ≤ M + M := add_le_add (hf_sm.norm_approxBounded_le hM_nonneg n x) hfx
          _ = 2 * M := by ring
      -- Apply dominated convergence: ∫⁻ ‖fn - f‖₊ → 0
      have h_lim_zero : ∀ᵐ x ∂μ, Filter.Tendsto (fun n => (‖(hf_sm.approxBounded M n) x - f x‖₊ : ℝ≥0∞))
          Filter.atTop (nhds 0) := by
        filter_upwards [h_ptwise] with x hx
        have htend : Filter.Tendsto (fun n => (hf_sm.approxBounded M n) x - f x)
            Filter.atTop (nhds 0) := by
          convert Filter.Tendsto.sub hx tendsto_const_nhds using 1
          simp
        have h1 : Filter.Tendsto (fun n => ‖(hf_sm.approxBounded M n) x - f x‖₊)
            Filter.atTop (nhds ‖(0 : ℝ)‖₊) := (continuous_nnnorm.tendsto 0).comp htend
        simp only [nnnorm_zero] at h1
        exact ENNReal.tendsto_coe.mpr h1
      -- Dominator is integrable on probability space
      have h_dom_int : ∫⁻ _, (2 * M).toNNReal ∂μ ≠ ⊤ := by
        simp only [lintegral_const, ne_eq]
        exact ENNReal.mul_ne_top (by simp) (measure_ne_top μ _)
      -- Define the functions explicitly for measurability
      let F := fun n x => (‖(hf_sm.approxBounded M n) x - f x‖₊ : ℝ≥0∞)
      have hF_meas : ∀ n, Measurable (F n) := fun n =>
        ((hf_sm.approxBounded M n).measurable.sub hf_meas).nnnorm.coe_nnreal_ennreal
      have h_lim_ae : ∀ᵐ x ∂μ, Filter.Tendsto (fun n => F n x) Filter.atTop (nhds 0) := h_lim_zero
      have h_result := tendsto_lintegral_of_dominated_convergence (fun _ => (2 * M).toNNReal)
        hF_meas ?_ h_dom_int h_lim_ae
      · -- Convert from ∫⁻ 0 = 0 to the goal
        simp only [lintegral_zero] at h_result
        exact h_result
      -- Bound condition
      · intro n
        filter_upwards [h_bdd_diff n] with x hx
        simp only [F, ENNReal.coe_le_coe]
        have h2M_nn : 0 ≤ 2 * M := by linarith
        -- Goal: ‖...‖₊ ≤ (2*M).toNNReal as NNReal
        -- We have hx : ‖...‖ ≤ 2*M as Real
        -- Use: x ≤ y ↔ (x : ℝ) ≤ (y : ℝ) for NNReal x y
        rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ h2M_nn]
        exact hx
  · -- Case M < 0: contradiction since |f x| ≥ 0 > M always
    -- The hypothesis hf_bdd : ∀ᵐ x ∂μ, |f x| ≤ M with M < 0 is impossible
    -- since |f x| ≥ 0 for all x. This implies μ = 0, contradicting probability measure.
    push_neg at hM_nonneg
    exfalso
    have h_ae_false : ∀ᵐ x ∂μ, False := by
      filter_upwards [hf_bdd] with x hx
      have h_abs_nonneg : 0 ≤ |f x| := abs_nonneg _
      linarith
    rw [Filter.eventually_false_iff_eq_bot, ae_eq_bot] at h_ae_false
    -- h_ae_false : μ = 0, but probability measure has μ univ = 1
    have h_univ : μ Set.univ = 1 := measure_univ
    rw [h_ae_false] at h_univ
    simp at h_univ
