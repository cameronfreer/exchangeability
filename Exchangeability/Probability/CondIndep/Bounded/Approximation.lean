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

/-!
## Eapprox-based approximation for real-valued functions

The following lemma provides a simple function approximation sequence for measurable
functions `f : α → ℝ` via the eapprox construction on positive/negative parts.

This is used in the conditional independence extension proofs where we need:
1. Pointwise bound: `|sf n x| ≤ |f x|` (not just ae, but everywhere)
2. Pointwise convergence: `sf n x → f x` for all x

Unlike `approx_bounded_measurable` which uses `StronglyMeasurable.approxBounded`,
this construction works via the ENNReal eapprox machinery and provides deterministic
(not almost-everywhere) bounds.
-/

/-- **Eapprox-based simple function approximation for real-valued functions.**

Given a measurable `f : α → ℝ`, this constructs a sequence of simple functions
that approximate `f` pointwise with the key property that `|sf n x| ≤ |f x|`
holds *everywhere* (not just almost everywhere).

The construction uses `SimpleFunc.eapprox` on the positive and negative parts:
- Split f = f⁺ - f⁻ where f⁺ = max(f, 0), f⁻ = max(-f, 0)
- Apply eapprox to ofReal ∘ f⁺ and ofReal ∘ f⁻
- Convert back to ℝ via toReal
- Take the difference

**Key properties:**
1. `|sf n x| ≤ |f x|` for all n, x (deterministic bound)
2. `sf n x → f x` as n → ∞ for all x (pointwise convergence)
-/
lemma eapprox_real_approx {α : Type*} [MeasurableSpace α] (f : α → ℝ) (hf : Measurable f) :
    ∃ (sf : ℕ → SimpleFunc α ℝ),
      (∀ n x, |sf n x| ≤ |f x|) ∧
      (∀ x, Filter.Tendsto (fun n => sf n x) Filter.atTop (nhds (f x))) := by
  -- Positive/negative parts
  let fp : α → ℝ := fun a => max (f a) 0
  let fm : α → ℝ := fun a => max (-f a) 0

  have hfp_meas : Measurable fp := hf.max measurable_const
  have hfm_meas : Measurable fm := hf.neg.max measurable_const

  -- Lift to ENNReal
  let gp : α → ℝ≥0∞ := fun a => ENNReal.ofReal (fp a)
  let gm : α → ℝ≥0∞ := fun a => ENNReal.ofReal (fm a)

  -- Eapprox sequences in ENNReal
  let up : ℕ → SimpleFunc α ℝ≥0∞ := SimpleFunc.eapprox gp
  let um : ℕ → SimpleFunc α ℝ≥0∞ := SimpleFunc.eapprox gm

  -- Convert back to ℝ
  let sp : ℕ → SimpleFunc α ℝ := fun n => (up n).map ENNReal.toReal
  let sm : ℕ → SimpleFunc α ℝ := fun n => (um n).map ENNReal.toReal

  -- Final approximation sequence
  let sf : ℕ → SimpleFunc α ℝ := fun n => sp n - sm n

  refine ⟨sf, ?_, ?_⟩

  -- Property 1: |sf n x| ≤ |f x| for all n, x
  · intro n x
    -- sp n x ≤ fp x and sm n x ≤ fm x
    have h_sp_le : sp n x ≤ fp x := by
      simp only [sp, up, gp, fp]
      have h_le : SimpleFunc.eapprox (fun a => ENNReal.ofReal (max (f a) 0)) n x
                  ≤ ENNReal.ofReal (max (f x) 0) := by
        have := @SimpleFunc.iSup_eapprox_apply α _ (fun a => ENNReal.ofReal (max (f a) 0))
                  (hf.max measurable_const).ennreal_ofReal x
        rw [← this]
        exact le_iSup (fun k => SimpleFunc.eapprox _ k x) n
      have h_fin : ENNReal.ofReal (max (f x) 0) ≠ ∞ := ENNReal.ofReal_ne_top
      have h_toReal := ENNReal.toReal_mono h_fin h_le
      rw [ENNReal.toReal_ofReal (le_max_right _ _)] at h_toReal
      exact h_toReal

    have h_sm_le : sm n x ≤ fm x := by
      simp only [sm, um, gm, fm]
      have h_le : SimpleFunc.eapprox (fun a => ENNReal.ofReal (max (-f a) 0)) n x
                  ≤ ENNReal.ofReal (max (-f x) 0) := by
        have := @SimpleFunc.iSup_eapprox_apply α _ (fun a => ENNReal.ofReal (max (-f a) 0))
                  (hf.neg.max measurable_const).ennreal_ofReal x
        rw [← this]
        exact le_iSup (fun k => SimpleFunc.eapprox _ k x) n
      have h_fin : ENNReal.ofReal (max (-f x) 0) ≠ ∞ := ENNReal.ofReal_ne_top
      have h_toReal := ENNReal.toReal_mono h_fin h_le
      rw [ENNReal.toReal_ofReal (le_max_right _ _)] at h_toReal
      exact h_toReal

    -- sp n x and sm n x are nonnegative
    have h_sp_nn : 0 ≤ sp n x := ENNReal.toReal_nonneg
    have h_sm_nn : 0 ≤ sm n x := ENNReal.toReal_nonneg

    -- |sp - sm| ≤ sp + sm when both nonnegative
    have h_abs_le : |sp n x - sm n x| ≤ sp n x + sm n x := by
      rw [abs_sub_le_iff]
      constructor <;> linarith

    -- sp + sm ≤ fp + fm
    have h_sum_le : sp n x + sm n x ≤ fp x + fm x :=
      add_le_add h_sp_le h_sm_le

    -- fp + fm = |f| (positive part + negative part = absolute value)
    have h_parts : fp x + fm x = |f x| := by
      simp only [fp, fm]
      exact max_zero_add_max_neg_zero_eq_abs_self (f x)

    calc |sf n x| = |sp n x - sm n x| := rfl
      _ ≤ sp n x + sm n x := h_abs_le
      _ ≤ fp x + fm x := h_sum_le
      _ = |f x| := h_parts

  -- Property 2: sf n x → f x for all x
  · intro x
    have h_sp_tendsto : Filter.Tendsto (fun n => sp n x) Filter.atTop (nhds (fp x)) := by
      simp only [sp, up, gp, fp]
      have h_tend_enn : Filter.Tendsto (fun n => SimpleFunc.eapprox (fun a => ENNReal.ofReal (max (f a) 0)) n x)
                                Filter.atTop
                                (nhds (ENNReal.ofReal (max (f x) 0))) := by
        apply SimpleFunc.tendsto_eapprox
        exact (hf.max measurable_const).ennreal_ofReal
      have h_fin : ENNReal.ofReal (max (f x) 0) ≠ ∞ := ENNReal.ofReal_ne_top
      have h_cont := ENNReal.tendsto_toReal h_fin
      have := h_cont.comp h_tend_enn
      rwa [ENNReal.toReal_ofReal (le_max_right _ _)] at this

    have h_sm_tendsto : Filter.Tendsto (fun n => sm n x) Filter.atTop (nhds (fm x)) := by
      simp only [sm, um, gm, fm]
      have h_tend_enn : Filter.Tendsto (fun n => SimpleFunc.eapprox (fun a => ENNReal.ofReal (max (-f a) 0)) n x)
                                Filter.atTop
                                (nhds (ENNReal.ofReal (max (-f x) 0))) := by
        apply SimpleFunc.tendsto_eapprox
        exact (hf.neg.max measurable_const).ennreal_ofReal
      have h_fin : ENNReal.ofReal (max (-f x) 0) ≠ ∞ := ENNReal.ofReal_ne_top
      have h_cont := ENNReal.tendsto_toReal h_fin
      have := h_cont.comp h_tend_enn
      rwa [ENNReal.toReal_ofReal (le_max_right _ _)] at this

    have := h_sp_tendsto.sub h_sm_tendsto
    simp only [sf, fp, fm, SimpleFunc.coe_sub] at this ⊢
    convert this using 2
    exact (max_zero_sub_eq_self (f x)).symm

/-!
## L¹ convergence helper lemmas

These lemmas capture common patterns in the bounded measurable extension proofs:
1. Product L¹ convergence: bounded × L¹-convergent → L¹-convergent
2. Set integral convergence: L¹ convergence implies set integral convergence
-/

/-- **Product L¹ convergence: bounded factor × L¹-convergent → L¹-convergent.**

If `f` is bounded a.e. by `M` and `∫|gn - g| → 0`, then `∫|f * (gn - g)| → 0`.
This pattern appears repeatedly in monotone class arguments. -/
lemma tendsto_integral_mul_of_bounded_L1
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {f : Ω → ℝ} {gn : ℕ → Ω → ℝ} {g : Ω → ℝ}
    (M : ℝ) (hM_nn : 0 ≤ M)
    (hf_asm : AEStronglyMeasurable f μ)
    (hf_bdd : ∀ᵐ ω ∂μ, |f ω| ≤ M)
    (hgn_int : ∀ n, Integrable (gn n) μ) (hg_int : Integrable g μ)
    (hL1 : Filter.Tendsto (fun n => ∫ ω, |gn n ω - g ω| ∂μ) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => ∫ ω, |f ω * (gn n ω - g ω)| ∂μ) Filter.atTop (nhds 0) := by
  -- Upper bound: ∫|f * (gn - g)| ≤ M * ∫|gn - g| → 0
  let h : ℕ → ℝ := fun n => M * ∫ ω, |gn n ω - g ω| ∂μ
  have h_tendsto : Filter.Tendsto h Filter.atTop (nhds 0) := by
    have := Filter.Tendsto.const_mul M hL1
    simp only [mul_zero] at this
    exact this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h_tendsto ?_ ?_
  · intro n; exact integral_nonneg (fun _ => abs_nonneg _)
  · intro n
    have h_bd : ∀ᵐ ω ∂μ, |f ω * (gn n ω - g ω)| ≤ M * |gn n ω - g ω| := by
      filter_upwards [hf_bdd] with ω hω
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right hω (abs_nonneg _)
    have h_lhs_int : Integrable (fun ω => |f ω * (gn n ω - g ω)|) μ := by
      have h_diff_int : Integrable (gn n - g) μ := (hgn_int n).sub hg_int
      have h_prod : Integrable (fun ω => f ω * (gn n ω - g ω)) μ := by
        have h_eq : (fun ω => f ω * (gn n ω - g ω)) = f * (gn n - g) := rfl
        rw [h_eq]
        -- bdd_mul' (c := M) hg hf_asm hf_bdd gives Integrable (hf * hg)
        refine Integrable.bdd_mul' (c := M) h_diff_int hf_asm ?_
        filter_upwards [hf_bdd] with ω hω
        rw [Real.norm_eq_abs]; exact hω
      exact h_prod.abs
    have h_rhs_int : Integrable (fun ω => M * |gn n ω - g ω|) μ :=
      ((hgn_int n).sub hg_int).abs.const_mul M
    calc ∫ ω, |f ω * (gn n ω - g ω)| ∂μ
        ≤ ∫ ω, M * |gn n ω - g ω| ∂μ := integral_mono_ae h_lhs_int h_rhs_int h_bd
      _ = M * ∫ ω, |gn n ω - g ω| ∂μ := integral_const_mul M _

/-- **Set integral convergence from L¹ convergence.**

If `∫|fn - f| → 0` and both `fn`, `f` are integrable, then for any measurable set `C`,
`∫_C fn → ∫_C f`. -/
lemma tendsto_setIntegral_of_L1
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {fn : ℕ → Ω → ℝ} {f : Ω → ℝ}
    (hfn_int : ∀ n, Integrable (fn n) μ) (hf_int : Integrable f μ)
    (hL1 : Filter.Tendsto (fun n => ∫ ω, |fn n ω - f ω| ∂μ) Filter.atTop (nhds 0))
    (C : Set Ω) :
    Filter.Tendsto (fun n => ∫ ω in C, fn n ω ∂μ) Filter.atTop (nhds (∫ ω in C, f ω ∂μ)) := by
  rw [Metric.tendsto_atTop] at hL1 ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := hL1 ε hε
  use N
  intro n hn
  rw [Real.dist_eq]
  have hN' := hN n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg (fun _ => abs_nonneg _))] at hN'
  calc |∫ ω in C, fn n ω ∂μ - ∫ ω in C, f ω ∂μ|
      = |∫ ω in C, (fn n ω - f ω) ∂μ| := by
        rw [← integral_sub (hfn_int n).integrableOn hf_int.integrableOn]
    _ ≤ ∫ ω in C, |fn n ω - f ω| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ ω, |fn n ω - f ω| ∂μ := by
        refine setIntegral_le_integral ((hfn_int n).sub hf_int).abs ?_
        filter_upwards with ω; exact abs_nonneg _
    _ < ε := hN'
