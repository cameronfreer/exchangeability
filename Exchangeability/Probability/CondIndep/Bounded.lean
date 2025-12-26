/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Exchangeability.Probability.CondIndep.Indicator

/-!
# Conditional Independence - Bounded Measurable Extension

This file extends conditional independence from simple functions to bounded measurable
functions using L¹ approximation and convergence arguments.

## Main results

* `tendsto_condexp_L1`: L¹ convergence of conditional expectations
* `condIndep_bounded_of_simpleFunc`: Extension to bounded measurable functions

## References

* Kallenberg (2005), *Probabilistic Symmetries and Invariance Principles*, Section 6.1
-/

open scoped Classical

noncomputable section
open scoped MeasureTheory ENNReal
open MeasureTheory ProbabilityTheory Set Exchangeability.Probability

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

/-- **Conditional independence for simple functions (left argument).**
Refactored to avoid instance pollution: works with σ(W) directly.

Given a simple function φ and bounded measurable function ψ with |ψ ∘ Z| ≤ Mψ a.e.,
proves the factorization: μ[(φ ∘ Y) * (ψ ∘ Z) | σ(W)] = μ[φ ∘ Y | σ(W)] * μ[ψ ∘ Z | σ(W)].

**Proof Strategy**:
1. Approximate ψ by simple functions ψₙ (using eapprox on positive/negative parts)
2. For each n: apply `condIndep_simpleFunc μ Y Z W hCI φ ψₙ hY hZ`
3. Pass to limit using dominated convergence (dominator: Mφ · Mψ where Mφ bounds φ)

**Key mathlib lemmas**:
- `condIndep_simpleFunc` : base case for both simple
- `tendsto_condExpL1_of_dominated_convergence` : L¹ convergence of condExp -/
lemma condIndep_simpleFunc_left
    {Ω α β γ : Type*}
    {m₀ : MeasurableSpace Ω}  -- Explicit ambient space
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure Ω) [IsProbabilityMeasure μ]  -- μ explicit, instances after
    (Y : Ω → α) (Z : Ω → β) (W : Ω → γ)  -- Then plain parameters
    (hCI : @CondIndep Ω α β γ m₀ _ _ _ μ Y Z W)
    (φ : SimpleFunc α ℝ) {ψ : β → ℝ}
    (hY : @Measurable Ω α m₀ _ Y) (hZ : @Measurable Ω β m₀ _ Z) (hW : @Measurable Ω γ m₀ _ W)
    (hψ_meas : Measurable ψ)
    (Mψ : ℝ) (hψ_bdd : ∀ᵐ ω ∂μ, |ψ (Z ω)| ≤ Mψ) :
    μ[ (φ ∘ Y) * (ψ ∘ Z) | MeasurableSpace.comap W inferInstance ] =ᵐ[μ]
    μ[ φ ∘ Y | MeasurableSpace.comap W inferInstance ] *
    μ[ ψ ∘ Z | MeasurableSpace.comap W inferInstance ] := by
  /-
  PROOF STRATEGY (complete proof infrastructure is in condIndep_bddMeas_extend_left for φ):
  1. Build simple function approximation of ψ via eapprox (pos/neg parts)
  2. Apply condIndep_simpleFunc for each (φ, sψ n)
  3. Use DCT + L¹ convergence to pass to the limit
  4. Conclude via ae_eq_condExp_of_forall_setIntegral_eq

  The key steps are:
  - Simple function approximation: sψ n → ψ pointwise with |sψ n| ≤ |ψ|
  - Base case: condIndep_simpleFunc for both simple functions
  - LHS convergence: DCT with bound Mφ * |ψ ∘ Z|
  - RHS convergence: L¹ convergence of condExp (product of bounded and L¹-converging)
  - Limit uniqueness: LHS = RHS sequences → limits equal

  The remaining sorry is for the L¹ product convergence:
  - Need: bounded * L¹ converging → set integral converging
  - mathlib lemmas: Integrable.bdd_mul', tendsto_setIntegral_of_L1
  -/
  sorry

/-- **Extend factorization from simple φ to bounded measurable φ, keeping ψ fixed.**
Refactored to avoid instance pollution: works with σ(W) directly. -/
lemma condIndep_bddMeas_extend_left
    {Ω α β γ : Type*}
    {m₀ : MeasurableSpace Ω}  -- Explicit ambient space
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure Ω) [IsProbabilityMeasure μ]  -- μ explicit, instances after
    (Y : Ω → α) (Z : Ω → β) (W : Ω → γ)  -- Then plain parameters
    (hCI : @CondIndep Ω α β γ m₀ _ _ _ μ Y Z W)
    (hY : @Measurable Ω α m₀ _ Y) (hZ : @Measurable Ω β m₀ _ Z) (hW : @Measurable Ω γ m₀ _ W)
    {φ : α → ℝ} {ψ : β → ℝ}
    (hφ_meas : Measurable φ) (hψ_meas : Measurable ψ)
    (Mφ Mψ : ℝ)
    (hφ_bdd : ∀ᵐ ω ∂μ, |φ (Y ω)| ≤ Mφ)
    (hψ_bdd : ∀ᵐ ω ∂μ, |ψ (Z ω)| ≤ Mψ) :
    μ[ (φ ∘ Y) * (ψ ∘ Z) | MeasurableSpace.comap W inferInstance ] =ᵐ[μ]
    μ[ (φ ∘ Y) | MeasurableSpace.comap W inferInstance ] *
    μ[ (ψ ∘ Z) | MeasurableSpace.comap W inferInstance ] := by
  classical
  -- Define mW := σ(W) for cleaner notation
  set mW := MeasurableSpace.comap W (inferInstance : MeasurableSpace γ) with hmW_def
  have hmW_le : mW ≤ m₀ := hW.comap_le
  -- Step 0: build real-valued simple-function approximation of φ via ℝ≥0∞ eapprox on pos/neg parts.
  -- positive/negative parts as ℝ
  set φp : α → ℝ := fun a => max (φ a) 0 with hφp
  set φm : α → ℝ := fun a => max (- φ a) 0 with hφm
  have hφp_nn : ∀ a, 0 ≤ φp a := by intro a; simp [φp]
  have hφm_nn : ∀ a, 0 ≤ φm a := by intro a; simp [φm]

  have hφp_meas : Measurable φp := hφ_meas.max measurable_const
  have hφm_meas : Measurable φm := hφ_meas.neg.max measurable_const

  -- lift to ℝ≥0∞ nonnegative functions
  let gp : α → ℝ≥0∞ := fun a => ENNReal.ofReal (φp a)
  let gm : α → ℝ≥0∞ := fun a => ENNReal.ofReal (φm a)
  have hgp_meas : Measurable gp := hφp_meas.ennreal_ofReal
  have hgm_meas : Measurable gm := hφm_meas.ennreal_ofReal

  -- eapprox sequences in ℝ≥0∞
  let up : ℕ → SimpleFunc α ℝ≥0∞ := SimpleFunc.eapprox gp
  let um : ℕ → SimpleFunc α ℝ≥0∞ := SimpleFunc.eapprox gm
  -- back to ℝ via toReal
  let sp : ℕ → SimpleFunc α ℝ := fun n => (up n).map ENNReal.toReal
  let sm : ℕ → SimpleFunc α ℝ := fun n => (um n).map ENNReal.toReal
  -- final real simple approximants
  let sφ : ℕ → SimpleFunc α ℝ := fun n => (sp n) - (sm n)

  -- properties: sφ n → φ pointwise, uniformly bounded
  have h_sp_le : ∀ n a, (sp n a) ≤ φp a := by
    intro n a
    -- sp n a = toReal (eapprox gp n a)
    -- φp a = toReal (ofReal (max (φ a) 0))
    simp only [sp, up, gp, φp]
    -- eapprox is monotonically increasing to its limit
    have h_le : SimpleFunc.eapprox (fun (x : α) => ENNReal.ofReal (max (φ x) 0)) n a
                ≤ ENNReal.ofReal (max (φ a) 0) := by
      have := @SimpleFunc.iSup_eapprox_apply α _ (fun x => ENNReal.ofReal (max (φ x) 0))
                (hφ_meas.max measurable_const).ennreal_ofReal a
      rw [← this]
      exact le_iSup (fun k => SimpleFunc.eapprox _ k a) n
    -- ofReal of bounded value is finite
    have h_fin : ENNReal.ofReal (max (φ a) 0) ≠ ∞ := ENNReal.ofReal_ne_top
    -- toReal is monotone
    have h_toReal := ENNReal.toReal_mono h_fin h_le
    -- toReal ∘ ofReal = id for nonnegative
    rw [ENNReal.toReal_ofReal (le_max_right _ _)] at h_toReal
    exact h_toReal

  have h_sm_le : ∀ n a, (sm n a) ≤ φm a := by
    intro n a
    simp only [sm, um, gm, φm]
    have h_le : SimpleFunc.eapprox (fun (x : α) => ENNReal.ofReal (max (- φ x) 0)) n a
                ≤ ENNReal.ofReal (max (- φ a) 0) := by
      have := @SimpleFunc.iSup_eapprox_apply α _ (fun x => ENNReal.ofReal (max (- φ x) 0))
                (hφ_meas.neg.max measurable_const).ennreal_ofReal a
      rw [← this]
      exact le_iSup (fun k => SimpleFunc.eapprox _ k a) n
    have h_fin : ENNReal.ofReal (max (- φ a) 0) ≠ ∞ := ENNReal.ofReal_ne_top
    have h_toReal := ENNReal.toReal_mono h_fin h_le
    rw [ENNReal.toReal_ofReal (le_max_right _ _)] at h_toReal
    exact h_toReal

  have h_sp_tendsto : ∀ a, Filter.Tendsto (fun n => sp n a) Filter.atTop (nhds (φp a)) := by
    intro a
    simp only [sp, up, gp, φp]
    -- eapprox converges pointwise to its limit
    have h_tend_enn : Filter.Tendsto (fun n => SimpleFunc.eapprox (fun a => ENNReal.ofReal (max (φ a) 0)) n a)
                              Filter.atTop
                              (nhds (ENNReal.ofReal (max (φ a) 0))) := by
      apply SimpleFunc.tendsto_eapprox
      exact (hφ_meas.max measurable_const).ennreal_ofReal
    -- ofReal is always finite
    have h_fin : ENNReal.ofReal (max (φ a) 0) ≠ ∞ := ENNReal.ofReal_ne_top
    -- toReal is continuous at finite points
    have h_cont := ENNReal.tendsto_toReal h_fin
    -- compose the two tendsto's
    have := h_cont.comp h_tend_enn
    -- simplify toReal (ofReal x) = x for nonnegative x
    rwa [ENNReal.toReal_ofReal (le_max_right _ _)] at this

  have h_sm_tendsto : ∀ a, Filter.Tendsto (fun n => sm n a) Filter.atTop (nhds (φm a)) := by
    intro a
    simp only [sm, um, gm, φm]
    have h_tend_enn : Filter.Tendsto (fun n => SimpleFunc.eapprox (fun a => ENNReal.ofReal (max (- φ a) 0)) n a)
                              Filter.atTop
                              (nhds (ENNReal.ofReal (max (- φ a) 0))) := by
      apply SimpleFunc.tendsto_eapprox
      exact (hφ_meas.neg.max measurable_const).ennreal_ofReal
    have h_fin : ENNReal.ofReal (max (- φ a) 0) ≠ ∞ := ENNReal.ofReal_ne_top
    have h_cont := ENNReal.tendsto_toReal h_fin
    have := h_cont.comp h_tend_enn
    rwa [ENNReal.toReal_ofReal (le_max_right _ _)] at this

  have h_sφ_tendsto : ∀ a, Filter.Tendsto (fun n => sφ n a) Filter.atTop (nhds (φ a)) := by
    intro a
    have := (h_sp_tendsto a).sub (h_sm_tendsto a)
    -- posPart - negPart = φ
    simp only [sφ, sp, sm, φp, φm, SimpleFunc.coe_sub] at this ⊢
    convert this using 2
    -- Show: max (φ a) 0 - max (-φ a) 0 = φ a
    exact (max_zero_sub_eq_self (φ a)).symm

  have h_sφ_bdd : ∀ n a, |sφ n a| ≤ |φ a| := by
    intro n a
    simp only [sφ, sp, sm, φp, φm, SimpleFunc.coe_sub]
    -- We have: sp n a ≤ φp a and sm n a ≤ φm a from h_sp_le and h_sm_le
    -- Both sp and sm are nonnegative (as toReal of eapprox applied to ofReal of max with 0)
    have h_sp_nn : 0 ≤ sp n a := by
      simp only [sp, up, gp]
      exact ENNReal.toReal_nonneg
    have h_sm_nn : 0 ≤ sm n a := by
      simp only [sm, um, gm]
      exact ENNReal.toReal_nonneg
    -- |sp - sm| ≤ sp + sm when both nonnegative
    have h_abs_le : |sp n a - sm n a| ≤ sp n a + sm n a := by
      rw [abs_sub_le_iff]
      constructor
      · linarith [h_sp_nn, h_sm_nn]
      · linarith [h_sp_nn, h_sm_nn]
    -- sp + sm ≤ φp + φm
    have h_sum_le : sp n a + sm n a ≤ φp a + φm a := by
      exact add_le_add (h_sp_le n a) (h_sm_le n a)
    -- φp + φm = |φ| (positive part + negative part = absolute value)
    have h_parts : φp a + φm a = |φ a| := by
      simp only [φp, φm]
      exact max_zero_add_max_neg_zero_eq_abs_self (φ a)
    -- Combine
    calc |sp n a - sm n a|
        ≤ sp n a + sm n a := h_abs_le
      _ ≤ φp a + φm a := h_sum_le
      _ = |φ a| := h_parts

  -- Step 1: reduce to equality of set integrals on σ(W)-sets C.

  have hC_sets :
    ∀ C, MeasurableSet[mW] C →
      ∫ ω in C, ((φ ∘ Y) * (ψ ∘ Z)) ω ∂μ
        = ∫ ω in C, (μ[(φ ∘ Y) | mW] * μ[(ψ ∘ Z) | mW]) ω ∂μ := by
    intro C hC

    -- For each n, simple φ-approximation: apply condIndep_simpleFunc
    have h_rect_n :
      ∀ n,
        μ[ ((sφ n) ∘ Y) * (ψ ∘ Z) | mW ]
          =ᵐ[μ]
        μ[ ((sφ n) ∘ Y) | mW ] * μ[ (ψ ∘ Z) | mW ] := by
      intro n
      -- Use the refactored lemma (now works directly with σ(W))
      -- mW is definitionally equal to MeasurableSpace.comap W inferInstance
      exact condIndep_simpleFunc_left μ Y Z W hCI (sφ n) hY hZ hW hψ_meas Mψ hψ_bdd

    -- Integrate both sides over C
    have h_int_n :
      ∀ n,
        ∫ ω in C, ((sφ n ∘ Y) * (ψ ∘ Z)) ω ∂μ
          = ∫ ω in C, (μ[(sφ n ∘ Y) | mW] * μ[(ψ ∘ Z) | mW]) ω ∂μ := by
      intro n
      -- First, need integrability
      have hsφn_int : Integrable ((sφ n) ∘ Y) μ := by
        refine Integrable.comp_measurable ?_ hY
        exact SimpleFunc.integrable_of_isFiniteMeasure (sφ n)
      have hψ_int : Integrable (ψ ∘ Z) μ := by
        refine Integrable.of_mem_Icc (-Mψ) Mψ (hψ_meas.comp hZ).aemeasurable ?_
        filter_upwards [hψ_bdd] with ω hω
        simp only [Function.comp_apply, Set.mem_Icc]
        exact abs_le.mp hω
      have hprod_int : Integrable (((sφ n) ∘ Y) * (ψ ∘ Z)) μ := by
        -- sφ n is bounded (simple function), ψ ∘ Z is integrable
        refine Integrable.bdd_mul' (c := Mφ) hψ_int ((sφ n).measurable.comp hY).aestronglyMeasurable ?_
        -- Need bound on sφ n ∘ Y: use that |sφ n| ≤ |φ| from h_sφ_bdd
        filter_upwards [hφ_bdd] with ω hω
        calc ‖((sφ n) ∘ Y) ω‖
            = |sφ n (Y ω)| := by simp [Real.norm_eq_abs]
          _ ≤ |φ (Y ω)| := h_sφ_bdd n (Y ω)
          _ ≤ Mφ := hω
      -- Use setIntegral_condExp followed by setIntegral_congr_ae
      calc ∫ ω in C, ((sφ n ∘ Y) * (ψ ∘ Z)) ω ∂μ
          = ∫ ω in C, μ[((sφ n ∘ Y) * (ψ ∘ Z)) | mW] ω ∂μ := by
              exact (setIntegral_condExp hmW_le hprod_int hC).symm
        _ = ∫ ω in C, (μ[(sφ n ∘ Y) | mW] * μ[(ψ ∘ Z) | mW]) ω ∂μ := by
              exact setIntegral_congr_ae (hmW_le _ hC) (by filter_upwards [h_rect_n n] with x hx _; exact hx)

    -- Limit passage n→∞ on both sides.
    -- LHS: DCT
    have hLHS :
      Filter.Tendsto (fun n => ∫ ω in C, ((sφ n ∘ Y) * (ψ ∘ Z)) ω ∂μ)
              Filter.atTop
              (nhds (∫ ω in C, ((φ ∘ Y) * (ψ ∘ Z)) ω ∂μ)) := by
      -- Apply DCT with bound Mφ * |ψ ∘ Z|
      have hψZ_int : Integrable (ψ ∘ Z) μ := by
        refine Integrable.of_mem_Icc (-Mψ) Mψ (hψ_meas.comp hZ).aemeasurable ?_
        filter_upwards [hψ_bdd] with ω hω
        simp only [Function.comp_apply, Set.mem_Icc]
        exact abs_le.mp hω

      -- Apply dominated convergence theorem with bound Mφ * ‖ψ ∘ Z‖
      refine tendsto_integral_filter_of_dominated_convergence
        (bound := fun ω => Mφ * ‖(ψ ∘ Z) ω‖) ?_ ?_ ?_ ?_

      -- Hypothesis 1: AEStronglyMeasurable for each n w.r.t. μ.restrict C
      · refine Filter.Eventually.of_forall (fun n => ?_)
        exact ((sφ n).measurable.comp hY).aestronglyMeasurable.mul (hψ_meas.comp hZ).aestronglyMeasurable

      -- Hypothesis 2: Dominated by bound a.e. w.r.t. μ.restrict C
      · refine Filter.Eventually.of_forall (fun n => ?_)
        refine ae_restrict_of_ae ?_
        filter_upwards [hφ_bdd] with ω hω_φ
        simp only [Function.comp_apply, Pi.mul_apply]
        calc ‖((sφ n ∘ Y) * (ψ ∘ Z)) ω‖
            = ‖(sφ n) (Y ω)‖ * ‖(ψ ∘ Z) ω‖ := norm_mul _ _
          _ = |(sφ n) (Y ω)| * ‖(ψ ∘ Z) ω‖ := by rw [Real.norm_eq_abs]
          _ ≤ |φ (Y ω)| * ‖(ψ ∘ Z) ω‖ := by apply mul_le_mul_of_nonneg_right (h_sφ_bdd n (Y ω)) (norm_nonneg _)
          _ ≤ Mφ * ‖(ψ ∘ Z) ω‖ := by apply mul_le_mul_of_nonneg_right hω_φ (norm_nonneg _)

      -- Hypothesis 3: Bound Mφ * ‖ψ ∘ Z‖ is integrable on C
      · exact (hψZ_int.norm.const_mul Mφ).integrableOn

      -- Hypothesis 4: Pointwise convergence a.e.
      · refine ae_restrict_of_ae ?_
        filter_upwards [] with ω
        apply Filter.Tendsto.mul
        · exact h_sφ_tendsto (Y ω)
        · exact tendsto_const_nhds

    -- RHS: convergence by dominated convergence theorem
    -- The conditional expectations μ[(sφ n ∘ Y) | mW] are uniformly bounded by Mφ,
    -- and μ[(ψ ∘ Z) | mW] is integrable, so DCT applies.
    have hRHS :
      Filter.Tendsto (fun n =>
          ∫ ω in C, (μ[(sφ n ∘ Y) | mW] * μ[(ψ ∘ Z) | mW]) ω ∂μ)
        Filter.atTop
        (nhds (∫ ω in C, (μ[(φ ∘ Y) | mW] * μ[(ψ ∘ Z) | mW]) ω ∂μ)) := by
      -- Integrability of μ[(ψ ∘ Z) | mW]
      have hψZ_ce_int : Integrable (μ[(ψ ∘ Z) | mW]) μ := integrable_condExp

      -- Key insight: h_int_n shows these two sequences are equal for all n.
      -- Since hLHS shows the LHS converges, the RHS must also converge (they're the same sequence!)
      -- We use L¹ convergence directly, without needing pointwise convergence.

      -- Step 1: Show L¹ convergence of conditional expectations
      have h_L1_conv : Filter.Tendsto (fun n => condExpL1 hmW_le μ ((sφ n) ∘ Y)) Filter.atTop
                                (nhds (condExpL1 hmW_le μ (φ ∘ Y))) := by
        apply tendsto_condExpL1_of_dominated_convergence hmW_le (fun ω => Mφ)
        · intro n
          exact ((sφ n).measurable.comp hY).aestronglyMeasurable
        · exact integrable_const Mφ
        · intro n
          filter_upwards [hφ_bdd] with ω hω
          calc ‖((sφ n) ∘ Y) ω‖
              = |(sφ n) (Y ω)| := by rw [Real.norm_eq_abs]; rfl
            _ ≤ |φ (Y ω)| := h_sφ_bdd n (Y ω)
            _ ≤ Mφ := hω
        · filter_upwards [] with ω
          exact h_sφ_tendsto (Y ω)

      -- Step 2: Show ψZ term is essentially bounded
      have hMψ_nn : 0 ≤ Mψ := by
        rcases hψ_bdd.exists with ⟨ω, hω⟩
        exact (abs_nonneg _).trans hω
      have hψZ_bdd : ∀ᵐ ω ∂μ, |μ[(ψ ∘ Z) | mW] ω| ≤ Mψ := by
        have h_bdd : ∀ᵐ ω ∂μ, |(ψ ∘ Z) ω| ≤ (⟨Mψ, hMψ_nn⟩ : NNReal) := by
          filter_upwards [hψ_bdd] with ω hω
          simpa using hω
        simpa [Real.norm_eq_abs] using
          ae_bdd_condExp_of_ae_bdd (m := mW) (R := ⟨Mψ, hMψ_nn⟩) h_bdd

      -- Step 3: Use bounded multiplication to show product converges in L¹, then get set integral convergence
      --
      -- PROOF STRATEGY (Hölder + L¹ convergence):
      --
      -- 1. h_L1_conv gives L¹ convergence: condExpL1 ((sφ n) ∘ Y) → condExpL1 (φ ∘ Y) in L¹
      --    This is equivalent to: ‖condExpL1 ((sφ n) ∘ Y) - condExpL1 (φ ∘ Y)‖₁ → 0
      --
      -- 2. Convert to conditional expectation (function) convergence using condExp_ae_eq_condExpL1:
      --    μ[(sφ n ∘ Y) | mW] =ᵐ[μ] condExpL1 hmW_le μ ((sφ n) ∘ Y)
      --
      -- 3. For products, use Hölder's inequality: ‖f * g‖₁ ≤ ‖f‖₁ * ‖g‖_∞
      --    Since hψZ_bdd gives: |μ[(ψ ∘ Z) | mW]| ≤ Mψ ae, we have ‖μ[(ψ ∘ Z) | mW]‖_∞ ≤ Mψ
      --    Thus: ‖(μ[(sφ n ∘ Y) | mW] - μ[(φ ∘ Y) | mW]) * μ[(ψ ∘ Z) | mW]‖₁
      --        ≤ ‖μ[(sφ n ∘ Y) | mW] - μ[(φ ∘ Y) | mW]‖₁ * Mψ → 0
      --
      -- 4. Apply tendsto_setIntegral_of_L1 to get set integral convergence from L¹ convergence
      --
      -- KEY MATHLIB LEMMAS:
      -- - condExp_ae_eq_condExpL1 : μ[f|m] =ᵐ[μ] condExpL1 hm μ f
      -- - eLpNorm_mul_le : Hölder for products (or Integrable.bdd_mul variants)
      -- - tendsto_setIntegral_of_L1 : L¹ convergence → set integral convergence
      -- - tendsto_Lp_iff_tendsto_eLpNorm' : convert Lp convergence to eLpNorm
      --
      -- IMPLEMENTATION NOTE: The main complexity is managing the ae equivalences and
      -- converting between condExpL1 (in L¹ space) and condExp (as functions).
      --
      -- APPROACH: Need to show product of condExps converges.
      -- Since h_L1_conv gives L¹ convergence of condExp (sφ n ∘ Y) → condExp (φ ∘ Y),
      -- and hψZ_bdd gives the bounded second factor μ[ψ∘Z|mW], we can use
      -- Integrable.tendsto_setIntegral_of_ae_tendsto_of_meas with product convergence.
      --
      -- The key steps:
      -- 1. Convert h_L1_conv from Lp convergence to ae pointwise (extract subsequence)
      -- 2. Use bounded multiplication: |condExp_n - condExp| * |bdd_factor| → 0 in L¹
      -- 3. Apply tendsto_setIntegral_of_L1 for set integral convergence
      --
      -- ISSUE: L¹ convergence ≠ pointwise convergence. Need different approach.
      -- Alternative: Use that h_int_n shows sequences equal, so if hLHS converges,
      -- RHS also converges (to some limit). Combined with tendsto_nhds_unique below.
      sorry

    -- Conclude by uniqueness of limits
    -- Since h_int_n shows the sequences are equal for all n, and both converge, their limits are equal
    have h_eq : (fun n => ∫ ω in C, ((sφ n ∘ Y) * (ψ ∘ Z)) ω ∂μ) =
                (fun n => ∫ ω in C, (μ[(sφ n ∘ Y) | mW] * μ[(ψ ∘ Z) | mW]) ω ∂μ) := by
      ext n; exact h_int_n n
    rw [← h_eq] at hRHS
    exact tendsto_nhds_unique hLHS hRHS

  -- Step 2: uniqueness of versions from set-integral equality on σ(W)-sets.
  -- Now we have: ∀ C ∈ σ(W), ∫_C (φY * ψZ) = ∫_C (μ[φY|W] * μ[ψZ|W])
  -- By uniqueness, this implies μ[φY * ψZ|W] =ᵐ μ[φY|W] * μ[ψZ|W]

  -- Use ae_eq_condExp_of_forall_setIntegral_eq: if g is mW-measurable and
  -- ∫_C g = ∫_C f for all mW-measurable sets C, then g =ᵐ μ[f|mW]

  -- Apply ae_eq_condExp_of_forall_setIntegral_eq
  -- This lemma says: if g is mW-measurable and ∫_C g = ∫_C f for all mW-measurable C,
  -- then g =ᵐ μ[f|mW]
  --
  -- Here: f = φ ∘ Y * ψ ∘ Z, g = μ[φ ∘ Y|mW] * μ[ψ ∘ Z|mW]
  -- We have: hC_sets gives ∫_C f = ∫_C g for all mW-measurable C
  -- Conclusion: g =ᵐ μ[f|mW], i.e., μ[φ ∘ Y|mW] * μ[ψ ∘ Z|mW] =ᵐ μ[φ ∘ Y * ψ ∘ Z|mW]

  -- First, establish integrability of f = φ ∘ Y * ψ ∘ Z
  have hφY_int : Integrable (φ ∘ Y) μ := by
    refine Integrable.of_mem_Icc (-Mφ) Mφ (hφ_meas.comp hY).aemeasurable ?_
    filter_upwards [hφ_bdd] with ω hω
    simp only [Function.comp_apply, Set.mem_Icc]
    exact abs_le.mp hω

  have hψZ_int : Integrable (ψ ∘ Z) μ := by
    refine Integrable.of_mem_Icc (-Mψ) Mψ (hψ_meas.comp hZ).aemeasurable ?_
    filter_upwards [hψ_bdd] with ω hω
    simp only [Function.comp_apply, Set.mem_Icc]
    exact abs_le.mp hω

  have hf_int : Integrable ((φ ∘ Y) * (ψ ∘ Z)) μ := by
    -- Product of bounded integrable functions: φ ∘ Y bounded a.e., ψ ∘ Z integrable
    -- Use Integrable.bdd_mul': requires hg integrable, hf ae strongly measurable, hf bounded a.e.
    refine Integrable.bdd_mul' (c := Mφ) hψZ_int (hφ_meas.comp hY).aestronglyMeasurable ?_
    -- Need: ∀ᵐ ω ∂μ, ‖(φ ∘ Y) ω‖ ≤ Mφ
    filter_upwards [hφ_bdd] with ω hω
    simp only [Function.comp_apply]
    rw [Real.norm_eq_abs]
    exact hω

  -- Apply the uniqueness characterization lemma (gives g =ᵐ μ[f|m], need symm)
  refine (ae_eq_condExp_of_forall_setIntegral_eq hmW_le hf_int ?_ ?_ ?_).symm

  -- Hypothesis 1: IntegrableOn for g on finite mW-measurable sets
  · intro s hs hμs
    haveI : Fact (μ s < ∞) := ⟨hμs⟩
    -- Conditional expectations are integrable
    have h1 : Integrable (μ[(φ ∘ Y) | mW]) μ := integrable_condExp
    have h2 : Integrable (μ[(ψ ∘ Z) | mW]) μ := integrable_condExp
    -- Product of integrable functions is integrable on whole space (finite measure)
    have hprod : Integrable (μ[(φ ∘ Y) | mW] * μ[(ψ ∘ Z) | mW]) μ := by
      -- Use Integrable.bdd_mul': product of integrable and bounded ae functions is integrable
      -- First, establish that μ[φ ∘ Y|mW] is bounded ae by Mφ
      have hMφ_nn : 0 ≤ Mφ := by
        rcases hφ_bdd.exists with ⟨ω, hω⟩
        exact (abs_nonneg _).trans hω
      have hφY_ce_bdd : ∀ᵐ ω ∂μ, |μ[(φ ∘ Y) | mW] ω| ≤ Mφ := by
        have h_bdd : ∀ᵐ ω ∂μ, |(φ ∘ Y) ω| ≤ (⟨Mφ, hMφ_nn⟩ : NNReal) := by
          filter_upwards [hφ_bdd] with ω hω
          simpa using hω
        simpa [Real.norm_eq_abs] using
          ae_bdd_condExp_of_ae_bdd (m := mW) (R := ⟨Mφ, hMφ_nn⟩) h_bdd
      -- Apply Integrable.bdd_mul': g integrable, f ae strongly measurable and bounded
      -- Use h1.aestronglyMeasurable since h1 : Integrable (μ[(φ ∘ Y) | mW]) μ
      refine h2.bdd_mul' (c := Mφ) h1.aestronglyMeasurable ?_
      filter_upwards [hφY_ce_bdd] with ω hω
      rw [Real.norm_eq_abs]
      exact hω
    -- Product integrable on whole space implies integrable on subset
    exact hprod.integrableOn

  -- Hypothesis 2: Set integral equality (from hC_sets)
  · intro s hs hμs
    exact (hC_sets s hs).symm

  -- Hypothesis 3: g is mW-measurable
  · -- Product of conditional expectations is mW-measurable
    refine AEStronglyMeasurable.mul ?_ ?_
    · exact stronglyMeasurable_condExp.aestronglyMeasurable
    · exact stronglyMeasurable_condExp.aestronglyMeasurable

/-- **Conditional independence extends to bounded measurable functions (monotone class).**

If Y ⊥⊥_W Z for indicators, then by approximation the factorization extends to all
bounded measurable functions.

**Mathematical content:** For bounded measurable f(Y) and g(Z):
E[f(Y)·g(Z)|σ(W)] = E[f(Y)|σ(W)]·E[g(Z)|σ(W)]

**Proof strategy:** Use monotone class theorem:
1. Simple functions are dense in bounded measurables
2. Conditional expectation is continuous w.r.t. bounded convergence
3. Approximate f, g by simple functions fₙ, gₙ
4. Pass to limit using dominated convergence

This is the key extension that enables proving measurability properties.
-/
lemma condIndep_boundedMeasurable (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Ω → α) (Z : Ω → β) (W : Ω → γ)
    (hCI : CondIndep μ Y Z W)
    (hY : Measurable Y) (hZ : Measurable Z) (hW : Measurable W)
    {φ : α → ℝ} {ψ : β → ℝ}
    (hφ_meas : Measurable φ) (hψ_meas : Measurable ψ)
    (Mφ Mψ : ℝ)
    (hφ_bdd : ∀ᵐ ω ∂μ, |φ (Y ω)| ≤ Mφ)
    (hψ_bdd : ∀ᵐ ω ∂μ, |ψ (Z ω)| ≤ Mψ) :
    μ[ (φ ∘ Y) * (ψ ∘ Z) | MeasurableSpace.comap W (by infer_instance) ] =ᵐ[μ]
    μ[ φ ∘ Y | MeasurableSpace.comap W (by infer_instance) ] *
    μ[ ψ ∘ Z | MeasurableSpace.comap W (by infer_instance) ] := by
  -- Strategy: Apply the left-extension lemma twice
  -- Step 1: Extend in φ (keeping ψ fixed) - this is condIndep_bddMeas_extend_left
  -- Step 2: The result already has φ bounded measurable, so we're done
  -- (Alternatively: could extend in ψ by symmetric argument)

  -- Apply the left extension directly
  exact condIndep_bddMeas_extend_left μ Y Z W hCI hY hZ hW hφ_meas hψ_meas Mφ Mψ hφ_bdd hψ_bdd

/-!
## Wrapper: Rectangle factorization implies conditional independence
-/

/-- **Rectangle factorization implies conditional independence.**

This is essentially the identity, since `CondIndep` is defined as rectangle factorization.
This wrapper allows replacing axioms in ViaMartingale.lean with concrete proofs. -/
lemma condIndep_of_rect_factorization (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Ω → α) (Z : Ω → β) (W : Ω → γ)
    (hRect :
      ∀ ⦃A B⦄, MeasurableSet A → MeasurableSet B →
        μ[ (Y ⁻¹' A).indicator (fun _ => (1:ℝ)) *
           (Z ⁻¹' B).indicator (fun _ => (1:ℝ)) | MeasurableSpace.comap W (by infer_instance) ]
          =ᵐ[μ]
        μ[(Y ⁻¹' A).indicator (fun _ => (1:ℝ)) | MeasurableSpace.comap W (by infer_instance)] *
        μ[(Z ⁻¹' B).indicator (fun _ => (1:ℝ)) | MeasurableSpace.comap W (by infer_instance)]) :
  CondIndep μ Y Z W :=
  hRect  -- CondIndep is defined as exactly this property

/-!
## Extension to product σ-algebras
-/

set_option maxHeartbeats 500000 in
/-- **Conditional expectation projection from conditional independence (helper).**

When Y ⊥⊥_W Z, conditioning on (Z,W) gives the same result as conditioning on W alone
for indicator functions of Y.

This is a key technical lemma used to prove the main projection theorem.
-/
lemma condExp_project_of_condIndep (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Ω → α) (Z : Ω → β) (W : Ω → γ)
    (hY : Measurable Y) (hZ : Measurable Z) (hW : Measurable W)
    (h_indep : CondIndep μ Y Z W)
    {A : Set α} (hA : MeasurableSet A) :
    μ[ Set.indicator (Y ⁻¹' A) (fun _ => (1 : ℝ))
       | MeasurableSpace.comap (fun ω => (Z ω, W ω)) (by infer_instance) ]
      =ᵐ[μ]
    μ[ Set.indicator (Y ⁻¹' A) (fun _ => (1 : ℝ))
       | MeasurableSpace.comap W (by infer_instance) ] := by
  -- Strategy: Use uniqueness characterization of conditional expectation
  -- Show that both CEs have the same integrals on all σ(W)-measurable sets

  -- 0) Name the ambient instance (no abbrev in tactic mode - use let but pin explicitly everywhere)
  let m0 : MeasurableSpace Ω := ‹MeasurableSpace Ω›

  -- Sub-σ-algebras as plain values (never instances)
  let mW := MeasurableSpace.comap W (by infer_instance)
  let mZW := MeasurableSpace.comap (fun ω => (Z ω, W ω)) (by infer_instance)
  let f := Set.indicator (Y ⁻¹' A) (fun _ => (1 : ℝ))

  -- σ-algebra ordering: σ(W) ⊆ σ(Z,W)
  have hle : mW ≤ mZW := by
    intro s hs
    obtain ⟨T, hT_meas, rfl⟩ := hs
    use Set.univ ×ˢ T
    constructor
    · exact MeasurableSet.univ.prod hT_meas
    · ext ω; simp [Set.mem_preimage, Set.mem_prod]

  -- Integrability
  have hf_int : Integrable f μ := by
    apply Integrable.indicator
    · exact integrable_const (1 : ℝ)
    · exact hY hA

  -- Key insight: Use tower property and apply uniqueness on σ(Z,W)
  -- We show μ[f|mW] has the same set integrals as f on all σ(Z,W)-sets

  -- σ-algebra orderings
  have hmZW_le : mZW ≤ _ := (hZ.prodMk hW).comap_le  -- σ(Z,W) ≤ 𝓜(Ω)

  -- μ[f|mW] is σ(W)-measurable, hence also σ(Z,W)-measurable (since mW ≤ mZW)
  have hgm : AEStronglyMeasurable[mZW] (μ[f | mW]) μ :=
    stronglyMeasurable_condExp.aestronglyMeasurable.mono hle

  -- For any S ∈ σ(Z,W): ∫_S μ[f|mW] = ∫_S f
  -- Use Dynkin π-λ theorem: define C(s) := "integrals match on s"
  have hg_eq : ∀ s : Set Ω, MeasurableSet[mZW] s → μ s < ∞ →
      ∫ x in s, (μ[f | mW]) x ∂μ = ∫ x in s, f x ∂μ := by
    -- First show: σ(Z,W) is generated by rectangles Z⁻¹(B) ∩ W⁻¹(C)
    have mZW_gen : mZW = MeasurableSpace.generateFrom
        {s | ∃ (B : Set β) (C : Set γ), MeasurableSet B ∧ MeasurableSet C ∧
             s = Z ⁻¹' B ∩ W ⁻¹' C} := by
      -- σ(Z,W) = comap (Z,W) (σ(β×γ))
      -- σ(β×γ) = generateFrom {B ×ˢ C | ...} by generateFrom_prod
      -- comap commutes with generateFrom
      unfold mZW
      conv_lhs => arg 2; rw [← generateFrom_prod (α := β) (β := γ)]
      rw [MeasurableSpace.comap_generateFrom]
      congr 1
      ext s
      constructor
      · intro ⟨t, ht_mem, ht_eq⟩
        -- t ∈ image2 (· ×ˢ ·) ... means ∃ B C, t = B ×ˢ C
        -- ht_mem : t ∈ image2 (·×ˢ·) {B | MeasurableSet B} {C | MeasurableSet C}
        simp only [Set.mem_image2, Set.mem_setOf_eq] at ht_mem
        obtain ⟨B, hB, C, hC, rfl⟩ := ht_mem
        use B, C, hB, hC
        -- Need: (Z,W)⁻¹(B ×ˢ C) = Z⁻¹B ∩ W⁻¹C
        rw [← ht_eq]
        ext ω
        simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_prod]
      · intro ⟨B, C, hB, hC, hs_eq⟩
        -- s = Z⁻¹B ∩ W⁻¹C, need to show it's in the preimage image
        simp only [Set.mem_image, Set.mem_image2, Set.mem_setOf_eq]
        use B ×ˢ C
        refine ⟨⟨B, hB, C, hC, rfl⟩, ?_⟩
        rw [hs_eq]
        ext ω
        simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_prod]

    -- Rectangles form a π-system
    have h_pi : IsPiSystem {s | ∃ (B : Set β) (C : Set γ), MeasurableSet B ∧ MeasurableSet C ∧
                                   s = Z ⁻¹' B ∩ W ⁻¹' C} := by
      -- Need to show: intersection of two rectangles is a rectangle
      intro s₁ hs₁ s₂ hs₂ _
      obtain ⟨B₁, C₁, hB₁, hC₁, rfl⟩ := hs₁
      obtain ⟨B₂, C₂, hB₂, hC₂, rfl⟩ := hs₂
      -- (Z⁻¹B₁ ∩ W⁻¹C₁) ∩ (Z⁻¹B₂ ∩ W⁻¹C₂) = Z⁻¹(B₁ ∩ B₂) ∩ W⁻¹(C₁ ∩ C₂)
      use B₁ ∩ B₂, C₁ ∩ C₂
      refine ⟨hB₁.inter hB₂, hC₁.inter hC₂, ?_⟩
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_preimage]
      tauto

    -- Apply π-λ induction
    intro s hs hμs
    apply MeasurableSpace.induction_on_inter (C := fun s _ => ∫ x in s, (μ[f | mW]) x ∂μ = ∫ x in s, f x ∂μ)
      mZW_gen h_pi

    · -- Empty set
      simp

    · -- Basic case: rectangles Z⁻¹(B) ∩ W⁻¹(C)
      intro t ht
      obtain ⟨B, C, hB, hC, rfl⟩ := ht
      -- Strategy: Use that Z⁻¹B ∩ W⁻¹C is in mZW, so by tower property and setIntegral_condExp
      -- Key: Z⁻¹B ∩ W⁻¹C ∈ σ(Z,W), so ∫_{Z⁻¹B ∩ W⁻¹C} μ[f|mZW] = ∫_{Z⁻¹B ∩ W⁻¹C} f
      -- And we'll show ∫_{Z⁻¹B ∩ W⁻¹C} μ[f|mW] = ∫_{Z⁻¹B ∩ W⁻¹C} μ[f|mZW]

      classical

      -- 1) Ambient measurability, explicitly pinned to m0
      have hZ_m0 : @Measurable Ω β m0 _ Z := by simpa [m0] using hZ
      have hW_m0 : @Measurable Ω γ m0 _ W := by simpa [m0] using hW

      have hBpre_m0 : @MeasurableSet Ω m0 (Z ⁻¹' B) := hB.preimage hZ_m0
      have hCpre_m0 : @MeasurableSet Ω m0 (W ⁻¹' C) := hC.preimage hW_m0

      -- Sub-σ-algebra ordering
      have hmW_le : mW ≤ m0 := hW_m0.comap_le

      -- mZW-measurable versions of Z and W (by construction of comap)
      have hZ_mZW : @Measurable Ω β mZW _ Z := measurable_fst.comp (Measurable.of_comap_le le_rfl)
      have hW_mZW : @Measurable Ω γ mZW _ W := measurable_snd.comp (Measurable.of_comap_le le_rfl)

      -- mW-measurable version of W (by construction of mW := comap W)
      have hW_mW : @Measurable Ω γ mW _ W := Measurable.of_comap_le le_rfl

      have hBpre : @MeasurableSet Ω mZW (Z ⁻¹' B) := hB.preimage hZ_mZW
      have hCpre_mZW : @MeasurableSet Ω mZW (W ⁻¹' C) := hC.preimage hW_mZW
      have hCpre : @MeasurableSet Ω mW (W ⁻¹' C) := hC.preimage hW_mW

      -- Convenience name for indicator on Z⁻¹B (f is already defined in outer scope)
      set gB : Ω → ℝ := (Z ⁻¹' B).indicator (fun _ => (1 : ℝ)) with hgB_def

      -- gB measurability
      have hsm_gB : @StronglyMeasurable Ω ℝ _ m0 gB :=
        stronglyMeasurable_const.indicator hBpre_m0

      -- CE basic facts
      have hsm_ce_mW : @StronglyMeasurable Ω ℝ _ mW (μ[f | mW]) :=
        stronglyMeasurable_condExp
      have hInt_ce : Integrable (μ[f | mW]) μ :=
        integrable_condExp

      -- AE version (for use later, keep mW-measurable)
      have haesm_ce : @AEStronglyMeasurable Ω ℝ _ mW _ (μ[f | mW]) μ :=
        hsm_ce_mW.aestronglyMeasurable

      -- Canonical product ↔ indicator identity (use often)
      have h_mul_eq_indicator :
          (fun ω => μ[f|mW] ω * gB ω) = (Z ⁻¹' B).indicator (μ[f|mW]) := by
        funext ω; by_cases hω : ω ∈ Z ⁻¹' B
        · simp [hgB_def, hω, Set.indicator_of_mem hω, mul_one]
        · simp [hgB_def, hω, Set.indicator_of_notMem hω, mul_zero]

      -- Product integrability: rewrite to indicator, then use Integrable.indicator
      have hint_prod : Integrable (fun ω => μ[f | mW] ω * gB ω) μ := by
        simpa [h_mul_eq_indicator] using hInt_ce.indicator hBpre_m0

      -- Rectangle is in mZW
      have hrect : MeasurableSet[mZW] (Z ⁻¹' B ∩ W ⁻¹' C) := by
        -- Z⁻¹B ∩ W⁻¹C = (Z,W)⁻¹(B ×ˢ C)
        have : Z ⁻¹' B ∩ W ⁻¹' C = (fun ω => (Z ω, W ω)) ⁻¹' (B ×ˢ C) := by
          ext ω
          simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_prod]
        rw [this]
        exact measurableSet_preimage (Measurable.of_comap_le le_rfl) (hB.prod hC)

      -- By setIntegral_condExp on mZW
      have h1 : ∫ x in Z ⁻¹' B ∩ W ⁻¹' C, (μ[f | mZW]) x ∂μ = ∫ x in Z ⁻¹' B ∩ W ⁻¹' C, f x ∂μ := by
        exact setIntegral_condExp hmZW_le hf_int hrect

      -- By tower property: E[E[f|mZW]|mW] = E[f|mW] (since mW ≤ mZW)
      have h2 : μ[μ[f | mZW] | mW] =ᵐ[μ] μ[f | mW] := by
        exact condExp_condExp_of_le hle hmZW_le

      -- So ∫_{rectangle} E[f|mW] = ∫_{rectangle} E[E[f|mZW]|mW]
      have h3 : ∫ x in Z ⁻¹' B ∩ W ⁻¹' C, (μ[f | mW]) x ∂μ =
                ∫ x in Z ⁻¹' B ∩ W ⁻¹' C, (μ[μ[f | mZW] | mW]) x ∂μ := by
        apply setIntegral_congr_ae (hmZW_le _ hrect)
        filter_upwards [h2] with x hx _
        exact hx.symm

      -- Now combine: ∫ μ[f|mW] = ∫ μ[μ[f|mZW]|mW] (by h3), and we want ∫ μ[f|mW] = ∫ f
      calc ∫ x in Z ⁻¹' B ∩ W ⁻¹' C, (μ[f | mW]) x ∂μ
          = ∫ x in Z ⁻¹' B ∩ W ⁻¹' C, (μ[μ[f | mZW] | mW]) x ∂μ := h3
        _ = ∫ x in Z ⁻¹' B ∩ W ⁻¹' C, f x ∂μ := by
          -- Key: Use CondIndep to show ∫_{Z⁻¹B ∩ W⁻¹C} μ[μ[f|mZW]|mW] = ∫_{Z⁻¹B ∩ W⁻¹C} f
          -- By tower property h2, μ[μ[f|mZW]|mW] =ᵐ μ[f|mW], so enough to show ∫_{rect} μ[f|mW] = ∫_{rect} f

          -- Rewrite LHS using h2
          have : ∫ x in Z ⁻¹' B ∩ W ⁻¹' C, (μ[μ[f | mZW] | mW]) x ∂μ =
                 ∫ x in Z ⁻¹' B ∩ W ⁻¹' C, (μ[f | mW]) x ∂μ := by
            apply setIntegral_congr_ae (hmZW_le _ hrect)
            filter_upwards [h2] with x hx _
            exact hx
          rw [this]

          -- Now show: ∫_{Z⁻¹B ∩ W⁻¹C} μ[f|mW] = ∫_{Z⁻¹B ∩ W⁻¹C} f
          -- Strategy: Use CondIndep to factor through W⁻¹C

          -- Apply CondIndep to sets A and B
          have hCI := h_indep A B hA hB
          -- Gives: E[1_A(Y) · 1_B(Z) | σ(W)] =ᵐ E[1_A(Y) | σ(W)] · E[1_B(Z) | σ(W)]

          -- W⁻¹C is σ(W)-measurable
          have hC_meas : MeasurableSet[mW] (W ⁻¹' C) := by
            exact measurableSet_preimage (Measurable.of_comap_le le_rfl) hC

          -- Integrability of gB (already defined at top of rectangle case)
          have hint_B : Integrable gB μ := by
            apply Integrable.indicator
            · exact integrable_const 1
            · exact hBpre_m0

          -- Integrability of f * gB: f · gB = f · 1_{Z⁻¹B} = f restricted to Z⁻¹B
          have hprod_int : Integrable (f * gB) μ := by
            -- f * gB = (Y⁻¹A).indicator(1) * (Z⁻¹B).indicator(1)
            -- This is bounded by 1, so integrable
            have : (f * gB) = (Y ⁻¹' A ∩ Z ⁻¹' B).indicator (fun _ => (1 : ℝ)) := by
              funext ω
              simp only [Pi.mul_apply, f, gB, Set.indicator_apply]
              by_cases hY : ω ∈ Y ⁻¹' A <;> by_cases hZ : ω ∈ Z ⁻¹' B
              · simp [hY, hZ, Set.mem_inter_iff]
              · simp [hY, hZ, Set.mem_inter_iff]
              · simp [hY, hZ, Set.mem_inter_iff]
              · simp [hY, hZ, Set.mem_inter_iff]
            rw [this]
            apply Integrable.indicator
            · exact integrable_const 1
            · exact (hY hA).inter (hZ hB)

          -- Chain of equalities: ∫_{Z⁻¹B ∩ W⁻¹C} μ[f|mW] = ∫_{Z⁻¹B ∩ W⁻¹C} f

          -- Helper: W⁻¹C is measurable in m0 (already defined above, but re-proving for clarity)
          -- (Actually, use the one from the prelude - this line is redundant)

          calc ∫ x in Z ⁻¹' B ∩ W ⁻¹' C, (μ[f | mW]) x ∂μ
              = ∫ x in W ⁻¹' C, (μ[f | mW] * gB) x ∂μ := by
                -- Rewrite using indicator: ∫_{W⁻¹C ∩ Z⁻¹B} μ[f|mW] = ∫_{W⁻¹C} (μ[f|mW] * gB)
                -- First: LHS = ∫_{W⁻¹C} (Z⁻¹B).indicator(μ[f|mW])
                have h1 : ∫ ω in W ⁻¹' C ∩ Z ⁻¹' B, μ[f|mW] ω ∂μ
                        = ∫ ω in W ⁻¹' C, (Z ⁻¹' B).indicator (μ[f|mW]) ω ∂μ := by
                  rw [setIntegral_indicator hBpre_m0]
                -- Second: RHS uses h_mul_eq_indicator
                have h2 : ∫ ω in W ⁻¹' C, (Z ⁻¹' B).indicator (μ[f|mW]) ω ∂μ
                        = ∫ ω in W ⁻¹' C, (μ[f|mW] ω * gB ω) ∂μ := by
                  congr 1
                  exact h_mul_eq_indicator.symm
                -- Combine
                rw [Set.inter_comm]
                exact h1.trans h2
            _ = ∫ x in W ⁻¹' C, (μ[f | mW] * μ[gB | mW]) x ∂μ := by
                -- Key: For σ(W)-measurable h: μ[h · g|σ(W)] =ᵐ h · μ[g|σ(W)]
                -- Since μ[f|mW] is mW-measurable, integrating over W⁻¹C ∈ mW gives equality
                have h_pull : μ[(μ[f | mW]) * gB | mW] =ᵐ[μ] (μ[f | mW]) * μ[gB | mW] := by
                  refine condExp_mul_of_aestronglyMeasurable_left ?_ ?_ hint_B
                  · exact haesm_ce
                  · -- Product: bounded measurable * integrable = integrable
                    -- Use hint_prod from prelude
                    exact hint_prod
                -- Apply setIntegral_condExp and the pull-out property
                calc ∫ x in W ⁻¹' C, (μ[f | mW] * gB) x ∂μ
                    = ∫ x in W ⁻¹' C, (μ[(μ[f | mW]) * gB | mW]) x ∂μ := by
                      -- Use setIntegral_condExp: ∫_{W⁻¹C} μ[h|mW] = ∫_{W⁻¹C} h for W⁻¹C ∈ mW
                      -- Avoids needing to prove (μ[f|mW]) * gB is mW-measurable
                      have h_set_eq :
                          ∫ x in W ⁻¹' C, μ[(μ[f | mW]) * gB | mW] x ∂μ
                        = ∫ x in W ⁻¹' C, ((μ[f | mW]) * gB) x ∂μ := by
                        simpa using
                          (setIntegral_condExp (μ := μ) (m := mW)
                            (hm := hmW_le) (hs := hCpre) (hf := hint_prod))
                      exact h_set_eq.symm
                  _ = ∫ x in W ⁻¹' C, ((μ[f | mW]) * μ[gB | mW]) x ∂μ := by
                      exact setIntegral_congr_ae (hmW_le _ hC_meas) (by filter_upwards [h_pull] with x hx _; exact hx)
            _ = ∫ x in W ⁻¹' C, (μ[f * gB | mW]) x ∂μ := by
                -- Reverse CondIndep factorization: E[f|mW] · E[gB|mW] =ᵐ E[f · gB|mW]
                -- Use hCI which states: μ[f · gB | mW] =ᵐ μ[f | mW] · μ[gB | mW]
                exact setIntegral_congr_ae (hmW_le _ hC_meas) (by filter_upwards [hCI] with x hx _; exact hx.symm)
            _ = ∫ x in W ⁻¹' C, (f * gB) x ∂μ := by
                -- Apply setIntegral_condExp
                exact setIntegral_condExp hmW_le hprod_int hC_meas
            _ = ∫ x in Z ⁻¹' B ∩ W ⁻¹' C, f x ∂μ := by
                -- Reverse the indicator rewrite: ∫_{W⁻¹C} f·gB = ∫_{W⁻¹C ∩ Z⁻¹B} f
                -- First: prove pointwise equality f * gB = (Z⁻¹B).indicator f
                have h_fg_indicator : (fun ω => f ω * gB ω) = (Z ⁻¹' B).indicator f := by
                  funext ω; by_cases hω : ω ∈ Z ⁻¹' B
                  · simp [hgB_def, hω, Set.indicator_of_mem hω, mul_one]
                  · simp [hgB_def, hω, Set.indicator_of_notMem hω, mul_zero]
                -- Second: rewrite integral
                calc ∫ ω in W ⁻¹' C, (f ω * gB ω) ∂μ
                    = ∫ ω in W ⁻¹' C, (Z ⁻¹' B).indicator f ω ∂μ := by
                      congr 1
                  _ = ∫ ω in W ⁻¹' C ∩ Z ⁻¹' B, f ω ∂μ := by
                      rw [setIntegral_indicator hBpre_m0]
                  _ = ∫ ω in Z ⁻¹' B ∩ W ⁻¹' C, f ω ∂μ := by
                      rw [Set.inter_comm]

    · -- Complement
      intro t htm ht_ind
      -- For complement: ∫_{t} g + ∫_{tᶜ} g = ∫_Ω g, so ∫_{tᶜ} g = ∫_Ω g - ∫_t g
      have h_add : ∫ x in t, (μ[f | mW]) x ∂μ + ∫ x in tᶜ, (μ[f | mW]) x ∂μ = ∫ x, (μ[f | mW]) x ∂μ := by
        exact integral_add_compl₀ (hmZW_le _ htm).nullMeasurableSet integrable_condExp
      have h_add' : ∫ x in t, f x ∂μ + ∫ x in tᶜ, f x ∂μ = ∫ x, f x ∂μ := by
        exact integral_add_compl₀ (hmZW_le _ htm).nullMeasurableSet hf_int
      -- ht_ind is the equality for t, use it to substitute in h_add
      rw [ht_ind] at h_add
      -- Now we have: ∫_t f + ∫_{tᶜ} E[f|mW] = ∫ E[f|mW]
      -- And we know: ∫_t f + ∫_{tᶜ} f = ∫ f
      -- Also: ∫ E[f|mW] = ∫ f (by conditional expectation property)
      have h_total : ∫ x, (μ[f | mW]) x ∂μ = ∫ x, f x ∂μ := by
        -- Use integral_condExp: ∫ μ[f|m] = ∫ f
        -- Requires SigmaFinite (μ.trim hle_amb), which follows from IsProbabilityMeasure
        -- Chain: IsProbabilityMeasure → IsFiniteMeasure → IsFiniteMeasure.trim → SigmaFinite.trim
        have hle_amb : mW ≤ _ := le_trans hle hmZW_le
        exact integral_condExp hle_amb
      linarith

    · -- Countable disjoint union
      intro t_seq hdisjoint htm_seq ht_ind_seq
      -- For disjoint union: ∫_{⋃ᵢ tᵢ} g = Σᵢ ∫_{tᵢ} g
      -- Use HasSum for both sides and show they're equal term by term
      -- Convert Disjoint to proper form for hasSum_integral_iUnion
      have hd : Pairwise (Function.onFun Disjoint t_seq) := hdisjoint
      -- Each t_seq i is measurable in ambient space since mZW ≤ ambient
      have h1 := hasSum_integral_iUnion (fun i => hmZW_le _ (htm_seq i)) hd
        (integrable_condExp : Integrable (μ[f | mW]) μ).integrableOn
      have h2 := hasSum_integral_iUnion (fun i => hmZW_le _ (htm_seq i)) hd hf_int.integrableOn
      -- Show the terms are equal using ht_ind_seq, so the sums are equal by uniqueness
      have h_eq : (fun i => ∫ x in t_seq i, (μ[f | mW]) x ∂μ) = (fun i => ∫ x in t_seq i, f x ∂μ) :=
        funext ht_ind_seq
      exact h1.unique (h_eq ▸ h2)

    · exact hs

  -- Apply uniqueness: μ[f|mW] =ᵐ μ[f|mZW]
  exact (ae_eq_condExp_of_forall_setIntegral_eq hmZW_le hf_int
    (fun _ _ _ => integrable_condExp.integrableOn) hg_eq hgm).symm

/-- **Conditional expectation projection from conditional independence.**

When Y ⊥⊥_W Z, conditioning on (Z,W) gives the same result as conditioning on W alone
for functions of Y.

**Key insight:** Conditional independence means that knowing Z provides no additional
information about Y beyond what W already provides. Therefore E[f(Y)|σ(Z,W)] = E[f(Y)|σ(W)].

**Proof strategy:**
1. By uniqueness, suffices to show integrals match on σ(W)-sets
2. For S ∈ σ(W), we have S ∈ σ(Z,W) since σ(W) ≤ σ(Z,W)
3. So ∫_S E[f(Y)|σ(Z,W)] = ∫_S f(Y) by conditional expectation property
4. And ∫_S E[f(Y)|σ(W)] = ∫_S f(Y) by conditional expectation property
5. Therefore the integrals match, giving the result

**Alternative via conditional independence definition:**
- Can show E[f(Y)|σ(Z,W)] is σ(W)-measurable by using the factorization from CondIndep
- Then apply that conditional expectation of a σ(W)-measurable function w.r.t. σ(W) is identity

TODO: Complete this proof using the integral-matching strategy.
-/
theorem condIndep_project (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Ω → α) (Z : Ω → β) (W : Ω → γ)
    (hY : Measurable Y) (hZ : Measurable Z) (hW : Measurable W)
    (h_indep : CondIndep μ Y Z W)
    {A : Set α} (hA : MeasurableSet A) :
    μ[ Set.indicator (Y ⁻¹' A) (fun _ => (1 : ℝ))
       | MeasurableSpace.comap (fun ω => (Z ω, W ω)) (by infer_instance) ]
      =ᵐ[μ]
    μ[ Set.indicator (Y ⁻¹' A) (fun _ => (1 : ℝ))
       | MeasurableSpace.comap W (by infer_instance) ] := by
  -- This follows directly from the helper lemma
  exact condExp_project_of_condIndep μ Y Z W hY hZ hW h_indep hA

/-!
### Kallenberg 1.3: Indicator Conditional Independence from Drop-Info

Infrastructure for deriving conditional independence from distributional equality
via the "drop information" property for Y.

Note: Helper lemmas `integrable_mul_of_bound_one` and `condExp_indicator_ae_bound_one`
are available from `CondExpHelpers.lean`.
-/

