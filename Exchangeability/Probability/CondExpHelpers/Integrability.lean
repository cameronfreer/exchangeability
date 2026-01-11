/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Unique
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Independence.Conditional

/-!
# Integrability and σ-algebra Factorization for Conditional Expectation

This file provides integrability lemmas, uniqueness arguments, and σ-algebra factorization
lemmas for conditional expectations.

## Main results

* `integrable_mul_of_bound_one`: Product with bounded factor is integrable
* `abs_condExp_le_condExp_abs`: Jensen's inequality for conditional expectation
* `condExp_indicator_ae_bound_one`: CE of indicator is a.e. in [0,1]
* `condExp_ae_unique_of_ae_eq`: Uniqueness of CE via L¹
* `sigma_factor_le`: Pullback σ-algebra inequality for factorizations
* `MeasureTheory.condExp_project_of_le`: Tower/projection property
-/

noncomputable section
open scoped MeasureTheory ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set

/-!
## Integrability of products with bounded factors
-/

/-- If `f ∈ L¹(μ)` and `g` is a.e. bounded by `1`, then `g⋅f ∈ L¹(μ)`. -/
lemma integrable_mul_of_bound_one
  {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  {f g : Ω → ℝ}
  (hf : Integrable f μ)
  (hg_meas : AEStronglyMeasurable g μ)
  (hbound : ∀ᵐ ω ∂μ, ‖g ω‖ ≤ (1 : ℝ)) :
  Integrable (fun ω => g ω * f ω) μ := hf.bdd_mul hg_meas hbound

/-- **Jensen's inequality for conditional expectation**: the absolute value of a conditional
expectation is a.e. bounded by the conditional expectation of the absolute value.

For integrable `f`: `|μ[f|m]| ≤ μ[|f||m]` almost everywhere.
-/
@[nolint unusedArguments]
lemma abs_condExp_le_condExp_abs
    {Ω : Type*} {m m₀ : MeasurableSpace Ω} {μ : Measure Ω}
    (hm : m ≤ m₀) [SigmaFinite (μ.trim hm)]
    {f : Ω → ℝ}
    (hf : Integrable f μ) :
    ∀ᵐ ω ∂μ, |(μ[f|m]) ω| ≤ (μ[(fun ω => |f ω|)|m]) ω := by
  -- Upper bound: μ[f|m] ≤ μ[|f||m]
  have h_up : μ[f|m] ≤ᵐ[μ] μ[(fun ω => |f ω|)|m] := by
    refine condExp_mono hf ?_ ?_
    · exact hf.abs
    · apply Filter.Eventually.of_forall
      intro ω; exact le_abs_self _
  -- Lower bound: -μ[|f||m] ≤ μ[f|m]
  -- Proof: f ≥ -|f| pointwise, so μ[f|m] ≥ μ[-|f||m] = -μ[|f||m]
  have h_low : (fun ω => -(μ[(fun ω => |f ω|)|m]) ω) ≤ᵐ[μ] μ[f|m] := by
    have neg_abs_bound : (fun ω => -(|f ω|)) ≤ᵐ[μ] f := by
      apply Filter.Eventually.of_forall
      intro ω; exact neg_abs_le _
    have ce_ineq : μ[(fun ω => -(|f ω|))|m] ≤ᵐ[μ] μ[f|m] :=
      condExp_mono hf.abs.neg hf neg_abs_bound
    have neg_eq : (fun ω => -(μ[(fun ω => |f ω|)|m]) ω) =ᵐ[μ] μ[(fun ω => -(|f ω|))|m] :=
      (condExp_neg (fun ω => |f ω|) m).symm
    exact neg_eq.le.trans ce_ineq
  -- Combine: |x| ≤ y iff -y ≤ x ≤ y
  filter_upwards [h_up, h_low] with ω hup hlow
  rw [abs_le]
  exact ⟨hlow, hup⟩

/-- The conditional expectation of an indicator (ℝ-valued) is a.e. in `[0,1]`. -/
lemma condExp_indicator_ae_bound_one
  {Ω β : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
  {mW : MeasurableSpace Ω} (hm : mW ≤ m0)
  {Z : Ω → β} [MeasurableSpace β] {B : Set β}
  (hZ : @Measurable Ω β m0 _ Z) (hB : MeasurableSet B) :
  ∀ᵐ ω ∂μ,
    0 ≤ MeasureTheory.condExp mW μ
          (fun ω => (Set.indicator (Z ⁻¹' B) (fun _ => (1 : ℝ)) ω)) ω
    ∧
    MeasureTheory.condExp mW μ
          (fun ω => (Set.indicator (Z ⁻¹' B) (fun _ => (1 : ℝ)) ω)) ω ≤ 1 := by
  classical
  -- Pointwise bounds for the integrand: 0 ≤ 1_B ≤ 1.
  have h0 : ∀ᵐ ω ∂μ, (0 : ℝ) ≤ Set.indicator (Z ⁻¹' B) (fun _ => (1 : ℝ)) ω :=
    .of_forall fun ω => Set.indicator_nonneg (fun _ _ => zero_le_one) ω
  have h1 : ∀ᵐ ω ∂μ, Set.indicator (Z ⁻¹' B) (fun _ => (1 : ℝ)) ω ≤ (1 : ℝ) :=
    .of_forall fun ω => Set.indicator_le_self' (fun _ _ => zero_le_one) ω
  -- Integrability of the indicator
  have h_ind_int : Integrable (Set.indicator (Z ⁻¹' B) (fun _ => (1 : ℝ))) μ := by
    have : @MeasurableSet Ω m0 (Z ⁻¹' B) := hZ hB
    exact (integrable_const (1 : ℝ)).indicator this
  -- Use condExp_mono
  have hCE0 : μ[fun _ => (0 : ℝ) | mW] ≤ᵐ[μ] μ[Set.indicator (Z ⁻¹' B) (fun _ => (1 : ℝ)) | mW] :=
    condExp_mono (integrable_const _) h_ind_int h0
  have hCE1 : μ[Set.indicator (Z ⁻¹' B) (fun _ => (1 : ℝ)) | mW] ≤ᵐ[μ] μ[fun _ => (1 : ℝ) | mW] :=
    condExp_mono h_ind_int (integrable_const _) h1
  -- Pack using condExp_const to simplify constant expectations
  filter_upwards [hCE0, hCE1] with ω h0' h1'
  simp only [condExp_const hm (0 : ℝ), condExp_const hm (1 : ℝ)] at h0' h1'
  exact ⟨h0', h1'⟩

/-- **Uniqueness of the conditional expectation via L¹**:
if the underlying integrands agree a.e., then `condExp` agrees a.e.
We do *not* require full-sequence a.e. convergence; L¹ is enough. -/
lemma condExp_ae_unique_of_ae_eq
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  {mW : MeasurableSpace Ω} (hmW_le : mW ≤ mΩ) [SigmaFinite (μ.trim hmW_le)]
  {f g : Ω → ℝ} (hfg : f =ᵐ[μ] g) :
  MeasureTheory.condExp mW μ f =ᵐ[μ] MeasureTheory.condExp mW μ g := by
  classical
  -- Step 1: L¹-level equality of the conditional expectations
  have hL1 :
      (MeasureTheory.condExpL1 hmW_le μ f : Ω →₁[μ] ℝ)
    = (MeasureTheory.condExpL1 hmW_le μ g : Ω →₁[μ] ℝ) := by
    simp [MeasureTheory.condExpL1_congr_ae hmW_le hfg]
  -- Step 2: bridge `condExp =ᵐ ↑condExpL1` on both sides
  have hf :
      MeasureTheory.condExp mW μ f
      =ᵐ[μ] ((MeasureTheory.condExpL1 hmW_le μ f : Ω →₁[μ] ℝ) : Ω → ℝ) :=
    MeasureTheory.condExp_ae_eq_condExpL1 hmW_le f
  have hg :
      MeasureTheory.condExp mW μ g
      =ᵐ[μ] ((MeasureTheory.condExpL1 hmW_le μ g : Ω →₁[μ] ℝ) : Ω → ℝ) :=
    MeasureTheory.condExp_ae_eq_condExpL1 hmW_le g
  -- Step 3: conclude
  calc MeasureTheory.condExp mW μ f
      =ᵐ[μ] ((MeasureTheory.condExpL1 hmW_le μ f : Ω →₁[μ] ℝ) : Ω → ℝ) := hf
    _ = ((MeasureTheory.condExpL1 hmW_le μ g : Ω →₁[μ] ℝ) : Ω → ℝ) := by simp [hL1]
    _ =ᵐ[μ] MeasureTheory.condExp mW μ g := hg.symm

/-- Drop-in replacement for sequence-based uniqueness:
it *only* needs L¹ convergence to the same target and `f =ᵐ g`. -/
@[nolint unusedArguments]
lemma tendsto_condExp_unique_L1
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  {mW : MeasurableSpace Ω} (hmW_le : mW ≤ mΩ) [SigmaFinite (μ.trim hmW_le)]
  {fs gs : ℕ → Ω → ℝ} {f g : Ω → ℝ}
  (_hfs : Filter.Tendsto
           (fun n => (MeasureTheory.condExpL1 hmW_le μ (fs n) : Ω →₁[μ] ℝ))
           Filter.atTop (nhds (MeasureTheory.condExpL1 hmW_le μ f)))
  (_hgs : Filter.Tendsto
           (fun n => (MeasureTheory.condExpL1 hmW_le μ (gs n) : Ω →₁[μ] ℝ))
           Filter.atTop (nhds (MeasureTheory.condExpL1 hmW_le μ g)))
  (hfg : f =ᵐ[μ] g) :
  MeasureTheory.condExp mW μ f =ᵐ[μ] MeasureTheory.condExp mW μ g :=
  condExp_ae_unique_of_ae_eq hmW_le hfg

/-!
## σ-algebra factorization
-/

/-- **Pullback σ-algebra inequality for factorizations.**

If `η = g ∘ ζ` with `g` measurable, then the σ-algebra generated by `η`
is contained in the σ-algebra generated by `ζ`.

This is the fundamental fact about σ-algebra factorization: knowing `ζ` gives
you at least as much information as knowing `η = g(ζ)`.

**Mathematical statement:** σ(η) ≤ σ(ζ) when η = g ∘ ζ.
-/
@[nolint unusedArguments]
lemma sigma_factor_le {Ω α β : Type*}
    [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
    {η : Ω → α} {ζ : Ω → β} {g : β → α}
    (hη : η = g ∘ ζ) (hg : Measurable g) :
    MeasurableSpace.comap η inferInstance ≤ MeasurableSpace.comap ζ inferInstance := by
  -- Key idea: η = g ∘ ζ with g measurable implies σ(η) ≤ σ(ζ)
  -- Every η-measurable set has form η⁻¹(t) = (g∘ζ)⁻¹(t) = ζ⁻¹(g⁻¹(t))
  intro s hs
  -- hs : s ∈ σ(η) means s = η⁻¹(t) for some measurable t
  obtain ⟨t, ht, rfl⟩ := hs
  -- Rewrite using hη: η⁻¹(t) = ζ⁻¹(g⁻¹(t))
  rw [hη, Set.preimage_comp]
  -- Goal: ζ⁻¹(g⁻¹(t)) ∈ σ(ζ)
  exact ⟨g ⁻¹' t, hg ht, rfl⟩

namespace MeasureTheory

/-- **Conditional expectation projection property.**

If m ≤ m' are sub-σ-algebras, then projecting from m' down to m via conditional
expectation is idempotent: μ[μ[f|m']|m] = μ[f|m] almost everywhere.

**Mathematical content:** This is the "tower property" or "projection property" for
conditional expectations. It says that conditioning twice (first on the finer σ-algebra m',
then on the coarser σ-algebra m) gives the same result as conditioning once on m.

**Intuition:** If you know less information (m ⊆ m'), then averaging over the additional
information in m' brings you back to what you'd get by conditioning on m directly.

**Application:** This is the key lemma for de Finetti's theorem Route 1, where we have
σ(η) ≤ σ(ζ) and need to show that μ[μ[f|σ(ζ)]|σ(η)] = μ[f|σ(η)].

**Proof strategy:** Use the uniqueness characterization from mathlib:
1. Define Yproj := μ[μ[f|m']|m], which is automatically m-measurable
2. Show that for every m-measurable set S, ∫_S Yproj = ∫_S f via two-step projection:
   - First: ∫_S Yproj = ∫_S μ[f|m'] (by CE property on m-sets)
   - Second: ∫_S μ[f|m'] = ∫_S f (by CE property, using m ≤ m' so S is also m'-measurable)
3. By uniqueness (`ae_eq_condExp_of_forall_setIntegral_eq`), Yproj = μ[f|m] a.e.
-/
lemma condExp_project_of_le {α : Type*} (m m' m₀ : MeasurableSpace α) {μ : Measure α}
    (hm : m ≤ m₀) (hm' : m' ≤ m₀) (h_le : m ≤ m')
    [SigmaFinite (Measure.trim μ hm)] [SigmaFinite (Measure.trim μ hm')]
    {f : α → ℝ} (hf_int : Integrable f μ) :
    μ[ μ[f | m'] | m ] =ᵐ[μ] μ[f | m] := by
  -- Define the projected representative
  set Yproj := μ[ μ[f | m'] | m ]

  -- Show integrals match on m-measurable sets via two-step projection
  have hYproj_integrals : ∀ s, MeasurableSet[m] s → μ s < ∞ →
      ∫ x in s, Yproj x ∂μ = ∫ x in s, f x ∂μ := by
    intro s hs hμs
    -- First projection step: use CE property on m-sets
    have step1 : ∫ x in s, Yproj x ∂μ = ∫ x in s, μ[f | m'] x ∂μ := by
      have : SigmaFinite (μ.trim hm) := inferInstance
      simpa [Yproj] using setIntegral_condExp hm integrable_condExp hs
    -- Second step: s is also m'-measurable since m ≤ m'
    calc
      ∫ x in s, Yproj x ∂μ
          = ∫ x in s, μ[f | m'] x ∂μ := step1
      _   = ∫ x in s, f x ∂μ := by
        have hs' : MeasurableSet[m'] s := h_le s hs
        have : SigmaFinite (μ.trim hm') := inferInstance
        simpa using setIntegral_condExp hm' hf_int hs'

  -- Apply uniqueness
  have hYproj : Yproj =ᵐ[μ] μ[f | m] := by
    refine ae_eq_condExp_of_forall_setIntegral_eq hm hf_int ?integrableOn hYproj_integrals ?sm
    · intro s hs hμs
      exact integrable_condExp.integrableOn
    · exact stronglyMeasurable_condExp.aestronglyMeasurable

  exact hYproj

/-!
## Wrappers for dominated convergence and L¹ continuity
-/

/-- **Restricted dominated convergence: L¹ convergence implies set integral convergence.**

If fn → f in L¹(μ), then ∫_s fn → ∫_s f for any measurable set s.

This requires integrability hypotheses to ensure the integrals are well-defined. -/
lemma tendsto_set_integral_of_L1 {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {s : Set α}
    {fn : ℕ → α → ℝ} {f : α → ℝ}
    (hf_int : Integrable f μ)
    (hfn_int : ∀ n, Integrable (fn n) μ)
    (hL1 : Filter.Tendsto (fun n => ∫⁻ ω, ‖(fn n) ω - f ω‖₊ ∂μ) Filter.atTop (nhds 0)) :
  Filter.Tendsto (fun n => ∫ ω in s, (fn n) ω ∂μ) Filter.atTop (nhds (∫ ω in s, f ω ∂μ)) := by
  -- Direct application of mathlib's tendsto_setIntegral_of_L1
  apply MeasureTheory.tendsto_setIntegral_of_L1 f hf_int _ hL1 s
  -- Show that fn is eventually integrable
  filter_upwards with n
  exact hfn_int n

/-- **L¹ convergence of product with bounded factor.**

If fn → f in L¹ and H is bounded a.e., then ∫_s (fn * H) → ∫_s (f * H). -/
lemma tendsto_set_integral_mul_of_L1 {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {s : Set α}
    {fn : ℕ → α → ℝ} {f H : α → ℝ} {C : ℝ}
    (hf_int : Integrable f μ)
    (hfn_int : ∀ n, Integrable (fn n) μ)
    (hH_int : Integrable H μ)
    (hL1 : Filter.Tendsto (fun n => ∫⁻ ω, ‖(fn n) ω - f ω‖₊ ∂μ) Filter.atTop (nhds 0))
    (hC : 0 ≤ C)
    (hH_bdd : ∀ᵐ ω ∂μ, ‖H ω‖ ≤ C) :
  Filter.Tendsto (fun n => ∫ ω in s, (fn n) ω * H ω ∂μ)
          Filter.atTop
          (nhds (∫ ω in s, f ω * H ω ∂μ)) := by
  -- Strategy: Show fn * H → f * H in L¹, then apply tendsto_setIntegral_of_L1
  apply MeasureTheory.tendsto_setIntegral_of_L1 (fun ω => f ω * H ω) _ _ _ s
  · -- Goal (a): Show f * H is integrable
    -- Apply bdd_mul: bounded function H times integrable function f
    have := hf_int.bdd_mul hH_int.aestronglyMeasurable hH_bdd
    simpa only [mul_comm] using this
  · -- Goal (b): Show fn * H is eventually integrable
    filter_upwards with n
    have := (hfn_int n).bdd_mul hH_int.aestronglyMeasurable hH_bdd
    simpa only [mul_comm] using this
  · -- Goal (c): Show ∫⁻ ‖(fn * H) - (f * H)‖₊ → 0
    -- Bound ∫⁻ ‖(fn - f) * H‖₊ by C * ∫⁻ ‖fn - f‖₊
    have h_bound : ∀ n, ∫⁻ ω, ‖(fn n) ω * H ω - f ω * H ω‖₊ ∂μ
                      ≤ ENNReal.ofReal C * ∫⁻ ω, ‖(fn n) ω - f ω‖₊ ∂μ := by
      intro n
      calc ∫⁻ ω, ‖(fn n) ω * H ω - f ω * H ω‖₊ ∂μ
          = ∫⁻ ω, ‖((fn n) ω - f ω) * H ω‖₊ ∂μ := by
            congr 1; ext ω; rw [sub_mul]
        _ = ∫⁻ ω, (‖(fn n) ω - f ω‖₊ * ‖H ω‖₊ : ℝ≥0∞) ∂μ := by
            congr 1; ext ω
            simp only [← ENNReal.coe_mul, nnnorm_mul]
        _ ≤ ∫⁻ ω, (‖(fn n) ω - f ω‖₊ * Real.toNNReal C : ℝ≥0∞) ∂μ := by
            apply lintegral_mono_ae
            filter_upwards [hH_bdd] with ω hω
            gcongr
            -- For real numbers: ‖x‖₊ ≤ C.toNNReal follows from ‖x‖ ≤ C
            show ‖H ω‖₊ ≤ Real.toNNReal C
            calc ‖H ω‖₊
                = Real.toNNReal ‖H ω‖ := norm_toNNReal.symm
              _ ≤ Real.toNNReal C := Real.toNNReal_le_toNNReal hω
        _ = ENNReal.ofReal C * ∫⁻ ω, ‖(fn n) ω - f ω‖₊ ∂μ := by
            rw [← lintegral_const_mul' _ (fun ω => ‖(fn n) ω - f ω‖₊) ENNReal.ofReal_ne_top]
            congr 1; ext ω
            -- Need: ↑‖fn n ω - f ω‖₊ * ↑(Real.toNNReal C) = ENNReal.ofReal C * ↑‖fn n ω - f ω‖₊
            rw [mul_comm]
            simp only [ENNReal.ofReal_eq_coe_nnreal hC]
            congr 1
            exact congr_arg ENNReal.ofNNReal (Real.toNNReal_of_nonneg hC)
    -- Apply squeeze theorem with C * hL1 → C * 0 = 0
    have h_limit : Filter.Tendsto (fun n => ENNReal.ofReal C * ∫⁻ ω, ‖(fn n) ω - f ω‖₊ ∂μ)
        Filter.atTop (nhds 0) := by
      convert ENNReal.Tendsto.const_mul hL1 (Or.inr ENNReal.ofReal_ne_top) using 2
      simp [mul_zero]
    -- Apply sandwichtendsto_of_tendsto_of_tendsto_of_le_of_le
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h_limit
      (fun n => zero_le _) h_bound

end MeasureTheory

end
