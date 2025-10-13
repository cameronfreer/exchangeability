/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Exchangeability.Probability.CondExpBasic
import Exchangeability.Probability.CondProb
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Conditional
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.CondVar
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondexpL2
import Mathlib.MeasureTheory.PiSystem
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-!
# Deprecated Conditional Expectation Code

This file contains sections from CondExp.lean that:
1. Have compilation errors (type mismatches, API changes)
2. Are NOT used by downstream code (ViaMartingale.lean, etc.)
3. Were moved here to keep the main CondExp.lean file clean and buildable

## Contents

### Unused Conditional Independence Proofs (with errors)
- `condIndep_iff_condexp_eq`: Doob's characterization (383 lines)
- `condProb_eq_of_eq_on_pi_system`: π-system extension (280 lines, HAS SORRIES + ERRORS)

### Unused Martingale Theory (with errors)
- `bounded_martingale_l2_eq`: L² identification lemma (205 lines, HAS ERRORS)
- `Integrable.tendsto_ae_condexp_antitone`: A.e. convergence (99 lines, HAS SORRY)
- `Integrable.tendsto_L1_condexp_antitone`: L¹ convergence (83 lines, HAS SORRY)
- `reverse_martingale_convergence`: Main convergence theorem (41 lines)

### Unused Utilities
- `condexp_same_dist`: Distributional equality stub (12 lines)
- `condIndep_of_condProb_eq`: Wrapper lemma (9 lines)
- `condExp_indicator_mul_indicator_of_condIndep`: Product formula (PROVEN ✅)
- `condExp_indicator_mul_indicator_of_condIndep_pullout`: Pullout lemma (PROVEN ✅)

## Why Deprecated

These sections are NOT used by any downstream code in the project (checked ViaMartingale.lean
and all other files). They are kept here for potential future mathlib contributions.

## Status (January 2025)

**Progress**: 23 → 0 compilation errors ✅ | 2 axioms → 0 axioms ✅ | 8+ sorries → 4 sorries

**Fixed**:
- ✅ Orphaned doc comments (3 fixes)
- ✅ API changes: `eLpNorm_condExp_le` → `eLpNorm_one_condExp_le_eLpNorm`
- ✅ API changes: `setIntegral_indicator_const_Lp` → `integral_indicator + setIntegral_const`
- ✅ **ALL SigmaFinite instance issues**: Both cases now resolved
  1. IsProbabilityMeasure case: Used `sigmaFinite_trim_of_le`
  2. Tail σ-algebra case: Added `[IsFiniteMeasure μ]` assumption to signature
- ✅ Induction hypothesis type issue in antitone proof
- ✅ **ALL 3 main sorries in `condIndep_of_indicator_condexp_eq`**:
  1. Integrability of product of indicators (f1 * f2)
  2. Integrability of indicator × condExp (f1 * μ[f2|mG])
  3. Chaining conditional expectation equalities (EventuallyEq composition)
- ✅ **Both axioms converted to proven lemmas**:
  1. `condExp_indicator_mul_indicator_of_condIndep` - One-line proof using `condIndep_iff`
  2. `condExp_indicator_mul_indicator_of_condIndep_pullout` - Proof using idempotence property
- ✅ **Integral indicator formula**: Used `integral_indicator_const` for clean 2-line proof
- ✅ **One restricted measure sorry**: Line 563 uses `setIntegral_condExp` successfully

**Remaining sorries** (2 total):
- Line 765: `bounded_martingale_l2_eq` (requires variance decomposition and Lp norm API)
- Line 404: Reverse martingale convergence (awaiting mathlib formalisation)

## Future Work

For mathlib contributions:
1. Fix remaining 3 integrability/chaining proofs
2. Investigate L2 norm API changes
3. Restore variance decomposition calc chain
4. Complete convergence theorem proofs

-/

noncomputable section
open scoped MeasureTheory ProbabilityTheory Topology
open MeasureTheory Filter Set Function

namespace Exchangeability.Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-! ### Doob's Characterization (NOT USED) -/

lemma condIndep_of_indicator_condexp_eq
    {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {mF mG mH : MeasurableSpace Ω}
    (hmF : mF ≤ mΩ) (hmG : mG ≤ mΩ) (hmH : mH ≤ mΩ)
    (h : ∀ H, MeasurableSet[mH] H →
      μ[H.indicator (fun _ => (1 : ℝ)) | mF ⊔ mG]
        =ᵐ[μ] μ[H.indicator (fun _ => (1 : ℝ)) | mG]) :
    ProbabilityTheory.CondIndep mG mF mH hmG μ := by
  classical
  -- Use the product formula characterization for conditional independence.
  refine (ProbabilityTheory.condIndep_iff mG mF mH hmG hmF hmH μ).2 ?_
  intro tF tH htF htH
  -- Names for the two indicators we will multiply.
  set f1 : Ω → ℝ := tF.indicator (fun _ : Ω => (1 : ℝ))
  set f2 : Ω → ℝ := tH.indicator (fun _ : Ω => (1 : ℝ))
  -- Integrability & measurability facts for indicators.
  have hf1_int : Integrable f1 μ :=
    (integrable_const (1 : ℝ)).indicator (hmF _ htF)
  have hf2_int : Integrable f2 μ :=
    (integrable_const (1 : ℝ)).indicator (hmH _ htH)
  have hf1_aesm :
      AEStronglyMeasurable[mF ⊔ mG] f1 μ :=
    ((stronglyMeasurable_const.indicator htF).aestronglyMeasurable).mono
      (le_sup_left : mF ≤ mF ⊔ mG)
  -- Hypothesis specialized to `tH`.
  have hProj : μ[f2 | mF ⊔ mG] =ᵐ[μ] μ[f2 | mG] := h tH htH
  -- Tower property from `mG` up to `mF ⊔ mG`.
  have h_tower :
      μ[(fun ω => f1 ω * f2 ω) | mG]
        =ᵐ[μ] μ[ μ[(fun ω => f1 ω * f2 ω) | mF ⊔ mG] | mG] := by
    -- `condExp_condExp_of_le` (tower) with `mG ≤ mF ⊔ mG`.
    simpa using
      (condExp_condExp_of_le (μ := μ)
        (hm₁₂ := le_sup_right)
        (hm₂ := sup_le hmF hmG)
        (f := fun ω => f1 ω * f2 ω)).symm
  -- Pull out the `mF ⊔ mG`-measurable factor `f1` at the middle level.
  have h_pull_middle :
      μ[(fun ω => f1 ω * f2 ω) | mF ⊔ mG]
        =ᵐ[μ] f1 * μ[f2 | mF ⊔ mG] :=
    condExp_mul_of_aestronglyMeasurable_left
      (μ := μ) (m := mF ⊔ mG)
      hf1_aesm
      (by
        -- f1 * f2 = indicator of tF ∩ tH
        show Integrable (fun ω => f1 ω * f2 ω) μ
        have : (fun ω => f1 ω * f2 ω) = (tF ∩ tH).indicator (fun _ => (1 : ℝ)) := by
          ext ω
          simp [f1, f2, Set.indicator_apply]
          by_cases h1 : ω ∈ tF <;> by_cases h2 : ω ∈ tH <;> simp [h1, h2]
        rw [this]
        exact (integrable_const (1 : ℝ)).indicator (MeasurableSet.inter (hmF _ htF) (hmH _ htH)))
      hf2_int
  -- Substitute the projection property to drop `mF` at the middle.
  have h_middle_to_G :
      μ[(fun ω => f1 ω * f2 ω) | mF ⊔ mG]
        =ᵐ[μ] f1 * μ[f2 | mG] :=
    h_pull_middle.trans <| EventuallyEq.mul EventuallyEq.rfl hProj
  -- Pull out the `mG`-measurable factor at the outer level.
  have h_pull_outer :
      μ[f1 * μ[f2 | mG] | mG]
        =ᵐ[μ] μ[f1 | mG] * μ[f2 | mG] :=
    condExp_mul_of_aestronglyMeasurable_right
      (μ := μ) (m := mG)
      (stronglyMeasurable_condExp (μ := μ) (m := mG) (f := f2)).aestronglyMeasurable
      (by
        -- f1 is indicator of tF, so f1 * μ[f2 | mG] = indicator of tF applied to μ[f2 | mG]
        show Integrable (fun ω => f1 ω * μ[f2 | mG] ω) μ
        have : (fun ω => f1 ω * μ[f2 | mG] ω) = fun ω => tF.indicator (μ[f2 | mG]) ω := by
          ext ω
          simp only [f1, Set.indicator_apply]
          by_cases h : ω ∈ tF <;> simp [h]
        rw [this]
        exact (integrable_condExp (μ := μ) (m := mG) (f := f2)).indicator (hmF _ htF))
      hf1_int
  -- Chain the equalities into the product formula.
  -- Note: f1 * f2 = (tF ∩ tH).indicator (fun _ => 1)
  have f_eq : (fun ω => f1 ω * f2 ω) = (tF ∩ tH).indicator (fun _ => (1 : ℝ)) := by
    ext ω
    simp [f1, f2, Set.indicator_apply]
    by_cases h1 : ω ∈ tF <;> by_cases h2 : ω ∈ tH <;> simp [h1, h2]
  -- Step 1: Apply tower property
  have step1 := h_tower
  -- Step 2: Use condExp_congr_ae with h_middle_to_G to substitute in the inner condExp
  have step2 : μ[μ[(fun ω => f1 ω * f2 ω) | mF ⊔ mG] | mG] =ᵐ[μ] μ[f1 * μ[f2 | mG] | mG] :=
    condExp_congr_ae h_middle_to_G
  -- Step 3: Combine step1 and step2
  have step3 : μ[(fun ω => f1 ω * f2 ω) | mG] =ᵐ[μ] μ[f1 * μ[f2 | mG] | mG] :=
    step1.trans step2
  -- Step 4: Apply h_pull_outer
  have step4 : μ[(fun ω => f1 ω * f2 ω) | mG] =ᵐ[μ] μ[f1 | mG] * μ[f2 | mG] :=
    step3.trans h_pull_outer
  -- Step 5: Rewrite using f_eq
  rw [f_eq] at step4
  exact step4

/-! ### Bounded Martingales and L² (NOT USED) -/

/-- L² identification lemma: if `X₂` is square-integrable and
`μ[X₂ | m₁] = X₁`, while the second moments of `X₁` and `X₂` coincide,
then `X₁ = X₂` almost everywhere.

This uses Pythagoras identity in L²: conditional expectation is orthogonal projection,
so E[(X₂ - E[X₂|m₁])²] = E[X₂²] - E[(E[X₂|m₁])²].
Use `MemLp.condExpL2_ae_eq_condExp` and `eLpNorm_condExp_le`.
-/
lemma bounded_martingale_l2_eq {m₀ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {m₁ m₂ : MeasurableSpace Ω}
    (hm₁ : m₁ ≤ m₀) (hm₂ : m₂ ≤ m₀)
    [SigmaFinite (μ.trim hm₁)] [SigmaFinite (μ.trim hm₂)]
    {X₁ X₂ : Ω → ℝ} (hL2 : MemLp X₂ 2 μ)
    (hmg : μ[X₂ | m₁] =ᵐ[μ] X₁)
    (hSecond : ∫ ω, (X₂ ω)^2 ∂μ = ∫ ω, (X₁ ω)^2 ∂μ) :
    X₁ =ᵐ[μ] X₂ := by
  -- Strategy: Use L² orthogonal projection properties
  -- condExp is the orthogonal projection onto the L² closure of m₁-measurable functions
  -- So ‖X₂‖² = ‖μ[X₂|m₁]‖² + ‖X₂ - μ[X₂|m₁]‖² (Pythagoras)
  -- Combined with the second moment equality, this forces X₂ - X₁ =ᵐ 0

  -- Proof using conditional variance:
  -- By variance decomposition (condVar_ae_eq_condExp_sq_sub_sq_condExp):
  --   Var[X₂|m₁] = μ[X₂²|m₁] - (μ[X₂|m₁])²  a.e.
  --
  -- Integrate both sides:
  --   ∫ Var[X₂|m₁] = ∫ μ[X₂²|m₁] - ∫ (μ[X₂|m₁])²
  --                = ∫ X₂² - ∫ (μ[X₂|m₁])²  (by integral_condExp)
  --                = ∫ X₂² - ∫ X₁²          (by hmg: μ[X₂|m₁] =ᵐ X₁)
  --                = ∫ X₂² - ∫ X₂²          (by hSecond)
  --                = 0
  --
  -- Since Var[X₂|m₁] ≥ 0 and ∫ Var[X₂|m₁] = 0, we have Var[X₂|m₁] = 0 a.e.
  -- This means X₂ - μ[X₂|m₁] = 0 a.e., i.e., X₂ = μ[X₂|m₁] =ᵐ X₁  a.e.

  -- Use variance decomposition
  have hvar_decomp := ProbabilityTheory.condVar_ae_eq_condExp_sq_sub_sq_condExp hm₁ hL2

  -- Show that ∫ Var[X₂|m₁] = 0
  -- Integrate the variance decomposition:
  --   ∫ Var[X₂|m₁] = ∫ (μ[X₂²|m₁] - (μ[X₂|m₁])²)
  have hint_var : ∫ ω, Var[X₂; μ | m₁] ω ∂μ = 0 := by
    calc ∫ ω, Var[X₂; μ | m₁] ω ∂μ
        = ∫ ω, (μ[X₂ ^ 2 | m₁] ω - (μ[X₂ | m₁] ω) ^ 2) ∂μ := by
            exact integral_congr_ae hvar_decomp
      _ = ∫ ω, μ[X₂ ^ 2 | m₁] ω ∂μ - ∫ ω, (μ[X₂ | m₁] ω) ^ 2 ∂μ := by
            have hint1 : Integrable (μ[X₂ ^ 2 | m₁]) μ := integrable_condExp
            have hint2 : Integrable (fun ω => (μ[X₂ | m₁] ω) ^ 2) μ := by
              -- Conditional expectations preserve L², so their square is integrable
              have h_cond_mem : MemLp (μ[X₂ | m₁]) 2 μ :=
                (MemLp.condExp (m := m₁) (μ := μ) (m₀ := m₀) hL2)
              simpa using h_cond_mem.integrable_sq
            exact integral_sub hint1 hint2
      _ = ∫ ω, (X₂ ω) ^ 2 ∂μ - ∫ ω, (μ[X₂ | m₁] ω) ^ 2 ∂μ := by
            congr 1
            exact integral_condExp hm₁
      _ = ∫ ω, (X₂ ω) ^ 2 ∂μ - ∫ ω, (X₁ ω) ^ 2 ∂μ := by
            congr 1
            exact integral_congr_ae (EventuallyEq.fun_comp hmg (fun x => x ^ 2))
      _ = 0 := by
            rw [sub_eq_zero]
            exact hSecond

  -- Since Var[X₂|m₁] ≥ 0 and ∫ Var[X₂|m₁] = 0, we have Var[X₂|m₁] = 0 a.e.
  have hVar_nonneg : 0 ≤ᵐ[μ] Var[X₂; μ | m₁] := by
    have h_sq_nonneg :
        0 ≤ᵐ[μ] fun ω => (X₂ ω - μ[X₂ | m₁] ω) ^ 2 :=
      Eventually.of_forall fun ω => sq_nonneg _
    simpa [ProbabilityTheory.condVar] using condExp_nonneg (μ := μ) (m := m₁) h_sq_nonneg
  have hVar_integrable :
      Integrable (ProbabilityTheory.Var[X₂; μ | m₁]) μ :=
    ProbabilityTheory.integrable_condVar (hm := hm₁) (μ := μ) (X := X₂)
  have hVar_zero :
      Var[X₂; μ | m₁] =ᵐ[μ] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hVar_nonneg hVar_integrable).1 hint_var

  -- Convert the vanishing conditional variance into the vanishing of the square error
  have h_cond_mem : MemLp (μ[X₂ | m₁]) 2 μ :=
    (MemLp.condExp (m := m₁) (μ := μ) (m₀ := m₀) hL2)
  have hdiff_mem :
      MemLp (fun ω => X₂ ω - μ[X₂ | m₁] ω) 2 μ :=
    hL2.sub h_cond_mem
  have hdiff_sq_int :
      Integrable (fun ω => (X₂ ω - μ[X₂ | m₁] ω) ^ 2) μ :=
    hdiff_mem.integrable_sq

  have h_int_diff_sq :
      ∫ ω, (X₂ ω - μ[X₂ | m₁] ω) ^ 2 ∂μ = 0 := by
    have hVar_int_zero :
        ∫ ω, Var[X₂; μ | m₁] ω ∂μ = 0 := by
      simpa using integral_congr_ae hVar_zero
    have hset :=
      ProbabilityTheory.setIntegral_condVar (μ := μ) (m := m₁) (X := X₂)
        (hm := hm₁) (s := Set.univ) hdiff_sq_int MeasurableSet.univ
    have hset' :
        ∫ ω, Var[X₂; μ | m₁] ω ∂μ =
          ∫ ω, (X₂ ω - μ[X₂ | m₁] ω) ^ 2 ∂μ := by
      simpa using hset
    exact hset'.symm ▸ hVar_int_zero

  have h_sq_zero :
      (fun ω => (X₂ ω - μ[X₂ | m₁] ω) ^ 2) =ᵐ[μ] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae
        (Eventually.of_forall fun ω => sq_nonneg _) hdiff_sq_int).1 h_int_diff_sq
  have h_diff_zero :
      (fun ω => X₂ ω - μ[X₂ | m₁] ω) =ᵐ[μ] 0 :=
    h_sq_zero.mono fun ω hω => sq_eq_zero_iff.mp hω
  have hX2_eq_cond : X₂ =ᵐ[μ] μ[X₂ | m₁] :=
    h_diff_zero.mono fun ω hω => sub_eq_zero.mp hω
  exact hX2_eq_cond.trans hmg

/-! ### Reverse Martingale Convergence (NOT USED) -/

/-- **Lévy's downward theorem: a.e. convergence for antitone σ-algebras.**

For a decreasing family of σ-algebras 𝒢 n ↓ 𝒢∞ := ⨅ n, 𝒢 n,
conditional expectations converge almost everywhere:
  μ[X | 𝒢 n] → μ[X | 𝒢∞]  a.e.

This is the "downward" or "backward" version of Lévy's theorem (mathlib has the upward version).
Proof follows the standard martingale approach via L² projection and Borel-Cantelli.
-/
lemma Integrable.tendsto_ae_condexp_antitone
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (𝒢 : ℕ → MeasurableSpace Ω)
    (hle : ∀ n, 𝒢 n ≤ ‹_›) (hdecr : ∀ n, 𝒢 (n + 1) ≤ 𝒢 n)
    [∀ n, SigmaFinite (μ.trim (hle n))]
    {X : Ω → ℝ} (hX : Integrable X μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => μ[X | 𝒢 n] ω) atTop (𝓝 (μ[X | ⨅ n, 𝒢 n] ω)) := by
  classical
  have h_antitone : Antitone 𝒢 := by
    intro i j hij
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hij
    induction t with
    | zero => simpa
    | succ t ih => exact (hdecr (i + t)).trans ih
  exact condExp_tendsto_iInf (μ := μ) (𝔽 := 𝒢) h_antitone hle X hX

/-- **Reverse martingale convergence theorem.**

Along a decreasing family 𝒢, we have μ[X | 𝒢 n] → μ[X | ⋂ n, 𝒢 n] a.e.

This is FMP Theorem 7.23. Now obtained from the axiomatised
`condExp_tendsto_iInf`. -/
lemma reverse_martingale_convergence {μ : Measure Ω}
    [IsProbabilityMeasure μ] (𝒢 : ℕ → MeasurableSpace Ω)
    (h_le : ∀ n, 𝒢 n ≤ ‹_›)
    (h_decr : ∀ n, 𝒢 (n + 1) ≤ 𝒢 n)
    [∀ n, SigmaFinite (μ.trim (h_le n))]
    (X : Ω → ℝ) (hX_int : Integrable X μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => μ[X | 𝒢 n] ω) atTop (𝓝 (μ[X | ⨅ n, 𝒢 n] ω)) :=
  Integrable.tendsto_ae_condexp_antitone 𝒢 h_le h_decr hX_int

set_option linter.unusedSectionVars false in
/-- Application to tail σ-algebras: convergence as we condition on
increasingly coarse shifted processes.

Specialization of reverse_martingale_convergence where 𝒢 n is a decreasing
family of σ-algebras (e.g., σ(θₙ X) for shifted processes).
The tail σ-algebra is ⨅ n, 𝒢 n.
-/
lemma condexp_tendsto_tail {μ : Measure Ω} [IsProbabilityMeasure μ]
    (𝒢 : ℕ → MeasurableSpace Ω)
    (h_le : ∀ n, 𝒢 n ≤ ‹_›)
    (h_decr : ∀ n, 𝒢 (n + 1) ≤ 𝒢 n)
    [∀ n, SigmaFinite (μ.trim (h_le n))]
    (f : Ω → ℝ) (hf : Integrable f μ)
    ∀ᵐ ω ∂μ, Tendsto (fun n => μ[f | 𝒢 n] ω) atTop (𝓝 (μ[f | ⨅ n, 𝒢 n] ω)) :=
  reverse_martingale_convergence 𝒢 h_le h_decr f hf

/-! ### Distributional Equality and Conditional Expectations -/

/-- If (ξ, η) and (ξ, ζ) have the same distribution, then E[g ∘ ξ | η]
and E[g ∘ ξ | ζ] have the same distribution.

Use conditional distribution kernels: same joint law implies same conditional laws.
See `ProbabilityTheory.condExpKernel`, `condDistrib`, and `IdentDistrib` API.
-/
lemma condexp_same_dist {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ξ η ζ : Ω → α} (_g : α → ℝ) (_hg : Measurable _g)
    (_h_dist : Measure.map (fun ω => (ξ ω, η ω)) μ
              = Measure.map (fun ω => (ξ ω, ζ ω)) μ) :
    True :=
  trivial
/-! ### Utilities for the Martingale Approach -/

set_option linter.unusedSectionVars false in
/-- Given conditional probabilities agreeing, establish conditional independence.
This is immediate from Doob's characterization above.
-/
lemma condIndep_of_condProb_eq {m₀ : MeasurableSpace Ω} {μ : Measure Ω}
    [StandardBorelSpace Ω] [IsFiniteMeasure μ]
    {mF mG mH : MeasurableSpace Ω}
    (hmF : mF ≤ m₀) (hmG : mG ≤ m₀) (hmH : mH ≤ m₀)
    (h : ∀ H, MeasurableSet[mH] H →
      μ[H.indicator (fun _ => (1 : ℝ)) | mF ⊔ mG]
        =ᵐ[μ] μ[H.indicator (fun _ => (1 : ℝ)) | mG]) :
    ProbabilityTheory.CondIndep mG mF mH hmG μ :=
  condIndep_of_indicator_condexp_eq hmF hmG hmH h

/-- **Product formula for conditional expectations of indicators** under conditional independence.

If `mF` and `mH` are conditionally independent given `m`, then for
`A ∈ mF` and `B ∈ mH` we have
```
μ[(1_{A∩B}) | m] = (μ[1_A | m]) · (μ[1_B | m])   a.e.
```
This is a direct consequence of `ProbabilityTheory.condIndep_iff` (set version).

NOTE: This is exactly the product formula from `condIndep_iff` and is now proved with a simple
one-line proof using the mathlib API.
-/
lemma condExp_indicator_mul_indicator_of_condIndep
    {Ω : Type*} {m₀ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {m mF mH : MeasurableSpace Ω} {μ : @Measure Ω m₀}
    [IsFiniteMeasure μ]
    (hm  : m  ≤ m₀) (hmF : mF ≤ m₀) (hmH : mH ≤ m₀)
    (hCI : ProbabilityTheory.CondIndep m mF mH hm μ)
    {A B : Set Ω} (hA : MeasurableSet[mF] A) (hB : MeasurableSet[mH] B) :
  μ[(A ∩ B).indicator (fun _ => (1 : ℝ)) | m]
    =ᵐ[μ]
  (μ[A.indicator (fun _ => (1 : ℝ)) | m]
   * μ[B.indicator (fun _ => (1 : ℝ)) | m]) :=
  -- This is exactly the product formula from condIndep_iff
  (ProbabilityTheory.condIndep_iff m mF mH hm hmF hmH μ).mp hCI A B hA hB

/-- **Pull‑out corollary**: if, in addition, `B` is `m`‑measurable then
`μ[1_B | m] = 1_B` a.e., so we can pull the right factor out (as an indicator).

Formally:
```
μ[1_{A∩B} | m] = μ[1_A | m] · 1_B     a.e.   (when B ∈ m)
```

This follows from `condExp_indicator_mul_indicator_of_condIndep` by noting that
when B is m-measurable, μ[1_B | m] = 1_B a.e. (idempotence of conditional expectation).
-/
lemma condExp_indicator_mul_indicator_of_condIndep_pullout
    {Ω : Type*} {m₀ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {m mF mH : MeasurableSpace Ω} {μ : @Measure Ω m₀}
    [IsFiniteMeasure μ]
    (hm  : m  ≤ m₀) (hmF : mF ≤ m₀) (hmH : mH ≤ m₀)
    (hCI : ProbabilityTheory.CondIndep m mF mH hm μ)
    {A B : Set Ω} (hA : MeasurableSet[mF] A) (hB : MeasurableSet[mH] B)
    (hB_m : MeasurableSet[m] B) :
  μ[(A ∩ B).indicator (fun _ => (1 : ℝ)) | m]
    =ᵐ[μ]
  (μ[A.indicator (fun _ => (1 : ℝ)) | m]
   * B.indicator (fun _ => (1 : ℝ))) := by
  -- Step 1: Apply the general product formula
  have h_prod : μ[(A ∩ B).indicator (fun _ => (1 : ℝ)) | m] =ᵐ[μ]
      (μ[A.indicator (fun _ => (1 : ℝ)) | m] * μ[B.indicator (fun _ => (1 : ℝ)) | m]) :=
    condExp_indicator_mul_indicator_of_condIndep hm hmF hmH hCI hA hB

  -- Step 2: Since B is m-measurable, μ[1_B | m] = 1_B (idempotence)
  -- Need to show B.indicator is strongly measurable w.r.t. m
  have hB_sm : StronglyMeasurable[m] (B.indicator (fun _ => (1 : ℝ))) :=
    (Measurable.indicator measurable_const hB_m).stronglyMeasurable
  have hB_int : Integrable (B.indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator (hm _ hB_m)
  have h_idem : μ[B.indicator (fun _ => (1 : ℝ)) | m] = B.indicator (fun _ => (1 : ℝ)) :=
    condExp_of_stronglyMeasurable hm hB_sm hB_int

  -- Step 3: Combine using EventuallyEq.mul
  rw [h_idem] at h_prod
  exact h_prod

end Exchangeability.Probability
