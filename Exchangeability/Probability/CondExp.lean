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
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondexpL2
import Mathlib.MeasureTheory.PiSystem
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-!
# Conditional Expectation API for Exchangeability Proofs

This file provides a specialized API for conditional expectations, conditional
independence, and martingale convergence, tailored for the exchangeability and
de Finetti proofs.

## Main Components

### 1. Conditional Independence
- `condIndep_of_indicator_condexp_eq`: Establish conditional independence from projection property
- `condExp_indicator_mul_indicator_of_condIndep`: Product formula for indicators
- `condexp_indicator_inter_bridge`: Bridge lemma managing typeclass instances

### 2. Distributional Equality ⇒ Conditional Expectation Equality
- `condexp_indicator_eq_of_pair_law_eq`: Core lemma using uniqueness of conditional expectation
- `condexp_indicator_eq_of_agree_on_future_rectangles`: Application to exchangeable sequences

### 3. Sub-σ-algebra Infrastructure
- `condExpWith`: Explicit instance management for conditioning on sub-σ-algebras
- `isFiniteMeasure_trim`, `sigmaFinite_trim`: Measure trimming instances
- `AgreeOnFutureRectangles`: Structure for distributional agreement

## Implementation Status

This file provides specialized lemmas for conditional independence and conditional expectation
equality under distributional assumptions, used in the de Finetti theorem proof.

**Key results:**
- `condIndep_of_indicator_condexp_eq`: Establish conditional independence from projection property
- `condExp_indicator_mul_indicator_of_condIndep`: Product formula under conditional independence
- `condexp_indicator_eq_of_pair_law_eq`: Conditional expectations equal when pair laws match
- `condexp_indicator_eq_of_agree_on_future_rectangles`: Application to sequence-valued tails

**Supporting infrastructure:**
- `condExpWith`: Wrapper managing typeclass instances for sub-σ-algebras
- `isFiniteMeasure_trim`, `sigmaFinite_trim`: Instances for trimmed measures
- `condexp_indicator_inter_bridge`: Bridge lemma for ViaMartingale.lean

All main results are proven. Additional conditional expectation utilities and conditional
probability definitions are in `CondExpBasic.lean` and `CondProb.lean`.

## References

* Kallenberg, *Probabilistic Symmetries and Invariance Principles* (2005)
* Mathlib's conditional expectation infrastructure
-/

noncomputable section
open scoped MeasureTheory ProbabilityTheory Topology
open MeasureTheory Filter Set Function

namespace Exchangeability.Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-
Note on linter warnings: Some theorems in this file explicitly include `{m₀ : MeasurableSpace Ω}`
as a parameter, which makes the section variable `[MeasurableSpace Ω]` unused for those theorems.
This is intentional: these theorems need to work with multiple measurable space structures on Ω
(e.g., m₀, m₁, m₂, mF, mG, mH) and explicitly naming m₀ makes the statements clearer. We disable
the unusedSectionVars linter for such theorems with `set_option linter.unusedSectionVars false`.
-/

/-! ### Pair-law ⇒ conditional indicator equality (stub) -/

/-- Standard cylinder on the first `r` coordinates starting at index 0. -/
def cylinder (α : Type*) (r : ℕ) (C : Fin r → Set α) : Set (ℕ → α) :=
  {f | ∀ i : Fin r, f i ∈ C i}

/-- Agreement on future rectangles property (inlined to avoid circular dependency). -/
structure AgreeOnFutureRectangles {α : Type*} [MeasurableSpace α]
    (μ ν : Measure (α × (ℕ → α))) : Prop where
  measure_eq : μ = ν

/-! ### Conditional Independence (Doob's Characterization)

## Mathlib Integration

Conditional independence is now available in mathlib as `ProbabilityTheory.CondIndep` from
`Mathlib.Probability.Independence.Conditional`.

For two σ-algebras m₁ and m₂ to be conditionally independent given m' with respect to μ,
we require that for any sets t₁ ∈ m₁ and t₂ ∈ m₂:
  μ⟦t₁ ∩ t₂ | m'⟧ =ᵐ[μ] μ⟦t₁ | m'⟧ * μ⟦t₂ | m'⟧

To use: `open ProbabilityTheory` to access `CondIndep`, or use
`ProbabilityTheory.CondIndep` directly.

Related definitions also available in mathlib:
- `ProbabilityTheory.CondIndepSet`: conditional independence of sets
- `ProbabilityTheory.CondIndepFun`: conditional independence of functions  
- `ProbabilityTheory.iCondIndep`: conditional independence of families
-/

/-- **Doob's characterization of conditional independence (FMP 6.6).**

For σ-algebras 𝒻, 𝒢, ℋ, we have 𝒻 ⊥⊥_𝒢 ℋ if and only if
```
P[H | 𝒻 ∨ 𝒢] = P[H | 𝒢] a.s. for all H ∈ ℋ
```

This characterization follows from the product formula in `condIndep_iff`:
- Forward direction: From the product formula, taking F = univ gives the projection property
- Reverse direction: The projection property implies the product formula via uniqueness of CE

Note: Requires StandardBorelSpace assumption from mathlib's CondIndep definition.
-/

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
  have hf1f2_int : Integrable (fun ω => f1 ω * f2 ω) μ := by
    have : (fun ω => f1 ω * f2 ω) = (tF ∩ tH).indicator (fun _ : Ω => (1 : ℝ)) := by
      funext ω; by_cases h1 : ω ∈ tF <;> by_cases h2 : ω ∈ tH <;>
        simp [f1, f2, Set.indicator, h1, h2, Set.mem_inter_iff] at *
    rw [this]
    exact (integrable_const (1 : ℝ) (μ := μ)).indicator
        (MeasurableSet.inter (hmF _ htF) (hmH _ htH))
  have h_pull_middle :
      μ[(fun ω => f1 ω * f2 ω) | mF ⊔ mG]
        =ᵐ[μ] f1 * μ[f2 | mF ⊔ mG] :=
    condExp_mul_of_aestronglyMeasurable_left
      (μ := μ) (m := mF ⊔ mG)
      hf1_aesm
      hf1f2_int
      hf2_int
  -- Substitute the projection property to drop `mF` at the middle.
  have h_middle_to_G :
      μ[(fun ω => f1 ω * f2 ω) | mF ⊔ mG]
        =ᵐ[μ] f1 * μ[f2 | mG] :=
    h_pull_middle.trans <| EventuallyEq.mul EventuallyEq.rfl hProj
  -- Pull out the `mG`-measurable factor at the outer level.
  have hf1_condexp_int : Integrable (f1 * μ[f2 | mG]) μ := by
    have h_eq : f1 * μ[f2 | mG] = tF.indicator (fun ω => μ[f2 | mG] ω) := by
      funext ω; by_cases hω : ω ∈ tF <;> simp [f1, Set.indicator, hω]
    rw [h_eq]
    exact (integrable_condExp (μ := μ) (m := mG) (f := f2)).indicator (hmF _ htF)
  have h_pull_outer :
      μ[f1 * μ[f2 | mG] | mG]
        =ᵐ[μ] μ[f1 | mG] * μ[f2 | mG] :=
    condExp_mul_of_aestronglyMeasurable_right
      (μ := μ) (m := mG)
      (stronglyMeasurable_condExp (μ := μ) (m := mG) (f := f2)).aestronglyMeasurable
      hf1_condexp_int
      hf1_int
  -- Chain the equalities into the product formula.
  have h_prod :
      μ[(fun ω => f1 ω * f2 ω) | mG]
        =ᵐ[μ] μ[f1 | mG] * μ[f2 | mG] :=
    h_tower.trans (condExp_congr_ae h_middle_to_G |>.trans h_pull_outer)
  -- Rephrase the product formula for indicators.
  have h_f1f2 : (fun ω => f1 ω * f2 ω) = (tF ∩ tH).indicator (fun _ => (1 : ℝ)) := by
    funext ω; by_cases h1 : ω ∈ tF <;> by_cases h2 : ω ∈ tH <;>
      simp [f1, f2, Set.indicator, h1, h2, Set.mem_inter_iff] at *
  simpa [h_f1f2, f1, f2] using h_prod

/-! ### Bounded Martingales and L² Inequalities -/

/-! ### Axioms for Conditional Independence Factorization -/

/-- **Product formula for conditional expectations of indicators** under conditional independence.

If `mF` and `mH` are conditionally independent given `m`, then for
`A ∈ mF` and `B ∈ mH` we have
```
μ[(1_{A∩B}) | m] = (μ[1_A | m]) · (μ[1_B | m])   a.e.
```
This is a direct consequence of `ProbabilityTheory.condIndep_iff` (set version).
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
   * μ[B.indicator (fun _ => (1 : ℝ)) | m]) := by
  -- This is exactly the product formula from condIndep_iff
  exact (ProbabilityTheory.condIndep_iff m mF mH hm hmF hmH μ).mp hCI A B hA hB

/-! ### Helper API for Sub-σ-algebras

These wrappers provide explicit instance management for conditional expectations
with sub-σ-algebras, working around Lean 4 typeclass inference issues. -/

/-! ### SigmaFinite instances for trimmed measures

When working with conditional expectations on sub-σ-algebras, we need `SigmaFinite (μ.trim hm)`.
For probability measures (or finite measures), this follows from showing the trimmed measure
is still finite. -/

/-- Helper lemma: Trimmed measure is finite when the original measure is finite. -/
lemma isFiniteMeasure_trim {Ω : Type*} {m₀ : MeasurableSpace Ω}
    (μ : Measure Ω) [IsFiniteMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ m₀) :
    IsFiniteMeasure (μ.trim hm) := by
  classical
  -- univ is m-measurable, so trim agrees with μ on univ
  have hU : (μ.trim hm) Set.univ = μ Set.univ := by
    rw [trim_measurableSet_eq hm MeasurableSet.univ]
  -- Now measure_univ_lt_top comes from [IsFiniteMeasure μ]
  refine ⟨?_⟩
  simp [hU, measure_lt_top]

/-- Helper lemma: Trimmed measure is sigma-finite when the original measure is finite. -/
lemma sigmaFinite_trim {Ω : Type*} {m₀ : MeasurableSpace Ω}
    (μ : Measure Ω) [IsFiniteMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ m₀) :
    SigmaFinite (μ.trim hm) := by
  haveI := isFiniteMeasure_trim μ hm
  infer_instance

/-! ### Stable conditional expectation wrapper

This wrapper manages typeclass instances to avoid metavariable issues
when calling `condexp` with sub-σ-algebras. -/

/-- Conditional expectation with explicit sub-σ-algebra and automatic instance management.

This wrapper "freezes" the conditioning σ-algebra and installs the necessary
sigma-finite instances before calling `μ[f | m]`, avoiding typeclass metavariable issues. -/
noncomputable
def condExpWith {Ω : Type*} {m₀ : MeasurableSpace Ω}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m : MeasurableSpace Ω) (_hm : m ≤ m₀)
    (f : Ω → ℝ) : Ω → ℝ := by
  classical
  haveI : IsFiniteMeasure μ := inferInstance
  haveI : IsFiniteMeasure (μ.trim _hm) := isFiniteMeasure_trim μ _hm
  haveI : SigmaFinite (μ.trim _hm) := sigmaFinite_trim μ _hm
  exact μ[f | m]

/-! ### Bridge lemma for indicator factorization

This adapter allows ViaMartingale.lean to use the proven factorization lemma
while managing typeclass instances correctly. -/

/-- Bridge lemma: Product formula for conditional expectations of indicators under conditional independence.

This is an adapter that manages typeclass instances and forwards to
`condExp_indicator_mul_indicator_of_condIndep`. Use this in ViaMartingale.lean
to avoid typeclass resolution issues. -/
lemma condexp_indicator_inter_bridge
    {Ω : Type*} {m₀ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {μ : @Measure Ω m₀} [IsProbabilityMeasure μ]
    {m mF mH : MeasurableSpace Ω}
    (hm : m ≤ m₀) (hmF : mF ≤ m₀) (hmH : mH ≤ m₀)
    (hCI : ProbabilityTheory.CondIndep m mF mH hm μ)
    {A B : Set Ω} (hA : MeasurableSet[mF] A) (hB : MeasurableSet[mH] B) :
    μ[(A ∩ B).indicator (fun _ => (1 : ℝ)) | m]
      =ᵐ[μ]
    (μ[A.indicator (fun _ => (1 : ℝ)) | m] *
     μ[B.indicator (fun _ => (1 : ℝ)) | m]) := by
  classical
  -- Install trimmed instances
  haveI : IsFiniteMeasure μ := inferInstance
  haveI : IsFiniteMeasure (μ.trim hm) := isFiniteMeasure_trim μ hm
  haveI : SigmaFinite (μ.trim hm) := sigmaFinite_trim μ hm
  -- Forward to the proven lemma
  exact condExp_indicator_mul_indicator_of_condIndep hm hmF hmH hCI hA hB

/-! ### Conditional expectation equality from distributional equality

This is the key bridge lemma for Axiom 1 (condexp_convergence): if (Y, Z) and (Y', Z)
have the same joint distribution, then their conditional expectations given σ(Z) are equal. -/

/-- **CE bridge lemma:** If `(Y, Z)` and `(Y', Z)` have the same law, then for every measurable `B`,
```
E[1_{Y ∈ B} | σ(Z)] = E[1_{Y' ∈ B} | σ(Z)]  a.e.
```

**Proof strategy:**
1. For any bounded h measurable w.r.t. σ(Z), we have
   ```
   ∫ 1_{Y ∈ B} · h ∘ Z dμ = ∫ 1_{Y' ∈ B} · h ∘ Z dμ
   ```
   by the equality of joint push-forward measures on rectangles B × E.

2. This equality holds for all σ(Z)-measurable test functions h.

3. By uniqueness of conditional expectation (`ae_eq_condExp_of_forall_setIntegral_eq`),
   ```
   E[1_{Y ∈ B} | σ(Z)] = E[1_{Y' ∈ B} | σ(Z)]  a.e.
   ```

**This is the key step for `condexp_convergence` in ViaMartingale.lean!**
Use with Y = X_m, Y' = X_k, Z = shiftRV X (m+1), and the equality comes from contractability
via `contractable_dist_eq`. -/
lemma condexp_indicator_eq_of_pair_law_eq
    {Ω α β : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace α] [mβ : MeasurableSpace β]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (Y Y' : Ω → α) (Z : Ω → β)
    (hY : Measurable Y) (hY' : Measurable Y') (hZ : Measurable Z)
    (hpair : Measure.map (fun ω => (Y ω, Z ω)) μ
           = Measure.map (fun ω => (Y' ω, Z ω)) μ)
    {B : Set α} (hB : MeasurableSet B) :
  μ[(Set.indicator B (fun _ => (1:ℝ))) ∘ Y | MeasurableSpace.comap Z mβ]
    =ᵐ[μ]
  μ[(Set.indicator B (fun _ => (1:ℝ))) ∘ Y' | MeasurableSpace.comap Z mβ] := by
  classical
  -- Set up notation
  set f := (Set.indicator B (fun _ => (1:ℝ))) ∘ Y
  set f' := (Set.indicator B (fun _ => (1:ℝ))) ∘ Y'
  set mZ := MeasurableSpace.comap Z mβ

  -- Prove that comap Z is a sub-σ-algebra of the ambient space
  have hmZ_le : mZ ≤ mΩ := by
    intro s hs
    -- s ∈ comap Z means s = Z⁻¹(E) for some measurable E
    rcases hs with ⟨E, hE, rfl⟩
    -- Z⁻¹(E) is measurable in ambient space since Z is measurable
    exact hZ hE

  -- Integrability
  have hf_int : Integrable f μ := (integrable_const (1:ℝ)).indicator (hY hB)
  have hf'_int : Integrable f' μ := (integrable_const (1:ℝ)).indicator (hY' hB)

  -- Apply ae_eq_condExp_of_forall_setIntegral_eq
  refine (MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq
    (hm := hmZ_le)
    (f := f)
    (g := μ[f' | mZ])
    (hf := hf_int)
    (hg_int_finite := ?hg_int_finite)
    (hg_eq := ?hg_eq)
    (hgm := MeasureTheory.stronglyMeasurable_condExp.aestronglyMeasurable)).symm

  case hg_int_finite =>
    intro s _ _
    exact integrable_condExp.integrableOn

  case hg_eq =>
    intro A hA _
    -- A is in σ(Z), so A = Z⁻¹(E) for some measurable E
    obtain ⟨E, hE, rfl⟩ := hA

    -- Key equality from distributional assumption
    have h_meas_eq : μ (Y ⁻¹' B ∩ Z ⁻¹' E) = μ (Y' ⁻¹' B ∩ Z ⁻¹' E) := by
      -- The pushforward measures agree on rectangles
      have := congr_arg (fun ν => ν (B ×ˢ E)) hpair
      simp only [Measure.map_apply (hY.prodMk hZ) (hB.prod hE),
                 Measure.map_apply (hY'.prodMk hZ) (hB.prod hE)] at this
      -- Convert product preimage to intersection
      have h1 : (fun ω => (Y ω, Z ω)) ⁻¹' (B ×ˢ E) = Y ⁻¹' B ∩ Z ⁻¹' E := by
        ext ω; simp [Set.mem_prod]
      have h2 : (fun ω => (Y' ω, Z ω)) ⁻¹' (B ×ˢ E) = Y' ⁻¹' B ∩ Z ⁻¹' E := by
        ext ω; simp [Set.mem_prod]
      rw [h1, h2] at this
      exact this

    -- LHS: ∫_{Z⁻¹(E)} f dμ = μ(Y⁻¹(B) ∩ Z⁻¹(E))
    -- f ω = indicator B (const 1) (Y ω) = indicator (Y⁻¹' B) (const 1) ω
    have h_lhs : ∫ ω in Z ⁻¹' E, f ω ∂μ = (μ (Y ⁻¹' B ∩ Z ⁻¹' E)).toReal := by
      -- Rewrite f in terms of preimage indicator
      have hf_eq : f = (Y ⁻¹' B).indicator (fun _ => (1:ℝ)) := by
        ext ω
        simp only [f, Function.comp_apply, Set.indicator, Set.mem_preimage]
      rw [hf_eq]
      -- Set integral of indicator: ∫_{Z⁻¹E} 1_{Y⁻¹B} = μ(Y⁻¹B ∩ Z⁻¹E)
      rw [integral_indicator (hY hB)]
      simp only [integral_const]
      -- Double restriction: μ.restrict(Z⁻¹E).restrict(Y⁻¹B) univ = μ(Y⁻¹B ∩ Z⁻¹E)
      rw [Measure.restrict_restrict (hY hB)]
      simp only [smul_eq_mul, mul_one]
      -- (μ.restrict S).real univ = (μ S).toReal
      simp [Measure.real, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]

    -- RHS: ∫_{Z⁻¹(E)} μ[f' | σ(Z)] dμ = ∫_{Z⁻¹(E)} f' dμ (by CE property)
    have h_rhs_ce : ∫ ω in Z ⁻¹' E, μ[f' | mZ] ω ∂μ = ∫ ω in Z ⁻¹' E, f' ω ∂μ :=
      setIntegral_condExp hmZ_le hf'_int ⟨E, hE, rfl⟩

    -- RHS: ∫_{Z⁻¹(E)} f' dμ = μ(Y'⁻¹(B) ∩ Z⁻¹(E))
    have h_rhs : ∫ ω in Z ⁻¹' E, f' ω ∂μ = (μ (Y' ⁻¹' B ∩ Z ⁻¹' E)).toReal := by
      -- Rewrite f' in terms of preimage indicator
      have hf'_eq : f' = (Y' ⁻¹' B).indicator (fun _ => (1:ℝ)) := by
        ext ω
        simp only [f', Function.comp_apply, Set.indicator, Set.mem_preimage]
      rw [hf'_eq]
      -- Set integral of indicator: ∫_{Z⁻¹E} 1_{Y'⁻¹B} = μ(Y'⁻¹B ∩ Z⁻¹E)
      rw [integral_indicator (hY' hB)]
      simp only [integral_const]
      -- Double restriction: μ.restrict(Z⁻¹E).restrict(Y'⁻¹B) univ = μ(Y'⁻¹B ∩ Z⁻¹E)
      rw [Measure.restrict_restrict (hY' hB)]
      simp only [smul_eq_mul, mul_one]
      -- (μ.restrict S).real univ = (μ S).toReal
      simp [Measure.real, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]

    -- Combine: ∫_{Z⁻¹(E)} f dμ = ∫_{Z⁻¹(E)} μ[f' | σ(Z)] dμ
    rw [h_lhs, h_rhs_ce, h_rhs, h_meas_eq]

/-- **Proof of condexp_indicator_eq_of_agree_on_future_rectangles.**

This is a direct application of `condexp_indicator_eq_of_pair_law_eq` with the sequence type. -/
lemma condexp_indicator_eq_of_agree_on_future_rectangles
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X₁ X₂ : Ω → α} {Y : Ω → ℕ → α}
    (hX₁ : Measurable X₁) (hX₂ : Measurable X₂) (hY : Measurable Y)
    (hagree : AgreeOnFutureRectangles
      (Measure.map (fun ω => (X₁ ω, Y ω)) μ)
      (Measure.map (fun ω => (X₂ ω, Y ω)) μ))
    (B : Set α) (hB : MeasurableSet B) :
    μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ X₁
        | MeasurableSpace.comap Y inferInstance]
      =ᵐ[μ]
    μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ X₂
        | MeasurableSpace.comap Y inferInstance] :=
  condexp_indicator_eq_of_pair_law_eq X₁ X₂ Y hX₁ hX₂ hY hagree.measure_eq hB

end Exchangeability.Probability
