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

/-!
# Conditional Expectation API for Exchangeability Proofs

This file provides a reusable API for conditional expectations, conditional independence,
and distributional equality, designed to eliminate repeated boilerplate in the de Finetti
theorem proofs (ViaMartingale, ViaL2, ViaKoopman).

## Purpose

The exchangeability proofs repeatedly need to:
1. Show bounded indicator compositions are integrable
2. Establish conditional independence via projection properties
3. Transfer conditional expectation equalities from distributional assumptions
4. Manage typeclass instances for sub-σ-algebras

This file centralizes these patterns to keep the main proofs clean and maintainable.

## Main Components

### 1. Integrability Infrastructure
- **`integrable_indicator_comp`**: Bounded indicator composition `(1_B ∘ X)` is integrable
  - **Used in**: ViaMartingale (lines 2897, 2904), CommonEnding, multiple locations
  - **Eliminates**: Repeated `(integrable_const 1).indicator` boilerplate
  - **Key insight**: Bounded measurable functions on finite measures are always integrable

### 2. Conditional Independence (Doob's Characterization)
- **`condIndep_of_indicator_condexp_eq`**: Projection property ⇒ conditional independence
  - **Used in**: ViaMartingale conditional independence arguments
  - **Key insight**: Uses mathlib's `ProbabilityTheory.CondIndep` product formula
  
- **`condExp_indicator_mul_indicator_of_condIndep`**: Product formula for indicators
  - Direct application of `ProbabilityTheory.condIndep_iff`
  
- **`condexp_indicator_inter_bridge`**: Typeclass-safe wrapper for ViaMartingale.lean
  - Manages `IsFiniteMeasure` and `SigmaFinite` instances automatically

### 3. Distributional Equality ⇒ Conditional Expectation Equality
- **`condexp_indicator_eq_of_pair_law_eq`**: Core lemma for Axiom 1 (condexp_convergence)
  - **Proof strategy**: If `(Y,Z)` and `(Y',Z)` have same law, then for measurable `B`:
    ```
    𝔼[1_{Y ∈ B} | σ(Z)] = 𝔼[1_{Y' ∈ B} | σ(Z)]  a.e.
    ```
  - **Used in**: ViaMartingale contractability arguments (with Y=X_m, Y'=X_k, Z=shift)
  - **Key technique**: Uniqueness of conditional expectation via integral identity
  
- **`condexp_indicator_eq_of_agree_on_future_rectangles`**: Application to sequences
  - Wrapper for exchangeable sequence contexts

### 4. Sub-σ-algebra Infrastructure
- **`condExpWith`**: Explicit instance management wrapper
  - **Purpose**: Avoids typeclass metavariable issues in `μ[f | m]`
  - **Used in**: ViaMartingale finite-future sigma algebras
  
- **`isFiniteMeasure_trim`**, **`sigmaFinite_trim`**: Trimmed measure instances
  - **Used in**: ViaMartingale (line 582), multiple sub-σ-algebra constructions
  - **Key fact**: Trimmed finite measures remain finite

## Design Philosophy

**Extract patterns that:**
1. Appear 3+ times across proof files
2. Have 5+ lines of boilerplate
3. Require careful typeclass management
4. Encode reusable probabilistic insights

**Keep in main proofs:**
- Domain-specific constructions (finFutureSigma, tailSigma, etc.)
- Proof-specific calculations
- High-level proof architecture

## Related Files

- **CondExpBasic.lean**: Basic conditional expectation utilities
- **CondProb.lean**: Conditional probability definitions
- **ViaMartingale.lean**: Main consumer of this API
- **ViaL2.lean**: Uses integrability lemmas
- **ViaKoopman.lean**: Uses integrability and independence lemmas

## References

* Kallenberg, *Probabilistic Symmetries and Invariance Principles* (2005)
* Mathlib's conditional expectation infrastructure (`MeasureTheory.Function.ConditionalExpectation`)
* Mathlib's conditional independence (`ProbabilityTheory.CondIndep`)
-/

noncomputable section
open scoped MeasureTheory ProbabilityTheory Topology
open MeasureTheory Filter Set Function

namespace Exchangeability.Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-! ### Integrability lemmas for indicators -/

/-- **Integrability of bounded indicator compositions.**

Given a measurable function `X : Ω → α`, a measurable set `B : Set α`, the indicator
composition `(Set.indicator B (fun _ => (1 : ℝ))) ∘ X` is integrable on any finite
measure space. This is immediate since the function is bounded by 1 and measurable.

This lemma is used repeatedly in de Finetti proofs when showing conditional expectations
of indicators are integrable. -/
lemma integrable_indicator_comp
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : Ω → α} (hX : Measurable X)
    {B : Set α} (hB : MeasurableSet B) :
    Integrable ((Set.indicator B (fun _ => (1 : ℝ))) ∘ X) μ := by
  -- Measurability of the composition
  have h_meas : Measurable ((Set.indicator B (fun _ : α => (1 : ℝ))) ∘ X) := by
    fun_prop (disch := measurability)
  
  -- Boundedness: ‖indicator ∘ X‖ ≤ 1 everywhere
  have h_bound : ∀ᵐ ω ∂μ, ‖((Set.indicator B (fun _ => (1 : ℝ))) ∘ X) ω‖ ≤ (1 : ℝ) := by
    apply ae_of_all
    intro ω
    by_cases hω : X ω ∈ B
    · simp [Function.comp, Set.indicator_of_mem hω]
    · simp [Function.comp, Set.indicator_of_notMem hω]
  
  -- Bounded measurable function on finite measure space is integrable
  exact Integrable.of_bound h_meas.aestronglyMeasurable 1 h_bound

/-! ### Pair-law ⇒ conditional indicator equality (stub) -/

/-- Standard cylinder on the first `r` coordinates starting at index 0.

**NOTE**: This is intentionally duplicated from `PathSpace.CylinderHelpers.cylinder` to
avoid a circular import. CondExp is a low-level module that cannot import PathSpace,
but needs this definition for working with product measures on sequence spaces. -/
def cylinder (α : Type*) (r : ℕ) (C : Fin r → Set α) : Set (ℕ → α) :=
  {f | ∀ i : Fin r, f i ∈ C i}

-- NOTE: AgreeOnFutureRectangles was removed - it was just wrapping measure equality.
-- The real AgreeOnFutureRectangles definition (rectangle agreement implies equality)
-- is in ViaMartingale.lean where it's actually used to prove measure equality from
-- agreement on generating sets.

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
    (μ : Measure Ω) [IsFiniteMeasure μ]
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
    {μ : Measure Ω} [IsFiniteMeasure μ]
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
      -- Set integral of indicator: ∫_{Z⁻¹E} 1_{Y⁻¹B} = μ(Y⁻¹B ∩ Z⁻¹E)
      simp_rw [hf_eq, integral_indicator (hY hB)]
      simp only [integral_const]
      -- Double restriction: μ.restrict(Z⁻¹E).restrict(Y⁻¹B) univ = μ(Y⁻¹B ∩ Z⁻¹E)
      simp_rw [Measure.restrict_restrict (hY hB)]
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
      -- Set integral of indicator: ∫_{Z⁻¹E} 1_{Y'⁻¹B} = μ(Y'⁻¹B ∩ Z⁻¹E)
      simp_rw [hf'_eq, integral_indicator (hY' hB)]
      simp only [integral_const]
      -- Double restriction: μ.restrict(Z⁻¹E).restrict(Y'⁻¹B) univ = μ(Y'⁻¹B ∩ Z⁻¹E)
      simp_rw [Measure.restrict_restrict (hY' hB)]
      simp only [smul_eq_mul, mul_one]
      -- (μ.restrict S).real univ = (μ S).toReal
      simp [Measure.real, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]

    -- Combine: ∫_{Z⁻¹(E)} f dμ = ∫_{Z⁻¹(E)} μ[f' | σ(Z)] dμ
    simp_rw [h_lhs, h_rhs_ce, h_rhs, h_meas_eq]

/-- **Proof of condexp_indicator_eq_of_agree_on_future_rectangles.**

This is a direct application of `condexp_indicator_eq_of_pair_law_eq` with the sequence type. -/
lemma condexp_indicator_eq_of_agree_on_future_rectangles
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X₁ X₂ : Ω → α} {Y : Ω → ℕ → α}
    (hX₁ : Measurable X₁) (hX₂ : Measurable X₂) (hY : Measurable Y)
    (heq : Measure.map (fun ω => (X₁ ω, Y ω)) μ = Measure.map (fun ω => (X₂ ω, Y ω)) μ)
    (B : Set α) (hB : MeasurableSet B) :
    μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ X₁
        | MeasurableSpace.comap Y inferInstance]
      =ᵐ[μ]
    μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ X₂
        | MeasurableSpace.comap Y inferInstance] :=
  condexp_indicator_eq_of_pair_law_eq X₁ X₂ Y hX₁ hX₂ hY heq hB

/-! ### Operator-Theoretic Conditional Expectation Utilities -/

section OperatorTheoretic

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Bounded measurable functions are integrable on finite measures.

NOTE: Check if this exists in mathlib! This is a standard result. -/
lemma integrable_of_bounded [IsFiniteMeasure μ]
    {f : Ω → ℝ} (hf : Measurable f) (hbd : ∃ C, ∀ ω, |f ω| ≤ C) :
    Integrable f μ := by
  obtain ⟨C, hC⟩ := hbd
  exact ⟨hf.aestronglyMeasurable, HasFiniteIntegral.of_bounded (ae_of_all μ hC)⟩

/-- Product of integrable and bounded measurable functions is integrable. -/
lemma integrable_of_bounded_mul [IsFiniteMeasure μ]
    {f g : Ω → ℝ} (hf : Integrable f μ) (hg : Measurable g)
    (hbd : ∃ C, ∀ ω, |g ω| ≤ C) :
    Integrable (f * g) μ := by
  sorry
  -- TODO: This should follow from Integrable.bdd_mul or similar
  -- Strategy: |f·g| ≤ C·|f|, so ∫|f·g| ≤ C·∫|f| < ∞

/-- Conditional expectation preserves monotonicity (in absolute value).

If |f| ≤ |g| everywhere, then |E[f|m]| ≤ E[|g||m]. -/
lemma condExp_abs_le_of_abs_le [IsFiniteMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ ‹_›)
    {f g : Ω → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (h : ∀ ω, |f ω| ≤ |g ω|) :
    ∀ᵐ ω ∂μ, |μ[f|m] ω| ≤ μ[(fun ω' => |g ω'|)|m] ω := by
  sorry
  -- Strategy:
  -- 1. Use that CE is linear and monotone
  -- 2. -|g| ≤ f ≤ |g| implies E[-|g||m] ≤ E[f|m] ≤ E[|g||m]
  -- 3. Therefore |E[f|m]| ≤ E[|g||m]

/-- **Conditional expectation is L¹-nonexpansive** (load-bearing lemma).

For integrable functions f, g, the conditional expectation is contractive in L¹:
  ‖E[f|m] - E[g|m]‖₁ ≤ ‖f - g‖₁

This is the key operator-theoretic property that makes CE well-behaved. -/
lemma condExp_L1_lipschitz [IsFiniteMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ ‹_›)
    {f g : Ω → ℝ} (hf : Integrable f μ) (hg : Integrable g μ) :
    ∫ ω, |μ[f|m] ω - μ[g|m] ω| ∂μ ≤ ∫ ω, |f ω - g ω| ∂μ := by
  sorry
  -- Strategy:
  -- 1. Rewrite LHS as ∫ |μ[f - g|m]|
  -- 2. Use that CE is a contractive projection: ‖CE(h)‖₁ ≤ ‖h‖₁
  -- 3. This follows from CE having operator norm = 1 as an L¹ → L¹ map
  -- 4. Apply Jensen's inequality or use mathlib's condexp_L1_clm properties

/-- Conditional expectation pull-out property for bounded measurable functions.

If g is m-measurable and bounded, then E[f·g|m] = E[f|m]·g a.e. -/
lemma condExp_mul_pullout [IsFiniteMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ ‹_›)
    {f g : Ω → ℝ} (hf : Integrable f μ)
    (hg_meas : @Measurable Ω ℝ m _ g)
    (hg_bd : ∃ C, ∀ ω, |g ω| ≤ C) :
    μ[f * g|m] =ᵐ[μ] fun ω => μ[f|m] ω * g ω := by
  sorry
  -- Strategy:
  -- 1. This is a standard pull-out property for m-measurable g
  -- 2. Can be derived from condExp_L1_lipschitz + approximation
  -- 3. Or use mathlib's condexp_smul if g is simple, then approximate

end OperatorTheoretic

end Exchangeability.Probability
