/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Exchangeability.Probability.CondExpHelpers
import Exchangeability.Probability.CondExp

/-!
# Conditional Independence

This file defines conditional independence for random variables and establishes
basic properties. The definition uses indicator functions on measurable rectangles,
which can then be extended to bounded measurable functions via monotone class arguments.

## Main definitions

* `CondIndep Y Z W μ`: Y and Z are conditionally independent given W under measure μ,
  denoted Y ⊥⊥_W Z, defined via indicator test functions on Borel sets.

## Main results

* `condIndep_symm`: Conditional independence is symmetric (Y ⊥⊥_W Z ↔ Z ⊥⊥_W Y)
* `condIndep_of_indep`: Unconditional independence implies conditional independence

## Implementation notes

We use an indicator-based characterization rather than σ-algebra formalism to avoid
requiring a full conditional distribution API. The definition states that for all
Borel sets A, B:

  E[1_A(Y) · 1_B(Z) | σ(W)] = E[1_A(Y) | σ(W)] · E[1_B(Z) | σ(W)]  a.e.

This is equivalent to the standard σ-algebra definition but more elementary to work with.

## References

* Kallenberg (2005), *Probabilistic Symmetries and Invariance Principles*, Section 6.1
* Kallenberg (2002), *Foundations of Modern Probability*, Chapter 6

## TODO

* Extend from indicators to bounded measurable functions (monotone class argument)
* Prove conditional independence from distributional equality (Kallenberg Lemma 1.3)
* Prove projection property: If Y ⊥⊥_W Z, then E[f(Y)|σ(Z,W)] = E[f(Y)|σ(W)]

-/

noncomputable section
open scoped MeasureTheory ENNReal
open MeasureTheory ProbabilityTheory Set Exchangeability.Probability

variable {Ω α β γ : Type*}
variable [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

/-!
## Definition of conditional independence
-/

/-- **Conditional independence via indicator test functions.**

Random variables Y and Z are **conditionally independent given W** under measure μ,
denoted Y ⊥⊥_W Z, if for all Borel sets A and B:

  E[1_A(Y) · 1_B(Z) | σ(W)] = E[1_A(Y) | σ(W)] · E[1_B(Z) | σ(W)]  a.e.

**Mathematical content:** This says that knowing W, the events {Y ∈ A} and {Z ∈ B}
are independent: P(Y ∈ A, Z ∈ B | W) = P(Y ∈ A | W) · P(Z ∈ B | W).

**Why indicators suffice:** By linearity and approximation, this extends to all bounded
measurable functions. The key is that indicators generate the bounded measurable functions
via monotone class arguments.

**Relation to σ-algebra definition:** This is equivalent to σ(Y) ⊥⊥_σ(W) σ(Z), but
stated more elementarily without requiring full conditional probability machinery.

**Implementation:** We use `Set.indicator` for the characteristic function 1_A.
-/
def CondIndep {Ω α β γ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure Ω) (Y : Ω → α) (Z : Ω → β) (W : Ω → γ) : Prop :=
  ∀ (A : Set α) (B : Set β), MeasurableSet A → MeasurableSet B →
    μ[ (Set.indicator (Y ⁻¹' A) (fun _ => (1 : ℝ))) *
       (Set.indicator (Z ⁻¹' B) (fun _ => (1 : ℝ)))
       | MeasurableSpace.comap W (by infer_instance) ]
      =ᵐ[μ]
    μ[ Set.indicator (Y ⁻¹' A) (fun _ => (1 : ℝ))
       | MeasurableSpace.comap W (by infer_instance) ]
    *
    μ[ Set.indicator (Z ⁻¹' B) (fun _ => (1 : ℝ))
       | MeasurableSpace.comap W (by infer_instance) ]

/-!
## Basic properties
-/

/-- **Symmetry of conditional independence.**

If Y ⊥⊥_W Z, then Z ⊥⊥_W Y. This follows immediately from commutativity of multiplication.
-/
theorem condIndep_symm (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Ω → α) (Z : Ω → β) (W : Ω → γ) :
    CondIndep μ Y Z W ↔ CondIndep μ Z Y W := by
  constructor <;> intro h A B hA hB
  · -- Y ⊥⊥_W Z implies Z ⊥⊥_W Y
    have := h B A hB hA
    -- Swap multiplication order
    simp only [mul_comm] at this ⊢
    exact this
  · -- Z ⊥⊥_W Y implies Y ⊥⊥_W Z (same proof by symmetry)
    have := h B A hB hA
    simp only [mul_comm] at this ⊢
    exact this

/-!
## Helper lemmas for independence and conditional expectation
-/

/-- **Conditional expectation against an independent σ-algebra is constant.**

If X is integrable and measurable with respect to a σ-algebra independent of σ(W),
then E[X | σ(W)] = E[X] almost everywhere.

This is the key property that makes independence "pass through" conditioning:
knowing W provides no information about X when X ⊥ W.
-/
/-
TODO: Add idempotence helper once correct lemma name is identified.

/-- Idempotence of conditional expectation on the target sub-σ-algebra.
If f is m-measurable, then E[f|m] = f almost everywhere.
This avoids hunting for the correct lemma name across mathlib versions. -/
lemma condExp_idem'
    (μ : Measure Ω) (m : MeasurableSpace Ω) (f : Ω → ℝ)
    (hm : m ≤ _)
    (hf_int : Integrable f μ)
    (hf_sm : StronglyMeasurable[m] f) :
    μ[f | m] =ᵐ[μ] f := by
  -- Try the most common name first:
  simpa using
    (condexp_of_stronglyMeasurable  -- This name doesn't exist in current mathlib
      (μ := μ) (m := m) (hm := hm) (hfmeas := hf_sm) (hfint := hf_int))
  -- If this fails in your build, replace the line above with either:
  -- (1) `condexp_of_aestronglyMeasurable'` (with `aestronglyMeasurable_of_stronglyMeasurable`)
  -- (2) `condexp_condexp` specialized to `m₁ = m₂ := m`
-/

lemma condExp_const_of_indepFun (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {W : Ω → γ}
    (hX : Measurable X) (hW : Measurable W)
    (h_indep : IndepFun X W μ)
    (hX_int : Integrable X μ) :
    μ[X | MeasurableSpace.comap W (by infer_instance)] =ᵐ[μ] (fun _ => μ[X]) := by
  -- Convert IndepFun to Indep of σ-algebras
  rw [IndepFun_iff_Indep] at h_indep
  -- Apply condExp_indep_eq: E[X|σ(W)] = E[X] when σ(X) ⊥ σ(W)
  refine condExp_indep_eq hX.comap_le hW.comap_le ?_ h_indep
  -- X is σ(X)-strongly measurable (X is measurable from (Ω, σ(X)) to ℝ by definition of comap)
  have : @Measurable Ω ℝ (MeasurableSpace.comap X (by infer_instance)) _ X :=
    Measurable.of_comap_le le_rfl
  exact this.stronglyMeasurable

/-- Extract independence of first component from pair independence. -/
lemma IndepFun.of_comp_left_fst {Y : Ω → α} {Z : Ω → β} {W : Ω → γ}
    (h : IndepFun (fun ω => (Y ω, Z ω)) W μ) :
    IndepFun Y W μ := by
  -- Y = Prod.fst ∘ (fun ω => (Y ω, Z ω))
  -- So Y ⊥ W follows from (Y,Z) ⊥ W by composition
  have : Y = Prod.fst ∘ (fun ω => (Y ω, Z ω)) := by rfl
  rw [this]
  exact h.comp measurable_fst measurable_id

/-- Extract independence of second component from pair independence. -/
lemma IndepFun.of_comp_left_snd {Y : Ω → α} {Z : Ω → β} {W : Ω → γ}
    (h : IndepFun (fun ω => (Y ω, Z ω)) W μ) :
    IndepFun Z W μ := by
  -- Z = Prod.snd ∘ (fun ω => (Y ω, Z ω))
  -- So Z ⊥ W follows from (Y,Z) ⊥ W by composition
  have : Z = Prod.snd ∘ (fun ω => (Y ω, Z ω)) := by rfl
  rw [this]
  exact h.comp measurable_snd measurable_id

/-!
## Conditional independence from unconditional independence
-/

/-- **Independence plus independence of pair from W implies conditional independence.**

If Y and Z are (unconditionally) independent, and the pair (Y,Z) is independent of W,
then Y ⊥⊥_W Z.

**Key insight:** Independence of (Y,Z) from W means the conditional law of (Y,Z) given W
equals the unconditional law, so the factorization E[1_A(Y)·1_B(Z)] = E[1_A(Y)]·E[1_B(Z)]
survives conditioning on W.

**Counterexample showing Y ⊥ Z alone is NOT enough:**
- Y, Z: independent fair coin flips
- W := Y + Z
- Then Y ⊥ Z unconditionally, but P(Y=1|Z=1,W=1) = 1 ≠ 1/2 = P(Y=1|W=1),
  so Y and Z are NOT conditionally independent given W.

**Proof strategy:**
1. Since (Y,Z) ⊥ W, conditional expectation of any function of (Y,Z) given σ(W)
   is the constant E[that function].
2. Apply to 1_A(Y), 1_B(Z), and their product.
3. The unconditional factorization E[1_A(Y)·1_B(Z)] = E[1_A(Y)]·E[1_B(Z)] (from Y ⊥ Z)
   transfers to the conditional expectations.
-/

-- Product of two unit indicator functions equals the indicator of the intersection.
private lemma mul_indicator_one_eq_indicator_inter {Ω : Type*} (S T : Set Ω) :
    (S.indicator (fun _ => (1 : ℝ))) * (T.indicator (fun _ => (1 : ℝ)))
      = (S ∩ T).indicator (fun _ => (1 : ℝ)) := by
  classical
  ext ω
  simp only [Pi.mul_apply]
  by_cases hS : ω ∈ S <;> by_cases hT : ω ∈ T
  · rw [Set.indicator_of_mem hS, Set.indicator_of_mem hT]
    have : ω ∈ S ∩ T := ⟨hS, hT⟩
    rw [Set.indicator_of_mem this]; norm_num
  · rw [Set.indicator_of_mem hS, Set.indicator_of_notMem hT]
    have : ω ∉ S ∩ T := fun h => hT h.2
    rw [Set.indicator_of_notMem this]; norm_num
  · rw [Set.indicator_of_notMem hS, Set.indicator_of_mem hT]
    have : ω ∉ S ∩ T := fun h => hS h.1
    rw [Set.indicator_of_notMem this]; norm_num
  · rw [Set.indicator_of_notMem hS, Set.indicator_of_notMem hT]
    have : ω ∉ S ∩ T := fun h => hS h.1
    rw [Set.indicator_of_notMem this]; norm_num

-- Product of indicators composed with functions equals indicator of product set composed with pair.
private lemma mul_indicator_comp_pair_eq_indicator_prod {Ω α β : Type*}
    (Y : Ω → α) (Z : Ω → β) (A : Set α) (B : Set β) :
    ((Y ⁻¹' A).indicator (fun _ => (1 : ℝ))) * ((Z ⁻¹' B).indicator (fun _ => (1 : ℝ)))
      = (fun p => (A ×ˢ B).indicator (fun _ => (1 : ℝ)) p) ∘ (fun ω => (Y ω, Z ω)) := by
  classical
  ext ω
  simp only [Pi.mul_apply, Function.comp_apply]
  by_cases hY : ω ∈ Y ⁻¹' A <;> by_cases hZ : ω ∈ Z ⁻¹' B
  · rw [Set.indicator_of_mem hY, Set.indicator_of_mem hZ]
    have : (Y ω, Z ω) ∈ A ×ˢ B := Set.mk_mem_prod hY hZ
    rw [Set.indicator_of_mem this]; norm_num
  · rw [Set.indicator_of_mem hY, Set.indicator_of_notMem hZ]
    have : (Y ω, Z ω) ∉ A ×ˢ B := fun h => hZ h.2
    rw [Set.indicator_of_notMem this]; norm_num
  · rw [Set.indicator_of_notMem hY, Set.indicator_of_mem hZ]
    have : (Y ω, Z ω) ∉ A ×ˢ B := fun h => hY h.1
    rw [Set.indicator_of_notMem this]; norm_num
  · rw [Set.indicator_of_notMem hY, Set.indicator_of_notMem hZ]
    have : (Y ω, Z ω) ∉ A ×ˢ B := fun h => hY h.1
    rw [Set.indicator_of_notMem this]; norm_num

theorem condIndep_of_indep_pair (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Ω → α) (Z : Ω → β) (W : Ω → γ)
    (hY : Measurable Y) (hZ : Measurable Z) (hW : Measurable W)
    (hYZ_indep : IndepFun Y Z μ)
    (hPairW_indep : IndepFun (fun ω => (Y ω, Z ω)) W μ) :
    CondIndep μ Y Z W := by
  intro A B hA hB
  -- Define the indicator functions
  let f := Set.indicator (Y ⁻¹' A) (fun _ => (1 : ℝ))
  let g := Set.indicator (Z ⁻¹' B) (fun _ => (1 : ℝ))

  -- f and g are measurable and integrable
  have hf_meas : Measurable f := measurable_const.indicator (hY hA)
  have hg_meas : Measurable g := measurable_const.indicator (hZ hB)
  have hf_int : Integrable f μ := (integrable_const (1 : ℝ)).indicator (hY hA)
  have hg_int : Integrable g μ := (integrable_const (1 : ℝ)).indicator (hZ hB)

  -- Extract Y ⊥ W and Z ⊥ W from pair independence
  have hY_W_indep : IndepFun Y W μ := IndepFun.of_comp_left_fst hPairW_indep
  have hZ_W_indep : IndepFun Z W μ := IndepFun.of_comp_left_snd hPairW_indep

  -- Key insight: f, g, and f*g are all independent of W
  -- Therefore their conditional expectations given σ(W) are constants

  -- Step 1: f is a function of Y, so f ⊥ W
  -- f = (Set.indicator A (fun _ => 1)) ∘ Y
  have hf_indep : IndepFun f W μ := by
    have : f = (Set.indicator A (fun _ => (1 : ℝ))) ∘ Y := by
      ext ω
      simp only [Function.comp_apply, Set.indicator_apply]
      rfl
    rw [this]
    exact hY_W_indep.comp (measurable_const.indicator hA) measurable_id

  -- Step 2: g is a function of Z, so g ⊥ W
  have hg_indep : IndepFun g W μ := by
    have : g = (Set.indicator B (fun _ => (1 : ℝ))) ∘ Z := by
      ext ω
      simp only [Function.comp_apply, Set.indicator_apply]
      rfl
    rw [this]
    exact hZ_W_indep.comp (measurable_const.indicator hB) measurable_id

  -- Step 3: f * g is a function of (Y,Z), so f * g ⊥ W
  have hfg_indep : IndepFun (f * g) W μ := by
    rw [show f * g = (fun p => (A ×ˢ B).indicator (fun _ => (1 : ℝ)) p) ∘ (fun ω => (Y ω, Z ω))
          from mul_indicator_comp_pair_eq_indicator_prod Y Z A B]
    exact hPairW_indep.comp (measurable_const.indicator (hA.prod hB)) measurable_id

  -- Step 4: Apply condExp_const_of_indepFun to get conditional expectations are constants
  have hf_ce : μ[f | MeasurableSpace.comap W (by infer_instance)] =ᵐ[μ] (fun _ => μ[f]) :=
    condExp_const_of_indepFun μ hf_meas hW hf_indep hf_int

  have hg_ce : μ[g | MeasurableSpace.comap W (by infer_instance)] =ᵐ[μ] (fun _ => μ[g]) :=
    condExp_const_of_indepFun μ hg_meas hW hg_indep hg_int

  have hfg_meas : Measurable (f * g) := hf_meas.mul hg_meas
  have hfg_int : Integrable (f * g) μ := by
    rw [show f * g = (Y ⁻¹' A ∩ Z ⁻¹' B).indicator (fun _ => (1 : ℝ))
          from mul_indicator_one_eq_indicator_inter (Y ⁻¹' A) (Z ⁻¹' B)]
    exact (integrable_const (1 : ℝ)).indicator ((hY hA).inter (hZ hB))
  have hfg_ce : μ[f * g | MeasurableSpace.comap W (by infer_instance)] =ᵐ[μ] (fun _ => μ[f * g]) :=
    condExp_const_of_indepFun μ hfg_meas hW hfg_indep hfg_int

  -- Step 5: Use Y ⊥ Z to get unconditional factorization E[f*g] = E[f] * E[g]
  -- Since f is a function of Y and g is a function of Z, f ⊥ g follows from Y ⊥ Z
  have hfg_indep' : IndepFun f g μ := by
    have hf_comp : f = (Set.indicator A (fun _ => (1 : ℝ))) ∘ Y := by
      ext ω
      show f ω = Set.indicator A (fun _ => 1) (Y ω)
      rfl
    have hg_comp : g = (Set.indicator B (fun _ => (1 : ℝ))) ∘ Z := by
      ext ω
      show g ω = Set.indicator B (fun _ => 1) (Z ω)
      rfl
    rw [hf_comp, hg_comp]
    exact hYZ_indep.comp (measurable_const.indicator hA) (measurable_const.indicator hB)

  have h_factor : μ[f * g] = μ[f] * μ[g] :=
    IndepFun.integral_mul_eq_mul_integral hfg_indep' hf_int.aestronglyMeasurable hg_int.aestronglyMeasurable

  -- Step 6: Combine everything
  calc μ[f * g | MeasurableSpace.comap W (by infer_instance)]
      =ᵐ[μ] (fun _ => μ[f * g]) := hfg_ce
    _ = (fun _ => μ[f] * μ[g]) := by rw [h_factor]
    _ =ᵐ[μ] (fun _ => μ[f]) * (fun _ => μ[g]) := by rfl
    _ =ᵐ[μ] μ[f | MeasurableSpace.comap W (by infer_instance)] * μ[g | MeasurableSpace.comap W (by infer_instance)] :=
        Filter.EventuallyEq.mul hf_ce.symm hg_ce.symm

/-!
## Extension to simple functions and bounded measurables (§C2)
-/

/-- **Base case: Factorization for scaled indicators.**

For φ = c • 1_A and ψ = d • 1_B, the factorization follows by extracting scalars
and applying the CondIndep definition. -/
lemma condIndep_indicator (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Ω → α) (Z : Ω → β) (W : Ω → γ)
    (hCI : CondIndep μ Y Z W)
    (c : ℝ) (A : Set α) (hA : MeasurableSet A)
    (d : ℝ) (B : Set β) (hB : MeasurableSet B) :
    μ[ ((A.indicator (fun _ => c)) ∘ Y) * ((B.indicator (fun _ => d)) ∘ Z)
       | MeasurableSpace.comap W (by infer_instance) ]
      =ᵐ[μ]
    μ[ (A.indicator (fun _ => c)) ∘ Y | MeasurableSpace.comap W (by infer_instance) ]
      * μ[ (B.indicator (fun _ => d)) ∘ Z | MeasurableSpace.comap W (by infer_instance) ] := by
  set mW := MeasurableSpace.comap W (by infer_instance)

  -- Rewrite indicators in terms of preimages
  have hY_eq : (A.indicator (fun _ => c)) ∘ Y = fun ω => A.indicator (fun _ => c) (Y ω) := rfl
  have hZ_eq : (B.indicator (fun _ => d)) ∘ Z = fun ω => B.indicator (fun _ => d) (Z ω) := rfl

  -- Rewrite product as scaled product of unit indicators
  have h_prod : ((A.indicator (fun _ => c)) ∘ Y) * ((B.indicator (fun _ => d)) ∘ Z)
      = (c * d) • (((Y ⁻¹' A).indicator (fun _ => 1)) * ((Z ⁻¹' B).indicator (fun _ => 1))) := by
    ext ω
    simp [Set.indicator, Function.comp_apply]
    by_cases hA : Y ω ∈ A <;> by_cases hB : Z ω ∈ B <;> simp [hA, hB] <;> ring

  -- Apply CondIndep to unit indicators
  have h_unit : μ[ ((Y ⁻¹' A).indicator (fun _ => (1 : ℝ))) * ((Z ⁻¹' B).indicator (fun _ => (1 : ℝ))) | mW ]
      =ᵐ[μ] μ[ (Y ⁻¹' A).indicator (fun _ => (1 : ℝ)) | mW ] * μ[ (Z ⁻¹' B).indicator (fun _ => (1 : ℝ)) | mW ] :=
    hCI A B hA hB

  -- Factor out scalars using condExp_smul and combine with h_unit
  calc μ[ ((A.indicator (fun _ => c)) ∘ Y) * ((B.indicator (fun _ => d)) ∘ Z) | mW ]
      = μ[ (c * d) • (((Y ⁻¹' A).indicator (fun _ => 1)) * ((Z ⁻¹' B).indicator (fun _ => 1))) | mW ] := by
        rw [h_prod]
    _ =ᵐ[μ] (c * d) • μ[ ((Y ⁻¹' A).indicator (fun _ => 1)) * ((Z ⁻¹' B).indicator (fun _ => 1)) | mW ] := by
        apply condExp_smul
    _ =ᵐ[μ] (c * d) • (μ[ (Y ⁻¹' A).indicator (fun _ => 1) | mW ] * μ[ (Z ⁻¹' B).indicator (fun _ => 1) | mW ]) := by
        refine Filter.EventuallyEq.fun_comp h_unit (fun x => (c * d) • x)
    _ =ᵐ[μ] (c • μ[ (Y ⁻¹' A).indicator (fun _ => 1) | mW ]) * (d • μ[ (Z ⁻¹' B).indicator (fun _ => 1) | mW ]) := by
        apply Filter.EventuallyEq.of_eq
        ext ω
        simp [Pi.smul_apply, Pi.mul_apply]
        ring
    _ =ᵐ[μ] μ[ c • (Y ⁻¹' A).indicator (fun _ => 1) | mW ] * μ[ d • (Z ⁻¹' B).indicator (fun _ => 1) | mW ] := by
        exact Filter.EventuallyEq.mul (condExp_smul c _ mW).symm (condExp_smul d _ mW).symm
    _ =ᵐ[μ] μ[ (A.indicator (fun _ => c)) ∘ Y | mW ] * μ[ (B.indicator (fun _ => d)) ∘ Z | mW ] := by
        -- Prove c • (Y ⁻¹' A).indicator (fun _ => 1) = (A.indicator (fun _ => c)) ∘ Y
        have hY_ind : c • (Y ⁻¹' A).indicator (fun _ => 1) = (A.indicator (fun _ => c)) ∘ Y := by
          ext ω
          simp only [Pi.smul_apply, Set.indicator, Function.comp_apply, Set.mem_preimage]
          by_cases h : Y ω ∈ A <;> simp [h]
        have hZ_ind : d • (Z ⁻¹' B).indicator (fun _ => 1) = (B.indicator (fun _ => d)) ∘ Z := by
          ext ω
          simp only [Pi.smul_apply, Set.indicator, Function.comp_apply, Set.mem_preimage]
          by_cases h : Z ω ∈ B <;> simp [h]
        rw [hY_ind, hZ_ind]

/-- **Factorization for simple functions (both arguments).**

If Y ⊥⊥_W Z for indicators, extend to simple functions via linearity.
Uses single induction avoiding nested complexity. -/
-- Helper lemma: φ = c • 1_A with arbitrary ψ
lemma condIndep_indicator_simpleFunc (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Ω → α) (Z : Ω → β) (W : Ω → γ)
    (hCI : CondIndep μ Y Z W)
    (c : ℝ) (A : Set α) (hA : MeasurableSet A)
    (ψ : SimpleFunc β ℝ)
    (hY : Measurable Y) (hZ : Measurable Z) :
    μ[ ((A.indicator (fun _ => c)) ∘ Y) * (ψ ∘ Z) | MeasurableSpace.comap W (by infer_instance) ]
      =ᵐ[μ]
    μ[ (A.indicator (fun _ => c)) ∘ Y | MeasurableSpace.comap W (by infer_instance) ]
      * μ[ ψ ∘ Z | MeasurableSpace.comap W (by infer_instance) ] := by
  -- Induct on ψ
  refine SimpleFunc.induction ?const ?add ψ
  case const =>
    intro d B hB
    exact condIndep_indicator μ Y Z W hCI c A hA d B hB
  case add =>
    intro ψ1 ψ2 hψ_disj hψ1_ih hψ2_ih
    -- Goal: μ[φY * (ψ1+ψ2)Z | mW] =ᵐ μ[φY | mW] * μ[(ψ1+ψ2)Z | mW]
    -- where φY = (A.indicator c) ∘ Y

    -- Distribute: φY * (ψ1+ψ2)Z = φY * ψ1Z + φY * ψ2Z
    have h_dist : ((A.indicator (fun _ => c)) ∘ Y) * ((ψ1 + ψ2) ∘ Z)
        = ((A.indicator (fun _ => c)) ∘ Y) * (ψ1 ∘ Z) + ((A.indicator (fun _ => c)) ∘ Y) * (ψ2 ∘ Z) := by
      ext ω; simp [Pi.add_apply, mul_add]

    -- Apply IH to get factorization for ψ1 and ψ2
    -- hψ1_ih : μ[φY * ψ1Z | mW] =ᵐ μ[φY | mW] * μ[ψ1Z | mW]
    -- hψ2_ih : μ[φY * ψ2Z | mW] =ᵐ μ[φY | mW] * μ[ψ2Z | mW]

    calc μ[((A.indicator (fun _ => c)) ∘ Y) * ((ψ1 + ψ2) ∘ Z) | MeasurableSpace.comap W (by infer_instance)]
        = μ[((A.indicator (fun _ => c)) ∘ Y) * (ψ1 ∘ Z) + ((A.indicator (fun _ => c)) ∘ Y) * (ψ2 ∘ Z)
            | MeasurableSpace.comap W (by infer_instance)] := by rw [h_dist]
      _ =ᵐ[μ] μ[((A.indicator (fun _ => c)) ∘ Y) * (ψ1 ∘ Z) | MeasurableSpace.comap W (by infer_instance)]
              + μ[((A.indicator (fun _ => c)) ∘ Y) * (ψ2 ∘ Z) | MeasurableSpace.comap W (by infer_instance)] := by
          -- Need integrability to apply condExp_add
          have hψ1_int : Integrable (ψ1 ∘ Z) μ := by
            refine Integrable.comp_measurable ?_ hZ
            exact SimpleFunc.integrable_of_isFiniteMeasure ψ1
          have hψ2_int : Integrable (ψ2 ∘ Z) μ := by
            refine Integrable.comp_measurable ?_ hZ
            exact SimpleFunc.integrable_of_isFiniteMeasure ψ2
          have h1_int : Integrable (((A.indicator (fun _ => c)) ∘ Y) * (ψ1 ∘ Z)) μ := by
            refine Integrable.bdd_mul' (c := |c|) ?_ ?_ ?_
            · exact hψ1_int
            · exact ((measurable_const.indicator hA).comp hY).aestronglyMeasurable
            · filter_upwards with ω
              simp only [Function.comp_apply, Set.indicator, norm_indicator_eq_indicator_norm]
              by_cases h : Y ω ∈ A <;> simp [h, le_abs_self, abs_nonneg]
          have h2_int : Integrable (((A.indicator (fun _ => c)) ∘ Y) * (ψ2 ∘ Z)) μ := by
            refine Integrable.bdd_mul' (c := |c|) ?_ ?_ ?_
            · exact hψ2_int
            · exact ((measurable_const.indicator hA).comp hY).aestronglyMeasurable
            · filter_upwards with ω
              simp only [Function.comp_apply, Set.indicator, norm_indicator_eq_indicator_norm]
              by_cases h : Y ω ∈ A <;> simp [h, le_abs_self, abs_nonneg]
          exact condExp_add h1_int h2_int _
      _ =ᵐ[μ] (μ[(A.indicator (fun _ => c)) ∘ Y | MeasurableSpace.comap W (by infer_instance)] * μ[ψ1 ∘ Z | MeasurableSpace.comap W (by infer_instance)])
              + (μ[(A.indicator (fun _ => c)) ∘ Y | MeasurableSpace.comap W (by infer_instance)] * μ[ψ2 ∘ Z | MeasurableSpace.comap W (by infer_instance)]) :=
          Filter.EventuallyEq.add hψ1_ih hψ2_ih
      _ =ᵐ[μ] μ[(A.indicator (fun _ => c)) ∘ Y | MeasurableSpace.comap W (by infer_instance)]
              * (μ[ψ1 ∘ Z | MeasurableSpace.comap W (by infer_instance)] + μ[ψ2 ∘ Z | MeasurableSpace.comap W (by infer_instance)]) := by
          apply Filter.EventuallyEq.of_eq
          simp only [Pi.add_apply, Pi.mul_apply, mul_add]
      _ =ᵐ[μ] μ[(A.indicator (fun _ => c)) ∘ Y | MeasurableSpace.comap W (by infer_instance)]
              * μ[(ψ1 + ψ2) ∘ Z | MeasurableSpace.comap W (by infer_instance)] := by
          -- Apply condExp_add in reverse on RHS to combine ψ1 and ψ2
          have hψ1_int : Integrable (ψ1 ∘ Z) μ := by
            refine Integrable.comp_measurable ?_ hZ
            exact SimpleFunc.integrable_of_isFiniteMeasure ψ1
          have hψ2_int : Integrable (ψ2 ∘ Z) μ := by
            refine Integrable.comp_measurable ?_ hZ
            exact SimpleFunc.integrable_of_isFiniteMeasure ψ2
          exact Filter.EventuallyEq.mul Filter.EventuallyEq.rfl (condExp_add hψ1_int hψ2_int _).symm

lemma condIndep_simpleFunc (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Ω → α) (Z : Ω → β) (W : Ω → γ)
    (hCI : CondIndep μ Y Z W)
    (φ : SimpleFunc α ℝ) (ψ : SimpleFunc β ℝ)
    (hY : Measurable Y) (hZ : Measurable Z) :
    μ[ (φ ∘ Y) * (ψ ∘ Z) | MeasurableSpace.comap W (by infer_instance) ]
      =ᵐ[μ]
    μ[ φ ∘ Y | MeasurableSpace.comap W (by infer_instance) ]
      * μ[ ψ ∘ Z | MeasurableSpace.comap W (by infer_instance) ] := by
  -- Induct on φ
  refine SimpleFunc.induction ?const ?add φ
  case const =>
    intro c A hA
    exact condIndep_indicator_simpleFunc μ Y Z W hCI c A hA ψ hY hZ
  case add =>
    intro φ1 φ2 hφ_disj hφ1_ih hφ2_ih
    -- Goal: μ[(φ1+φ2)Y * ψZ | mW] =ᵐ μ[(φ1+φ2)Y | mW] * μ[ψZ | mW]

    -- Distribute: (φ1+φ2)Y * ψZ = φ1Y * ψZ + φ2Y * ψZ
    have h_dist : ((φ1 + φ2) ∘ Y) * (ψ ∘ Z)
        = ((φ1 ∘ Y) * (ψ ∘ Z)) + ((φ2 ∘ Y) * (ψ ∘ Z)) := by
      ext ω; simp [Pi.add_apply, add_mul]

    calc μ[((φ1 + φ2) ∘ Y) * (ψ ∘ Z) | MeasurableSpace.comap W (by infer_instance)]
        = μ[((φ1 ∘ Y) * (ψ ∘ Z)) + ((φ2 ∘ Y) * (ψ ∘ Z)) | MeasurableSpace.comap W (by infer_instance)] := by rw [h_dist]
      _ =ᵐ[μ] μ[(φ1 ∘ Y) * (ψ ∘ Z) | MeasurableSpace.comap W (by infer_instance)]
              + μ[(φ2 ∘ Y) * (ψ ∘ Z) | MeasurableSpace.comap W (by infer_instance)] := by
          -- Need integrability
          have hφ1_int : Integrable (φ1 ∘ Y) μ := by
            refine Integrable.comp_measurable ?_ hY
            exact SimpleFunc.integrable_of_isFiniteMeasure φ1
          have hφ2_int : Integrable (φ2 ∘ Y) μ := by
            refine Integrable.comp_measurable ?_ hY
            exact SimpleFunc.integrable_of_isFiniteMeasure φ2
          have hψ_int : Integrable (ψ ∘ Z) μ := by
            refine Integrable.comp_measurable ?_ hZ
            exact SimpleFunc.integrable_of_isFiniteMeasure ψ
          have h1_int : Integrable ((φ1 ∘ Y) * (ψ ∘ Z)) μ := by
            apply Integrable.bdd_mul hψ_int
            · exact (φ1.measurable.comp hY).aestronglyMeasurable
            · use (φ1.range.sup (fun x => ‖x‖₊)).toReal
              intro x
              simp only [Function.comp_apply]
              rw [← coe_nnnorm, NNReal.coe_le_coe]
              exact Finset.le_sup (SimpleFunc.mem_range_self φ1 (Y x))
          have h2_int : Integrable ((φ2 ∘ Y) * (ψ ∘ Z)) μ := by
            apply Integrable.bdd_mul hψ_int
            · exact (φ2.measurable.comp hY).aestronglyMeasurable
            · use (φ2.range.sup (fun x => ‖x‖₊)).toReal
              intro x
              simp only [Function.comp_apply]
              rw [← coe_nnnorm, NNReal.coe_le_coe]
              exact Finset.le_sup (SimpleFunc.mem_range_self φ2 (Y x))
          exact condExp_add h1_int h2_int _
      _ =ᵐ[μ] (μ[φ1 ∘ Y | MeasurableSpace.comap W (by infer_instance)] * μ[ψ ∘ Z | MeasurableSpace.comap W (by infer_instance)])
              + (μ[φ2 ∘ Y | MeasurableSpace.comap W (by infer_instance)] * μ[ψ ∘ Z | MeasurableSpace.comap W (by infer_instance)]) :=
          Filter.EventuallyEq.add hφ1_ih hφ2_ih
      _ =ᵐ[μ] (μ[φ1 ∘ Y | MeasurableSpace.comap W (by infer_instance)] + μ[φ2 ∘ Y | MeasurableSpace.comap W (by infer_instance)])
              * μ[ψ ∘ Z | MeasurableSpace.comap W (by infer_instance)] := by
          apply Filter.EventuallyEq.of_eq
          simp only [Pi.add_apply, Pi.mul_apply, add_mul]
      _ =ᵐ[μ] μ[(φ1 + φ2) ∘ Y | MeasurableSpace.comap W (by infer_instance)]
              * μ[ψ ∘ Z | MeasurableSpace.comap W (by infer_instance)] := by
          -- Apply condExp_add in reverse on LHS
          have hφ1_int : Integrable (φ1 ∘ Y) μ := by
            refine Integrable.comp_measurable ?_ hY
            exact SimpleFunc.integrable_of_isFiniteMeasure φ1
          have hφ2_int : Integrable (φ2 ∘ Y) μ := by
            refine Integrable.comp_measurable ?_ hY
            exact SimpleFunc.integrable_of_isFiniteMeasure φ2
          exact Filter.EventuallyEq.mul (condExp_add hφ1_int hφ2_int _).symm Filter.EventuallyEq.rfl

/-!
## Helper lemmas for bounded measurable extension
-/

/-- **CE is continuous from L¹ to L¹ (wrapper around mathlib's lemma).** -/
lemma tendsto_condexp_L1 {mΩ : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    {fn : ℕ → Ω → ℝ} {f : Ω → ℝ}
    (h_int : ∀ n, Integrable (fn n) μ) (hf : Integrable f μ)
    (hL1 : Filter.Tendsto (fun n => ∫⁻ ω, ‖(fn n) ω - f ω‖₊ ∂μ) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => μ[fn n | m]) Filter.atTop (nhds (μ[f | m])) := by
  -- Replace with the proper lemma in your mathlib build
  -- e.g., condexp_tendsto_L1 or use condexpL1 continuity
  sorry

/-- **Helper: approximate bounded measurable function by simple functions.** -/
lemma approx_bounded_measurable (μ : Measure α) [IsProbabilityMeasure μ]
    {f : α → ℝ} (M : ℝ) (hf_meas : Measurable f)
    (hf_bdd : ∀ᵐ x ∂μ, |f x| ≤ M) :
    ∃ (fn : ℕ → SimpleFunc α ℝ),
      (∀ n, ∀ᵐ x ∂μ, |fn n x| ≤ M) ∧
      (∀ᵐ x ∂μ, Filter.Tendsto (fun n => (fn n) x) Filter.atTop (nhds (f x))) ∧
      (Filter.Tendsto (fun n => ∫⁻ x, ‖(fn n) x - f x‖₊ ∂μ) Filter.atTop (nhds 0)) := by
  -- Use SimpleFunc.eapprox or similar from mathlib
  sorry

/-- **Conditional independence for simple functions (left argument).**
Refactored to avoid instance pollution: works with σ(W) directly. -/
lemma condIndep_simpleFunc_left
    {Ω α β γ : Type*}
    {m₀ : MeasurableSpace Ω}  -- Explicit ambient space
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure Ω) [IsProbabilityMeasure μ]  -- μ explicit, instances after
    (Y : Ω → α) (Z : Ω → β) (W : Ω → γ)  -- Then plain parameters
    (hCI : @CondIndep Ω α β γ m₀ _ _ _ μ Y Z W)
    (φ : SimpleFunc α ℝ) {ψ : β → ℝ}
    (hY : @Measurable Ω α m₀ _ Y) (hZ : @Measurable Ω β m₀ _ Z)
    (hψ_meas : Measurable ψ) :
    μ[ (φ ∘ Y) * (ψ ∘ Z) | MeasurableSpace.comap W inferInstance ] =ᵐ[μ]
    μ[ φ ∘ Y | MeasurableSpace.comap W inferInstance ] *
    μ[ ψ ∘ Z | MeasurableSpace.comap W inferInstance ] := by
  -- Approximate ψ by simple functions, apply condIndep_simpleFunc at each step, pass to limit
  -- This requires similar approximation machinery as condIndep_bddMeas_extend_left
  -- For now, we'll leave this as a sorry and implement it after the approximation helpers are done
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
      exact condIndep_simpleFunc_left μ Y Z W hCI (sφ n) hY hZ hψ_meas

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
      -- Strategy: h_L1_conv gives Lp convergence of condExpL1, which is equivalent to eLpNorm convergence:
      --   ‖condExpL1 ((sφ n) ∘ Y) - condExpL1 (φ ∘ Y)‖₁ → 0
      --
      -- Combined with hψZ_bdd (ψZ term is essentially bounded by Mψ), we get:
      --   ‖(condExpL1 ((sφ n) ∘ Y) - condExpL1 (φ ∘ Y)) * condExpL1 (ψ ∘ Z)‖₁ → 0
      -- by Hölder's inequality with L¹ and L^∞ (since ‖f*g‖₁ ≤ ‖f‖₁ * ‖g‖_∞).
      --
      -- Then use tendsto_setIntegral_of_L1 to get the desired set integral convergence.
      sorry  -- TODO: Use tendsto_Lp_iff_tendsto_eLpNorm', eLpNorm_le_eLpNorm_mul_eLpNorm_top,
             -- and tendsto_setIntegral_of_L1' to complete

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
      -- Use Hölder: on finite measure, L¹ × L¹ ⊆ L¹
      sorry  -- TODO: Need Memℒp.mul or similar for finite measure spaces
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

section KallenbergIndicator

/-- **From drop‑info for `Y` to indicator conditional independence**.

Assume for all Borel `A` we have
`condExp μ (σ[Z,W]) (1_A ∘ Y) =ᵐ condExp μ (σ[W]) (1_A ∘ Y)`.
Then for all Borel `A,B`:

E[ 1_A(Y) 1_B(Z) | σ(W) ]
= E[ 1_A(Y) | σ(W) ] * E[ 1_B(Z) | σ(W) ] a.e.
-/
lemma condIndep_indicator_of_dropInfoY
  {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
  {Y Z W : Ω → ℝ}
  {mW : MeasurableSpace Ω}
  (dropY :
    ∀ A : Set ℝ, MeasurableSet A →
      condExp (MeasurableSpace.comap (fun ω => (Z ω, W ω)) inferInstance) μ
        (fun ω => Set.indicator (Y ⁻¹' A) (fun _ => (1 : ℝ)) ω)
      =ᵐ[μ]
      condExp mW μ (fun ω => Set.indicator (Y ⁻¹' A) (fun _ => (1 : ℝ)) ω))
  (hZ : Measurable Z)
  {A B : Set ℝ} (hA : MeasurableSet A) (hB : MeasurableSet B) :
  condExp mW μ
    (fun ω =>
      (Set.indicator (Y ⁻¹' A) (fun _ => (1 : ℝ)) ω) *
      (Set.indicator (Z ⁻¹' B) (fun _ => (1 : ℝ)) ω))
  =ᵐ[μ]
  (condExp mW μ (fun ω => Set.indicator (Y ⁻¹' A) (fun _ => (1 : ℝ)) ω))
  *
  (condExp mW μ (fun ω => Set.indicator (Z ⁻¹' B) (fun _ => (1 : ℝ)) ω)) := by
  classical
  set mZW := MeasurableSpace.comap (fun ω => (Z ω, W ω)) inferInstance with hmZW_def
  
  -- Simplified proof with sorries for infrastructure pieces
  -- TODO: Complete with proper σ-algebra arguments and pull-out lemmas
  sorry

end KallenbergIndicator

end  -- noncomputable section
