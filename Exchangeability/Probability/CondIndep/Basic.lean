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

open scoped Classical

/-!
# Conditional Independence - Basic Definitions and Properties

This file defines conditional independence for random variables and establishes
basic properties. The definition uses indicator functions on measurable rectangles.

## Main definitions

* `CondIndep Y Z W μ`: Y and Z are conditionally independent given W under measure μ,
  denoted Y ⊥⊥_W Z, defined via indicator test functions on Borel sets.

## Main results

* `condIndep_symm`: Conditional independence is symmetric (Y ⊥⊥_W Z ↔ Z ⊥⊥_W Y)
* `condExp_const_of_indepFun`: Independence implies constant conditional expectation

## Implementation notes

We use an indicator-based characterization rather than σ-algebra formalism to avoid
requiring a full conditional distribution API. The definition states that for all
Borel sets A, B:

  E[1_A(Y) · 1_B(Z) | σ(W)] = E[1_A(Y) | σ(W)] · E[1_B(Z) | σ(W)]  a.e.

This is equivalent to the standard σ-algebra definition but more elementary to work with.

## References

* Kallenberg (2005), *Probabilistic Symmetries and Invariance Principles*, Section 6.1
* Kallenberg (2002), *Foundations of Modern Probability*, Chapter 6
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
  constructor <;> (intro h A B hA hB; simpa [mul_comm] using h B A hB hA)

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
    (_hX_int : Integrable X μ) :
    μ[X | MeasurableSpace.comap W (by infer_instance)] =ᵐ[μ] (fun _ => μ[X]) := by
  -- Convert IndepFun to Indep of σ-algebras
  rw [IndepFun_iff_Indep] at h_indep
  -- Apply condExp_indep_eq: E[X|σ(W)] = E[X] when σ(X) ⊥ σ(W)
  refine condExp_indep_eq hX.comap_le hW.comap_le ?_ h_indep
  -- X is σ(X)-strongly measurable (X is measurable from (Ω, σ(X)) to ℝ by definition of comap)
  have : @Measurable Ω ℝ (MeasurableSpace.comap X (by infer_instance)) _ X :=
    Measurable.of_comap_le le_rfl
  exact this.stronglyMeasurable

variable {μ : Measure Ω} in
/-- Extract independence of first component from pair independence. -/
lemma IndepFun.of_comp_left_fst {Y : Ω → α} {Z : Ω → β} {W : Ω → γ}
    (h : IndepFun (fun ω => (Y ω, Z ω)) W μ) :
    IndepFun Y W μ :=
  h.comp measurable_fst measurable_id

variable {μ : Measure Ω} in
/-- Extract independence of second component from pair independence. -/
lemma IndepFun.of_comp_left_snd {Y : Ω → α} {Z : Ω → β} {W : Ω → γ}
    (h : IndepFun (fun ω => (Y ω, Z ω)) W μ) :
    IndepFun Z W μ :=
  h.comp measurable_snd measurable_id
