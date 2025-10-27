/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Probability.ConditionalExpectation
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

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
open MeasureTheory ProbabilityTheory Set

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
       | MeasurableSpace.comap W inferInstance ]
      =ᵐ[μ]
    μ[ Set.indicator (Y ⁻¹' A) (fun _ => (1 : ℝ))
       | MeasurableSpace.comap W inferInstance ]
    *
    μ[ Set.indicator (Z ⁻¹' B) (fun _ => (1 : ℝ))
       | MeasurableSpace.comap W inferInstance ]

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

/-- **Constant conditioning: unconditional independence implies conditional independence.**

If Y and Z are unconditionally independent, then they are conditionally independent
given any W. This is because conditioning on W only adds information, and independent
events remain independent when we add a common conditioning event.

TODO: Requires defining unconditional independence first, or proving directly from
the product measure property.
-/
theorem condIndep_of_indep (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Ω → α) (Z : Ω → β) (W : Ω → γ)
    (hY : Measurable Y) (hZ : Measurable Z) (hW : Measurable W) :
    -- TODO: Add hypothesis that Y and Z are independent
    -- For now, placeholder
    True → CondIndep μ Y Z W := by
  intro _
  sorry
  -- Proof sketch:
  -- 1. From unconditional independence: E[1_A(Y) · 1_B(Z)] = E[1_A(Y)] · E[1_B(Z)]
  -- 2. Take conditional expectation given W on both sides
  -- 3. Use linearity and that E[E[·|W]|W] = E[·|W]
  -- 4. Get E[1_A(Y) · 1_B(Z)|W] = E[1_A(Y)|W] · E[1_B(Z)|W]

/-!
## Extension to product σ-algebras
-/

/-- **Conditional independence with product conditioning.**

Helper lemma for when we condition on a pair (Z, W) and need to show independence
properties. This will be needed for the projection property in Sorry #2.

The statement is: if Y ⊥⊥_W Z, then certain conditional expectations with respect to
σ(Z, W) can be simplified to conditioning on σ(W) alone.

TODO: Full proof requires the monotone class extension and the projection property.
-/
theorem condIndep_project (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Ω → α) (Z : Ω → β) (W : Ω → γ)
    (hY : Measurable Y) (hZ : Measurable Z) (hW : Measurable W)
    (h_indep : CondIndep μ Y Z W)
    {A : Set α} (hA : MeasurableSet A) :
    μ[ Set.indicator (Y ⁻¹' A) (fun _ => (1 : ℝ))
       | MeasurableSpace.comap (fun ω => (Z ω, W ω)) inferInstance ]
      =ᵐ[μ]
    μ[ Set.indicator (Y ⁻¹' A) (fun _ => (1 : ℝ))
       | MeasurableSpace.comap W inferInstance ] := by
  sorry
  -- Proof sketch:
  -- 1. From CondIndep, we have E[1_A(Y) · 1_B(Z) | W] = E[1_A(Y) | W] · E[1_B(Z) | W]
  -- 2. Need to show E[1_A(Y) | (Z,W)] = E[1_A(Y) | W]
  -- 3. Suffices to show integrals match on sets in σ(Z,W)
  -- 4. Sets in σ(Z,W) have form {Z ∈ B, W ∈ C}
  -- 5. On such sets, use conditional independence to factor
  -- 6. This is exactly Sorry #2!

end  -- noncomputable section
