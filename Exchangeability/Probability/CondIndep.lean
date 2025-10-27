/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Probability.ConditionalExpectation
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Exchangeability.Probability.CondExpHelpers

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

/-- **Conditional expectations given (Z,W) are σ(W)-measurable when Y ⊥⊥_W Z.**

This is the key measurability property from conditional independence: if Y and Z are
conditionally independent given W, then conditioning on (Z,W) doesn't use the information
in Z for predicting Y-measurable functions. Therefore, E[f(Y)|σ(Z,W)] is actually
σ(W)-measurable (factors through W alone).

**Mathematical content:** Y ⊥⊥_W Z implies E[1_A(Y)|σ(Z,W)] ∈ L^0(σ(W)).

**Proof strategy:** This requires showing that the conditional expectation factors through W.
The conditional independence hypothesis provides the factorization for products of indicators,
which needs to be leveraged to show the measurability property.

TODO: Complete this proof. This is the key technical lemma for the projection property.
-/
lemma condExp_measurable_of_condIndep (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Ω → α) (Z : Ω → β) (W : Ω → γ)
    (hY : Measurable Y) (hZ : Measurable Z) (hW : Measurable W)
    (h_indep : CondIndep μ Y Z W)
    {A : Set α} (hA : MeasurableSet A) :
    Measurable[MeasurableSpace.comap W inferInstance]
      (μ[ Set.indicator (Y ⁻¹' A) (fun _ => (1 : ℝ))
         | MeasurableSpace.comap (fun ω => (Z ω, W ω)) inferInstance ]) := by
  sorry
  /-
  Proof outline:
  1. Use conditional independence to show E[1_A(Y)·1_B(Z)|σ(W)] factors
  2. This factorization implies E[1_A(Y)|σ(Z,W)] is determined by W alone
  3. The key is to show that for any two ω, ω' with W(ω) = W(ω'), we have
     E[1_A(Y)|σ(Z,W)](ω) = E[1_A(Y)|σ(Z,W)](ω')
  4. This follows from the conditional independence factorization property

  This is a deep property requiring careful measure-theoretic analysis. It may be
  necessary to go through disintegration or to extend the conditional independence
  from indicators to general functions first.
  -/

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
       | MeasurableSpace.comap (fun ω => (Z ω, W ω)) inferInstance ]
      =ᵐ[μ]
    μ[ Set.indicator (Y ⁻¹' A) (fun _ => (1 : ℝ))
       | MeasurableSpace.comap W inferInstance ] := by
  -- Defer: This requires proving condExp_measurable_of_condIndep first
  sorry
  /-
  Proof outline (once condExp_measurable_of_condIndep is proven):

  1. Show σ(W) ≤ σ(Z,W): Any W⁻¹(T) = (Z,W)⁻¹(univ × T)

  2. Use condExp_measurable_of_condIndep to get:
     E[1_A(Y)|σ(Z,W)] is σ(W)-measurable

  3. Apply tower property: E[E[f|σ(Z,W)]|σ(W)] = E[f|σ(W)]

  4. Since E[f|σ(Z,W)] is σ(W)-measurable:
     E[E[f|σ(Z,W)]|σ(W)] = E[f|σ(Z,W)]

  5. Combine: E[f|σ(Z,W)] = E[f|σ(W)]
  -/

end  -- noncomputable section
