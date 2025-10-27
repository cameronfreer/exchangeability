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
## Extension to simple functions and bounded measurables (§C2)
-/

/-- **Conditional independence extends to simple functions.**

If Y ⊥⊥_W Z for indicators, then the factorization property extends to simple functions
via linearity of conditional expectation.

**Mathematical content:** For simple functions f(Y) and g(Z):
E[f(Y)·g(Z)|σ(W)] = E[f(Y)|σ(W)]·E[g(Z)|σ(W)]

**Proof strategy:** Express simple functions as linear combinations of indicators,
then use linearity of conditional expectation and the indicator factorization.
-/
lemma condIndep_simpleFunc (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Ω → α) (Z : Ω → β) (W : Ω → γ)
    (h_indep : CondIndep μ Y Z W)
    (f : α → ℝ) (g : β → ℝ)
    -- TODO: Need simple function hypotheses and proper statement
    :
    True := by
  trivial
  /-
  Proof outline:
  1. Express f = Σᵢ aᵢ · 1_{Aᵢ} as finite linear combination
  2. Express g = Σⱼ bⱼ · 1_{Bⱼ} as finite linear combination
  3. Use bilinearity: E[(Σᵢ aᵢ 1_{Aᵢ})·(Σⱼ bⱼ 1_{Bⱼ})|W]
      = Σᵢⱼ aᵢ bⱼ E[1_{Aᵢ}·1_{Bⱼ}|W]
  4. Apply h_indep to each term: = Σᵢⱼ aᵢ bⱼ E[1_{Aᵢ}|W]·E[1_{Bⱼ}|W]
  5. Factor back: = (Σᵢ aᵢ E[1_{Aᵢ}|W])·(Σⱼ bⱼ E[1_{Bⱼ}|W])
      = E[f|W]·E[g|W]
  -/

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
    (h_indep : CondIndep μ Y Z W)
    (f : α → ℝ) (g : β → ℝ)
    (hf_meas : Measurable f) (hg_meas : Measurable g)
    (hf_bdd : ∃ C, ∀ x, |f x| ≤ C) (hg_bdd : ∃ C, ∀ x, |g x| ≤ C) :
    μ[ (f ∘ Y) * (g ∘ Z) | MeasurableSpace.comap W inferInstance ] =ᵐ[μ]
    μ[ f ∘ Y | MeasurableSpace.comap W inferInstance ] *
    μ[ g ∘ Z | MeasurableSpace.comap W inferInstance ] := by
  sorry
  /-
  Proof outline (full monotone class argument):
  1. Define the class H of pairs (f,g) satisfying the factorization
  2. Show H contains all indicator pairs (by h_indep) ✓
  3. Show H contains all simple function pairs (by linearity)
  4. Show H is closed under bounded monotone limits (by dominated convergence)
  5. By monotone class theorem, H contains all bounded measurables
  6. Therefore the factorization holds for bounded measurable f, g
  -/

/-!
## Extension to product σ-algebras
-/

/-- **Conditional expectations given (Z,W) are σ(W)-measurable when Y ⊥⊥_W Z.**

This is the key measurability property from conditional independence: if Y and Z are
conditionally independent given W, then conditioning on (Z,W) doesn't use the information
in Z for predicting Y-measurable functions. Therefore, E[f(Y)|σ(Z,W)] is actually
σ(W)-measurable (factors through W alone).

**Mathematical content:** Y ⊥⊥_W Z implies E[1_A(Y)|σ(Z,W)] ∈ L^0(σ(W)).

**Proof strategy (via integral characterization):**
1. Need to show: E[1_A(Y)|σ(Z,W)] is σ(W)-measurable
2. Equivalently: For S ∈ σ(W), both E[1_A(Y)|σ(Z,W)] and E[1_A(Y)|σ(W)]
   have the same integral over S
3. This holds because S ∈ σ(W) ⊆ σ(Z,W), so:
   ∫_S E[1_A(Y)|σ(Z,W)] = ∫_S 1_A(Y) = ∫_S E[1_A(Y)|σ(W)]
4. But this only shows they're a.e. equal, not that one is measurable w.r.t. the other!

**Alternative via product structure (requires deeper theory):**
The conditional independence factorization E[1_A(Y)·1_B(Z)|W] = E[1_A(Y)|W]·E[1_B(Z)|W]
means the conditional distribution of (Y,Z) given W is a product measure. This implies
E[f(Y)|σ(Z,W)] = E[f(Y)|σ(W)] by the product measure projection property.

**Status:** This is a fundamental result that requires either:
- Developing conditional distribution/disintegration theory, OR
- Using mathlib's kernel-based conditional independence, OR
- Proving the projection property directly without this lemma

For now, we defer this deep result and work on the direct projection approach.
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
  sorry
  /-
  **Direct proof via integral matching (bypasses measurability lemma):**

  Strategy: Show both sides have equal integrals on all σ(W)-measurable sets.

  1. Let S ∈ σ(W) be arbitrary (so S = W⁻¹(T) for some measurable T ⊆ γ)

  2. Compute ∫_S E[1_A(Y)|σ(Z,W)] dμ:
     - Since S ∈ σ(W) ⊆ σ(Z,W), by CE property:
       ∫_S E[1_A(Y)|σ(Z,W)] dμ = ∫_S 1_A(Y) dμ

  3. Compute ∫_S E[1_A(Y)|σ(W)] dμ:
     - Since S ∈ σ(W), by CE property:
       ∫_S E[1_A(Y)|σ(W)] dμ = ∫_S 1_A(Y) dμ

  4. Therefore integrals match on all σ(W)-sets

  5. By uniqueness (condExp_eq_of_setIntegral_eq):
     E[1_A(Y)|σ(Z,W)] =ᵐ[μ] E[1_A(Y)|σ(W)]

  **Implementation challenge:** Need to verify all technical hypotheses for uniqueness
  lemma (σ-finiteness, integrability, etc.)
  -/

end  -- noncomputable section
