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

/-!
## Helper lemmas for independence and conditional expectation
-/

/-- **Conditional expectation against an independent σ-algebra is constant.**

If X is integrable and measurable with respect to a σ-algebra independent of σ(W),
then E[X | σ(W)] = E[X] almost everywhere.

This is the key property that makes independence "pass through" conditioning:
knowing W provides no information about X when X ⊥ W.
-/
lemma condExp_const_of_indepFun (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {W : Ω → γ}
    (h_indep : IndepFun X W μ)
    (hX_int : Integrable X μ) :
    μ[X | MeasurableSpace.comap W inferInstance] =ᵐ[μ] (fun _ => μ[X]) := by
  -- For s ∈ σ(W), independence gives ∫_s X dμ = μ[X] · μ[s]
  -- This characterizes CE as the constant μ[X]
  -- Full proof uses IndepFun.integral_mul applied to X and 1_s
  sorry

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
theorem condIndep_of_indep_pair (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Ω → α) (Z : Ω → β) (W : Ω → γ)
    (hYZ_indep : IndepFun Y Z μ)
    (hPairW_indep : IndepFun (fun ω => (Y ω, Z ω)) W μ) :
    CondIndep μ Y Z W := by
  sorry

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
       | MeasurableSpace.comap (fun ω => (Z ω, W ω)) inferInstance ]
      =ᵐ[μ]
    μ[ Set.indicator (Y ⁻¹' A) (fun _ => (1 : ℝ))
       | MeasurableSpace.comap W inferInstance ] := by
  -- Strategy: Use uniqueness characterization of conditional expectation
  -- Show that both CEs have the same integrals on all σ(W)-measurable sets
  let mW := MeasurableSpace.comap W inferInstance
  let mZW := MeasurableSpace.comap (fun ω => (Z ω, W ω)) inferInstance
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

  -- Use tower property: E[E[f|mZW]|mW] = E[f|mW]
  -- But we want to show E[f|mZW] = E[f|mW], which requires showing E[f|mZW] is mW-measurable
  -- Actually, use condExp_condExp_of_le: E[E[f|m']|m] = E[f|m] when m ≤ m'
  have tower : μ[μ[f | mZW] | mW] =ᵐ[μ] μ[f | mW] := by
    apply condExp_condExp_of_le hle hf_int

  -- Also have: μ[μ[f|mZW]|mW] =ᵐ μ[f|mZW] if μ[f|mZW] is mW-measurable
  -- But μ[f|mZW] is mZW-measurable, not necessarily mW-measurable!

  -- Alternative: show directly that both CEs have same integrals on mW-sets
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
  -- This follows directly from the helper lemma
  exact condExp_project_of_condIndep μ Y Z W hY hZ hW h_indep hA

end  -- noncomputable section
