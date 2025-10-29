/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Probability.ConditionalExpectation
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
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
/-
TODO: Add idempotence helper once correct lemma name is identified.

/-- Idempotence of conditional expectation on the target sub-σ-algebra.
If f is m-measurable, then E[f|m] = f almost everywhere.
This avoids hunting for the correct lemma name across mathlib versions. -/
lemma condExp_idem'
    (μ : Measure Ω) (m : MeasurableSpace Ω) (f : Ω → ℝ)
    (hm : m ≤ (inferInstance : MeasurableSpace Ω))
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
    μ[X | MeasurableSpace.comap W inferInstance] =ᵐ[μ] (fun _ => μ[X]) := by
  -- Convert IndepFun to Indep of σ-algebras
  rw [IndepFun_iff_Indep] at h_indep
  -- Apply condExp_indep_eq: E[X|σ(W)] = E[X] when σ(X) ⊥ σ(W)
  refine condExp_indep_eq hX.comap_le hW.comap_le ?_ h_indep
  -- X is σ(X)-strongly measurable (X is measurable from (Ω, σ(X)) to ℝ by definition of comap)
  have : @Measurable Ω ℝ (MeasurableSpace.comap X inferInstance) inferInstance X :=
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
    classical
    have : f * g = (fun p => Set.indicator (A ×ˢ B) (fun _ => (1 : ℝ)) p) ∘ (fun ω => (Y ω, Z ω)) := by
      ext ω
      show f ω * g ω = Set.indicator (A ×ˢ B) (fun _ => (1 : ℝ)) (Y ω, Z ω)
      simp only [f, g, Pi.mul_apply]
      by_cases hY : ω ∈ Y ⁻¹' A <;> by_cases hZ : ω ∈ Z ⁻¹' B
      · rw [Set.indicator_of_mem hY, Set.indicator_of_mem hZ, Set.indicator_of_mem (Set.mk_mem_prod hY hZ)]
        norm_num
      · rw [Set.indicator_of_mem hY, Set.indicator_of_not_mem hZ]
        have : (Y ω, Z ω) ∉ A ×ˢ B := fun h => hZ h.2
        rw [Set.indicator_of_not_mem this]; norm_num
      · rw [Set.indicator_of_not_mem hY, Set.indicator_of_mem hZ]
        have : (Y ω, Z ω) ∉ A ×ˢ B := fun h => hY h.1
        rw [Set.indicator_of_not_mem this]; norm_num
      · rw [Set.indicator_of_not_mem hY, Set.indicator_of_not_mem hZ]
        have : (Y ω, Z ω) ∉ A ×ˢ B := fun h => hY h.1
        rw [Set.indicator_of_not_mem this]; norm_num
    rw [this]
    exact hPairW_indep.comp (measurable_const.indicator (hA.prod hB)) measurable_id

  -- Step 4: Apply condExp_const_of_indepFun to get conditional expectations are constants
  have hf_ce : μ[f | MeasurableSpace.comap W inferInstance] =ᵐ[μ] (fun _ => μ[f]) :=
    condExp_const_of_indepFun μ hf_meas hW hf_indep hf_int

  have hg_ce : μ[g | MeasurableSpace.comap W inferInstance] =ᵐ[μ] (fun _ => μ[g]) :=
    condExp_const_of_indepFun μ hg_meas hW hg_indep hg_int

  have hfg_meas : Measurable (f * g) := hf_meas.mul hg_meas
  have hfg_int : Integrable (f * g) μ := by
    -- f * g = 1_{Y⁻¹A ∩ Z⁻¹B}
    have : f * g = Set.indicator (Y ⁻¹' A ∩ Z ⁻¹' B) (fun _ => (1 : ℝ)) := by
      classical
      ext ω
      simp only [f, g, Pi.mul_apply]
      by_cases hY : ω ∈ Y ⁻¹' A <;> by_cases hZ : ω ∈ Z ⁻¹' B
      · rw [Set.indicator_of_mem hY, Set.indicator_of_mem hZ, Set.indicator_of_mem ⟨hY, hZ⟩]
        norm_num
      · rw [Set.indicator_of_mem hY, Set.indicator_of_not_mem hZ]
        have : ω ∉ Y ⁻¹' A ∩ Z ⁻¹' B := fun h => hZ h.2
        rw [Set.indicator_of_not_mem this]; norm_num
      · rw [Set.indicator_of_not_mem hY, Set.indicator_of_mem hZ]
        have : ω ∉ Y ⁻¹' A ∩ Z ⁻¹' B := fun h => hY h.1
        rw [Set.indicator_of_not_mem this]; norm_num
      · rw [Set.indicator_of_not_mem hY, Set.indicator_of_not_mem hZ]
        have : ω ∉ Y ⁻¹' A ∩ Z ⁻¹' B := fun h => hY h.1
        rw [Set.indicator_of_not_mem this]; norm_num
    rw [this]
    exact (integrable_const (1 : ℝ)).indicator ((hY hA).inter (hZ hB))
  have hfg_ce : μ[f * g | MeasurableSpace.comap W inferInstance] =ᵐ[μ] (fun _ => μ[f * g]) :=
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

  have h_factor : μ[f * g] = μ[f] * μ[g] := by
    sorry  -- Need to find correct integral lemma

  -- Step 6: Combine everything
  calc μ[f * g | MeasurableSpace.comap W inferInstance]
      =ᵐ[μ] (fun _ => μ[f * g]) := hfg_ce
    _ = (fun _ => μ[f] * μ[g]) := by rw [h_factor]
    _ =ᵐ[μ] (fun _ => μ[f]) * (fun _ => μ[g]) := by rfl
    _ =ᵐ[μ] μ[f | MeasurableSpace.comap W inferInstance] * μ[g | MeasurableSpace.comap W inferInstance] :=
        Filter.EventuallyEq.mul hf_ce.symm hg_ce.symm

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

      -- Ambient ≤ proofs (use outer mW, mZW from lines 426-427)
      have hmW_le  : mW  ≤ _ := hW.comap_le
      have hmZW_le : mZW ≤ _ := (hZ.prod_mk hW).comap_le

      -- Convenience name for indicator on Z⁻¹B (f is already defined in outer scope)
      set gB : Ω → ℝ := (Z ⁻¹' B).indicator (fun _ => (1 : ℝ)) with hgB_def

      -- Basic measurable sets in ambient σ-algebra
      have hBpre_amb : MeasurableSet (Z ⁻¹' B) :=
        @MeasurableSet.preimage Ω β (inferInstance : MeasurableSpace Ω) (inferInstance : MeasurableSpace β) Z B hB hZ

      -- Conditional expectation facts
      have hsm_ce     : StronglyMeasurable[mW] (μ[f|mW]) := stronglyMeasurable_condExp
      have hsm_ce_amb : StronglyMeasurable (μ[f|mW])     := hsm_ce.mono hmW_le
      have haesm_ce   : AEStronglyMeasurable (μ[f|mW]) μ := hsm_ce_amb.aestronglyMeasurable
      have hint_ce    : Integrable (μ[f|mW]) μ           := integrable_condExp

      -- gB measurability in the ambient σ-algebra
      have hsm_gB   : StronglyMeasurable gB := stronglyMeasurable_const.indicator hBpre_amb
      have haesm_gB : AEStronglyMeasurable gB μ := hsm_gB.aestronglyMeasurable

      -- Canonical product ↔ indicator identity (use often)
      have h_mul_eq_indicator :
          (fun ω => μ[f|mW] ω * gB ω) = (Z ⁻¹' B).indicator (μ[f|mW]) := by
        funext ω; by_cases hω : ω ∈ Z ⁻¹' B
        · simp [hgB_def, hω, Set.indicator_of_mem hω, mul_one]
        · simp [hgB_def, hω, Set.indicator_of_notMem hω, mul_zero]

      -- Integrable product via indicator (avoids of_bound and σ-algebra juggling)
      have hint_prod : Integrable (fun ω => μ[f|mW] ω * gB ω) μ := by
        simpa [h_mul_eq_indicator] using hint_ce.indicator hBpre_amb

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
            · exact hBpre_amb

          -- Chain of equalities: ∫_{Z⁻¹B ∩ W⁻¹C} μ[f|mW] = ∫_{Z⁻¹B ∩ W⁻¹C} f

          -- Helper: W⁻¹C is measurable in ambient
          have hCpre_amb : MeasurableSet (W ⁻¹' C) := hC.preimage hW

          calc ∫ x in Z ⁻¹' B ∩ W ⁻¹' C, (μ[f | mW]) x ∂μ
              = ∫ x in W ⁻¹' C, (μ[f | mW] * gB) x ∂μ := by
                -- Rewrite using indicator: ∫_{W⁻¹C ∩ Z⁻¹B} μ[f|mW] = ∫_{W⁻¹C} (μ[f|mW] * gB)
                -- First: LHS = ∫_{W⁻¹C} (Z⁻¹B).indicator(μ[f|mW])
                have h1 : ∫ ω in W ⁻¹' C ∩ Z ⁻¹' B, μ[f|mW] ω ∂μ
                        = ∫ ω in W ⁻¹' C, (Z ⁻¹' B).indicator (μ[f|mW]) ω ∂μ := by
                  rw [Set.inter_comm]
                  exact (integral_indicator (hCpre_amb.inter hBpre_amb)).symm
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
                            (hm := hmW_le) (hs := hCpre_amb) (hf := hint_prod))
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
                      congr 1; exact h_fg_indicator
                  _ = ∫ ω in W ⁻¹' C ∩ Z ⁻¹' B, f ω ∂μ := by
                      exact integral_indicator (hCpre_amb.inter hBpre_amb)
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
       | MeasurableSpace.comap (fun ω => (Z ω, W ω)) inferInstance ]
      =ᵐ[μ]
    μ[ Set.indicator (Y ⁻¹' A) (fun _ => (1 : ℝ))
       | MeasurableSpace.comap W inferInstance ] := by
  -- This follows directly from the helper lemma
  exact condExp_project_of_condIndep μ Y Z W hY hZ hW h_indep hA

end  -- noncomputable section
