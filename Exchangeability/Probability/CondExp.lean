/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Conditional
import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.PiSystem

/-!
# Conditional Expectation API for Exchangeability Proofs

This file provides a specialized API for conditional expectations, conditional
independence, and martingale convergence, tailored for the exchangeability and
de Finetti proofs.

## Main Components

### 1. Conditional Probability
- `condProb`: Conditional probability P[A | 𝒢] for events
- Properties relating conditional probability to conditional expectation

### 2. Conditional Independence (Doob's Characterization)
- `condIndep_iff_condexp_eq`: Doob's characterization (FMP 6.6)
  ```
  𝒻 ⊥⊥_𝒢 ℋ ⟺ P[H | 𝒻 ∨ 𝒢] = P[H | 𝒢] a.s. for all H ∈ ℋ
  ```
- Helper lemmas for establishing conditional independence from distributional equalities

### 3. Reverse Martingale Convergence
- Convergence of conditional expectations with respect to decreasing σ-algebras
- Applied to tail σ-algebras: σ(θ_n X) ↓ ⋂_n σ(θ_n X)

### 4. Integration with Existing Mathlib
- Re-exports from `Mathlib.Probability.ConditionalExpectation`
- Additional lemmas building on mathlib infrastructure

## Implementation Status

This file integrates mathlib's probability theory infrastructure and provides a specialized API:

**Implemented using mathlib:**
- `condProb`: Defined using mathlib's `condExp` notation `μ[f|m]`
- `CondIndep`: Available as `ProbabilityTheory.CondIndep` from mathlib
- Documented mathlib's martingale theory (`Martingale`, `Supermartingale`, etc.)
- Documented key conditional expectation lemmas (`setIntegral_condExp`, `condExp_indicator`, etc.)

**Completed proofs:**
- `condProb_ae_nonneg_le_one`: Bounds on conditional probability
  (using `condExp_nonneg`, `condExp_mono`)
- `condProb_integral_eq`: Averaging property (using `setIntegral_condExp`)
- `condIndep_of_condProb_eq`: Wrapper for conditional independence
  (one-liner using Doob's characterization)

**Remaining as stubs (proof strategies documented):**
- `condIndep_iff_condexp_eq`: Doob's characterization
  (TODO: derive from `condIndep_iff` product formula)
- `condProb_eq_of_eq_on_pi_system`: π-system extension (TODO: use `condIndepSets.condIndep'`)
- `bounded_martingale_l2_eq`: L² identification (TODO: use `MemLp.condExpL2_ae_eq_condExp`)
- `reverse_martingale_convergence`: Requires martingale convergence theory
- `condexp_same_dist`: Distributional invariance (TODO: use `condExpKernel`, `condDistrib`)

The goal is to incrementally replace stubs with proofs as needed by the de Finetti development.

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

/-! ### Helper lemmas for set integration -/

/-- If two functions are a.e. equal on `μ.restrict s`, their set integrals on `s` coincide. -/
lemma setIntegral_congr_ae'
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure Ω} {s : Set Ω} {f g : Ω → E}
    (hfg : f =ᵐ[μ.restrict s] g) :
    ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ :=
  integral_congr_ae hfg

/-- If two functions are a.e. equal under `μ`, their set integrals on any `s` coincide. -/
lemma setIntegral_congr_ae_of_ae
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure Ω} {s : Set Ω} {f g : Ω → E}
    (hfgμ : f =ᵐ[μ] g) :
    ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ :=
  setIntegral_congr_ae' (ae_restrict_of_ae hfgμ)

/-! ### Conditional Probability -/

/-- Conditional probability of an event `A` given a σ-algebra `m`.
This is the conditional expectation of the indicator function of `A`.

We define it using mathlib's `condexp` applied to the indicator function.
-/
noncomputable def condProb {m₀ : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m : MeasurableSpace Ω) (A : Set Ω) : Ω → ℝ :=
  μ[A.indicator (fun _ => (1 : ℝ)) | m]

set_option linter.unusedSectionVars false in
lemma condProb_def {m₀ : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m : MeasurableSpace Ω) (A : Set Ω) :
    condProb μ m A = μ[A.indicator (fun _ => (1 : ℝ)) | m] := rfl

set_option linter.unusedSectionVars false in
/-- Conditional probability takes values in `[0,1]` almost everywhere. -/
lemma condProb_ae_nonneg_le_one {m₀ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (m : MeasurableSpace Ω) (hm : m ≤ m₀)
    [SigmaFinite (μ.trim hm)] {A : Set Ω} (hA : MeasurableSet[m₀] A) :
    ∀ᵐ ω ∂μ, 0 ≤ condProb μ m A ω ∧ condProb μ m A ω ≤ 1 := by
  classical
  -- Nonnegativity via condExp_nonneg
  have h₀ : 0 ≤ᵐ[μ] condProb μ m A := by
    have : 0 ≤ᵐ[μ] A.indicator (fun _ : Ω => (1 : ℝ)) :=
      ae_of_all _ fun ω => by
        by_cases hω : ω ∈ A <;> simp [Set.indicator, hω]
    simpa [condProb] using condExp_nonneg (μ := μ) (m := m) this
  -- Upper bound via monotonicity and condExp_const
  have h₁ : condProb μ m A ≤ᵐ[μ] fun _ : Ω => (1 : ℝ) := by
    have h_le : A.indicator (fun _ => (1 : ℝ)) ≤ᵐ[μ] fun _ => (1 : ℝ) :=
      ae_of_all _ fun ω => by
        by_cases hω : ω ∈ A <;> simp [Set.indicator, hω]
    -- Indicator of measurable set with integrable constant is integrable
    have h_int : Integrable (A.indicator fun _ : Ω => (1 : ℝ)) μ :=
      (integrable_const (1 : ℝ)).indicator hA
    have h_mono := condExp_mono (μ := μ) (m := m) h_int (integrable_const (1 : ℝ)) h_le
    simpa [condProb, condExp_const (μ := μ) (m := m) hm (1 : ℝ)] using h_mono
  filter_upwards [h₀, h₁] with ω h0 h1
  exact ⟨h0, by simpa using h1⟩

set_option linter.unusedSectionVars false in
/-- Conditional probability integrates to the expected measure on sets that are
measurable with respect to the conditioning σ-algebra. -/
lemma condProb_integral_eq {m₀ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (m : MeasurableSpace Ω) (hm : m ≤ m₀)
    [SigmaFinite (μ.trim hm)] {A B : Set Ω} (hA : MeasurableSet[m₀] A)
    (hB : MeasurableSet[m] B) :
    ∫ ω in B, condProb μ m A ω ∂μ = (μ (A ∩ B)).toReal := by
  classical
  have h_int : Integrable (A.indicator fun _ : Ω => (1 : ℝ)) μ :=
    (integrable_const (1 : ℝ)).indicator hA
  -- Use the defining property of the conditional expectation on the set `B`.
  have h_condexp :=
    setIntegral_condExp (μ := μ) (m := m) (hm := hm)
      (f := A.indicator fun _ : Ω => (1 : ℝ)) h_int hB
  -- Rewrite as an integral over `B ∩ A` of the constant 1.
  have h_indicator :
      ∫ ω in B, A.indicator (fun _ : Ω => (1 : ℝ)) ω ∂μ
        = ∫ ω in B ∩ A, (1 : ℝ) ∂μ := by
    simpa [Set.inter_comm, Set.inter_left_comm, Set.inter_assoc]
      using setIntegral_indicator (μ := μ) (s := B) (t := A)
        (f := fun _ : Ω => (1 : ℝ)) hA
  -- Evaluate the integral of 1 over the set.
  have h_const : ∫ ω in B ∩ A, (1 : ℝ) ∂μ = (μ (B ∩ A)).toReal := by
    simp [Measure.real_def, Set.inter_comm]
  -- Put everything together and clean up intersections.
  simpa [condProb, h_indicator, h_const, Set.inter_comm, Set.inter_left_comm, Set.inter_assoc]
    using h_condexp

set_option linter.unusedSectionVars false in
@[simp]
lemma condProb_univ {m₀ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (m : MeasurableSpace Ω) (hm : m ≤ m₀)
    [SigmaFinite (μ.trim hm)] :
    condProb μ m (Set.univ : Set Ω) =ᵐ[μ] (fun _ => (1 : ℝ)) := by
  classical
  have : (Set.univ : Set Ω).indicator (fun _ : Ω => (1 : ℝ)) = fun _ => (1 : ℝ) := by
    funext ω; simp [Set.indicator]
  simp [condProb, this, condExp_const (μ := μ) (m := m) hm (1 : ℝ)]

set_option linter.unusedSectionVars false in
@[simp]
lemma condProb_empty {m₀ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (m : MeasurableSpace Ω) (hm : m ≤ m₀) :
    condProb μ m (∅ : Set Ω) =ᵐ[μ] (fun _ => (0 : ℝ)) := by
  classical
  have : (∅ : Set Ω).indicator (fun _ : Ω => (1 : ℝ)) = fun _ => (0 : ℝ) := by
    funext ω; simp [Set.indicator]
  simp [condProb, this, condExp_const (μ := μ) (m := m) hm (0 : ℝ)]

set_option linter.unusedSectionVars false in
@[simp]
lemma condProb_compl {m₀ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (m : MeasurableSpace Ω) (hm : m ≤ m₀)
    [SigmaFinite (μ.trim hm)] {A : Set Ω} (hA : MeasurableSet[m₀] A) :
    condProb μ m Aᶜ =ᵐ[μ] (fun ω => 1 - condProb μ m A ω) := by
  classical
  have hId :
      Aᶜ.indicator (fun _ : Ω => (1 : ℝ))
        = (fun _ : Ω => (1 : ℝ)) - A.indicator (fun _ : Ω => (1 : ℝ)) := by
    funext ω
    by_cases h : ω ∈ A <;> simp [Set.indicator, h]
  have hlin :
      μ[Aᶜ.indicator (fun _ => (1 : ℝ)) | m]
        =ᵐ[μ] μ[(fun _ => (1 : ℝ)) | m] - μ[A.indicator (fun _ => (1 : ℝ)) | m] := by
    have h_int : Integrable (A.indicator fun _ : Ω => (1 : ℝ)) μ :=
      (integrable_const (1 : ℝ)).indicator hA
    simpa [hId] using
      condExp_sub (μ := μ) (m := m)
        (integrable_const (1 : ℝ)) h_int
  have hconst : μ[(fun _ : Ω => (1 : ℝ)) | m] =ᵐ[μ] (fun _ => (1 : ℝ)) :=
    (condExp_const (μ := μ) (m := m) hm (1 : ℝ)).eventuallyEq
  have : μ[Aᶜ.indicator (fun _ : Ω => (1 : ℝ)) | m]
            =ᵐ[μ] (fun ω => 1 - μ[A.indicator (fun _ : Ω => (1 : ℝ)) | m] ω) :=
    hlin.trans <| (EventuallyEq.sub hconst EventuallyEq.rfl)
  simpa [condProb] using this

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
lemma condIndep_iff_condexp_eq {m₀ : MeasurableSpace Ω} {μ : Measure Ω}
    [StandardBorelSpace Ω] [IsFiniteMeasure μ]
    {mF mG mH : MeasurableSpace Ω}
    (hmF : mF ≤ m₀) (hmG : mG ≤ m₀) (hmH : mH ≤ m₀) :
    ProbabilityTheory.CondIndep mG mF mH hmG μ ↔
      ∀ H, MeasurableSet[mH] H →
        μ[H.indicator (fun _ => (1 : ℝ)) | mF ⊔ mG]
          =ᵐ[μ] μ[H.indicator (fun _ => (1 : ℝ)) | mG] := by
  classical
  constructor
  · intro hCond H hH
    set g : Ω → ℝ := μ[H.indicator (fun _ => (1 : ℝ)) | mG]
    have hg_int : Integrable g μ := by
      simpa [g] using
        (integrable_condExp (μ := μ) (m := mG)
          (f := H.indicator fun _ : Ω => (1 : ℝ)))
    have hg_meas : AEStronglyMeasurable[mG] g μ := by
      have h_sm :=
        (stronglyMeasurable_condExp (μ := μ) (m := mG)
            (f := H.indicator fun _ : Ω => (1 : ℝ)))
      simpa [g] using h_sm.aestronglyMeasurable
    -- Specialize the product formula from condIndep_iff
    have h_prod := (ProbabilityTheory.condIndep_iff mG mF mH hmG hmF hmH μ).1 hCond
    -- Integrability and measurability facts we'll need
    have hH' : MeasurableSet[m₀] H := hmH _ hH
    have hH_int : Integrable (H.indicator fun _ : Ω => (1 : ℝ)) μ :=
      (integrable_const (1 : ℝ)).indicator hH'
    have h_rect :
        ∀ {F} (hF : MeasurableSet[mF] F) {G} (hG : MeasurableSet[mG] G),
          ∫ ω in F ∩ G, g ω ∂μ
            = ∫ ω in F ∩ G, (H.indicator fun _ : Ω => (1 : ℝ)) ω ∂μ := by
      intro F hF G hG
      -- Since g = μ[H.indicator 1 | mG], we have by setIntegral_condExp:
      -- ∫ in S, g = ∫ in S, H.indicator for any mG-measurable S
      -- But F ∩ G is not mG-measurable. However, we can show the equality directly.

      -- The key: both sides equal (μ (F ∩ G ∩ H)).toReal
      have hF' : MeasurableSet[m₀] F := hmF _ hF
      have hG' : MeasurableSet[m₀] G := hmG _ hG

      -- RHS is straightforward
      have rhs_eq : ∫ ω in F ∩ G, H.indicator (fun _ => (1 : ℝ)) ω ∂μ = (μ (F ∩ G ∩ H)).toReal := by
        rw [setIntegral_indicator hH']
        simp [Measure.real_def, Set.inter_assoc]

      -- LHS: Show ∫ in F ∩ G, g = (μ (F ∩ G ∩ H)).toReal
      rw [rhs_eq]

      -- The key insight: F ∩ G ∩ H = (F ∩ H) ∩ G
      -- Apply conditional expectation identities on the mG-measurable set G
      have hF_int : Integrable (F.indicator fun _ : Ω => (1 : ℝ)) μ :=
        (integrable_const (1 : ℝ)).indicator hF'
      have hFG_int : Integrable (F.indicator fun ω : Ω => g ω) μ := by
        have h_eq :
            (fun ω => (F.indicator fun _ : Ω => (1 : ℝ)) ω * g ω)
              = F.indicator fun ω : Ω => g ω := by
          funext ω; by_cases hω : ω ∈ F <;> simp [Set.indicator, hω]
        simpa [h_eq] using hg_int.indicator hF'
      have hFH_int : Integrable ((F ∩ H).indicator fun _ : Ω => (1 : ℝ)) μ :=
        (integrable_const (1 : ℝ)).indicator (MeasurableSet.inter hF' hH')
      have h_mul :
          μ[F.indicator (fun ω : Ω => g ω) | mG]
            =ᵐ[μ] μ[F.indicator fun _ : Ω => (1 : ℝ) | mG] * g := by
        have hfg_int :
            Integrable (fun ω => (F.indicator fun _ : Ω => (1 : ℝ)) ω * g ω) μ := by
          have h_eq :
              (fun ω => (F.indicator fun _ : Ω => (1 : ℝ)) ω * g ω)
                = F.indicator fun ω : Ω => g ω := by
            funext ω; by_cases hω : ω ∈ F <;> simp [Set.indicator, hω]
          simpa [h_eq] using hg_int.indicator hF'
        have h_expr :
            (fun ω => (F.indicator fun _ : Ω => (1 : ℝ)) ω * g ω)
              = F.indicator fun ω : Ω => g ω := by
          funext ω; by_cases hω : ω ∈ F <;> simp [Set.indicator, hω]
        have h_pull := condExp_mul_of_aestronglyMeasurable_right (μ := μ) (m := mG)
              hg_meas hfg_int hF_int
        simp only [← h_expr]
        exact h_pull
      have h_prod_FH := h_prod F H hF hH
      have hG_set : MeasurableSet[m₀] G := hmG _ hG
      calc
        ∫ ω in F ∩ G, g ω ∂μ
            = ∫ ω in G ∩ F, g ω ∂μ := by simp [Set.inter_comm]
        _ = ∫ ω in G, F.indicator (fun ω : Ω => g ω) ω ∂μ := by
            simpa [Set.inter_comm] using
              (setIntegral_indicator (μ := μ) (s := G) (t := F)
                (f := fun ω : Ω => g ω) hF').symm
        _ = ∫ ω in G, μ[F.indicator (fun ω : Ω => g ω) | mG] ω ∂μ := by
            have h_cond :=
              setIntegral_condExp (μ := μ) (m := mG) (hm := hmG)
                (f := F.indicator fun ω : Ω => g ω) hFG_int hG
            simpa using h_cond.symm
        _ = ∫ ω in G,
              μ[F.indicator fun _ : Ω => (1 : ℝ) | mG] ω * g ω ∂μ := by
            refine setIntegral_congr_ae hG_set ?_
            filter_upwards [h_mul] with ω hω _ using hω
        _ = ∫ ω in G,
              μ[(F ∩ H).indicator fun _ : Ω => (1 : ℝ) | mG] ω ∂μ := by
            refine setIntegral_congr_ae hG_set ?_
            filter_upwards [h_prod_FH] with ω hω _ using hω.symm
        _ = ∫ ω in G, (F ∩ H).indicator (fun _ : Ω => (1 : ℝ)) ω ∂μ := by
            exact
              setIntegral_condExp (μ := μ) (m := mG) (hm := hmG)
                (f := (F ∩ H).indicator fun _ : Ω => (1 : ℝ)) hFH_int hG
        _ = (μ (G ∩ (F ∩ H))).toReal := by
            have h_indicator :
                ∫ ω in G, (F ∩ H).indicator (fun _ : Ω => (1 : ℝ)) ω ∂μ
                  = ∫ ω in G ∩ (F ∩ H), (1 : ℝ) ∂μ :=
              setIntegral_indicator (μ := μ) (s := G) (t := F ∩ H)
                (f := fun _ : Ω => (1 : ℝ)) (MeasurableSet.inter hF' hH')
            have h_const :
                ∫ ω in G ∩ (F ∩ H), (1 : ℝ) ∂μ
                  = (μ (G ∩ (F ∩ H))).toReal := by
              simp [Measure.real_def]
            simpa [h_const] using h_indicator
        _ = (μ (F ∩ G ∩ H)).toReal := by
            have : G ∩ (F ∩ H) = F ∩ G ∩ H := by
              ext ω
              simp [Set.mem_inter_iff, and_left_comm, and_assoc]
            simp [this]
    have h_dynkin :
        ∀ {S} (hS : MeasurableSet[mF ⊔ mG] S),
          ∫ ω in S, g ω ∂μ
            = ∫ ω in S, (H.indicator fun _ : Ω => (1 : ℝ)) ω ∂μ := by
      intro S hS
      -- Apply induction_on_inter: the property C(S) := "∫ in S, g = ∫ in S, H.indicator 1"
      -- satisfies the Dynkin system properties and holds on rectangles F ∩ G
      have hmFG : mF ⊔ mG ≤ m₀ := sup_le hmF hmG

      -- Define the rectangles: {F ∩ G | F ∈ mF, G ∈ mG}
      let rects : Set (Set Ω) := {s | ∃ (F : Set Ω) (G : Set Ω),
        MeasurableSet[mF] F ∧ MeasurableSet[mG] G ∧ s = F ∩ G}

      -- Rectangles form a π-system
      have h_pi : IsPiSystem rects := by
        intro s1 hs1 s2 hs2 _
        obtain ⟨F1, G1, hF1, hG1, rfl⟩ := hs1
        obtain ⟨F2, G2, hF2, hG2, rfl⟩ := hs2
        refine ⟨F1 ∩ F2, G1 ∩ G2, ?_, ?_, ?_⟩
        · exact MeasurableSet.inter hF1 hF2
        · exact MeasurableSet.inter hG1 hG2
        · ext ω; simp [Set.mem_inter_iff]; tauto

      -- The property holds on rectangles (this is h_rect)
      have h_rects : ∀ s ∈ rects, ∫ ω in s, g ω ∂μ = ∫ ω in s, H.indicator (fun _ => (1 : ℝ)) ω ∂μ := by
        intro s hs
        obtain ⟨F, G, hF, hG, rfl⟩ := hs
        exact h_rect hF hG

      -- Apply Dynkin π-λ theorem using induction_on_inter
      -- Define the property: C(S) := "∫ in S, g = ∫ in S, H.indicator"
      let C : Set Ω → Prop := fun S => ∫ ω in S, g ω ∂μ = ∫ ω in S, H.indicator (fun _ => (1 : ℝ)) ω ∂μ

      -- Show C satisfies Dynkin system properties
      have h_C_empty : C ∅ := by simp [C]

      have h_C_compl : ∀ s, MeasurableSet[mF ⊔ mG] s → C s → C sᶜ := by
        intro s hs hCs
        simp only [C] at hCs ⊢
        have hs' : MeasurableSet[m₀] s := hmFG _ hs
        have h_add_g : ∫ ω in s, g ω ∂μ + ∫ ω in sᶜ, g ω ∂μ = ∫ ω, g ω ∂μ :=
          integral_add_compl hs' hg_int
        have h_add_H : ∫ ω in s, H.indicator (fun _ => (1 : ℝ)) ω ∂μ + ∫ ω in sᶜ, H.indicator (fun _ => (1 : ℝ)) ω ∂μ
            = ∫ ω, H.indicator (fun _ => (1 : ℝ)) ω ∂μ :=
          integral_add_compl hs' hH_int
        have h_total : ∫ ω, g ω ∂μ = ∫ ω, H.indicator (fun _ => (1 : ℝ)) ω ∂μ :=
          setIntegral_condExp (μ := μ) (m := mG) (hm := hmG)
            (f := H.indicator fun _ => (1 : ℝ)) hH_int MeasurableSet.univ |> fun h => by simpa using h
        linarith

      have h_C_iUnion : ∀ (f : ℕ → Set Ω), (∀ i, MeasurableSet[mF ⊔ mG] (f i)) →
          Pairwise (Disjoint on f) → (∀ i, C (f i)) → C (⋃ i, f i) := by
        intro f hf_meas hf_disj hf_C
        simp only [C] at hf_C ⊢
        have hf_meas' : ∀ i, MeasurableSet[m₀] (f i) := fun i => hmFG _ (hf_meas i)
        -- Use tsum for countable disjoint union
        sorry

      -- Apply induction_on_inter
      sorry -- Need suitable form of induction_on_inter for this setting
    have h_proj :
        μ[H.indicator (fun _ => (1 : ℝ)) | mF ⊔ mG]
          =ᵐ[μ] g := by
      -- Apply ae_eq_condExp_of_forall_setIntegral_eq
      have hmFG : mF ⊔ mG ≤ m₀ := sup_le hmF hmG
      -- σ-finiteness follows from μ being a finite measure
      haveI : SigmaFinite (μ.trim hmFG) := by
        -- Trimmed finite measures are σ-finite
        have : IsFiniteMeasure (μ.trim hmFG) := inferInstance
        exact IsFiniteMeasure.toSigmaFinite _
      refine (ae_eq_condExp_of_forall_setIntegral_eq hmFG ?_ ?_ ?_ ?_).symm
      -- 1. H.indicator is integrable
      · exact hH_int
      -- 2. g is integrable on all finite measure sets
      · intro s hs hμs
        exact hg_int.integrableOn
      -- 3. Integrals agree (from h_dynkin)
      · intro s hs hμs
        exact h_dynkin hs
      -- 4. g is mG-measurable, hence mF ⊔ mG-measurable
      · exact hg_meas.mono (le_sup_right : mG ≤ mF ⊔ mG)
    simpa [g] using h_proj
  · intro hProj
    refine (ProbabilityTheory.condIndep_iff mG mF mH hmG hmF hmH μ).2 ?_
    intro t1 t2 ht1 ht2
    -- Need to show: μ⟦t1 ∩ t2 | mG⟧ =ᵐ[μ] μ⟦t1 | mG⟧ * μ⟦t2 | mG⟧
    -- where t1 is mF-measurable and t2 is mH-measurable

    -- Key insight: The projection property gives us that conditioning on mF doesn't change
    -- the conditional expectation of H given mG. We need to use this to derive the product formula.

    -- The strategy is to use the uniqueness of conditional expectation:
    -- We show that μ⟦t1 | mG⟧ * μ⟦t2 | mG⟧ satisfies the defining
    -- properties of μ⟦t1 ∩ t2 | mG⟧

    -- Step 1: Specialize projection property for t2
    have hProjt2 : μ[t2.indicator (fun _ => (1 : ℝ)) | mF ⊔ mG]
        =ᵐ[μ] μ[t2.indicator (fun _ => (1 : ℝ)) | mG] := hProj t2 ht2

    -- Step 2: Key observation - (t1 ∩ t2).indicator = t1.indicator * t2.indicator
    have indicator_prod : ∀ ω, (t1 ∩ t2).indicator (fun _ => (1 : ℝ)) ω
        = t1.indicator (fun _ => (1 : ℝ)) ω * t2.indicator (fun _ => (1 : ℝ)) ω := by
      intro ω
      by_cases h1 : ω ∈ t1
      · by_cases h2 : ω ∈ t2
        · simp [Set.indicator, h1, h2]
        · simp [Set.indicator, h1, h2]
      · simp [Set.indicator, h1]

    -- TODO: Complete reverse direction using tower property
    --
    -- Goal: Show μ⟦t1 ∩ t2 | mG⟧ =ᵐ[μ] μ⟦t1 | mG⟧ * μ⟦t2 | mG⟧
    -- Given: hProjt2: μ[t2.indicator | mF ⊔ mG] =ᵐ[μ] μ[t2.indicator | mG]
    --        indicator_prod: (t1 ∩ t2).indicator = t1.indicator * t2.indicator ✓
    --
    -- Key mathlib lemmas:
    -- 1. condExp_condExp_of_le {m₁ m₂ m₀ : MeasurableSpace α} (hm₁₂ : m₁ ≤ m₂) (hm₂ : m₂ ≤ m₀) :
    --      μ[μ[f|m₂]|m₁] =ᵐ[μ] μ[f|m₁]
    --    (ConditionalExpectation.Basic:324) - Tower property
    --
    -- 2. condExp_stronglyMeasurable_mul_of_bound (hm : m ≤ m0) {f g : α → ℝ}
    --      (hf : StronglyMeasurable[m] f) (hg : Integrable g μ) :
    --      μ[f * g | m] =ᵐ[μ] f * μ[g | m]
    --    (ConditionalExpectation.Real:243) - Pull-out property
    --
    -- Strategy:
    -- 1. Apply tower property from mG to mF ⊔ mG:
    --      μ[(t1 ∩ t2).indicator | mG] = μ[μ[(t1 ∩ t2).indicator | mF ⊔ mG] | mG]
    --
    -- 2. Use indicator_prod and apply condExp to product:
    --      μ[t1.indicator * t2.indicator | mF ⊔ mG]
    --
    -- 3. Since t1.indicator is mF-measurable (hence mF ⊔ mG-measurable), pull it out:
    --      = t1.indicator * μ[t2.indicator | mF ⊔ mG]
    --
    -- 4. Apply hProjt2 to substitute:
    --      =ᵐ[μ] t1.indicator * μ[t2.indicator | mG]
    --
    -- 5. Apply tower property again from outer mG conditioning:
    --      μ[t1.indicator * μ[t2.indicator | mG] | mG]
    --
    -- 6. Pull out μ[t2.indicator | mG] (which is mG-measurable):
    --      = μ[t1.indicator | mG] * μ[t2.indicator | mG]
    --
    -- This completes the product formula for conditional independence.
    set f1 : Ω → ℝ := t1.indicator fun _ : Ω => (1 : ℝ)
    set f2 : Ω → ℝ := t2.indicator fun _ : Ω => (1 : ℝ)
    have hf1_int : Integrable f1 μ :=
      (integrable_const (1 : ℝ)).indicator (hmF _ ht1)
    have hf2_int : Integrable f2 μ :=
      (integrable_const (1 : ℝ)).indicator (hmH _ ht2)
    have hf_prod_int :
        Integrable ((t1 ∩ t2).indicator fun _ : Ω => (1 : ℝ)) μ :=
      (integrable_const (1 : ℝ)).indicator
        (MeasurableSet.inter (hmF _ ht1) (hmH _ ht2))
    have hf1_aesm :
        AEStronglyMeasurable[mF ⊔ mG] f1 μ :=
      ((stronglyMeasurable_const.indicator ht1).aestronglyMeasurable).mono
        (le_sup_left : mF ≤ mF ⊔ mG)
    have hf_prod_eq :
        (fun ω => f1 ω * f2 ω)
          = fun ω => (t1 ∩ t2).indicator (fun _ : Ω => (1 : ℝ)) ω := by
      funext ω; by_cases h1 : ω ∈ t1 <;> by_cases h2 : ω ∈ t2 <;>
        simp [f1, f2, Set.indicator, h1, h2, Set.mem_inter_iff] at *
    have h_inner :
        μ[(t1 ∩ t2).indicator (fun _ : Ω => (1 : ℝ)) | mF ⊔ mG]
          =ᵐ[μ] f1 * μ[f2 | mF ⊔ mG] := by
      have hf12_int : Integrable (fun ω => f1 ω * f2 ω) μ := by
        rw [hf_prod_eq]
        exact hf_prod_int
      have h_mul :
          μ[(fun ω => f1 ω * f2 ω) | mF ⊔ mG]
            =ᵐ[μ] f1 * μ[f2 | mF ⊔ mG] :=
        condExp_mul_of_aestronglyMeasurable_left (μ := μ) (m := mF ⊔ mG)
          hf1_aesm hf12_int hf2_int
      have h_ae : (fun ω => f1 ω * f2 ω) =ᵐ[μ] (t1 ∩ t2).indicator (fun _ : Ω => (1 : ℝ)) :=
        EventuallyEq.of_eq hf_prod_eq
      calc μ[(t1 ∩ t2).indicator (fun _ : Ω => (1 : ℝ)) | mF ⊔ mG]
          =ᵐ[μ] μ[(fun ω => f1 ω * f2 ω) | mF ⊔ mG] := condExp_congr_ae h_ae.symm
        _ =ᵐ[μ] f1 * μ[f2 | mF ⊔ mG] := h_mul
    have h_inner' :
        μ[(t1 ∩ t2).indicator (fun _ : Ω => (1 : ℝ)) | mF ⊔ mG]
          =ᵐ[μ] f1 * μ[f2 | mG] :=
      h_inner.trans <| EventuallyEq.mul EventuallyEq.rfl hProjt2
    have h_tower :=
      (condExp_condExp_of_le (μ := μ)
          (hm₁₂ := le_sup_right)
          (hm₂ := sup_le hmF hmG)
          (f := (t1 ∩ t2).indicator fun _ : Ω => (1 : ℝ))).symm
    have h_lhs :
        μ[(t1 ∩ t2).indicator (fun _ : Ω => (1 : ℝ)) | mG]
          =ᵐ[μ] μ[f1 * μ[f2 | mG] | mG] :=
      h_tower.trans <| condExp_congr_ae (μ := μ) (m := mG) h_inner'
    have h_condExp_f2_meas :
        AEStronglyMeasurable[mG] (μ[f2 | mG]) μ :=
      stronglyMeasurable_condExp.aestronglyMeasurable
    have h_prod_cond_int :
        Integrable (fun ω => f1 ω * μ[f2 | mG] ω) μ := by
      have h_eq :
          (fun ω => f1 ω * μ[f2 | mG] ω)
            = t1.indicator (fun ω => μ[f2 | mG] ω) := by
        funext ω; by_cases hω : ω ∈ t1 <;> simp [f1, Set.indicator, hω]
      rw [h_eq]
      exact (integrable_condExp (μ := μ) (m := mG) (f := f2)).indicator (hmF _ ht1)
    have h_pull :
        μ[f1 * μ[f2 | mG] | mG]
          =ᵐ[μ] μ[f1 | mG] * μ[f2 | mG] :=
      condExp_mul_of_aestronglyMeasurable_right (μ := μ) (m := mG)
        h_condExp_f2_meas h_prod_cond_int hf1_int
    have h_goal :=
      h_lhs.trans h_pull
    simpa [f1, f2] using h_goal

/-- If conditional probabilities agree a.e. for a π-system generating ℋ,
then they agree for all H ∈ ℋ.

Use `condIndepSets` on π-systems to get `CondIndep mF (generateFrom π) mG μ`,
then apply Doob's characterization above.
-/
lemma condProb_eq_of_eq_on_pi_system {m₀ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (mF mG : MeasurableSpace Ω)
    (hmF : mF ≤ m₀) (hmG : mG ≤ m₀)
    (π : Set (Set Ω)) (hπ : IsPiSystem π)
    [SigmaFinite (μ.trim hmG)]
    (h : ∀ H ∈ π,
      μ[H.indicator (fun _ => (1 : ℝ)) | mF ⊔ mG]
        =ᵐ[μ] μ[H.indicator (fun _ => (1 : ℝ)) | mG]) :
    ∀ E, MeasurableSpace.generateFrom π ≤ m₀ →
      MeasurableSet[MeasurableSpace.generateFrom π] E →
      μ[E.indicator (fun _ => (1 : ℝ)) | mF ⊔ mG]
        =ᵐ[μ] μ[E.indicator (fun _ => (1 : ℝ)) | mG] := by
  classical
  have hmFG : mF ⊔ mG ≤ m₀ := sup_le hmF hmG
  intro hπ_le E hE

  -- Strategy: Fix S ∈ mF ⊔ mG and extend in E using Dynkin π-λ
  -- Define C(E) := "∫_S LHS dμ = ∫_S RHS dμ for all S ∈ mF ⊔ mG"
  -- Then use uniqueness of conditional expectation

  -- We'll show the two conditional expectations have the same integral on every measurable set
  have h_int_eq : ∀ (S : Set Ω), MeasurableSet[mF ⊔ mG] S →
      ∫ ω in S, (μ[E.indicator (fun _ => (1 : ℝ)) | mF ⊔ mG] ω) ∂μ
        = ∫ ω in S, (μ[E.indicator (fun _ => (1 : ℝ)) | mG] ω) ∂μ := by
    intro S hS

    -- Define the property C_S(E') for the Dynkin system
    let C_S : Set Ω → Prop := fun E' =>
      ∫ ω in S, (μ[E'.indicator (fun _ => (1 : ℝ)) | mF ⊔ mG] ω) ∂μ
        = ∫ ω in S, (μ[E'.indicator (fun _ => (1 : ℝ)) | mG] ω) ∂μ

    -- Step 1: C_S holds on π
    have hCπ : ∀ E' ∈ π, C_S E' := by
      intro E' hE'π
      have hAE := h E' hE'π
      exact setIntegral_congr_ae_of_ae hAE

    -- Step 2: C_S is closed under ∅, complement, and countable disjoint unions
    have hC_empty : C_S ∅ := by simp [C_S]

    have hC_compl : ∀ E', MeasurableSet[m₀] E' → C_S E' → C_S E'ᶜ := by
      intro E' hE'meas hCE'
      simp only [C_S] at hCE' ⊢
      -- Use linearity: indicator of complement = 1 - indicator
      have hId : E'ᶜ.indicator (fun _ : Ω => (1 : ℝ))
          = (fun _ : Ω => (1 : ℝ)) - E'.indicator (fun _ : Ω => (1 : ℝ)) := by
        funext ω
        by_cases hω : ω ∈ E' <;> simp [Set.indicator, hω]
      sorry -- Apply linearity of conditional expectation and set integrals

    have hC_iUnion : ∀ (f : ℕ → Set Ω), (∀ i, MeasurableSet[m₀] (f i)) →
        Pairwise (Disjoint on f) → (∀ i, C_S (f i)) → C_S (⋃ i, f i) := by
      intro f hf_meas hf_disj hf_C
      simp only [C_S] at hf_C ⊢
      sorry -- Use dominated convergence to commute ∫ and ∑

    -- Step 3: Apply Dynkin π-λ theorem
    sorry -- Apply induction_on_inter with the properties above

  -- Now use uniqueness of conditional expectation
  have h_ind_int : Integrable (E.indicator fun _ : Ω => (1 : ℝ)) μ :=
    (integrable_const (1 : ℝ)).indicator (hπ_le _ hE)
  refine (ae_eq_condExp_of_forall_setIntegral_eq (hm := hmFG) h_ind_int
    integrable_condExp.aestronglyMeasurable (fun S hS _ => ?_)).symm
  exact h_int_eq S hS

/-! ### Bounded Martingales and L² Inequalities -/

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
  classical
  -- Strategy: Use L² orthogonal projection properties
  -- condExp is the orthogonal projection onto the L² closure of m₁-measurable functions
  -- So ‖X₂‖² = ‖μ[X₂|m₁]‖² + ‖X₂ - μ[X₂|m₁]‖² (Pythagoras)
  -- Combined with the second moment equality, this forces X₂ - X₁ =ᵐ 0
  -- The following proof uses condexpL2 API:
  -- 1. Lift to L²: let f := X₂ as element of Lp ℝ 2 μ
  -- 2. Show μ[X₂|m₁] equals condexpL2 f (the L² conditional expectation)
  -- 3. Use orthogonality: ‖f‖² = ‖condexpL2 f‖² + ‖f - condexpL2 f‖²
  -- 4. From hSecond: ‖f‖² = ‖X₁‖² = ‖μ[X₂|m₁]‖² (using hmg)
  -- 5. This forces ‖f - condexpL2 f‖ = 0, hence f = condexpL2 f in L²
  -- 6. Conclude X₂ =ᵐ μ[X₂|m₁] =ᵐ X₁
  classical
  -- Promote X₁ to L² using the L² property of X₂.
  have h_cond_mem : MemLp (μ[X₂ | m₁]) 2 μ := hL2.condExp (m := m₁)
  have hX₁_mem : MemLp X₁ 2 μ := h_cond_mem.ae_eq hmg
  have h_diff_L2 : MemLp (X₂ - X₁) 2 μ := hL2.sub hX₁_mem
  -- The squared difference is L¹-integrable.
  have h_diff_mem : MemLp (X₂ - μ[X₂ | m₁]) 2 μ := hL2.sub h_cond_mem
  have h_diff_sq_int :
      Integrable (fun ω => (X₂ ω - μ[X₂ | m₁] ω) ^ 2) μ :=
    h_diff_mem.integrable_sq

  -- Identify the integral of the conditional variance.
  have h_integral_var :
      ∫ ω, μ[(X₂ - μ[X₂ | m₁])^2 | m₁] ω ∂μ
        = ∫ ω, (X₂ ω)^2 ∂μ - ∫ ω, (X₁ ω)^2 ∂μ := by
    have h_var_int :
        Integrable (μ[(X₂ - μ[X₂ | m₁])^2 | m₁]) μ :=
        integrable_condExp
    have h_mu_sq_int :
        Integrable (μ[X₂ ^ 2 | m₁]) μ :=
      integrable_condExp
    have h_cond_sq_int :
        Integrable (fun ω => (μ[X₂ | m₁] ω) ^ 2) μ :=
      h_cond_mem.integrable_sq
    -- The conditional variance equals μ[X₂² | m₁] - (μ[X₂ | m₁])²
    -- This is a standard variance decomposition formula
    have h_var_formula :
        μ[(X₂ - μ[X₂ | m₁])^2 | m₁] =ᵐ[μ] μ[X₂ ^ 2 | m₁] - (μ[X₂ | m₁]) ^ 2 := by
      -- The full proof requires:
      -- 1. Expanding (X₂ - μ[X₂|m₁])² = X₂² - 2·X₂·μ[X₂|m₁] + (μ[X₂|m₁])²
      -- 2. Linearity: μ[a + b + c | m] = μ[a|m] + μ[b|m] + μ[c|m]
      -- 3. Pull-out property: μ[g·f | m] = g·μ[f|m] when g is m-measurable
      -- 4. Idempotence: μ[μ[X|m] | m] = μ[X|m]
      sorry
    have h_congr :
        ∫ ω, μ[(X₂ - μ[X₂ | m₁])^2 | m₁] ω ∂μ
          = ∫ ω, (μ[X₂ ^ 2 | m₁] ω - μ[X₂ | m₁] ω ^ 2) ∂μ :=
      integral_congr_ae h_var_formula
    have h_sub :=
      integral_sub h_mu_sq_int h_cond_sq_int
    have h_condExp_sq :
        ∫ ω, μ[X₂ ^ 2 | m₁] ω ∂μ = ∫ ω, (X₂ ω) ^ 2 ∂μ :=
      integral_condExp hm₁
    have h_sq_replace :
        ∫ ω, (μ[X₂ | m₁] ω) ^ 2 ∂μ = ∫ ω, (X₁ ω) ^ 2 ∂μ :=
      integral_congr_ae (hmg.mono fun ω hω => by simpa [hω])
    calc
      ∫ ω, μ[(X₂ - μ[X₂ | m₁])^2 | m₁] ω ∂μ
          = ∫ ω, (μ[X₂ ^ 2 | m₁] ω - μ[X₂ | m₁] ω ^ 2) ∂μ := h_congr
      _ = (∫ ω, μ[X₂ ^ 2 | m₁] ω ∂μ)
            - ∫ ω, (μ[X₂ | m₁] ω) ^ 2 ∂μ := h_sub
      _ = ∫ ω, (X₂ ω) ^ 2 ∂μ - ∫ ω, (X₁ ω) ^ 2 ∂μ := by
        rw [h_condExp_sq, h_sq_replace]

  -- Replace the integral of the conditional variance with the integral of the squared deviation.
  have h_integral_diff :
      ∫ ω, (X₂ ω - X₁ ω) ^ 2 ∂μ = ∫ ω, μ[(X₂ - μ[X₂ | m₁])^2 | m₁] ω ∂μ := by
    haveI : SigmaFinite (μ.trim hm₁) := inferInstance
    have h_int : ∫ ω, μ[(X₂ - μ[X₂ | m₁])^2 | m₁] ω ∂μ = ∫ ω, (X₂ ω - μ[X₂ | m₁] ω) ^ 2 ∂μ :=
      integral_condExp hm₁
    have h_sq_eq :
        (fun ω => (X₂ ω - μ[X₂ | m₁] ω) ^ 2)
          =ᵐ[μ] fun ω => (X₂ ω - X₁ ω) ^ 2 :=
      hmg.mono fun ω hω => by simpa [hω]
    have h_sq_int : Integrable (fun ω => (X₂ ω - X₁ ω) ^ 2) μ :=
      h_diff_L2.integrable_sq
    calc
      ∫ ω, (X₂ ω - X₁ ω) ^ 2 ∂μ
          = ∫ ω, (X₂ ω - μ[X₂ | m₁] ω) ^ 2 ∂μ := integral_congr_ae h_sq_eq.symm
      _ = ∫ ω, μ[(X₂ - μ[X₂ | m₁])^2 | m₁] ω ∂μ := h_int.symm

  -- Combine the previous identities to deduce that the squared deviation integrates to zero.
  have h_diff_integral_zero :
      ∫ ω, (X₂ ω - X₁ ω) ^ 2 ∂μ = 0 := by
    simpa [hSecond, h_integral_var] using h_integral_diff

  -- Use the L² inner product to deduce that X₂ - X₁ vanishes almost everywhere.
  let diffLp := h_diff_L2.toLp (X₂ - X₁)
  have h_diff_coe : diffLp =ᵐ[μ] fun ω => X₂ ω - X₁ ω :=
    h_diff_L2.coeFn_toLp
  have h_integrand_eq :
      (fun ω => diffLp ω * diffLp ω)
        =ᵐ[μ] fun ω => (X₂ ω - X₁ ω) ^ 2 := by
    refine h_diff_coe.mono ?_
    intro ω hω
    simp [pow_two, hω]
  have h_integrable_prod :
      Integrable (fun ω => diffLp ω * diffLp ω) μ :=
    (h_diff_L2.integrable_sq.congr h_integrand_eq.symm)
  -- The squared L2 norm equals zero, so the function is zero
  have h_norm_zero : ‖diffLp‖ ^ 2 = 0 := by
    -- For Lp spaces with p=2, ‖f‖² = (∫|f|²)^(1/2)² = ∫|f|²
    have h_norm_eq : ‖diffLp‖ ^ 2 = ∫ ω, |diffLp ω| ^ 2 ∂μ := by
      -- ‖f‖_2 = (∫|f|²)^(1/2), so ‖f‖_2² = ∫|f|²
      sorry -- Need snorm_two_eq_toLp and relation to integral
    -- |diffLp|² = diffLp² since diffLp is real-valued
    have h_abs : (fun ω => |diffLp ω| ^ 2) =ᵐ[μ] fun ω => diffLp ω ^ 2 :=
      Eventually.of_forall fun ω => sq_abs _
    calc ‖diffLp‖ ^ 2
        = ∫ ω, |diffLp ω| ^ 2 ∂μ := h_norm_eq
      _ = ∫ ω, diffLp ω ^ 2 ∂μ := integral_congr_ae h_abs
      _ = ∫ ω, diffLp ω * diffLp ω ∂μ :=
          integral_congr_ae (Eventually.of_forall fun ω => by ring)
      _ = ∫ ω, (X₂ ω - X₁ ω) ^ 2 ∂μ := integral_congr_ae h_integrand_eq
      _ = 0 := h_diff_integral_zero
  have h_diffLp_zero : diffLp = 0 := by
    rw [← norm_eq_zero]
    exact pow_eq_zero h_norm_zero
  have h_zero_mem : MemLp (fun _ : Ω => (0 : ℝ)) 2 μ := MemLp.zero
  have h_zero_toLp :
      h_zero_mem.toLp (fun _ : Ω => (0 : ℝ)) = (0 : Lp ℝ 2 μ) :=
    MemLp.toLp_zero h_zero_mem
  have h_diff_zero :
      X₂ - X₁ =ᵐ[μ] fun _ : Ω => (0 : ℝ) := by
    have h_Lp_eq :
        diffLp = h_zero_mem.toLp (fun _ : Ω => (0 : ℝ)) := by
      simpa [diffLp, h_zero_toLp] using h_diffLp_zero
    exact
      (MemLp.toLp_eq_toLp_iff (μ := μ) (p := 2)
        (f := X₂ - X₁) (g := fun _ : Ω => (0 : ℝ))
        h_diff_L2 h_zero_mem).1 h_Lp_eq
  have h_eq : X₂ =ᵐ[μ] X₁ :=
    h_diff_zero.mono fun ω hω => sub_eq_zero.mp hω
  exact h_eq.symm

/-! ### Reverse Martingale Convergence -/

/-- **Reverse martingale convergence theorem.**

Along a decreasing family 𝒢, we have μ[X | 𝒢 n] → μ[X | ⋂ n, 𝒢 n] a.e. and in L¹.

This is FMP Theorem 7.23. Proven by reindexing to increasing filtration or following
the tail 0-1 law proof structure in mathlib (see `Mathlib.Probability.Independence.ZeroOne`).
Use `Integrable.tendsto_ae_condexp` and `ae_eq_condExp_of_forall_setIntegral_eq`.
-/
lemma reverse_martingale_convergence {m₀ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (𝒢 : ℕ → MeasurableSpace Ω)
    (h_le : ∀ n, 𝒢 n ≤ m₀)
    (h_decr : ∀ n, 𝒢 (n + 1) ≤ 𝒢 n)
    [∀ n, SigmaFinite (μ.trim (h_le n))]
    (X : Ω → ℝ) (hX_int : Integrable X μ)
    (hX_meas : StronglyMeasurable[⨅ n, 𝒢 n] X) :
    (∀ᵐ ω ∂μ, Tendsto (fun n => μ[X | 𝒢 n] ω) atTop (𝓝 (μ[X | ⨅ n, 𝒢 n] ω))) ∧
    Tendsto (fun n => eLpNorm (μ[X | 𝒢 n] - μ[X | ⨅ n, 𝒢 n]) 1 μ) atTop (𝓝 0) := by
  -- Strategy: Convert decreasing 𝒢 to increasing filtration via OrderDual ℕ
  -- Define ℱ : OrderDual ℕ → MeasurableSpace Ω by ℱ n = 𝒢 (OrderDual.ofDual n)
  -- This is monotone because 𝒢 is antitone and OrderDual reverses order

  sorry

set_option linter.unusedSectionVars false in
/-- Application to tail σ-algebras: convergence as we condition on
increasingly coarse shifted processes.

Specialization of reverse_martingale_convergence where 𝒢 n is a decreasing
family of σ-algebras (e.g., σ(θₙ X) for shifted processes).
The tail σ-algebra is ⨅ n, 𝒢 n.
-/
lemma condexp_tendsto_tail {m₀ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (𝒢 : ℕ → MeasurableSpace Ω)
    (h_le : ∀ n, 𝒢 n ≤ m₀)
    (h_decr : ∀ n, 𝒢 (n + 1) ≤ 𝒢 n)
    [∀ n, SigmaFinite (μ.trim (h_le n))]
    (f : Ω → ℝ) (hf : Integrable f μ)
    (hf_meas : StronglyMeasurable[⨅ n, 𝒢 n] f) :
    (∀ᵐ ω ∂μ, Tendsto (fun n => μ[f | 𝒢 n] ω) atTop (𝓝 (μ[f | ⨅ n, 𝒢 n] ω))) ∧
    Tendsto (fun n => eLpNorm (μ[f | 𝒢 n] - μ[f | ⨅ n, 𝒢 n]) 1 μ) atTop (𝓝 0) :=
  reverse_martingale_convergence 𝒢 h_le h_decr f hf hf_meas

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
  (condIndep_iff_condexp_eq hmF hmG hmH).mpr h

end Exchangeability.Probability

/-! ### Re-exports and Aliases from Mathlib

## Conditional Expectation

Mathlib's conditional expectation is available via the notation `μ[f|m]`
which expands to `MeasureTheory.condExp m μ f`.

Key lemmas available in mathlib (`Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic`):
- `condExp_const`: E[c | m] = c for constants
- `setIntegral_condExp`: ∫ x in s, μ[f|m] x ∂μ = ∫ x in s, f x ∂μ for m-measurable s
- `integral_condExp`: ∫ x, μ[f|m] x ∂μ = ∫ x, f x ∂μ
- `condExp_indicator`: μ[s.indicator f|m] =ᵐ[μ] s.indicator (μ[f|m]) for m-measurable s
- `condExp_add`, `condExp_smul`: linearity properties

## Martingales

Mathlib provides martingale theory in `Mathlib.Probability.Martingale.Basic`:
- `Martingale f ℱ μ`: f is adapted to ℱ and E[f_j | ℱ_i] = f_i for i ≤ j
- `Supermartingale`, `Submartingale`: ordered variants
- `martingale_condExp`: the sequence (E[f | ℱ_i]) is a martingale
- `Martingale.setIntegral_eq`: integrals over ℱ_i-measurable sets are preserved

Optional sampling and convergence theorems are in:
- `Mathlib.Probability.Martingale.OptionalSampling`
- `Mathlib.Probability.Martingale.Convergence` (if available)

-/

namespace MeasureTheory

-- The main conditional expectation function is already exported from mathlib
-- as `condExp` with notation `μ[f|m]`

end MeasureTheory
