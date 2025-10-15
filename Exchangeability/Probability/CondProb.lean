/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Probability.ConditionalExpectation
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

/-!
# Conditional Probability

This file provides the conditional probability API for probability theory, built on
mathlib's conditional expectation infrastructure.

## Main Definitions

- `condProb μ m A`: Conditional probability of event `A` given σ-algebra `m`
  Defined as `μ[1_A | m]` (conditional expectation of the indicator)

## Main Results

- `condProb_ae_nonneg_le_one`: Conditional probability takes values in [0,1] a.e.
- `condProb_integral_eq`: Integration property: ∫ P[A|m] over B equals μ(A ∩ B)
- `condProb_univ`, `condProb_empty`, `condProb_compl`: Basic properties

All proofs are complete with no sorries.

-/

noncomputable section
open scoped MeasureTheory ProbabilityTheory Topology
open MeasureTheory Filter Set Function

namespace Exchangeability.Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-! ### Conditional Probability

Note: Many lemmas in this file explicitly include `{m₀ : MeasurableSpace Ω}` as a parameter
to work with multiple measurable space structures on Ω (e.g., m₀, m for conditioning). This makes
the section variable `[MeasurableSpace Ω]` unused for those lemmas, requiring `set_option
linter.unusedSectionVars false` before each affected declaration. -/

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
/-- Uniform bound: conditional probability is in `[0,1]` a.e. uniformly over `A`. -/
lemma condProb_ae_bound_one {m₀ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (m : MeasurableSpace Ω) (hm : m ≤ m₀) [SigmaFinite (μ.trim hm)]
    (A : Set Ω) (hA : MeasurableSet[m₀] A) :
    ∀ᵐ ω ∂μ, ‖μ[A.indicator (fun _ => (1 : ℝ)) | m] ω‖ ≤ 1 := by
  have h : ∀ᵐ ω ∂μ, 0 ≤ condProb μ m A ω ∧ condProb μ m A ω ≤ 1 := condProb_ae_nonneg_le_one (m₀ := m₀) m hm hA
  filter_upwards [h] with ω hω
  rcases hω with ⟨h0, h1⟩
  have : |condProb μ m A ω| ≤ 1 := by
    have : |condProb μ m A ω| = condProb μ m A ω := abs_of_nonneg h0
    simpa [this]
  simpa [Real.norm_eq_abs, condProb] using this

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

end Exchangeability.Probability
