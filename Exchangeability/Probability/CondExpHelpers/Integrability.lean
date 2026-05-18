/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Unique
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Independence.Conditional

/-!
# Integrability and σ-algebra Factorization for Conditional Expectation

This file provides integrability lemmas, uniqueness arguments, and σ-algebra factorization
lemmas for conditional expectations.

## Main results

* `integrable_mul_of_bound_one`: Product with bounded factor is integrable
* `abs_condExp_le_condExp_abs`: Jensen's inequality for conditional expectation
* `condExp_indicator_ae_bound_one`: CE of indicator is a.e. in [0,1]
-/

noncomputable section
open scoped MeasureTheory ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set

/-!
## Integrability of products with bounded factors
-/

/-- If `f ∈ L¹(μ)` and `g` is a.e. bounded by `1`, then `g⋅f ∈ L¹(μ)`. -/
lemma integrable_mul_of_bound_one
  {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  {f g : Ω → ℝ}
  (hf : Integrable f μ)
  (hg_meas : AEStronglyMeasurable g μ)
  (hbound : ∀ᵐ ω ∂μ, ‖g ω‖ ≤ (1 : ℝ)) :
  Integrable (fun ω => g ω * f ω) μ := hf.bdd_mul hg_meas hbound

/-- **Jensen's inequality for conditional expectation**: the absolute value of a conditional
expectation is a.e. bounded by the conditional expectation of the absolute value.

For integrable `f`: `|μ[f|m]| ≤ μ[|f||m]` almost everywhere.
-/
@[nolint unusedArguments]
lemma abs_condExp_le_condExp_abs
    {Ω : Type*} {m m₀ : MeasurableSpace Ω} {μ : Measure Ω}
    (hm : m ≤ m₀) [SigmaFinite (μ.trim hm)]
    {f : Ω → ℝ}
    (hf : Integrable f μ) :
    ∀ᵐ ω ∂μ, |(μ[f|m]) ω| ≤ (μ[(fun ω => |f ω|)|m]) ω := by
  -- Upper bound: μ[f|m] ≤ μ[|f||m]
  have h_up : μ[f|m] ≤ᵐ[μ] μ[(fun ω => |f ω|)|m] := by
    refine condExp_mono hf ?_ ?_
    · exact hf.abs
    · exact .of_forall fun _ => le_abs_self _
  -- Lower bound: -μ[|f||m] ≤ μ[f|m]
  -- Proof: f ≥ -|f| pointwise, so μ[f|m] ≥ μ[-|f||m] = -μ[|f||m]
  have h_low : (fun ω => -(μ[(fun ω => |f ω|)|m]) ω) ≤ᵐ[μ] μ[f|m] := by
    have neg_abs_bound : (fun ω => -(|f ω|)) ≤ᵐ[μ] f := .of_forall fun _ => neg_abs_le _
    have ce_ineq : μ[(fun ω => -(|f ω|))|m] ≤ᵐ[μ] μ[f|m] :=
      condExp_mono hf.abs.neg hf neg_abs_bound
    have neg_eq : (fun ω => -(μ[(fun ω => |f ω|)|m]) ω) =ᵐ[μ] μ[(fun ω => -(|f ω|))|m] :=
      (condExp_neg (fun ω => |f ω|) m).symm
    exact neg_eq.le.trans ce_ineq
  -- Combine: |x| ≤ y iff -y ≤ x ≤ y
  filter_upwards [h_up, h_low] with ω hup hlow
  rw [abs_le]
  exact ⟨hlow, hup⟩

/-- The conditional expectation of an indicator (ℝ-valued) is a.e. in `[0,1]`. -/
lemma condExp_indicator_ae_bound_one
  {Ω β : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
  {mW : MeasurableSpace Ω} (hm : mW ≤ m0)
  {Z : Ω → β} [MeasurableSpace β] {B : Set β}
  (hZ : @Measurable Ω β m0 _ Z) (hB : MeasurableSet B) :
  ∀ᵐ ω ∂μ,
    0 ≤ MeasureTheory.condExp mW μ
          (fun ω => (Set.indicator (Z ⁻¹' B) (fun _ => (1 : ℝ)) ω)) ω
    ∧
    MeasureTheory.condExp mW μ
          (fun ω => (Set.indicator (Z ⁻¹' B) (fun _ => (1 : ℝ)) ω)) ω ≤ 1 := by
  have h_int : Integrable (Set.indicator (Z ⁻¹' B) (fun _ => (1 : ℝ))) μ :=
    (integrable_const 1).indicator (hZ hB)
  have h0 : ∀ᵐ ω ∂μ, (0 : ℝ) ≤ Set.indicator (Z ⁻¹' B) (fun _ => (1 : ℝ)) ω :=
    .of_forall fun ω => Set.indicator_nonneg (fun _ _ => zero_le_one) ω
  have h1 : ∀ᵐ ω ∂μ, Set.indicator (Z ⁻¹' B) (fun _ => (1 : ℝ)) ω ≤ 1 :=
    .of_forall fun ω => Set.indicator_le_self' (fun _ _ => zero_le_one) ω
  have hCE1 : μ[Set.indicator (Z ⁻¹' B) (fun _ => (1 : ℝ)) | mW] ≤ᵐ[μ] μ[fun _ => (1 : ℝ) | mW] :=
    condExp_mono h_int (integrable_const _) h1
  filter_upwards [condExp_nonneg h0, hCE1] with ω h0' h1'
  simp only [condExp_const hm (1 : ℝ)] at h1'
  exact ⟨h0', h1'⟩

end
