/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Probability.Independence.Conditional
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-!
# Doob's Characterization of Conditional Independence

This file provides a characterization of conditional independence via the
projection property of conditional expectation.

## Main Results

* `condIndep_of_indicator_condexp_eq`: **Doob's characterization** (reverse direction):
  If for all H ∈ mH we have E[1_H | mF ⊔ mG] = E[1_H | mG] a.e., then mF and mH
  are conditionally independent given mG.

## Mathematical Context

For σ-algebras 𝒻, 𝒢, ℋ, we have 𝒻 ⊥⊥_𝒢 ℋ if and only if
```
P[H | 𝒻 ∨ 𝒢] = P[H | 𝒢] a.s. for all H ∈ ℋ
```

This characterization follows from the product formula in `condIndep_iff`:
- Forward direction: From the product formula, taking F = univ gives the
  projection property
- Reverse direction (this file): The projection property implies the product
  formula via uniqueness of conditional expectation

Mathlib has `condIndep_iff` (equivalence via product formula), but this lemma
proves the reverse via a different route (projection property), which is
mathematically valuable.

## Suggested Mathlib Location

`Mathlib.Probability.Independence.Conditional`

## References

* Kallenberg (2005), *Probabilistic Symmetries and Invariance Principles*, §6.6
* Folland (1999), *Real Analysis*, Theorem 6.18 (conditional independence)
-/

open MeasureTheory Filter Set Function
open scoped MeasureTheory ProbabilityTheory

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]

/-- **Doob's characterization of conditional independence (reverse direction).**

If for all H ∈ mH we have E[1_H | mF ⊔ mG] = E[1_H | mG] a.e., then mF and mH
are conditionally independent given mG.

The proof uses:
1. Tower property from mG up to mF ⊔ mG
2. Pull-out property at the middle level (mF ⊔ mG)
3. The projection hypothesis to drop mF at the middle level
4. Pull-out property at the outer level (mG)
5. Chaining the equalities into the product formula -/
theorem condIndep_of_indicator_condexp_eq
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {mF mG mH : MeasurableSpace Ω}
    (hmF : mF ≤ mΩ) (hmG : mG ≤ mΩ) (hmH : mH ≤ mΩ)
    (h : ∀ H, MeasurableSet[mH] H →
      μ[H.indicator (fun _ => (1 : ℝ)) | mF ⊔ mG]
        =ᵐ[μ] μ[H.indicator (fun _ => (1 : ℝ)) | mG]) :
    CondIndep mG mF mH hmG μ := by
  classical
  refine (condIndep_iff mG mF mH hmG hmF hmH μ).2 ?_
  intro tF tH htF htH
  -- Indicator functions for tF and tH
  set f1 : Ω → ℝ := tF.indicator 1 with hf1_def
  set f2 : Ω → ℝ := tH.indicator 1 with hf2_def
  -- Key: product of indicators equals indicator of intersection
  have hf1f2 : f1 * f2 = (tF ∩ tH).indicator 1 := inter_indicator_one.symm
  -- Integrability facts
  have hf1_int : Integrable f1 μ := (integrable_const 1).indicator (hmF _ htF)
  have hf2_int : Integrable f2 μ := (integrable_const 1).indicator (hmH _ htH)
  have hf1f2_int : Integrable (f1 * f2) μ := by
    rw [hf1f2]; exact (integrable_const 1).indicator (hmF _ htF |>.inter (hmH _ htH))
  -- f1 is AEStronglyMeasurable w.r.t. mF ⊔ mG
  have hf1_aesm : AEStronglyMeasurable[mF ⊔ mG] f1 μ :=
    (stronglyMeasurable_const.indicator htF).aestronglyMeasurable.mono le_sup_left
  -- Tower property: E[f1·f2 | mG] = E[E[f1·f2 | mF⊔mG] | mG]
  have h_tower : μ[f1 * f2 | mG] =ᵐ[μ] μ[μ[f1 * f2 | mF ⊔ mG] | mG] := by
    simpa using (condExp_condExp_of_le (hm₁₂ := le_sup_right)
      (hm₂ := sup_le hmF hmG) (f := f1 * f2)).symm
  -- Pull-out at middle level: E[f1·f2 | mF⊔mG] = f1 · E[f2 | mF⊔mG]
  have h_pull_middle : μ[f1 * f2 | mF ⊔ mG] =ᵐ[μ] f1 * μ[f2 | mF ⊔ mG] :=
    condExp_mul_of_aestronglyMeasurable_left hf1_aesm hf1f2_int hf2_int
  -- Projection hypothesis: E[f2 | mF⊔mG] = E[f2 | mG]
  have hProj : μ[f2 | mF ⊔ mG] =ᵐ[μ] μ[f2 | mG] := h tH htH
  -- Combine: E[f1·f2 | mF⊔mG] = f1 · E[f2 | mG]
  have h_middle_to_G : μ[f1 * f2 | mF ⊔ mG] =ᵐ[μ] f1 * μ[f2 | mG] :=
    h_pull_middle.trans (EventuallyEq.mul EventuallyEq.rfl hProj)
  -- Integrability of f1 · E[f2 | mG]
  have hf1_cond_int : Integrable (f1 * μ[f2 | mG]) μ := by
    have h_eq : f1 * μ[f2 | mG] = tF.indicator (fun ω => μ[f2 | mG] ω) := by
      funext ω; by_cases hω : ω ∈ tF <;> simp [f1, indicator, hω]
    rw [h_eq]; exact integrable_condExp.indicator (hmF _ htF)
  -- Pull-out at outer level: E[f1 · E[f2|mG] | mG] = E[f1|mG] · E[f2|mG]
  have h_pull_outer : μ[f1 * μ[f2 | mG] | mG] =ᵐ[μ] μ[f1 | mG] * μ[f2 | mG] :=
    condExp_mul_of_aestronglyMeasurable_right
      stronglyMeasurable_condExp.aestronglyMeasurable hf1_cond_int hf1_int
  -- Chain: E[f1·f2 | mG] = E[f1|mG] · E[f2|mG]
  have h_prod : μ[f1 * f2 | mG] =ᵐ[μ] μ[f1 | mG] * μ[f2 | mG] :=
    h_tower.trans ((condExp_congr_ae h_middle_to_G).trans h_pull_outer)
  simp only [hf1f2, hf1_def, hf2_def, Pi.one_apply] at h_prod ⊢
  convert h_prod using 2 <;> ext ω <;> by_cases h1 : ω ∈ tF <;> by_cases h2 : ω ∈ tH <;>
    simp [indicator, h1, h2, mem_inter_iff]

end ProbabilityTheory
