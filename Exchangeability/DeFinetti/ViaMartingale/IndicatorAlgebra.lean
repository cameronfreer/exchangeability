/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Exchangeability.DeFinetti.MartingaleHelpers
import Exchangeability.PathSpace.CylinderHelpers

/-!
# Indicator Algebra for Finite Cylinders

This file contains the `indProd` definition and related lemmas for working with
products of indicator functions on finite cylinders.

## Main definitions

* `indProd X r C` - Product of indicators: ∏ᵢ 𝟙_{X_i ∈ C_i}

## Main results

* `indProd_as_indicator` - indProd equals indicator of intersection
* `indProd_eq_firstRCylinder_indicator` - Connection to firstRCylinder
* `indProd_integrable` - Integrability under finite measures

These are extracted from ViaMartingale.lean to enable modular imports.
-/

noncomputable section
open scoped MeasureTheory
open MeasureTheory

namespace Exchangeability.DeFinetti.ViaMartingale

open Exchangeability.PathSpace

variable {Ω α : Type*}

/-! ## Product of indicators for finite cylinders -/

/-- Product of indicator functions for a finite cylinder on the first `r` coordinates. -/
def indProd (X : ℕ → Ω → α) (r : ℕ) (C : Fin r → Set α) : Ω → ℝ :=
  fun ω => ∏ i : Fin r, Set.indicator (C i) (fun _ => (1 : ℝ)) (X i ω)

lemma indProd_as_indicator (X : ℕ → Ω → α) (r : ℕ) (C : Fin r → Set α) :
    indProd X r C
      = Set.indicator {ω | ∀ i : Fin r, X i ω ∈ C i} (fun _ => (1 : ℝ)) := by
  funext ω
  simp only [indProd, Set.indicator]
  split_ifs with h
  · -- ω satisfies all conditions: product equals 1
    calc ∏ i : Fin r, Set.indicator (C i) (fun _ => (1 : ℝ)) (X i ω)
        = ∏ i : Fin r, (1 : ℝ) := by congr 1; ext i; simp [Set.indicator, h i]
      _ = 1 := Finset.prod_const_one
  · -- ω doesn't satisfy all conditions
    obtain ⟨i, hi⟩ := not_forall.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

/-- Connection between `indProd` and `firstRCylinder`: the product indicator
equals the indicator of the first-`r` cylinder. -/
lemma indProd_eq_firstRCylinder_indicator (X : ℕ → Ω → α) (r : ℕ) (C : Fin r → Set α) :
    indProd X r C = (firstRCylinder X r C).indicator (fun _ => (1 : ℝ)) := by
  rw [indProd_as_indicator]; rfl

/-- Basic integrability: `indProd` is an indicator of a measurable set, hence integrable
under a finite measure. -/
lemma indProd_integrable [MeasurableSpace Ω] [MeasurableSpace α]
    {μ : Measure Ω} [IsFiniteMeasure μ] (X : ℕ → Ω → α)
    (r : ℕ) (C : Fin r → Set α)
    (hX : ∀ n, Measurable (X n)) (hC : ∀ i, MeasurableSet (C i)) :
    Integrable (indProd X r C) μ := by
  -- indProd X r C is the indicator of firstRCylinder X r C
  rw [indProd_eq_firstRCylinder_indicator]
  -- Indicator functions of measurable sets are integrable under finite measures
  exact Integrable.indicator (integrable_const 1) (firstRCylinder_measurable_ambient X r C hX hC)

/-- indProd of zero coordinates is identically 1. -/
@[simp] lemma indProd_zero (X : ℕ → Ω → α) (C : Fin 0 → Set α) :
    indProd X 0 C = fun _ => 1 := funext fun _ => by simp [indProd]

end Exchangeability.DeFinetti.ViaMartingale
