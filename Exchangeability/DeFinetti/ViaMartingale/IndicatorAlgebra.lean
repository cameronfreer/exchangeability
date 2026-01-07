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
* `indProd_mul` - Product formula for indProd

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
        = ∏ i : Fin r, (1 : ℝ) := by
          congr 1
          ext i
          simp only [Set.indicator]
          rw [if_pos (h i)]
      _ = 1 := Finset.prod_const_one
  · -- ω doesn't satisfy all conditions
    by_cases hr : ∃ i : Fin r, X i ω ∉ C i
    · obtain ⟨i, hi⟩ := hr
      have : Set.indicator (C i) (fun _ => (1 : ℝ)) (X i ω) = 0 := by
        simp only [Set.indicator]
        rw [if_neg hi]
      rw [Finset.prod_eq_zero (Finset.mem_univ i) this]
    · simp only [not_exists, not_not] at hr
      exact absurd hr h

/-- Connection between `indProd` and `firstRCylinder`: the product indicator
equals the indicator of the first-`r` cylinder. -/
lemma indProd_eq_firstRCylinder_indicator (X : ℕ → Ω → α) (r : ℕ) (C : Fin r → Set α) :
    indProd X r C = (firstRCylinder X r C).indicator (fun _ => (1 : ℝ)) := by
  rw [indProd_as_indicator]
  rfl

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
  apply Integrable.indicator
  · exact integrable_const 1
  · exact firstRCylinder_measurable_ambient X r C hX hC

/-- indProd is strongly measurable when coordinates and sets are measurable. -/
@[measurability, fun_prop]
lemma indProd_stronglyMeasurable [MeasurableSpace Ω] [MeasurableSpace α]
    (X : ℕ → Ω → α) (r : ℕ) (C : Fin r → Set α)
    (hX : ∀ n, Measurable (X n)) (hC : ∀ i, MeasurableSet (C i)) :
    StronglyMeasurable (indProd X r C) := by
  rw [indProd_eq_firstRCylinder_indicator]
  exact .indicator stronglyMeasurable_const (firstRCylinder_measurable_ambient X r C hX hC)

/-- indProd takes values in [0,1]. -/
lemma indProd_nonneg_le_one (X : ℕ → Ω → α) (r : ℕ) (C : Fin r → Set α) (ω : Ω) :
    0 ≤ indProd X r C ω ∧ indProd X r C ω ≤ 1 := by
  rw [indProd_as_indicator]
  by_cases h : ∀ i : Fin r, X i ω ∈ C i
  · simp [Set.indicator, h]
  · simp [Set.indicator, h]

/-- indProd of zero coordinates is identically 1. -/
@[simp] lemma indProd_zero (X : ℕ → Ω → α) (C : Fin 0 → Set α) :
    indProd X 0 C = fun _ => 1 := by
  funext ω
  simp [indProd]

/-- indProd on the universal sets is identically 1. -/
lemma indProd_univ (X : ℕ → Ω → α) (r : ℕ) :
    indProd X r (fun _ => Set.univ) = fun _ => 1 := by
  funext ω
  simp [indProd, Set.indicator]

/-- indProd is measurable when coordinates are measurable. -/
@[measurability, fun_prop]
lemma indProd_measurable [MeasurableSpace Ω] [MeasurableSpace α]
    (X : ℕ → Ω → α) (r : ℕ) (C : Fin r → Set α)
    (hX : ∀ n, Measurable (X n)) (hC : ∀ i, MeasurableSet (C i)) :
    Measurable (indProd X r C) :=
  (indProd_stronglyMeasurable X r C hX hC).measurable

/-- indProd product equals multiplication of indProds. -/
lemma indProd_mul (X : ℕ → Ω → α) {r : ℕ} {C D : Fin r → Set α} (ω : Ω) :
    indProd X r C ω * indProd X r D ω = indProd X r (fun i => C i ∩ D i) ω := by
  simp only [indProd]
  rw [← Finset.prod_mul_distrib]
  congr 1
  funext i
  simp only [Set.indicator]
  by_cases hC : X i ω ∈ C i <;> by_cases hD : X i ω ∈ D i <;>
    simp [hC, hD, Set.mem_inter_iff]

/-- indProd on intersection via firstRCylinder. -/
lemma indProd_inter_eq (X : ℕ → Ω → α) {r : ℕ} {C D : Fin r → Set α} :
    indProd X r (fun i => C i ∩ D i)
      = (firstRCylinder X r C ∩ firstRCylinder X r D).indicator (fun _ => (1 : ℝ)) := by
  rw [indProd_eq_firstRCylinder_indicator, firstRCylinder_inter]

end Exchangeability.DeFinetti.ViaMartingale
