/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Exchangeability.PathSpace.Shift

/-!
# Cylinder Functions for de Finetti's Theorem

This file defines cylinder functions on infinite path spaces and proves their
measurability and boundedness properties.

## Main Definitions

* `cylinderFunction`: A function on path space depending only on finitely many coordinates
* `productCylinder`: Product of functions evaluated at different coordinates
* `productCylinderLp`: Lp representative for bounded product cylinders
* `shiftedCylinder`: Cylinder function composed with shift^n

## Main Results

* `measurable_cylinderFunction`: Cylinder functions are measurable
* `measurable_productCylinder`: Product cylinders are measurable
* `productCylinder_bounded`: Product cylinders are bounded
* `productCylinder_memLp`: Product cylinders are in L²
-/

open Filter MeasureTheory Exchangeability.PathSpace

noncomputable section

variable {α : Type*} [MeasurableSpace α]

/-- Cylinder function: a function on path space depending only on finitely many coordinates.
For simplicity, we take the first m coordinates. -/
def cylinderFunction {m : ℕ} (φ : (Fin m → α) → ℝ) : (ℕ → α) → ℝ :=
  fun ω => φ (fun k => ω k.val)

/-- Product cylinder: ∏_{k < m} fₖ(ω k). -/
def productCylinder {m : ℕ} (fs : Fin m → α → ℝ) : (ℕ → α) → ℝ :=
  fun ω => ∏ k : Fin m, fs k (ω k.val)

omit [MeasurableSpace α] in
lemma productCylinder_eq_cylinder {m : ℕ} (fs : Fin m → α → ℝ) :
    productCylinder fs = cylinderFunction (fun coords => ∏ k, fs k (coords k)) := rfl

/-- Measurability of cylinder functions. -/
lemma measurable_cylinderFunction {m : ℕ} {φ : (Fin m → α) → ℝ}
    (_hφ : Measurable φ) :
    Measurable (cylinderFunction φ) := by
  classical
  simpa [cylinderFunction] using _hφ.comp (by measurability :
    Measurable fun ω : ℕ → α => fun k : Fin m => ω k.val)

/-- Measurability of product cylinders. -/
lemma measurable_productCylinder {m : ℕ} {fs : Fin m → α → ℝ}
    (hmeas : ∀ k, Measurable (fs k)) :
    Measurable (productCylinder fs) := by
  classical
  unfold productCylinder
  -- Product of measurable functions is measurable
  apply Finset.measurable_prod
  intro k _
  exact (hmeas k).comp (measurable_pi_apply k.val)

omit [MeasurableSpace α] in
/-- Boundedness of product cylinders. -/
lemma productCylinder_bounded {m : ℕ} {fs : Fin m → α → ℝ}
    (hbd : ∀ k, ∃ C, ∀ x, |fs k x| ≤ C) :
    ∃ C, ∀ ω, |productCylinder fs ω| ≤ C := by
  -- Take C = ∏ Cₖ where |fₖ| ≤ Cₖ
  classical
  choose bound hbound using hbd
  let C : Fin m → ℝ := fun k => max (bound k) 1
  refine ⟨∏ k : Fin m, C k, ?_⟩
  intro ω
  have h_abs_le : ∀ k : Fin m, |fs k (ω k.val)| ≤ C k := by
    intro k
    have := hbound k (ω k.val)
    exact this.trans (le_max_left _ _)
  have h_nonneg : ∀ k : Fin m, 0 ≤ |fs k (ω k.val)| := fun _ => abs_nonneg _
  have hprod : ∏ k : Fin m, |fs k (ω k.val)| ≤ ∏ k : Fin m, C k := by
    simpa using
      (Finset.prod_le_prod (s := Finset.univ)
        (f := fun k : Fin m => |fs k (ω k.val)|)
        (g := fun k : Fin m => C k)
        (fun k _ => h_nonneg k)
        (fun k _ => h_abs_le k))
  have habs_eq : |productCylinder fs ω| = ∏ k : Fin m, |fs k (ω k.val)| := by
    simp [productCylinder, Finset.abs_prod]
  exact (by simpa [habs_eq] using hprod)

/-- Membership of product cylinders in `L²`. -/
lemma productCylinder_memLp
    {m : ℕ} (fs : Fin m → α → ℝ)
    (hmeas : ∀ k, Measurable (fs k))
    (hbd : ∀ k, ∃ C, ∀ x, |fs k x| ≤ C)
    {μ : Measure (ℕ → α)} [IsProbabilityMeasure μ] :
    MeasureTheory.MemLp (productCylinder fs) 2 μ := by
  classical
  obtain ⟨C, hC⟩ := productCylinder_bounded (fs:=fs) hbd
  refine MeasureTheory.MemLp.of_bound (μ := μ) (p := 2)
    (measurable_productCylinder hmeas).aestronglyMeasurable C ?_
  filter_upwards with ω
  simpa [Real.norm_eq_abs] using hC ω

/-- `Lp` representative associated to a bounded product cylinder. -/
noncomputable def productCylinderLp
    {m : ℕ} (fs : Fin m → α → ℝ)
    (hmeas : ∀ k, Measurable (fs k))
    (hbd : ∀ k, ∃ C, ∀ x, |fs k x| ≤ C)
    {μ : Measure (ℕ → α)} [IsProbabilityMeasure μ] : Lp ℝ 2 μ :=
  (productCylinder_memLp (fs := fs) hmeas hbd).toLp (productCylinder fs)

lemma productCylinderLp_ae_eq
    {m : ℕ} (fs : Fin m → α → ℝ)
    (hmeas : ∀ k, Measurable (fs k))
    (hbd : ∀ k, ∃ C, ∀ x, |fs k x| ≤ C)
    {μ : Measure (ℕ → α)} [IsProbabilityMeasure μ] :
    (∀ᵐ ω ∂μ, productCylinderLp (μ := μ) (fs := fs) hmeas hbd ω =
      productCylinder fs ω) := by
  classical
  exact MeasureTheory.MemLp.coeFn_toLp
    (productCylinder_memLp (μ := μ) (fs := fs) hmeas hbd)

/-- The shifted cylinder function: F ∘ shift^n. -/
def shiftedCylinder (n : ℕ) (F : (ℕ → α) → ℝ) : (ℕ → α) → ℝ :=
  fun ω => F ((shift^[n]) ω)
