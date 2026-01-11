/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Exchangeability.Core
import Exchangeability.Contractability
import Exchangeability.PathSpace.Shift

/-!
# Bridge: Path Space Measure and Shift Preservation

This file provides the path space measure `μ_path` and proves that contractability
implies the shift map is measure-preserving on path space.

## Main definitions

* `pathify X`: Factor map `ω ↦ (n ↦ X n ω)` from sample space to path space
* `μ_path μ X`: Law of process X as a measure on path space

## Main results

* `contractable_shift_invariant_law`: Contractability implies shift-invariant law
* `measurePreserving_shift_path`: Packages above as `MeasurePreserving` for MET
-/

noncomputable section
open MeasureTheory

namespace Exchangeability.Bridge

/-! ## Path Space and Factor Map -/

-- Note: We use explicit parameters throughout to avoid variable scoping issues

/-- Path space for a type α -/
abbrev PathSpace (α : Type*) := ℕ → α

-- Only use the Ω[α] notation in display contexts to avoid shadowing the variable Ω

/-- Factor map that sends `ω : Ω` to the path `(n ↦ X n ω)` -/
def pathify {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α] (X : ℕ → Ω → α) :
    Ω → PathSpace α :=
  fun ω n => X n ω

lemma measurable_pathify {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α] {X : ℕ → Ω → α}
    (hX_meas : ∀ n, Measurable (X n)) :
    Measurable (pathify X) :=
  measurable_pi_lambda _ hX_meas

/-- Law of the process as a probability measure on path space. -/
def μ_path {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (μ : Measure Ω) (X : ℕ → Ω → α) : Measure (PathSpace α) :=
  Measure.map (pathify X) μ

/-- Alternate definition of process law without explicit μ for compatibility.
Equivalent to `μ_path` but with μ as an implicit argument. -/
def μ_path' {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {α : Type*} [MeasurableSpace α] (X : ℕ → Ω → α) : Measure (PathSpace α) :=
  Measure.map (pathify X) μ

lemma isProbabilityMeasure_μ_path {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → α) (hX : ∀ n, Measurable (X n)) :
    IsProbabilityMeasure (μ_path μ X) :=
  Measure.isProbabilityMeasure_map (measurable_pathify hX).aemeasurable

/-! ## B. Bridge 1: Contractable → Shift Invariance -/

open Exchangeability
open Exchangeability.PathSpace  -- For shift operator

/-- **Bridge 1.** `Contractable` ⇒ shift-invariant law on path space. -/
lemma contractable_shift_invariant_law {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} (hX : Exchangeability.Contractable μ X)
    (hX_meas : ∀ n, Measurable (X n)) :
    Measure.map (shift (α := ℝ)) (μ_path μ X) = (μ_path μ X) := by
  /- Proof: Use `measure_eq_of_fin_marginals_eq_prob` - two probability measures on ℕ → ℝ
     are equal if all finite marginals agree. Then use contractability to show
     that shift doesn't change finite marginals. -/
  -- Both measures are probability measures
  haveI : IsProbabilityMeasure (μ_path μ X) :=
    isProbabilityMeasure_μ_path μ X hX_meas
  haveI : IsProbabilityMeasure (Measure.map (shift (α := ℝ)) (μ_path μ X)) :=
    Measure.isProbabilityMeasure_map shift_measurable.aemeasurable

  -- Apply the finite marginals theorem
  apply Exchangeability.measure_eq_of_fin_marginals_eq_prob (α := ℝ)

  -- For each n, show finite marginals agree
  intro n S hS

  -- Measurability facts
  have h_shift_meas : Measurable (shift (α := ℝ)) := shift_measurable
  have h_pathify_meas : Measurable (pathify X) := measurable_pathify hX_meas
  have h_prefix_meas : Measurable (Exchangeability.prefixProj (α := ℝ) n) :=
    Exchangeability.measurable_prefixProj (α := ℝ) (n := n)

  -- μ_path μ X = Measure.map (pathify X) μ by definition
  unfold μ_path

  -- LHS: Measure.map (prefixProj n) (Measure.map shift (Measure.map (pathify X) μ))
  --    = Measure.map (prefixProj n ∘ shift ∘ pathify X) μ
  rw [Measure.map_map h_prefix_meas h_shift_meas,
      Measure.map_map (h_prefix_meas.comp h_shift_meas) h_pathify_meas]

  -- RHS: Measure.map (prefixProj n) (Measure.map (pathify X) μ)
  --    = Measure.map (prefixProj n ∘ pathify X) μ
  rw [Measure.map_map h_prefix_meas h_pathify_meas]

  -- Now the goal is about Measure.map of two compositions
  -- LHS map: prefixProj n ∘ shift ∘ pathify X = fun ω i => X (i + 1) ω
  -- RHS map: prefixProj n ∘ pathify X = fun ω i => X i ω

  -- Define k : Fin n → ℕ as k i = i + 1 (strictly monotone)
  let k : Fin n → ℕ := fun i => i.val + 1
  have hk_strictMono : StrictMono k := fun i j hij => Nat.add_lt_add_right hij 1

  -- Show both maps equal the standard forms
  -- Note: goal has (prefixProj ∘ shift) ∘ pathify X, so match that form
  have h_lhs : ((Exchangeability.prefixProj ℝ n ∘ shift) ∘ pathify X)
      = (fun ω i => X (k i) ω) := by
    funext ω i
    simp only [Function.comp_apply, Exchangeability.prefixProj, shift_apply, pathify, k]

  have h_rhs : (Exchangeability.prefixProj ℝ n ∘ pathify X)
      = (fun ω i => X i.val ω) := by
    funext ω i
    simp only [Function.comp_apply, Exchangeability.prefixProj, pathify]

  rw [h_lhs, h_rhs]

  -- Apply contractability: k is strictly monotone, so distributions match
  -- hX n k hk_strictMono : Measure.map (fun ω i => X (k i) ω) μ = Measure.map (fun ω i => X i.val ω) μ
  rw [hX n k hk_strictMono]

/-- Measurability of `shift` on path space. -/
lemma measurable_shift_real : Measurable (shift (α := ℝ)) :=
  shift_measurable

/-- **Bridge 1'.** Package the previous lemma as `MeasurePreserving` for MET. -/
lemma measurePreserving_shift_path {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX : Exchangeability.Contractable μ X)
    (hX_meas : ∀ n, Measurable (X n)) :
    MeasurePreserving (shift (α := ℝ)) (μ_path μ X) (μ_path μ X) := by
  refine ⟨measurable_shift_real, ?_⟩
  exact contractable_shift_invariant_law μ hX hX_meas

end Exchangeability.Bridge
