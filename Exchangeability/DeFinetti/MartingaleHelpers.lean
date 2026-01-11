/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Basic
import Mathlib.Data.Real.Basic
import Exchangeability.PathSpace.CylinderHelpers

/-!
# Helper Lemmas for Martingale-based de Finetti Proof

This file contains technical helper lemmas extracted from `ViaMartingale.lean`.
These are general-purpose utilities for:
- Comap (pullback σ-algebra) operations
- Sequence shifting and manipulation
- Finset ordering and monotonicity
- Indicator algebra
- Re-exports from PathSpace.CylinderHelpers for backward compatibility

All lemmas are complete (no sorries) and have been validated for code quality.

## Main sections

* `ComapTools`: Comap σ-algebra utilities
* `SequenceShift`: Sequence shifting operations
* `FinsetOrder`: Finset ordering and strict monotonicity lemmas
* `IndicatorAlgebra`: Helper lemmas for indicator functions
* Re-exports from `PathSpace.CylinderHelpers` for compatibility
-/

noncomputable section
open scoped MeasureTheory

namespace Exchangeability
namespace DeFinetti
namespace MartingaleHelpers

-- Re-export cylinder infrastructure from PathSpace for backward compatibility
export PathSpace (tailCylinder tailCylinder_measurable cylinder finCylinder
  finCylinder_measurable cylinder_measurable firstRMap firstRSigma firstRCylinder
  firstRCylinder_eq_preimage_finCylinder firstRCylinder_measurable_in_firstRSigma
  firstRCylinder_measurable_ambient measurable_firstRMap firstRSigma_le_ambient
  firstRSigma_mono firstRCylinder_zero mem_firstRCylinder_iff firstRCylinder_univ
  firstRCylinder_inter drop drop_apply measurable_drop tailCylinder_eq_preimage_cylinder
  mem_cylinder_iff mem_tailCylinder_iff cylinder_measurable_set cylinder_zero
  tailCylinder_zero' cylinder_univ tailCylinder_univ cylinder_inter)

open MeasureTheory

section ComapTools

/-- If `g` is measurable, then `comap (g ∘ f) ≤ comap f`. -/
@[nolint unusedArguments]
lemma comap_comp_le
    {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    (f : X → Y) (g : Y → Z) (hg : Measurable g) :
    MeasurableSpace.comap (g ∘ f) (inferInstance : MeasurableSpace Z)
      ≤ MeasurableSpace.comap f (inferInstance : MeasurableSpace Y) := by
  intro s hs
  -- s is a set in the comap (g ∘ f) algebra, so s = (g ∘ f) ⁻¹' t for some t
  obtain ⟨t, ht, rfl⟩ := hs
  -- Show (g ∘ f) ⁻¹' t is in comap f
  refine ⟨g ⁻¹' t, hg ht, ?_⟩
  ext x
  simp [Set.mem_preimage, Function.comp_apply]

end ComapTools

section SequenceShift

variable {β : Type*} [MeasurableSpace β]

/-- Shift a sequence by dropping the first `d` entries. -/
def shiftSeq (d : ℕ) (f : ℕ → β) : ℕ → β := fun n => f (n + d)

omit [MeasurableSpace β] in
@[simp]
lemma shiftSeq_apply {d : ℕ} (f : ℕ → β) (n : ℕ) :
    shiftSeq d f n = f (n + d) := rfl

@[measurability]
lemma measurable_shiftSeq {d : ℕ} :
    Measurable (shiftSeq (β:=β) d) :=
  measurable_pi_lambda _ (fun n => measurable_pi_apply (n + d))

lemma forall_mem_erase {γ : Type*} [DecidableEq γ]
    {s : Finset γ} {a : γ} {P : γ → Prop} (ha : a ∈ s) :
    (∀ x ∈ s, P x) ↔ P a ∧ ∀ x ∈ s.erase a, P x := by
  constructor
  · intro h
    refine ⟨h _ ha, ?_⟩
    intro x hx
    exact h _ (Finset.mem_of_mem_erase hx)
  · rintro ⟨haP, hrest⟩ x hx
    by_cases hxa : x = a
    · simpa [hxa] using haP
    · have hx' : x ∈ s.erase a := by
        exact Finset.mem_erase.mpr ⟨hxa, hx⟩
      exact hrest _ hx'

end SequenceShift

section FinsetOrder

open Finset

lemma orderEmbOfFin_strictMono {s : Finset ℕ} :
    StrictMono fun i : Fin s.card => s.orderEmbOfFin rfl i := by
  classical
  simpa using (s.orderEmbOfFin rfl).strictMono

lemma orderEmbOfFin_mem {s : Finset ℕ} {i : Fin s.card} :
    s.orderEmbOfFin rfl i ∈ s := by
  classical
  simp [Finset.orderEmbOfFin_mem (s:=s) (h:=rfl) i]

lemma orderEmbOfFin_surj {s : Finset ℕ} {x : ℕ} (hx : x ∈ s) :
    ∃ i : Fin s.card, s.orderEmbOfFin rfl i = x := by
  classical
  -- orderEmbOfFin is an order isomorphism, hence bijective onto s
  -- Use the fact that it's an injective function from a finite type to itself
  have h_inj : Function.Injective (s.orderEmbOfFin rfl : Fin s.card → ℕ) :=
    (s.orderEmbOfFin rfl).injective
  have h_range_sub : ∀ i, s.orderEmbOfFin rfl i ∈ s := fun i => s.orderEmbOfFin_mem rfl i
  -- Define a function to s viewed as a subtype
  let f : Fin s.card → s := fun i => ⟨s.orderEmbOfFin rfl i, h_range_sub i⟩
  have hf_inj : Function.Injective f := by
    intro i j hij
    exact h_inj (Subtype.ext_iff.mp hij)
  -- Injective function between finite types of equal cardinality is surjective
  haveI : Fintype s := Finset.fintypeCoeSort s
  have hcard : Fintype.card (Fin s.card) = Fintype.card s := by simp
  have hf_bij : Function.Bijective f := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨hf_inj, hcard⟩
  have hf_surj : Function.Surjective f := hf_bij.2
  obtain ⟨i, hi⟩ := hf_surj ⟨x, hx⟩
  use i
  exact Subtype.ext_iff.mp hi

/-- If `f : Fin n → ℕ` is strictly monotone and `a < f i` for all `i`,
then `Fin.cases a f : Fin (n+1) → ℕ` is strictly monotone. -/
lemma strictMono_fin_cases
    {n : ℕ} {f : Fin n → ℕ} (hf : StrictMono f) {a : ℕ}
    (ha : ∀ i, a < f i) :
    StrictMono (Fin.cases a (fun i => f i)) := by
  intro i j hij
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases with
    | zero => exact absurd hij (lt_irrefl _)
    | succ j => simpa using ha j
  | succ i =>
    cases j using Fin.cases with
    | zero =>
      have : (Fin.succ i : Fin (n + 1)).1 < 0 := by
        set_option linter.unnecessarySimpa false in
        simpa [Fin.lt_def] using hij
      exact absurd this (Nat.not_lt.mpr (Nat.zero_le _))
    | succ j =>
      have hij' : i < j := (Fin.succ_lt_succ_iff).1 hij
      simpa using hf hij'

end FinsetOrder

section IndicatorAlgebra

/-- The product of two indicator functions equals the indicator of their intersection. -/
@[nolint unusedArguments]
lemma indicator_mul_indicator_eq_indicator_inter
    {Ω : Type*} [MeasurableSpace Ω]
    (A B : Set Ω) (c d : ℝ) :
    (A.indicator (fun _ => c)) * (B.indicator (fun _ => d))
      = (A ∩ B).indicator (fun _ => c * d) := by
  ext ω
  by_cases hA : ω ∈ A <;> by_cases hB : ω ∈ B <;>
    simp [Set.indicator, hA, hB, Set.mem_inter_iff]

/-- Indicator function composed with preimage. -/
@[nolint unusedArguments]
lemma indicator_comp_preimage
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (f : Ω → α) (B : Set α) (c : ℝ) :
    (B.indicator (fun _ => c)) ∘ f = (f ⁻¹' B).indicator (fun _ => c) := by
  ext ω
  simp only [Function.comp_apply, Set.indicator, Set.mem_preimage]
  rfl

/-- Binary indicator takes values in {0, 1}. -/
@[nolint unusedArguments]
lemma indicator_binary
    {Ω : Type*} [MeasurableSpace Ω]
    (A : Set Ω) (ω : Ω) :
    A.indicator (fun _ => (1 : ℝ)) ω = 0 ∨ A.indicator (fun _ => (1 : ℝ)) ω = 1 := by
  by_cases h : ω ∈ A
  · simp [Set.indicator, h]
  · simp [Set.indicator, h]

/-- Indicator is bounded by its constant. -/
@[nolint unusedArguments]
lemma indicator_le_const
    {Ω : Type*} [MeasurableSpace Ω]
    (A : Set Ω) (c : ℝ) (hc : 0 ≤ c) (ω : Ω) :
    A.indicator (fun _ => c) ω ≤ c := by
  by_cases h : ω ∈ A
  · simp [Set.indicator, h]
  · simp [Set.indicator, h, hc]

/-- Indicator is nonnegative when constant is nonnegative. -/
@[nolint unusedArguments]
lemma indicator_nonneg
    {Ω : Type*} [MeasurableSpace Ω]
    (A : Set Ω) (c : ℝ) (hc : 0 ≤ c) (ω : Ω) :
    0 ≤ A.indicator (fun _ => c) ω := by
  by_cases h : ω ∈ A
  · simp [Set.indicator, h, hc]
  · simp [Set.indicator, h]

end IndicatorAlgebra

end MartingaleHelpers
end DeFinetti
end Exchangeability
