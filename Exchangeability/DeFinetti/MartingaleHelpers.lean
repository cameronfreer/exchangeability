/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Basic
import Mathlib.Data.Real.Basic

/-!
# Helper Lemmas for Martingale-based de Finetti Proof

This file contains technical helper lemmas extracted from `ViaMartingale.lean`.
These are general-purpose utilities for:
- Comap (pullback σ-algebra) operations
- Sequence shifting and manipulation
- Cylinder sets on tail coordinates
- Finset ordering and monotonicity

All lemmas are complete (no sorries) and have been validated for code quality.

## Main sections

* `ComapTools`: Comap σ-algebra utilities
* `SequenceShift`: Sequence shifting operations
* `TailCylinders`: Cylinder sets on tail coordinates
* `FinsetOrder`: Finset ordering and strict monotonicity lemmas
-/

noncomputable section
open scoped MeasureTheory

namespace Exchangeability
namespace DeFinetti
namespace MartingaleHelpers

open MeasureTheory

section ComapTools

/-- If `g` is measurable, then `comap (g ∘ f) ≤ comap f`. -/
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

lemma measurable_shiftSeq {d : ℕ} :
    Measurable (shiftSeq (β:=β) d) := by
  classical
  refine measurable_pi_iff.mpr fun n => ?_
  -- Evaluation at `n + d` is measurable in the product σ-algebra.
  simp only [shiftSeq]
  exact measurable_pi_apply (n + d)

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

section TailCylinders

variable {α : Type*} [MeasurableSpace α]

/-- Cylinder on the first `r` tail coordinates (shifted by one). -/
def tailCylinder (r : ℕ) (C : Fin r → Set α) : Set (ℕ → α) :=
  {f | ∀ i : Fin r, f (i.1 + 1) ∈ C i}

set_option linter.unusedSectionVars false in
/-- Basic measurability for tail cylinders. -/
lemma tailCylinder_measurable {r : ℕ} {C : Fin r → Set α}
    (hC : ∀ i, MeasurableSet (C i)) :
    MeasurableSet (tailCylinder (α:=α) r C) := by
  classical
  simp only [tailCylinder, Set.setOf_forall]
  exact MeasurableSet.iInter fun i => by
    have : (fun f : ℕ → α => f (i.val + 1)) ⁻¹' C i = {f | f (i.1 + 1) ∈ C i} := by
      ext f; simp [Set.mem_preimage]
    rw [← this]
    exact (hC i).preimage (measurable_pi_apply (i.val + 1))

end TailCylinders

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
        simpa [Fin.lt_iff_val_lt_val] using hij
      exact absurd this (Nat.not_lt.mpr (Nat.zero_le _))
    | succ j =>
      have hij' : i < j := (Fin.succ_lt_succ_iff).1 hij
      simpa using hf hij'

end FinsetOrder

section FutureCylinders

variable {α : Type*}

/-- Standard cylinder on the first `r` coordinates starting at index 0. -/
def cylinder (r : ℕ) (C : Fin r → Set α) : Set (ℕ → α) :=
  {f | ∀ i : Fin r, f i ∈ C i}

/-- Cylinder for functions with domain Fin r. -/
def finCylinder (r : ℕ) (C : Fin r → Set α) : Set (Fin r → α) :=
  {f | ∀ i : Fin r, f i ∈ C i}

variable [MeasurableSpace α]

lemma finCylinder_measurable {r : ℕ} {C : Fin r → Set α}
    (hC : ∀ i, MeasurableSet (C i)) :
    MeasurableSet (finCylinder r C) := by
  classical
  simp only [finCylinder, Set.setOf_forall]
  exact MeasurableSet.iInter fun i => by
    have : (fun f : Fin r → α => f i) ⁻¹' C i = {f | f i ∈ C i} := by
      ext f; simp [Set.mem_preimage]
    rw [← this]
    exact (hC i).preimage (measurable_pi_apply i)

lemma cylinder_measurable {r : ℕ} {C : Fin r → Set α}
    (hC : ∀ i, MeasurableSet (C i)) :
    MeasurableSet (cylinder (α:=α) r C) := by
  classical
  simp only [cylinder, Set.setOf_forall]
  exact MeasurableSet.iInter fun i => by
    have : (fun f : ℕ → α => f i.val) ⁻¹' C i = {f | f i ∈ C i} := by
      ext f; simp [Set.mem_preimage]
    rw [← this]
    exact (hC i).preimage (measurable_pi_apply i.val)

end FutureCylinders

section FirstBlockCylinder

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- The map collecting the first `r` coordinates. -/
def firstRMap (X : ℕ → Ω → α) (r : ℕ) : Ω → (Fin r → α) :=
  fun ω i => X i ω

/-- The σ‑algebra generated by the first `r` coordinates. -/
abbrev firstRSigma (X : ℕ → Ω → α) (r : ℕ) : MeasurableSpace Ω :=
  MeasurableSpace.comap (firstRMap X r) inferInstance

/-- The finite block cylinder event on the first `r` coordinates. -/
def firstRCylinder (X : ℕ → Ω → α) (r : ℕ) (C : Fin r → Set α) : Set Ω :=
  {ω | ∀ i : Fin r, X i ω ∈ C i}

omit [MeasurableSpace Ω] [MeasurableSpace α] in
/-- As expected, the block cylinder is the preimage of a finite cylinder
   under the `firstRMap`. -/
lemma firstRCylinder_eq_preimage_finCylinder
    (X : ℕ → Ω → α) (r : ℕ) (C : Fin r → Set α) :
    firstRCylinder X r C
      = (firstRMap X r) ⁻¹' (finCylinder (α:=α) r C) := rfl

omit [MeasurableSpace Ω] in
/-- **Measurable in the first-`r` σ‑algebra.**
If each `C i` is measurable in `α`, then the block cylinder is measurable in
`firstRSigma X r` (no measurability assumptions on the `X i` are needed for this
comap‑level statement). -/
lemma firstRCylinder_measurable_in_firstRSigma
    (X : ℕ → Ω → α) (r : ℕ) (C : Fin r → Set α)
    (hC : ∀ i, MeasurableSet (C i)) :
    MeasurableSet[firstRSigma X r] (firstRCylinder X r C) := by
  -- firstRSigma X r = comap (firstRMap X r)
  -- A set is measurable in the comap iff it's a preimage of a measurable set
  rw [firstRCylinder_eq_preimage_finCylinder]
  exact ⟨_, finCylinder_measurable hC, rfl⟩

/-- **Measurable in the ambient σ‑algebra.**
If each coordinate `X i` is measurable, then the block cylinder is measurable
in the ambient σ‑algebra (useful for `Integrable.indicator`). -/
lemma firstRCylinder_measurable_ambient
    (X : ℕ → Ω → α) (r : ℕ) (C : Fin r → Set α)
    (hX : ∀ i, Measurable (X i)) (hC : ∀ i, MeasurableSet (C i)) :
    MeasurableSet (firstRCylinder X r C) := by
  classical
  -- Directly as an intersection over `Fin r`.
  simp only [firstRCylinder, Set.setOf_forall]
  exact MeasurableSet.iInter fun i => (hX i) (hC i)

/-- The firstRMap is measurable when all coordinates are measurable. -/
lemma measurable_firstRMap
    (X : ℕ → Ω → α) (r : ℕ) (hX : ∀ i, Measurable (X i)) :
    Measurable (firstRMap X r) := by
  apply measurable_pi_lambda
  intro i
  exact hX i

/-- The first-r σ-algebra is a sub-σ-algebra of the ambient σ-algebra when coordinates are measurable. -/
lemma firstRSigma_le_ambient
    (X : ℕ → Ω → α) (r : ℕ) (hX : ∀ i, Measurable (X i)) :
    firstRSigma X r ≤ (inferInstance : MeasurableSpace Ω) := by
  simp only [firstRSigma]
  intro s hs
  obtain ⟨t, ht, rfl⟩ := hs
  exact (measurable_firstRMap X r hX) ht

omit [MeasurableSpace Ω] in
/-- Stronger version: firstRSigma increases with r. -/
lemma firstRSigma_mono
    (X : ℕ → Ω → α) {r s : ℕ} (hrs : r ≤ s) :
    firstRSigma X r ≤ firstRSigma X s := by
  -- Strategy: firstRMap X r factors through firstRMap X s via projection
  simp only [firstRSigma]
  intro t ht
  obtain ⟨u, hu, rfl⟩ := ht
  -- Define projection π : (Fin s → α) → (Fin r → α) taking first r coords
  let π : (Fin s → α) → (Fin r → α) := fun f i => f ⟨i.val, Nat.lt_of_lt_of_le i.isLt hrs⟩
  -- Show firstRMap X r = π ∘ firstRMap X s
  have h_comp : firstRMap X r = π ∘ firstRMap X s := by
    funext ω i
    simp [firstRMap, π]
  -- π is measurable (composition of coordinate projections)
  have hπ : Measurable π := by
    rw [measurable_pi_iff]
    intro i
    simp only [π]
    exact measurable_pi_apply _
  -- Preimage factors through composition
  rw [h_comp, Set.preimage_comp]
  exact ⟨π ⁻¹' u, hπ hu, rfl⟩

omit [MeasurableSpace Ω] [MeasurableSpace α] in
/-- The empty cylinder (r = 0) is the whole space. -/
@[simp]
lemma firstRCylinder_zero (X : ℕ → Ω → α) (C : Fin 0 → Set α) :
    firstRCylinder X 0 C = Set.univ := by
  ext ω
  simp [firstRCylinder]

omit [MeasurableSpace Ω] [MeasurableSpace α] in
/-- Cylinder membership characterization. -/
lemma mem_firstRCylinder_iff (X : ℕ → Ω → α) (r : ℕ) (C : Fin r → Set α) (ω : Ω) :
    ω ∈ firstRCylinder X r C ↔ ∀ i : Fin r, X i ω ∈ C i :=
  Iff.rfl

omit [MeasurableSpace Ω] [MeasurableSpace α] in
/-- firstRCylinder on universal sets is the whole space. -/
lemma firstRCylinder_univ (X : ℕ → Ω → α) (r : ℕ) :
    firstRCylinder X r (fun _ => Set.univ) = Set.univ := by
  ext ω; simp [firstRCylinder]

omit [MeasurableSpace Ω] [MeasurableSpace α] in
/-- Intersection of firstRCylinders equals coordinate-wise intersection. -/
lemma firstRCylinder_inter (X : ℕ → Ω → α) {r : ℕ} {C D : Fin r → Set α} :
    firstRCylinder X r C ∩ firstRCylinder X r D = firstRCylinder X r (fun i => C i ∩ D i) := by
  ext ω
  simp [firstRCylinder, Set.mem_inter_iff]
  constructor
  · intro ⟨hC, hD⟩ i
    exact ⟨hC i, hD i⟩
  · intro h
    exact ⟨fun i => (h i).1, fun i => (h i).2⟩

end FirstBlockCylinder

section IndicatorAlgebra

/-- The product of two indicator functions equals the indicator of their intersection. -/
lemma indicator_mul_indicator_eq_indicator_inter
    {Ω : Type*} [MeasurableSpace Ω]
    (A B : Set Ω) (c d : ℝ) :
    (A.indicator (fun _ => c)) * (B.indicator (fun _ => d))
      = (A ∩ B).indicator (fun _ => c * d) := by
  ext ω
  by_cases hA : ω ∈ A <;> by_cases hB : ω ∈ B <;>
    simp [Set.indicator, hA, hB, Set.mem_inter_iff]

/-- Indicator function composed with preimage. -/
lemma indicator_comp_preimage
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (f : Ω → α) (B : Set α) (c : ℝ) :
    (B.indicator (fun _ => c)) ∘ f = (f ⁻¹' B).indicator (fun _ => c) := by
  ext ω
  simp only [Function.comp_apply, Set.indicator, Set.mem_preimage]
  rfl

/-- Binary indicator takes values in {0, 1}. -/
lemma indicator_binary
    {Ω : Type*} [MeasurableSpace Ω]
    (A : Set Ω) (ω : Ω) :
    A.indicator (fun _ => (1 : ℝ)) ω = 0 ∨ A.indicator (fun _ => (1 : ℝ)) ω = 1 := by
  by_cases h : ω ∈ A
  · simp [Set.indicator, h]
  · simp [Set.indicator, h]

/-- Indicator is bounded by its constant. -/
lemma indicator_le_const
    {Ω : Type*} [MeasurableSpace Ω]
    (A : Set Ω) (c : ℝ) (hc : 0 ≤ c) (ω : Ω) :
    A.indicator (fun _ => c) ω ≤ c := by
  by_cases h : ω ∈ A
  · simp [Set.indicator, h]
  · simp [Set.indicator, h, hc]

/-- Indicator is nonnegative when constant is nonnegative. -/
lemma indicator_nonneg
    {Ω : Type*} [MeasurableSpace Ω]
    (A : Set Ω) (c : ℝ) (hc : 0 ≤ c) (ω : Ω) :
    0 ≤ A.indicator (fun _ => c) ω := by
  by_cases h : ω ∈ A
  · simp [Set.indicator, h, hc]
  · simp [Set.indicator, h]

end IndicatorAlgebra

section CylinderBridge

variable {α : Type*} [MeasurableSpace α]

/-- Drop the first coordinate of a path. -/
def drop (f : ℕ → α) : ℕ → α := shiftSeq (β:=α) 1 f

omit [MeasurableSpace α] in
@[simp] lemma drop_apply (f : ℕ → α) (n : ℕ) :
    drop f n = f (n + 1) := rfl

lemma measurable_drop : Measurable (drop : (ℕ → α) → (ℕ → α)) := by
  simpa [drop] using (measurable_shiftSeq (β:=α) (d:=1))

omit [MeasurableSpace α] in
/-- `tailCylinder` is the preimage of a standard cylinder under `drop`. -/
lemma tailCylinder_eq_preimage_cylinder
    {r : ℕ} {C : Fin r → Set α} :
    tailCylinder (α:=α) r C
      = (drop : (ℕ → α) → (ℕ → α)) ⁻¹' (cylinder (α:=α) r C) := by
  ext f
  constructor <;> intro hf
  · simpa [tailCylinder, drop, shiftSeq, cylinder]
  · simpa [tailCylinder, drop, shiftSeq, cylinder]

omit [MeasurableSpace α] in
@[simp] lemma mem_cylinder_iff {r : ℕ} {C : Fin r → Set α} {f : ℕ → α} :
    f ∈ cylinder (α:=α) r C ↔ ∀ i : Fin r, f i ∈ C i := Iff.rfl

omit [MeasurableSpace α] in
@[simp] lemma mem_tailCylinder_iff {r : ℕ} {C : Fin r → Set α} {f : ℕ → α} :
    f ∈ tailCylinder (α:=α) r C ↔ ∀ i : Fin r, f (i.1 + 1) ∈ C i := Iff.rfl

/-- The cylinder set is measurable when each component set is measurable. -/
lemma cylinder_measurable_set {r : ℕ} {C : Fin r → Set α}
    (hC : ∀ i, MeasurableSet (C i)) :
    MeasurableSet (cylinder (α:=α) r C) :=
  cylinder_measurable hC

omit [MeasurableSpace α] in
/-- Empty cylinder is the whole space. -/
@[simp] lemma cylinder_zero : cylinder (α:=α) 0 (fun _ => Set.univ) = Set.univ := by
  ext f; simp [cylinder]

omit [MeasurableSpace α] in
/-- Empty tail cylinder is the whole space. -/
@[simp] lemma tailCylinder_zero' : tailCylinder (α:=α) 0 (fun _ => Set.univ) = Set.univ := by
  ext f; simp [tailCylinder]

omit [MeasurableSpace α] in
/-- Cylinder on universal sets is the whole space. -/
lemma cylinder_univ {r : ℕ} : cylinder (α:=α) r (fun _ => Set.univ) = Set.univ := by
  ext f; simp [cylinder]

omit [MeasurableSpace α] in
/-- Tail cylinder on universal sets is the whole space. -/
lemma tailCylinder_univ {r : ℕ} : tailCylinder (α:=α) r (fun _ => Set.univ) = Set.univ := by
  ext f; simp [tailCylinder]

omit [MeasurableSpace α] in
/-- Cylinders form intersections coordinate-wise. -/
lemma cylinder_inter {r : ℕ} {C D : Fin r → Set α} :
    cylinder (α:=α) r C ∩ cylinder (α:=α) r D = cylinder (α:=α) r (fun i => C i ∩ D i) := by
  ext f
  simp [cylinder, Set.mem_inter_iff]
  constructor
  · intro ⟨hC, hD⟩ i
    exact ⟨hC i, hD i⟩
  · intro h
    exact ⟨fun i => (h i).1, fun i => (h i).2⟩

end CylinderBridge

end MartingaleHelpers
end DeFinetti
end Exchangeability
