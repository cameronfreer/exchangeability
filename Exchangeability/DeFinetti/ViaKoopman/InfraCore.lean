/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.SimpleFuncDense
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.Independence.Kernel.IndepFun
import Exchangeability.Ergodic.KoopmanMeanErgodic
import Exchangeability.Ergodic.InvariantSigma
import Exchangeability.Ergodic.ProjectionLemmas
import Exchangeability.Ergodic.BirkhoffAvgCLM
import Exchangeability.DeFinetti.CommonEnding
import Exchangeability.DeFinetti.MartingaleHelpers
import Exchangeability.ConditionallyIID
import Exchangeability.Probability.CondExp
import Exchangeability.PathSpace.Shift
import Exchangeability.Core
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp

open Filter MeasureTheory

/-! # Core Infrastructure for ViaKoopman Proof

This file contains foundational infrastructure for the Koopman-based de Finetti proof:
- Reusable micro-lemmas
- Lp coercion lemmas
- Two-sided natural extension infrastructure (Ωℤ, shiftℤ)
- NaturalExtensionData structure
- Helper lemmas for shift operations
- Instance-locking shims for conditional expectation

All lemmas in this file are proved (no sorries).

**Extracted from**: Infrastructure.lean (Part 1/3)
**Status**: Complete (no sorries in proofs)
-/

noncomputable section

/-! ### API compatibility aliases -/

-- NOTE: The original condIndep_of_indep_pair alias has been removed because:
-- 1. It had type errors (wrong argument order for mathlib's CondIndep)
-- 2. It was unused in this file
-- 3. The local project already has Exchangeability.Probability.CondIndep.condIndep_of_indep_pair
--    which serves a similar purpose with a different signature

/-! ### Lp coercion lemmas for measure spaces -/

/-- Coercion of finite sums in Lp is almost everywhere equal to pointwise sums.
    This is the measure-space analogue of lp.coeFn_sum (which is for sequence spaces). -/
@[nolint unusedArguments]
lemma coeFn_finset_sum
  {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {p : ENNReal} {ι : Type*} (s : Finset ι) (F : ι → Lp E p μ) :
  ((s.sum F : Lp E p μ) : Ω → E) =ᵐ[μ] fun ω => s.sum (fun i => (F i : Ω → E) ω) := by
  haveI : DecidableEq ι := Classical.decEq _
  refine Finset.induction_on s ?h0 ?hstep
  · -- base: sum over ∅ is 0
    simp only [Finset.sum_empty]
    filter_upwards [Lp.coeFn_zero (E := E) (p := p) (μ := μ)] with ω hω
    rw [hω]
    rfl
  · -- step: sum over insert
    intro a s ha hs
    simp only [Finset.sum_insert ha]
    -- Combine coeFn_add with induction hypothesis
    filter_upwards [Lp.coeFn_add (F a) (s.sum F), hs] with ω h_add h_ih
    simp only [Pi.add_apply] at h_add
    rw [h_add, h_ih]

namespace Exchangeability.DeFinetti.ViaKoopman

open MeasureTheory Filter Topology ProbabilityTheory
open Exchangeability.Ergodic
open Exchangeability.PathSpace
open scoped BigOperators RealInnerProductSpace

variable {α : Type*} [MeasurableSpace α]

-- Short notation for shift-invariant σ-algebra (used throughout this file)
local notation "mSI" => shiftInvariantSigma (α := α)

/-! ## Two-sided natural extension infrastructure -/

/-- Bi-infinite path space indexed by `ℤ`. -/
abbrev Ωℤ (α : Type*) := ℤ → α

/-- Notation for bi-infinite path space `ℤ → α`. -/
notation "Ωℤ[" α "]" => Ωℤ α

/-- The two-sided shift on bi-infinite sequences. -/
def shiftℤ (ω : Ωℤ[α]) : Ωℤ[α] := fun n => ω (n + 1)

omit [MeasurableSpace α] in
@[simp] lemma shiftℤ_apply (ω : Ωℤ[α]) (n : ℤ) :
    shiftℤ (α := α) ω n = ω (n + 1) := rfl

/-- The inverse shift on bi-infinite sequences. -/
def shiftℤInv (ω : Ωℤ[α]) : Ωℤ[α] := fun n => ω (n - 1)

omit [MeasurableSpace α] in
@[simp] lemma shiftℤInv_apply (ω : Ωℤ[α]) (n : ℤ) :
    shiftℤInv (α := α) ω n = ω (n - 1) := rfl

omit [MeasurableSpace α] in
@[simp] lemma shiftℤ_comp_shiftℤInv (ω : Ωℤ[α]) :
    shiftℤ (α := α) (shiftℤInv (α := α) ω) = ω := by ext; simp [shiftℤ, shiftℤInv]

omit [MeasurableSpace α] in
@[simp] lemma shiftℤInv_comp_shiftℤ (ω : Ωℤ[α]) :
    shiftℤInv (α := α) (shiftℤ (α := α) ω) = ω := by ext; simp [shiftℤ, shiftℤInv]

/-- Restrict a bi-infinite path to its nonnegative coordinates. -/
def restrictNonneg (ω : Ωℤ[α]) : Ω[α] := fun n => ω (Int.ofNat n)

omit [MeasurableSpace α] in
@[simp] lemma restrictNonneg_apply (ω : Ωℤ[α]) (n : ℕ) :
    restrictNonneg (α := α) ω n = ω (Int.ofNat n) := rfl

/-- Extend a one-sided path to the bi-infinite path space by duplicating the zeroth
coordinate on the negative side. This is a convenient placeholder when we only need
the right-infinite coordinates. -/
def extendByZero (ω : Ω[α]) : Ωℤ[α] :=
  fun
  | Int.ofNat n => ω n
  | Int.negSucc _ => ω 0

omit [MeasurableSpace α] in
@[simp] lemma restrictNonneg_extendByZero (ω : Ω[α]) :
    restrictNonneg (α := α) (extendByZero (α := α) ω) = ω := by ext; simp [extendByZero]

omit [MeasurableSpace α] in
@[simp] lemma extendByZero_apply_nat (ω : Ω[α]) (n : ℕ) :
    extendByZero (α := α) ω ↑n = ω n := by simp [extendByZero]

omit [MeasurableSpace α] in
lemma restrictNonneg_shiftℤ (ω : Ωℤ[α]) :
    restrictNonneg (α := α) (shiftℤ (α := α) ω)
      = shift (restrictNonneg (α := α) ω) := by ext; simp [restrictNonneg, shiftℤ, shift]

omit [MeasurableSpace α] in
lemma restrictNonneg_shiftℤInv (ω : Ωℤ[α]) :
    restrictNonneg (α := α) (shiftℤInv (α := α) ω)
      = fun n => ω (Int.ofNat n - 1) := by ext; simp [restrictNonneg, shiftℤInv]

@[measurability, fun_prop]
lemma measurable_shiftℤ : Measurable (shiftℤ (α := α)) := by
  unfold shiftℤ; fun_prop

@[measurability, fun_prop]
lemma measurable_shiftℤInv : Measurable (shiftℤInv (α := α)) := by
  unfold shiftℤInv; fun_prop

/-- Two-sided shift-invariant sets. A set is shift-invariant if it is measurable and equals its preimage under the shift. -/
def IsShiftInvariantℤ (S : Set (Ωℤ[α])) : Prop :=
  MeasurableSet S ∧ shiftℤ (α := α) ⁻¹' S = S

lemma isShiftInvariantℤ_iff (S : Set (Ωℤ[α])) :
    IsShiftInvariantℤ (α := α) S ↔
      MeasurableSet S ∧ ∀ ω, shiftℤ (α := α) ω ∈ S ↔ ω ∈ S := by
  constructor
  · intro ⟨hm, heq⟩
    exact ⟨hm, fun ω => by rw [← Set.mem_preimage, heq]⟩
  · intro ⟨hm, hiff⟩
    refine ⟨hm, Set.ext fun ω => ?_⟩
    simp only [Set.mem_preimage]
    exact hiff ω

/-- Shift-invariant σ-algebra on the two-sided path space.

This is defined directly as the sub-σ-algebra of measurable shift-invariant sets.
-/
def shiftInvariantSigmaℤ : MeasurableSpace (Ωℤ[α]) where
  MeasurableSet' := fun s => IsShiftInvariantℤ (α := α) s
  measurableSet_empty := by
    refine ⟨MeasurableSet.empty, ?_⟩
    simp
  measurableSet_compl := by
    intro s hs
    obtain ⟨hs_meas, hs_eq⟩ := hs
    refine ⟨hs_meas.compl, ?_⟩
    simp [Set.preimage_compl, hs_eq]
  measurableSet_iUnion := by
    intro f hf
    refine ⟨MeasurableSet.iUnion fun n => (hf n).1, ?_⟩
    simp only [Set.preimage_iUnion]
    ext ω
    simp only [Set.mem_iUnion, Set.mem_preimage]
    constructor
    · intro ⟨i, hi⟩
      use i
      -- hi : shiftℤ ω ∈ f i
      -- By (hf i), f i is shift-invariant: shiftℤ ω ∈ f i ↔ ω ∈ f i
      have := isShiftInvariantℤ_iff (f i)
      exact (this.1 (hf i)).2 ω |>.1 hi
    · intro ⟨i, hi⟩
      use i
      -- hi : ω ∈ f i
      -- By (hf i), f i is shift-invariant: shiftℤ ω ∈ f i ↔ ω ∈ f i
      have := isShiftInvariantℤ_iff (f i)
      exact (this.1 (hf i)).2 ω |>.2 hi

/-- The shift-invariant σ-algebra is a sub-σ-algebra of the product σ-algebra. -/
lemma shiftInvariantSigmaℤ_le :
    shiftInvariantSigmaℤ (α := α) ≤ (inferInstance : MeasurableSpace (Ωℤ[α])) := by
  intro s hs
  exact hs.1

/-- Data describing the natural two-sided extension of a one-sided stationary process. -/
structure NaturalExtensionData (μ : Measure (Ω[α])) where
  /-- The two-sided extension measure on bi-infinite path space. -/
  μhat : Measure (Ωℤ[α])
  μhat_isProb : IsProbabilityMeasure μhat
  shift_preserving : MeasurePreserving (shiftℤ (α := α)) μhat μhat
  shiftInv_preserving : MeasurePreserving (shiftℤInv (α := α)) μhat μhat
  restrict_pushforward :
    Measure.map (restrictNonneg (α := α)) μhat = μ

attribute [instance] NaturalExtensionData.μhat_isProb

/-! ## General infrastructure lemmas for factor maps and invariance -/

section Helpers
variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
variable {μ : Measure Ω} {μ' : Measure Ω'} {g : Ω' → Ω}

/-- Construct MeasurePreserving from a pushforward equality.
This is a simple wrapper but avoids repeating the `by simp [hpush]` pattern. -/
private lemma measurePreserving_of_map_eq
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} {μ' : Measure Ω'} {g : Ω' → Ω}
    (hg : Measurable g) (hpush : Measure.map g μ' = μ) :
    MeasurePreserving g μ' μ :=
  ⟨hg, by simp [hpush]⟩

/-- Push AE along a factor map using only null sets and a measurable null *superset*. -/
lemma ae_comp_of_pushforward
    (hg : Measurable g) (hpush : Measure.map g μ' = μ)
    {P : Ω → Prop} :
    (∀ᶠ x in ae μ, P x) → (∀ᶠ x' in ae μ', P (g x')) := by
  classical
  intro h
  -- Turn AE into a measurable null *superset*
  have h0 : μ {x | ¬ P x} = 0 := (ae_iff).1 h
  obtain ⟨T, hsubset, hTmeas, hTzero⟩ :=
    exists_measurable_superset_of_null (s := {x | ¬ P x}) h0
  -- Push the measurable null set through the factor map
  have : μ' (g ⁻¹' T) = 0 := by
    -- `map g μ' = μ` gives the preimage formula on measurable sets
    have hmp : MeasurePreserving g μ' μ := measurePreserving_of_map_eq hg hpush
    rw [hmp.measure_preimage hTmeas.nullMeasurableSet]
    exact hTzero
  -- Conclude AE via `measure_mono_null`
  refine (ae_iff).2 ?_
  -- `{x' | ¬ P (g x') } ⊆ g ⁻¹' T`
  have hsub : {x' | ¬ P (g x')} ⊆ g ⁻¹' T := by
    intro x' hx'
    have : g x' ∈ {x | ¬ P x} := by simpa
    exact hsubset this
  exact measure_mono_null hsub this

end Helpers

/-- Transport integrability across a pushforward equality and then pull back by composition.
This avoids instance gymnastics by rewriting the measure explicitly, then using `comp_measurable`. -/
lemma integrable_comp_of_pushforward
    {Ω Ω' : Type*} [mΩ : MeasurableSpace Ω] [mΩ' : MeasurableSpace Ω']
    {μ : Measure Ω} {μ' : Measure Ω'} {g : Ω' → Ω} {H : Ω → ℝ}
    (hg : Measurable g) (hpush : Measure.map g μ' = μ)
    (hH : Integrable H μ) :
    Integrable (H ∘ g) μ' := by
  -- first, switch μ to (Measure.map g μ') using the equality
  have hH_map : Integrable H (Measure.map g μ') := by
    simpa [hpush] using hH
  -- then pull integrability back along g
  simpa [Function.comp] using hH_map.comp_measurable hg

/-! ### Instance-locking shims for conditional expectation

These wrappers lock the ambient measurable space instance to prevent Lean from synthesizing
the sub-σ-algebra as the ambient instance in type class arguments. -/

namespace MeasureTheory

/-- The defining property of conditional expectation on `m`-measurable sets, with ambient locked. -/
lemma setIntegral_condExp'
    {Ω} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ) [SigmaFinite (μ.trim hm)]
    {s : Set Ω} (hs : MeasurableSet[m] s)
    {f : Ω → ℝ} (hf : Integrable f μ) :
    ∫ x in s, condExp m μ f x ∂μ = ∫ x in s, f x ∂μ :=
  setIntegral_condExp hm hf hs

/-- Set integral change of variables for pushforward measures.

If `g : Ω' → Ω` pushes forward `μ'` to `μ`, then integrating `f ∘ g` over `g ⁻¹' s`
equals integrating `f` over `s`.

**Note:** we require `AEMeasurable f μ` and derive `AEMeasurable f (Measure.map g μ')` by rewriting with `hpush`. -/
lemma setIntegral_map_preimage
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} {μ' : Measure Ω'}
    (g : Ω' → Ω) (hg : Measurable g) (hpush : Measure.map g μ' = μ)
    (f : Ω → ℝ) (s : Set Ω) (hs : MeasurableSet s)
    (hf : AEMeasurable f μ) :
    ∫ x in g ⁻¹' s, (f ∘ g) x ∂ μ' = ∫ x in s, f x ∂ μ := by
  -- Use setIntegral_map which requires AEStronglyMeasurable
  -- For ℝ, AEMeasurable implies AEStronglyMeasurable (second countable topology)
  have hf_aesm : AEStronglyMeasurable f (Measure.map g μ') := by
    rw [← hpush] at hf
    exact hf.aestronglyMeasurable
  have hg_ae : AEMeasurable g μ' := hg.aemeasurable
  simp only [Function.comp]
  rw [← setIntegral_map hs hf_aesm hg_ae, hpush]

/-- On a finite measure space, an a.e.-bounded, a.e.-measurable real function is integrable. -/
lemma integrable_of_ae_bound
    {Ω} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {f : Ω → ℝ}
    (hf : AEMeasurable f μ)
    (hbd : ∃ C : ℝ, ∀ᵐ x ∂μ, |f x| ≤ C) :
    Integrable f μ := by
  classical
  rcases hbd with ⟨C, hC⟩
  -- bound the `lintegral` of `|f|`
  have hC' : (fun x => ENNReal.ofReal |f x|) ≤ᵐ[μ] (fun _ => ENNReal.ofReal C) := by
    filter_upwards [hC] with x hx
    exact ENNReal.ofReal_le_ofReal hx
  have hlin :
      ∫⁻ x, ENNReal.ofReal |f x| ∂μ ≤ ENNReal.ofReal C * μ Set.univ := by
    simpa [lintegral_const, measure_univ] using lintegral_mono_ae hC'
  constructor
  · exact hf.aestronglyMeasurable
  · have : ENNReal.ofReal C * μ Set.univ < ⊤ := by
      have hμ : μ Set.univ < ⊤ := measure_lt_top μ Set.univ
      refine ENNReal.mul_lt_top ?_ hμ
      simp
    calc ∫⁻ x, ‖f x‖₊ ∂μ
        = ∫⁻ x, ENNReal.ofReal |f x| ∂μ := by
            congr 1 with x
            rw [← Real.enorm_eq_ofReal_abs]
            rfl
      _ ≤ ENNReal.ofReal C * μ Set.univ := hlin
      _ < ⊤ := this

-- Helper lemmas for rectangle-case conditional expectation proofs

end MeasureTheory

end Exchangeability.DeFinetti.ViaKoopman
