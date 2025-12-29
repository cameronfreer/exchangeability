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
import Mathlib.Probability.Independence.Kernel
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

/-! # Infrastructure for ViaKoopman Proof

This file contains completed infrastructure for the Koopman-based de Finetti proof:
- Reusable micro-lemmas
- Lp coercion lemmas
- Two-sided natural extension infrastructure
- Helper lemmas for shift operations
- Instance-locking shims for conditional expectation
- Conditional expectation pullback lemmas

All lemmas in this file are proved (no sorries) except for axiomatized results
marked as `axiom` with mathematical justification.

**Extracted from**: ViaKoopman.lean (Section 1: Infrastructure)
**Status**: ✅ COMPLETE (no sorries in proofs)
-/

noncomputable section

/-! ### API compatibility aliases -/

-- NOTE: The original condIndep_of_indep_pair alias has been removed because:
-- 1. It had type errors (wrong argument order for mathlib's CondIndep)
-- 2. It was unused in this file
-- 3. The local project already has Exchangeability.Probability.CondIndep.condIndep_of_indep_pair
--    which serves a similar purpose with a different signature

/-! ### Reusable micro-lemmas for Steps 4b–4c -/

/-- `ae_ball_iff` in the direction we need on a finite index set (`Finset.range n`). -/
lemma ae_ball_range_mpr
  {Ω : Type _} [MeasurableSpace Ω] (μ : Measure Ω) {n : ℕ}
  {P : ℕ → Ω → Prop}
  (h : ∀ k ∈ Finset.range n, ∀ᵐ ω ∂ μ, P k ω) :
  ∀ᵐ ω ∂ μ, ∀ k ∈ Finset.range n, P k ω := by
  have hcount : (Finset.range n : Set ℕ).Countable := Finset.countable_toSet _
  simpa using (MeasureTheory.ae_ball_iff hcount).mpr h

/-- Handy arithmetic fact repeatedly needed: split `k ≤ n` into cases. -/
private lemma le_eq_or_lt {k n : ℕ} (hk : k ≤ n) : k = n ∨ k < n :=
  eq_or_lt_of_le hk

/-- Pull absolute value through division when denominator is nonnegative. -/
private lemma abs_div_of_nonneg {x y : ℝ} (hy : 0 ≤ y) :
  |x / y| = |x| / y := by simpa [abs_div, abs_of_nonneg hy]

/-! ### Lp coercion lemmas for measure spaces -/

/-- Coercion of finite sums in Lp is almost everywhere equal to pointwise sums.
    This is the measure-space analogue of lp.coeFn_sum (which is for sequence spaces). -/
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
open Exchangeability.DeFinetti.MartingaleHelpers (comap_comp_le)
open scoped BigOperators RealInnerProductSpace

variable {α : Type*} [MeasurableSpace α]

-- Short notation for shift-invariant σ-algebra (used throughout this file)
local notation "mSI" => shiftInvariantSigma (α := α)

/-! ## Two-sided natural extension infrastructure -/

/-- Bi-infinite path space indexed by `ℤ`. -/
abbrev Ωℤ (α : Type*) := ℤ → α

notation "Ωℤ[" α "]" => Ωℤ α

/-- The two-sided shift on bi-infinite sequences. -/
def shiftℤ (ω : Ωℤ[α]) : Ωℤ[α] := fun n => ω (n + 1)

@[simp] lemma shiftℤ_apply (ω : Ωℤ[α]) (n : ℤ) :
    shiftℤ (α := α) ω n = ω (n + 1) := rfl

/-- The inverse shift on bi-infinite sequences. -/
def shiftℤInv (ω : Ωℤ[α]) : Ωℤ[α] := fun n => ω (n - 1)

@[simp] lemma shiftℤInv_apply (ω : Ωℤ[α]) (n : ℤ) :
    shiftℤInv (α := α) ω n = ω (n - 1) := rfl

@[simp] lemma shiftℤ_comp_shiftℤInv (ω : Ωℤ[α]) :
    shiftℤ (α := α) (shiftℤInv (α := α) ω) = ω := by
  funext n
  simp [shiftℤ, shiftℤInv, add_comm, add_left_comm, add_assoc]

@[simp] lemma shiftℤInv_comp_shiftℤ (ω : Ωℤ[α]) :
    shiftℤInv (α := α) (shiftℤ (α := α) ω) = ω := by
  funext n
  simp [shiftℤ, shiftℤInv, add_comm, add_left_comm, add_assoc]

/-- Restrict a bi-infinite path to its nonnegative coordinates. -/
def restrictNonneg (ω : Ωℤ[α]) : Ω[α] := fun n => ω (Int.ofNat n)

@[simp] lemma restrictNonneg_apply (ω : Ωℤ[α]) (n : ℕ) :
    restrictNonneg (α := α) ω n = ω (Int.ofNat n) := rfl

/-- Extend a one-sided path to the bi-infinite path space by duplicating the zeroth
coordinate on the negative side. This is a convenient placeholder when we only need
the right-infinite coordinates. -/
def extendByZero (ω : Ω[α]) : Ωℤ[α] :=
  fun
  | Int.ofNat n => ω n
  | Int.negSucc _ => ω 0

@[simp] lemma restrictNonneg_extendByZero (ω : Ω[α]) :
    restrictNonneg (α := α) (extendByZero (α := α) ω) = ω := by
  funext n
  simp [extendByZero]

@[simp] lemma extendByZero_apply_nat (ω : Ω[α]) (n : ℕ) :
    extendByZero (α := α) ω (Int.ofNat n) = ω n := by
  simp [extendByZero]

lemma restrictNonneg_shiftℤ (ω : Ωℤ[α]) :
    restrictNonneg (α := α) (shiftℤ (α := α) ω)
      = shift (restrictNonneg (α := α) ω) := by
  funext n
  simp [restrictNonneg, shiftℤ, shift]

lemma restrictNonneg_shiftℤInv (ω : Ωℤ[α]) :
    restrictNonneg (α := α) (shiftℤInv (α := α) ω)
      = fun n => ω (Int.ofNat n - 1) := by
  funext n
  simp [restrictNonneg, shiftℤInv]

@[measurability, fun_prop]
lemma measurable_restrictNonneg : Measurable (restrictNonneg (α := α)) := by
  apply measurable_pi_lambda
  intro n
  simp only [restrictNonneg]
  exact measurable_pi_apply (Int.ofNat n)

@[measurability, fun_prop]
lemma measurable_shiftℤ : Measurable (shiftℤ (α := α)) := by
  measurability

@[measurability, fun_prop]
lemma measurable_shiftℤInv : Measurable (shiftℤInv (α := α)) := by
  measurability

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

/-- Indicator pulls through a preimage under composition. -/
lemma indicator_preimage_comp {B : Set Ω} (K : Ω → ℝ) :
    (Set.indicator (g ⁻¹' B) (K ∘ g))
  = (fun x' => Set.indicator B K (g x')) := by
  classical
  funext x'
  by_cases hx : g x' ∈ B
  · simp [Set.indicator, hx]
  · simp [Set.indicator, hx]

end Helpers

/-! ## Infrastructure Lemmas for Conditional Expectation Pullback

This section contains three infrastructure lemmas needed for the Koopman approach to de Finetti's
theorem. These lemmas handle the interaction between conditional expectation, factor maps, and
measure-preserving transformations.

### Current Status (as of 2025-10-18)

**Structurally Complete**: All three lemmas have complete proof structures using the indicator trick.

**Remaining Issues**: 22 type class synthesis errors in later parts of the calc chains.
- Error reduction: 66 → 22 (67% improvement)
- Core binder order issue fixed by naming ambient instance `inst` and moving `m` parameter after it
- Main blocker: Remaining cascade errors from type class synthesis in `mpOfPushforward` applications

### Key Technical Details

**The Indicator Trick**:
- Converts set integrals `∫ x in s, f x ∂μ` to whole-space integrals `∫ x, (indicator s f) x ∂μ`
- Avoids measure composition `Measure.restrict` which has type class defeq issues
- Uses `MeasureTheory.integral_indicator` for the conversion

**Type Class Management** (CRITICAL):
- `m : MeasurableSpace Ω` is a plain parameter, NEVER installed as an instance
- Ambient instance explicitly named: `[inst : MeasurableSpace Ω]`
- Binder order matters: `m` must come AFTER all instance parameters
- Measurability lift: `have hBm' : @MeasurableSet Ω inst B := hm B hBm`

**Helper Function**:
- `mpOfPushforward`: Builds `MeasurePreserving g μ' μ` from pushforward equality
- Ensures ambient instances are used (not the sub-σ-algebra `m`)

### Next Steps for Debugging

1. Check remaining `mpOfPushforward` applications for type class issues
2. Verify `setIntegral_condExp` is using correct instances
3. Check if `integrable_map_measure` needs similar binder treatment
4. Consider if `ae_eq_condExp_of_forall_setIntegral_eq` needs instance annotations

### Mathematical Content

1. `ae_pullback_iff`: AE equalities transport through factor maps
2. `condexp_pullback_factor`: CE pullback along factor maps (main workhorse)
3. `condexp_precomp_iterate_eq_of_invariant`: CE invariance under measure-preserving iterates

All three use the same indicator trick strategy for change of variables.
-/

/-- Build a `MeasurePreserving` from a pushforward equality.
This helper ensures the ambient MeasurableSpace instances are used. -/
private def mpOfPushforward
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} {μ' : Measure Ω'}
    (g : Ω' → Ω) (hg : Measurable g) (hpush : Measure.map g μ' = μ) :
    MeasurePreserving g μ' μ :=
  ⟨hg, hpush⟩

/-- **AE-pullback along a factor map**: Almost-everywhere equalities transport along pushforward.

If `g : Ω̂ → Ω` is a factor map (i.e., `map g μ̂ = μ`), then two functions are
a.e.-equal on `Ω` iff their pullbacks are a.e.-equal on `Ω̂`.

**Note**: For our use case with `restrictNonneg : Ωℤ[α] → Ω[α]`, the forward direction
(which is what we primarily need) works and the map is essentially surjective onto
a set of full measure. -/
lemma ae_pullback_iff
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} {μ' : Measure Ω'}
    (g : Ω' → Ω) (hg : Measurable g) (hpush : Measure.map g μ' = μ)
    {F G : Ω → ℝ} (hF : AEMeasurable F μ) (hG : AEMeasurable G μ) :
    F =ᵐ[μ] G ↔ (F ∘ g) =ᵐ[μ'] (G ∘ g) := by
  classical
  -- Replace by measurable modifications so the {≠}-sets are measurable.
  let Fm := hF.mk F
  let Gm := hG.mk G
  have hF_eq : F =ᵐ[μ] Fm := hF.ae_eq_mk
  have hG_eq : G =ᵐ[μ] Gm := hG.ae_eq_mk
  have hFm_meas : Measurable Fm := hF.measurable_mk
  have hGm_meas : Measurable Gm := hG.measurable_mk

  -- Reduce both directions to the measurable representatives.
  have h_left :
      (F =ᵐ[μ] G) ↔ (Fm =ᵐ[μ] Gm) := by
    constructor
    · intro h; exact hF_eq.symm.trans (h.trans hG_eq)
    · intro h; exact hF_eq.trans (h.trans hG_eq.symm)

  have h_right :
      (F ∘ g =ᵐ[μ'] G ∘ g) ↔ (Fm ∘ g =ᵐ[μ'] Gm ∘ g) := by
    constructor
    · intro h
      -- strengthen both sides using AE equivalence pushed along g
      have hF' : (F ∘ g) =ᵐ[μ'] (Fm ∘ g) :=
        ae_comp_of_pushforward (μ := μ) (μ' := μ') (g := g) hg hpush hF_eq
      have hG' : (G ∘ g) =ᵐ[μ'] (Gm ∘ g) :=
        ae_comp_of_pushforward (μ := μ) (μ' := μ') (g := g) hg hpush hG_eq
      exact hF'.symm.trans (h.trans hG')
    · intro h
      have hF' : (F ∘ g) =ᵐ[μ'] (Fm ∘ g) :=
        ae_comp_of_pushforward (μ := μ) (μ' := μ') (g := g) hg hpush hF_eq
      have hG' : (G ∘ g) =ᵐ[μ'] (Gm ∘ g) :=
        ae_comp_of_pushforward (μ := μ) (μ' := μ') (g := g) hg hpush hG_eq
      exact hF'.trans (h.trans hG'.symm)

  -- Now prove the equivalence for measurable reps by null-set/preimage.
  have h_core :
      (Fm =ᵐ[μ] Gm) ↔ (Fm ∘ g =ᵐ[μ'] Gm ∘ g) := by
    -- Use measurable {x | Fm x ≠ Gm x}.
    have hSmeas :
        MeasurableSet {x | Fm x ≠ Gm x} := by
      -- `{f ≠ g} = {f < g} ∪ {g < f}`
      have h1 : MeasurableSet {x | Fm x < Gm x} :=
        measurableSet_lt hFm_meas hGm_meas
      have h2 : MeasurableSet {x | Gm x < Fm x} :=
        measurableSet_lt hGm_meas hFm_meas
      have : {x | Fm x ≠ Gm x} = {x | Fm x < Gm x} ∪ {x | Gm x < Fm x} := by
        ext x
        constructor
        · intro h; exact ne_iff_lt_or_gt.mp h
        · intro h; exact ne_iff_lt_or_gt.mpr h
      rw [this]
      exact h1.union h2
    constructor
    · intro h
      -- μ S = 0 → μ' (g ⁻¹' S) = 0  → AE on μ' after composing with g.
      have : μ {x | Fm x ≠ Gm x} = 0 := (ae_iff).1 h
      -- push it through the factor map using measurability
      have hmp : MeasurePreserving g μ' μ := measurePreserving_of_map_eq hg hpush
      have : μ' (g ⁻¹' {x | Fm x ≠ Gm x}) = 0 := by
        rw [hmp.measure_preimage hSmeas.nullMeasurableSet]
        exact this
      -- identify the preimage set with the set for the composed functions
      have : μ' {x' | (Fm ∘ g) x' ≠ (Gm ∘ g) x'} = 0 := by
        simpa using this
      exact (ae_iff).2 this
    · intro h
      have : μ' {x' | (Fm ∘ g) x' ≠ (Gm ∘ g) x'} = 0 := (ae_iff).1 h
      -- convert back using the same preimage identity and measure-preserving fact
      have hmp : MeasurePreserving g μ' μ := measurePreserving_of_map_eq hg hpush
      -- `{x' | (Fm∘g) x' ≠ (Gm∘g) x'} = g ⁻¹' {x | Fm x ≠ Gm x}`
      have : μ' (g ⁻¹' {x | Fm x ≠ Gm x}) = 0 := by simpa using this
      -- and `μ S = μ' (g ⁻¹' S)` for S measurable
      have : μ {x | Fm x ≠ Gm x} = 0 := by
        rw [← hmp.measure_preimage hSmeas.nullMeasurableSet]
        exact this
      exact (ae_iff).2 this

  -- Stitch the three equivalences together.
  simpa [h_left, h_right] using h_core

/-- Transport integrability across a pushforward equality and then pull back by composition.
This avoids instance gymnastics by rewriting the measure explicitly, then using `comp_measurable`. -/
private lemma integrable_comp_of_pushforward
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

/-- CE is a.e.-strongly measurable w.r.t. the *sub* σ-algebra, with ambient locked. -/
lemma aestronglyMeasurable_condExp'
    {Ω β} [mΩ : MeasurableSpace Ω] [NormedAddCommGroup β] [NormedSpace ℝ β] [CompleteSpace β]
    {μ : Measure Ω} (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (f : Ω → β) :
    AEStronglyMeasurable[m] (condExp m μ f) μ :=
  stronglyMeasurable_condExp.aestronglyMeasurable

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

/-- Norm/abs bound for indicators (ℝ and general normed targets). -/
lemma abs_indicator_le_abs_self {Ω} (s : Set Ω) (f : Ω → ℝ) :
    ∀ x, |s.indicator f x| ≤ |f x| := by
  intro x
  by_cases hx : x ∈ s
  · simp [Set.indicator_of_mem hx]
  · simp [Set.indicator_of_notMem hx, abs_nonneg]

lemma norm_indicator_le_norm_self
    {Ω E} [SeminormedAddCommGroup E] (s : Set Ω) (f : Ω → E) :
    ∀ x, ‖s.indicator f x‖ ≤ ‖f x‖ := by
  intro x
  by_cases hx : x ∈ s
  · simp [Set.indicator_of_mem hx]
  · simp [Set.indicator_of_notMem hx]

/-- Indicator ↔ product with a 0/1 mask (for ℝ). -/
lemma indicator_as_mul_one {Ω} (s : Set Ω) (f : Ω → ℝ) :
    s.indicator f = fun x => f x * s.indicator (fun _ => (1 : ℝ)) x := by
  funext x
  by_cases hx : x ∈ s
  · simp [Set.indicator_of_mem hx]
  · simp [Set.indicator_of_notMem hx]

lemma integral_indicator_as_mul {Ω} [MeasurableSpace Ω] {μ : Measure Ω}
    (s : Set Ω) (f : Ω → ℝ) :
    ∫ x, s.indicator f x ∂μ = ∫ x, f x * s.indicator (fun _ => (1 : ℝ)) x ∂μ := by
  simpa [indicator_as_mul_one s f]

/-- "Lift" a measurable-in-sub-σ-algebra set to ambient measurability. -/
lemma measurableSet_of_sub {Ω} [mΩ : MeasurableSpace Ω]
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ) {s : Set Ω}
    (hs : MeasurableSet[m] s) : @MeasurableSet Ω mΩ s :=
  hm s hs

/-- AEMeasurable indicator under ambient from sub-σ-algebra measurability. -/
lemma aemeasurable_indicator_of_sub {Ω} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    {s : Set Ω} (hs : MeasurableSet[m] s)
    {f : Ω → ℝ} (hf : AEMeasurable f μ) :
    AEMeasurable (s.indicator f) μ := by
  letI : MeasurableSpace Ω := mΩ  -- Fix ambient space instance
  exact hf.indicator (measurableSet_of_sub m hm hs)

/-- Idempotence of conditional expectation for m-measurable integrable functions.

**TODO**: Find the correct mathlib API for this standard result. Candidates:
- `condExp_of_stronglyMeasurable` (needs StronglyMeasurable, not AEStronglyMeasurable)
- Some version of `condexp_of_aestronglyMeasurable` (not found in current snapshot)
- Direct proof via uniqueness characterization

The statement is correct and will be used in rectangle-case proofs. -/
lemma condExp_idempotent'
    {Ω} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    [SigmaFinite (μ.trim hm)]
    {f : Ω → ℝ}
    (hf_m : AEStronglyMeasurable[m] f μ)
    (hf_int : Integrable f μ) :
    μ[f | m] =ᵐ[μ] f := by
  -- Idempotence: CE[f|m] = f a.e. when f is m-measurable
  exact MeasureTheory.condExp_of_aestronglyMeasurable' hm hf_m hf_int

end MeasureTheory

/-- **Factor-map pullback for conditional expectation**.

If `g : Ω' → Ω` is a factor map (i.e., `map g μ' = μ`), then conditional expectation
pulls back correctly: `CE[H | 𝒢] ∘ g = CE[H ∘ g | comap g 𝒢]` a.e.

This is the key lemma for transporting conditional expectations between spaces. -/
lemma condexp_pullback_factor
    {Ω Ω' : Type*} [inst : MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} [IsFiniteMeasure μ] {μ' : Measure Ω'} [IsFiniteMeasure μ']
    (g : Ω' → Ω) (hg : Measurable g) (hpush : Measure.map g μ' = μ)
    {H : Ω → ℝ} (hH : Integrable H μ)
    (m : MeasurableSpace Ω) (hm : m ≤ inst) :
    (fun ω' => μ[H | m] (g ω'))
      =ᵐ[μ'] μ'[(H ∘ g) | MeasurableSpace.comap g m] := by
  classical

  -- 1) Set-integral equality on every comap set
  have h_sets :
      ∀ s, MeasurableSet[MeasurableSpace.comap g m] s →
        ∫ x in s, (μ[H | m] ∘ g) x ∂ μ' = ∫ x in s, (H ∘ g) x ∂ μ' := by
    intro s hs
    rcases hs with ⟨B, hBm, rfl⟩
    -- lift measurability from m to ambient inst
    have hBm' : @MeasurableSet Ω inst B := hm B hBm
    -- a.e.-measurability for the integrands (under μ)
    -- Lift stronglyMeasurable from m to inst using hm : m ≤ inst
    have hCE_ae : AEMeasurable (condExp m μ H) μ :=
      (stronglyMeasurable_condExp.mono hm).aestronglyMeasurable.aemeasurable
    have hH_ae : AEMeasurable H μ := hH.aestronglyMeasurable.aemeasurable
    -- Three-step calc: change variables, apply CE property, change back
    calc
      ∫ x in g ⁻¹' B, (condExp m μ H ∘ g) x ∂ μ'
          = ∫ x in B, condExp m μ H x ∂ μ := by
            -- ★ explicit instance-locked change of variables
            exact
              @MeasureTheory.setIntegral_map_preimage Ω Ω' inst _ μ μ' g hg hpush
                (condExp m μ H) B hBm' hCE_ae
      _ = ∫ x in B, H x ∂ μ := by
            -- ★ explicit instance-locked CE property on m
            -- Provide `SigmaFinite (μ.trim hm)` if your build doesn't infer it automatically from finiteness.
            -- You can move this `haveI` up if you prefer a global instance.
            haveI : SigmaFinite (μ.trim hm) := inferInstance
            exact
              @MeasureTheory.setIntegral_condExp' Ω inst μ m hm _ B (by simpa using hBm) H hH
      _ = ∫ x in g ⁻¹' B, (H ∘ g) x ∂ μ' := by
            -- ★ explicit instance-locked change of variables (back)
            exact
              (@MeasureTheory.setIntegral_map_preimage Ω Ω' inst _ μ μ' g hg hpush
                H B hBm' hH_ae).symm
    /-
    PROOF STRATEGY (blocked by type class synthesis for sub-σ-algebras):

    Goal: ∫ x in g⁻¹'B, (μ[H|m] ∘ g) x ∂μ' = ∫ x in g⁻¹'B, (H ∘ g) x ∂μ'

    The proof follows a three-step calc chain:
    1. Change variables: ∫ x in g⁻¹'B, (μ[H|m] ∘ g) x ∂μ' = ∫ x in B, μ[H|m] x ∂μ
       - Use setIntegral_map with hpush : map g μ' = μ
       - Requires: AEStronglyMeasurable (μ[H|m]) (map g μ')

    2. Conditional expectation: ∫ x in B, μ[H|m] x ∂μ = ∫ x in B, H x ∂μ
       - Use setIntegral_condExp hm hH hBm

    3. Reverse change of variables: ∫ x in B, H x ∂μ = ∫ x in g⁻¹'B, (H ∘ g) x ∂μ'
       - Use setIntegral_map with hpush
       - Requires: AEStronglyMeasurable H (map g μ')

    BLOCKER: Lean's type class synthesis gets confused between the sub-σ-algebra `m`
    and the ambient measurable space `inst` when applying setIntegral_map. The lemma
    expects the ambient space, but conditional expectation μ[H|m] is defined with
    respect to `m`, causing "synthesized type class instance is not definitionally
    equal to expression inferred by typing rules" errors.

    POTENTIAL FIXES:
    1. Use fully explicit @-syntax for all lemmas with manual type class arguments
    2. Reformulate using indicator functions and whole-space integrals
    3. Wait for mathlib to add better support for sub-σ-algebra type class synthesis
    4. Use convert_to instead of rw to handle definitional inequality

    This is a known limitation when working with sub-σ-algebras in measure theory.
    -/
    /-
    OLD PROOF IDEA (Type class synthesis issues with m vs inst):

    Turn set integrals into whole integrals of indicators and change variables.
    The key steps are:
    1. Convert set integral to indicator integral
    2. Pull indicator through preimage
    3. Change of variables using measure-preserving property
    4. Apply defining property of conditional expectation on m-measurable sets
    5. Reverse the process for H

    This requires careful instance management:
    - hCEint : Integrable (μ[H | m]) μ := integrable_condExp
    - hCEind_int : Integrable (Set.indicator B (μ[H | m])) μ := hCEint.indicator hBm'
    - hHind_int : Integrable (Set.indicator B H) μ := hH.indicator hBm'

    calc chain:
      ∫ x in g ⁻¹' B, (μ[H | m] ∘ g) x ∂ μ'
      = ∫ x, (Set.indicator (g ⁻¹' B) (μ[H | m] ∘ g)) x ∂ μ'  [integral_indicator]
      = ∫ x, ((Set.indicator B (μ[H | m])) ∘ g) x ∂ μ'        [indicator_preimage_comp]
      = ∫ x, (Set.indicator B (μ[H | m])) x ∂ μ                [mpOfPushforward integral_comp] **ERROR: instance synthesis**
      = ∫ x in B, μ[H | m] x ∂ μ                               [integral_indicator]
      = ∫ x in B, H x ∂ μ                                       [setIntegral_condExp] **ERROR: instance annotations needed**
      = ∫ x, (Set.indicator B H) x ∂ μ                          [integral_indicator]
      = ∫ x, ((Set.indicator B H) ∘ g) x ∂ μ'                   [mpOfPushforward integral_comp] **ERROR: same as above**
      = ∫ x, (Set.indicator (g ⁻¹' B) (H ∘ g)) x ∂ μ'          [indicator_preimage_comp]
      = ∫ x in g ⁻¹' B, (H ∘ g) x ∂ μ'                          [integral_indicator]

    BLOCKERS:
    - mpOfPushforward needs explicit @-syntax for type class arguments
    - setIntegral_condExp may need (m := m) (inst := inst) annotations
    - May need convert instead of exact for definitional equality issues
    -/

  -- 2) Uniqueness of the conditional expectation on `m.comap g`
  have hm' : MeasurableSpace.comap g m ≤ ‹MeasurableSpace Ω'› := by
    intro s hs
    rcases hs with ⟨B, hBm, rfl⟩
    -- Lift measurability from m to ambient inst, then apply preimage
    have hB_inst : @MeasurableSet Ω inst B := hm B hBm
    exact hB_inst.preimage hg
  -- Integrability of the pulled-back function (no instance shenanigans)
  have hHg' : Integrable (H ∘ g) μ' :=
    @integrable_comp_of_pushforward Ω Ω' inst _ μ μ' g H hg hpush hH

  -- Apply uniqueness of conditional expectation: we want to show (μ[H | m] ∘ g) = μ'[H ∘ g | comap g m]
  -- The lemma signature is: ae_eq_condExp_of_forall_setIntegral_eq (hf : Integrable f) ... : g =ᵐ[μ] μ[f | m]
  -- So f = H ∘ g (the integrable function we're taking condExp of)
  -- And g = μ[H | m] ∘ g (the function we're claiming equals the condExp)
  refine ae_eq_condExp_of_forall_setIntegral_eq (μ := μ') (m := MeasurableSpace.comap g m) (hm := hm') hHg' ?_ ?_ ?_
  -- 1) IntegrableOn for (μ[H | m] ∘ g) on finite measure comap sets
  · intro s hs hμs
    -- μ[H | m] ∘ g is integrable because μ[H | m] is integrable
    have : Integrable (μ[H | m]) μ := integrable_condExp
    exact (@integrable_comp_of_pushforward Ω Ω' inst _ μ μ' g (μ[H | m]) hg hpush this).integrableOn
  -- 2) Integral equality (h_sets but with added finite measure hypothesis)
  · intro s hs _
    exact h_sets s hs
  -- 3) AEStronglyMeasurable for (μ[H | m] ∘ g) with respect to comap g m
  · -- Key: g is measurable from (Ω', comap g m) to (Ω, m) by definition of comap
    have hf_meas_comap : @Measurable Ω' Ω (MeasurableSpace.comap g m) m g :=
      fun s hs => ⟨s, hs, rfl⟩
    -- condExp m μ H is strongly measurable w.r.t. m
    have h_sm : StronglyMeasurable[m] (condExp m μ H) := stronglyMeasurable_condExp
    -- Composition preserves strong measurability
    have h_comp_sm : StronglyMeasurable[MeasurableSpace.comap g m] (condExp m μ H ∘ g) :=
      h_sm.comp_measurable hf_meas_comap
    exact h_comp_sm.aestronglyMeasurable

/-
**Invariance of conditional expectation under iterates**.

If `T` is measure-preserving and `𝒢` is the T-invariant σ-algebra (i.e., `T⁻¹'s = s` for all `s ∈ 𝒢`),
then conditional expectation is invariant: `CE[f ∘ T^[k] | 𝒢] = CE[f | 𝒢]` a.e.

This is the key for proving lag-constancy and other invariance properties.

TODO: Complete the proof. The strategy is:
1. Use iteration to show T^[k] is measure-preserving
2. Prove T^[k] preserves m-measurable sets via induction
3. Show set-integral equality on m-measurable sets using change of variables
4. Apply uniqueness of conditional expectation

Axiom temporarily commented out due to type class elaboration issues with sub-σ-algebras
TODO: Fix the type annotation for condExp with explicit sub-σ-algebra parameter
-/
/-
axiom condexp_precomp_iterate_eq_of_invariant
    {Ω : Type*} [inst : MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (T : Ω → Ω) (hT : MeasurePreserving T μ μ)
    {k : ℕ} {f : Ω → ℝ} (hf : Integrable f μ)
    (m : MeasurableSpace Ω) (hm : m ≤ inst)
    (h_inv : ∀ s, MeasurableSet[m] s → T ⁻¹' s = s) :
    ∀ᵐ ω ∂μ, (@condExp Ω ℝ _ _ inst m _ μ _ (f ∘ (T^[k]))) ω = (@condExp Ω ℝ _ _ inst m _ μ _ f) ω
-/

/-
OLD PROOF ATTEMPT (commented out due to instance synthesis issues):

  ✅ FIXED: Induction for h_preimage (line 576-583)
  - Changed order of rewrites: rw [Set.preimage_comp, h_inv s hs, ih]
  - This works because after preimage_comp, goal is T^[n]⁻¹'(T⁻¹'s) = s
  - First apply h_inv to get T⁻¹'s = s, then ih gives result

  ⚠️ REMAINING ISSUES:

  1. Line 598-607: Indicator equality proof (unsolved goals)
     - Goal: indicator s (f ∘ T^[k]) = (indicator (T^[k]⁻¹'s) f) ∘ T^[k]
     - The logic is correct but the proof doesn't go through
     - Issue: After simp, still have unresolved goals about membership

  2. Line 609: integral_comp has instance synthesis issue
     - synthesized: m, inferred: inst
     - Same pattern as hHg' blocker

  3. Line 616-620: ae_eq_condExp_of_forall_setIntegral_eq signature mismatch
     - Using `convert ... using 2` but the _ placeholders don't match signature
     - Need to check exact signature of ae_eq_condExp_of_forall_setIntegral_eq

  ROOT CAUSE: Same as hHg' - pervasive instance synthesis issues between m and inst.

  /-
  ORIGINAL OLD PROOF (Multiple type class instance errors):

  classical
  -- iterate is measure-preserving
  have hTk : MeasurePreserving (T^[k]) μ μ := hT.iterate k

  -- Prove: ∀ s ∈ m, (T^[k]) ⁻¹' s = s
  have h_preimage :
      ∀ s, MeasurableSet[m] s → (T^[k]) ⁻¹' s = s := by
    intro s hs
    induction k with
    | zero => rfl
    | succ n ih =>
      -- T^[n+1] = T ∘ T^[n] as functions
      have : (T^[n + 1]) = (T ∘ (T^[n])) := by
        funext x
        simp [Function.iterate_succ_apply']
      rw [this, Set.preimage_comp, ih, h_inv s hs]  **ERROR: rewrite failed**

  -- Set-integral equality on `m`-measurable sets
  have h_sets :
      ∀ s, MeasurableSet[m] s →
        ∫ x in s, (f ∘ (T^[k])) x ∂ μ = ∫ x in s, f x ∂ μ :=
  by
    intro s hs
    have hs' : @MeasurableSpace Ω inst s := hm s hs
    have hf_ind : Integrable (Set.indicator s f) μ := hf.indicator hs'

    calc
      ∫ x in s, (f ∘ (T^[k])) x ∂ μ
      = ∫ x, (Set.indicator s (f ∘ (T^[k]))) x ∂ μ  [integral_indicator]
      = ∫ x, ((Set.indicator ((T^[k]) ⁻¹' s) f) ∘ (T^[k])) x ∂ μ  [funext + indicator manipulation] **ERROR: apply funext failed**
      = ∫ x, (Set.indicator ((T^[k]) ⁻¹' s) f) x ∂ μ  [hTk.integral_comp] **ERROR: Type mismatch**
      = ∫ x, (Set.indicator s f) x ∂ μ  [use h_preimage]  **ERROR: Application type mismatch**
      = ∫ x in s, f x ∂ μ  [integral_indicator]

  -- Uniqueness of conditional expectation on `m`
  exact ae_eq_condExp_of_forall_setIntegral_eq hm hf h_sets  **ERROR: Application type mismatch**

BLOCKERS:
- Instance synthesis issues throughout
- Rewrite failures with h_inv
- funext application issues
- Type mismatches in MeasurePreserving.integral_comp
-/
-/

/-! ### Lag-Constancy from Exchangeability: The Transposition Argument

This section proves that exchangeability implies lag-constancy for conditional
expectations. The proof uses Kallenberg's transposition argument:

1. For k ≥ 1, the transposition τ = swap(k, k+1) fixes index 0
2. Exchangeability gives measure invariance under reindex τ
3. Shift-invariant sets are preserved by reindex τ (they depend only on tails)
4. Therefore CE[f(ω₀)·g(ω_{k+1}) | ℐ] = CE[f(ω₀)·g(ω_k) | ℐ]

**Key lemmas:**
- `shift_reindex_swap_eq`: For m > k+1, shift^m ∘ reindex τ = shift^m
- `reindex_swap_preimage_shiftInvariant`: Shift-invariant sets are τ-invariant
- `condexp_lag_constant_from_exchangeability`: The main result
-/

section LagConstancyProof

variable {α : Type*} [MeasurableSpace α]

/-- Shift^m applied to reindex (swap k (k+1)) ω equals shift^m applied to ω when m > k + 1.

This is because the swap only affects coordinates k and k+1, which are "shifted away"
after m iterations of shift when m > k + 1. -/
-- Helper: iterated shift satisfies shift^[j] ξ n = ξ (n + j)
private lemma shift_iterate_apply (j n : ℕ) (ξ : ℕ → α) :
    ((shift (α := α))^[j] ξ) n = ξ (n + j) := by
  induction j generalizing n with
  | zero => simp
  | succ j ih =>
    simp only [Function.iterate_succ', Function.comp_apply, shift_apply]
    rw [ih]
    congr 1
    omega

private lemma shift_iterate_reindex_swap_eq (k m : ℕ) (hm : k + 1 < m) (ω : ℕ → α) :
    shift^[m] (Exchangeability.reindex (Equiv.swap k (k + 1)) ω) = shift^[m] ω := by
  ext n
  rw [shift_iterate_apply, shift_iterate_apply, Exchangeability.reindex_apply]
  -- Need to show: ω (swap k (k+1) (n + m)) = ω (n + m)
  -- Since n + m ≥ m > k + 1, we have n + m ≠ k and n + m ≠ k + 1
  have h1 : n + m ≠ k := by omega
  have h2 : n + m ≠ k + 1 := by omega
  rw [Equiv.swap_apply_of_ne_of_ne h1 h2]

/-- Preimages of shift-invariant sets under reindex (swap k (k+1)) are the same set.

**Proof strategy**: A set s is shift-invariant iff membership depends only on tails.
Since swap k (k+1) only affects coordinates k and k+1, for any n > k+1,
the n-tail of ω equals the n-tail of (reindex τ ω). By shift-invariance,
membership in s is determined by any tail, hence ω ∈ s ↔ (reindex τ ω) ∈ s. -/
private lemma reindex_swap_preimage_shiftInvariant (k : ℕ) (s : Set (ℕ → α))
    (hs : isShiftInvariant (α := α) s) :
    (Exchangeability.reindex (Equiv.swap k (k + 1))) ⁻¹' s = s := by
  ext ω
  simp only [Set.mem_preimage]
  -- Use that s is shift-invariant: ω ∈ s ↔ shift^[m] ω ∈ s for any m
  obtain ⟨_, hs_shift⟩ := hs
  -- Key: shift⁻¹' s = s means ω ∈ s ↔ shift ω ∈ s, hence ω ∈ s ↔ shift^m ω ∈ s
  have h_iter : ∀ m, (shift (α := α))^[m] ⁻¹' s = s := by
    intro m
    induction m with
    | zero => simp
    | succ n ih =>
      calc shift^[n + 1] ⁻¹' s = shift^[n] ⁻¹' (shift ⁻¹' s) := by
              simp only [Function.iterate_succ', Set.preimage_comp]
        _ = shift^[n] ⁻¹' s := by rw [hs_shift]
        _ = s := ih
  -- Choose m = k + 2 > k + 1
  have hm : k + 1 < k + 2 := Nat.lt_succ_self _
  -- The key: shift^[k+2] (reindex τ ω) = shift^[k+2] ω
  have h_eq := shift_iterate_reindex_swap_eq k (k + 2) hm ω
  -- Use that s is shift^[k+2]-invariant: ω ∈ s ↔ shift^[k+2] ω ∈ s
  have h_iter_k2 := h_iter (k + 2)
  -- ω ∈ shift^[m] ⁻¹' s ↔ shift^[m] ω ∈ s, and h_iter_k2 says shift^[k+2] ⁻¹' s = s
  -- h_iter_k2 means: ξ ∈ s ↔ ξ ∈ shift^[k+2] ⁻¹' s ↔ shift^[k+2] ξ ∈ s
  constructor
  · -- Assume reindex τ ω ∈ s, show ω ∈ s
    intro h
    -- Step 1: reindex τ ω ∈ s → shift^[k+2] (reindex τ ω) ∈ s (using h_iter_k2 backwards)
    have h1 : (Exchangeability.reindex (Equiv.swap k (k + 1)) ω) ∈ (shift (α := α))^[k + 2] ⁻¹' s := by
      rw [h_iter_k2]; exact h
    -- Step 2: shift^[k+2] (reindex τ ω) ∈ s (by definition of preimage)
    simp only [Set.mem_preimage] at h1
    -- Step 3: By h_eq, shift^[k+2] (reindex τ ω) = shift^[k+2] ω
    rw [h_eq] at h1
    -- Step 4: shift^[k+2] ω ∈ s → ω ∈ s (using h_iter_k2)
    have h2 : ω ∈ (shift (α := α))^[k + 2] ⁻¹' s := by simp only [Set.mem_preimage]; exact h1
    rw [h_iter_k2] at h2; exact h2
  · -- Assume ω ∈ s, show reindex τ ω ∈ s
    intro h
    -- Step 1: ω ∈ s → shift^[k+2] ω ∈ s (using h_iter_k2 backwards)
    have h1 : ω ∈ (shift (α := α))^[k + 2] ⁻¹' s := by rw [h_iter_k2]; exact h
    simp only [Set.mem_preimage] at h1
    -- Step 2: By h_eq (reversed), shift^[k+2] ω = shift^[k+2] (reindex τ ω)
    rw [← h_eq] at h1
    -- Step 3: shift^[k+2] (reindex τ ω) ∈ s → reindex τ ω ∈ s (using h_iter_k2)
    have h2 : (Exchangeability.reindex (Equiv.swap k (k + 1)) ω) ∈ (shift (α := α))^[k + 2] ⁻¹' s := by
      simp only [Set.mem_preimage]; exact h1
    rw [h_iter_k2] at h2; exact h2

/-- **Generalized reindex preimage invariance**: For any permutation π that is identity
beyond some bound M, shift-invariant sets are reindex-invariant.

This generalizes `reindex_swap_preimage_shiftInvariant` from transpositions to arbitrary
finite-support permutations. The proof uses the same key insight: shift^[M] commutes with
reindex π when π is identity beyond M, so membership in shift-invariant sets is preserved. -/
lemma reindex_perm_preimage_shiftInvariant (π : Equiv.Perm ℕ) (M : ℕ)
    (h_id_beyond : ∀ n, M ≤ n → π n = n)
    (s : Set (ℕ → α)) (hs : isShiftInvariant (α := α) s) :
    (Exchangeability.reindex π) ⁻¹' s = s := by
  ext ω
  simp only [Set.mem_preimage]
  -- Use that s is shift-invariant: ω ∈ s ↔ shift^[m] ω ∈ s for any m
  obtain ⟨_, hs_shift⟩ := hs
  have h_iter : ∀ m, (shift (α := α))^[m] ⁻¹' s = s := by
    intro m
    induction m with
    | zero => simp
    | succ n ih =>
      calc shift^[n + 1] ⁻¹' s = shift^[n] ⁻¹' (shift ⁻¹' s) := by
              simp only [Function.iterate_succ', Set.preimage_comp]
        _ = shift^[n] ⁻¹' s := by rw [hs_shift]
        _ = s := ih
  -- Key: shift^[M] (reindex π ω) = shift^[M] ω pointwise
  have h_eq : shift^[M] (Exchangeability.reindex π ω) = shift^[M] ω := by
    ext n
    rw [shift_iterate_apply, shift_iterate_apply, Exchangeability.reindex_apply]
    -- π (n + M) = n + M since n + M ≥ M
    have hle : M ≤ n + M := Nat.le_add_left M n
    rw [h_id_beyond (n + M) hle]
  have h_iter_M := h_iter M
  constructor
  · -- Assume reindex π ω ∈ s, show ω ∈ s
    intro h
    have h1 : (Exchangeability.reindex π ω) ∈ (shift (α := α))^[M] ⁻¹' s := by
      rw [h_iter_M]; exact h
    simp only [Set.mem_preimage] at h1
    rw [h_eq] at h1
    have h2 : ω ∈ (shift (α := α))^[M] ⁻¹' s := by simp only [Set.mem_preimage]; exact h1
    rw [h_iter_M] at h2; exact h2
  · -- Assume ω ∈ s, show reindex π ω ∈ s
    intro h
    have h1 : ω ∈ (shift (α := α))^[M] ⁻¹' s := by rw [h_iter_M]; exact h
    simp only [Set.mem_preimage] at h1
    rw [← h_eq] at h1
    have h2 : (Exchangeability.reindex π ω) ∈ (shift (α := α))^[M] ⁻¹' s := by
      simp only [Set.mem_preimage]; exact h1
    rw [h_iter_M] at h2; exact h2

/-! ### Cycle permutation for lag constancy -/

/-- A cycle on [L, R] that maps n → n-1 (for L < n ≤ R) and L → R.
This is useful for proving lag constancy of cylinder sets: it shifts coordinates
down by 1 within the range, wrapping L to R. -/
def cycleShiftDown (L R : ℕ) (hLR : L ≤ R) : Equiv.Perm ℕ where
  toFun := fun n =>
    if L < n ∧ n ≤ R then n - 1
    else if n = L then R
    else n
  invFun := fun n =>
    if L ≤ n ∧ n < R then n + 1
    else if n = R then L
    else n
  left_inv := by intro n; simp only; split_ifs <;> omega
  right_inv := by intro n; simp only; split_ifs <;> omega

lemma cycleShiftDown_lt (L R n : ℕ) (hLR : L ≤ R) (hn : n < L) :
    cycleShiftDown L R hLR n = n := by
  simp only [cycleShiftDown, Equiv.coe_fn_mk]; split_ifs <;> omega

lemma cycleShiftDown_gt (L R n : ℕ) (hLR : L ≤ R) (hn : R < n) :
    cycleShiftDown L R hLR n = n := by
  simp only [cycleShiftDown, Equiv.coe_fn_mk]; split_ifs <;> omega

lemma cycleShiftDown_sub (L R n : ℕ) (hLR : L ≤ R) (hLn : L < n) (hnR : n ≤ R) :
    cycleShiftDown L R hLR n = n - 1 := by
  simp only [cycleShiftDown, Equiv.coe_fn_mk]; split_ifs <;> omega

lemma cycleShiftDown_L (L R : ℕ) (hLR : L ≤ R) :
    cycleShiftDown L R hLR L = R := by
  simp only [cycleShiftDown, Equiv.coe_fn_mk]; split_ifs <;> omega

/-- The cycle is identity beyond R. -/
lemma cycleShiftDown_id_beyond (L R : ℕ) (hLR : L ≤ R) (n : ℕ) (hn : R < n) :
    cycleShiftDown L R hLR n = n := cycleShiftDown_gt L R n hLR hn

/-- The function f(ω 0) * g(ω (k+1)) composed with reindex τ gives f(ω 0) * g(ω k)
when τ = swap k (k+1) and k ≥ 1 (so τ fixes 0). -/
private lemma product_reindex_swap_eq (f g : α → ℝ) (k : ℕ) (hk : 0 < k) :
    (fun ω => f (ω 0) * g (ω (k + 1))) ∘ Exchangeability.reindex (Equiv.swap k (k + 1))
    = fun ω => f (ω 0) * g (ω k) := by
  ext ω
  simp only [Function.comp_apply, Exchangeability.reindex_apply]
  congr 1
  · -- Show: ω (swap k (k+1) 0) = ω 0
    have h1 : (0 : ℕ) ≠ k := by omega
    have h2 : (0 : ℕ) ≠ k + 1 := by omega
    rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
  · -- Show: ω (swap k (k+1) (k+1)) = ω k
    rw [Equiv.swap_apply_right]

end LagConstancyProof

/-- For exchangeable measures, set integrals are equal for functions that agree on reindexing.
This is a key step in proving lag-constancy: ∫_s F = ∫_s G when F ∘ reindex τ = G
and the set s is shift-invariant (hence also reindex-invariant). -/
lemma setIntegral_eq_of_reindex_eq
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α]
    {μ : Measure (ℕ → α)} [IsProbabilityMeasure μ]
    (τ : Equiv.Perm ℕ)
    (hμ_inv : Measure.map (Exchangeability.reindex τ) μ = μ)
    (F G : (ℕ → α) → ℝ)
    (hFG : F ∘ Exchangeability.reindex τ = G)
    (hF_meas : Measurable F)
    (s : Set (ℕ → α))
    (hs_meas : MeasurableSet s)
    (h_preimage : (Exchangeability.reindex τ) ⁻¹' s = s) :
    ∫ ω in s, F ω ∂μ = ∫ ω in s, G ω ∂μ := by
  have hτ_meas : Measurable (Exchangeability.reindex (α := α) τ) :=
    Exchangeability.measurable_reindex (α := α) (π := τ)
  have hF' : AEStronglyMeasurable F (Measure.map (Exchangeability.reindex τ) μ) := by
    rw [hμ_inv]; exact hF_meas.aestronglyMeasurable
  calc ∫ ω in s, F ω ∂μ
      = ∫ ω in s, F ω ∂(Measure.map (Exchangeability.reindex τ) μ) := by rw [hμ_inv]
    _ = ∫ ω in (Exchangeability.reindex τ) ⁻¹' s, F ((Exchangeability.reindex τ) ω) ∂μ :=
        setIntegral_map hs_meas hF' hτ_meas.aemeasurable
    _ = ∫ ω in s, F ((Exchangeability.reindex τ) ω) ∂μ := by rw [h_preimage]
    _ = ∫ ω in s, G ω ∂μ := by congr 1

/-- If ∫_s (F - G) = 0 for all s in sub-σ-algebra, then CE[F|m] = CE[G|m] a.e. -/
lemma condExp_ae_eq_of_setIntegral_diff_eq_zero
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α]
    {μ : Measure (ℕ → α)} [IsProbabilityMeasure μ]
    {F G : (ℕ → α) → ℝ}
    (hF_int : Integrable F μ)
    (hG_int : Integrable G μ)
    (h_diff_zero : ∀ s, MeasurableSet[shiftInvariantSigma (α := α)] s → μ s < ⊤ →
        ∫ ω in s, (F - G) ω ∂μ = 0) :
    μ[F | shiftInvariantSigma (α := α)] =ᵐ[μ] μ[G | shiftInvariantSigma (α := α)] := by
  have hm := shiftInvariantSigma_le (α := α)
  have hFG_int : Integrable (F - G) μ := hF_int.sub hG_int
  -- Step 1: 0 =ᵐ CE[F-G|mSI] since both have same integrals over mSI-sets
  have h_zero_eq_ce : (0 : (ℕ → α) → ℝ) =ᵐ[μ] μ[F - G | shiftInvariantSigma (α := α)] :=
    ae_eq_condExp_of_forall_setIntegral_eq hm hFG_int
      (fun _ _ _ => integrableOn_zero)
      (fun s hs hμs => by simp only [Pi.zero_apply, integral_zero, h_diff_zero s hs hμs])
      aestronglyMeasurable_zero
  -- Step 2: CE[F-G|mSI] = 0 a.e.
  have h_ce_diff_zero : μ[F - G | shiftInvariantSigma (α := α)] =ᵐ[μ] 0 := h_zero_eq_ce.symm
  -- Step 3: CE[F-G|mSI] = CE[F|mSI] - CE[G|mSI] by linearity
  have h_ce_sub : μ[F - G | shiftInvariantSigma (α := α)] =ᵐ[μ]
      μ[F | shiftInvariantSigma (α := α)] - μ[G | shiftInvariantSigma (α := α)] :=
    condExp_sub hF_int hG_int (shiftInvariantSigma (α := α))
  -- Step 4: Combine to get CE[F|mSI] - CE[G|mSI] = 0, hence CE[F|mSI] = CE[G|mSI]
  have h_eq := h_ce_sub.symm.trans h_ce_diff_zero
  exact h_eq.mono fun ω hω => sub_eq_zero.mp hω

set_option maxHeartbeats 600000 in
/-- **Lag-constancy from exchangeability via transpositions** (Kallenberg's approach).

For EXCHANGEABLE measures μ on path space, the conditional expectation
CE[f(ω₀)·g(ω_{k+1}) | ℐ] equals CE[f(ω₀)·g(ω_k) | ℐ] for k ≥ 1.

**Key insight**: This uses EXCHANGEABILITY (not just stationarity). The proof is:
1. Let τ be the transposition swapping indices k and k+1
2. Exchangeability gives: Measure.map (reindex τ) μ = μ
3. Since k ≥ 1, τ fixes 0: τ(0) = 0
4. Therefore: CE[f(ω₀)·g(ω_{k+1}) | ℐ] = CE[(f∘τ)(ω₀)·(g∘τ)(ω_{k+1}) | ℐ]
                                        = CE[f(ω₀)·g(ω_k) | ℐ]

**Why k ≥ 1 is required (CRITICAL)**:
- When k=0, τ = swap(0, 1) does NOT fix 0 (τ sends 0 ↦ 1)
- So (f∘τ)(ω₀) = f(ω₁) ≠ f(ω₀), breaking the argument
- Counterexample for k=0: i.i.d. Bernoulli(1/2):
  * CE[ω₀·ω₁ | ℐ] = E[ω₀]·E[ω₁] = 1/4
  * CE[ω₀² | ℐ] = E[ω₀²] = 1/2 (since ω₀ ∈ {0,1})
  * These are NOT equal!

**Why stationarity alone is NOT enough**: Stationary non-exchangeable processes
(Markov chains, AR processes) can have lag-dependent conditional correlations.
The transposition trick requires the FULL permutation invariance of exchangeability. -/
lemma condexp_lag_constant_from_exchangeability
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α]
    {μ : Measure (ℕ → α)} [IsProbabilityMeasure μ]
    (hExch : ∀ π : Equiv.Perm ℕ, Measure.map (Exchangeability.reindex π) μ = μ)
    (f g : α → ℝ)
    (hf_meas : Measurable f) (hf_bd : ∃ C, ∀ x, |f x| ≤ C)
    (hg_meas : Measurable g) (hg_bd : ∃ C, ∀ x, |g x| ≤ C)
    (k : ℕ) (hk : 0 < k) :
    μ[(fun ω => f (ω 0) * g (ω (k + 1))) | shiftInvariantSigma (α := α)]
      =ᵐ[μ]
    μ[(fun ω => f (ω 0) * g (ω k)) | shiftInvariantSigma (α := α)] := by
  -- Define the transposition τ = swap k (k+1)
  let τ := Equiv.swap k (k + 1)
  -- Define the two functions
  let F := fun ω : ℕ → α => f (ω 0) * g (ω (k + 1))
  let G := fun ω : ℕ → α => f (ω 0) * g (ω k)
  -- Key fact 1: F ∘ reindex τ = G
  have hFG : F ∘ Exchangeability.reindex τ = G := product_reindex_swap_eq f g k hk
  -- Key fact 2: μ.map (reindex τ) = μ (exchangeability)
  have hμ_inv : Measure.map (Exchangeability.reindex τ) μ = μ := hExch τ
  -- Key fact 3: reindex τ is measurable
  have hτ_meas : Measurable (Exchangeability.reindex (α := α) τ) :=
    Exchangeability.measurable_reindex (α := α) (π := τ)
  -- Both F and G are integrable (bounded measurable on probability space)
  obtain ⟨Cf, hCf⟩ := hf_bd
  obtain ⟨Cg, hCg⟩ := hg_bd
  have hF_meas : Measurable F := (hf_meas.comp (measurable_pi_apply 0)).mul
                                  (hg_meas.comp (measurable_pi_apply (k + 1)))
  have hG_meas : Measurable G := (hf_meas.comp (measurable_pi_apply 0)).mul
                                  (hg_meas.comp (measurable_pi_apply k))
  have hF_bd : ∀ ω, ‖F ω‖ ≤ Cf * Cg := fun ω => by
    simp only [Real.norm_eq_abs]
    calc |F ω| = |f (ω 0) * g (ω (k + 1))| := rfl
      _ = |f (ω 0)| * |g (ω (k + 1))| := abs_mul _ _
      _ ≤ Cf * Cg := mul_le_mul (hCf _) (hCg _) (abs_nonneg _)
                       (le_trans (abs_nonneg _) (hCf (ω 0)))
  have hG_bd : ∀ ω, ‖G ω‖ ≤ Cf * Cg := fun ω => by
    simp only [Real.norm_eq_abs]
    calc |G ω| = |f (ω 0) * g (ω k)| := rfl
      _ = |f (ω 0)| * |g (ω k)| := abs_mul _ _
      _ ≤ Cf * Cg := mul_le_mul (hCf _) (hCg _) (abs_nonneg _)
                       (le_trans (abs_nonneg _) (hCf (ω 0)))
  have hF_int : Integrable F μ := Integrable.of_bound hF_meas.aestronglyMeasurable (Cf * Cg)
    (Filter.Eventually.of_forall hF_bd)
  have hG_int : Integrable G μ := Integrable.of_bound hG_meas.aestronglyMeasurable (Cf * Cg)
    (Filter.Eventually.of_forall hG_bd)
  -- Strategy: Show ∫_s F = ∫_s G for all s ∈ mSI, then μ[F|mSI] = μ[G|mSI]
  have h_int_eq : ∀ s, MeasurableSet[shiftInvariantSigma (α := α)] s → μ s < ⊤ →
      ∫ ω in s, F ω ∂μ = ∫ ω in s, G ω ∂μ := fun s hs _ => by
    have hs_inv : isShiftInvariant (α := α) s := (mem_shiftInvariantSigma_iff (α := α)).mp hs
    exact setIntegral_eq_of_reindex_eq τ hμ_inv F G hFG hF_meas s hs_inv.1
      (reindex_swap_preimage_shiftInvariant k s hs_inv)
  -- Show ∫_s (F - G) = 0 for all s ∈ mSI, then use helper lemma
  have h_diff_zero : ∀ s, MeasurableSet[shiftInvariantSigma (α := α)] s → μ s < ⊤ →
      ∫ ω in s, (F - G) ω ∂μ = 0 := fun s hs hμs => by
    simp only [Pi.sub_apply, integral_sub hF_int.integrableOn hG_int.integrableOn,
               h_int_eq s hs hμs, sub_self]
  exact condExp_ae_eq_of_setIntegral_diff_eq_zero hF_int hG_int h_diff_zero

/-- The comap of shiftInvariantSigma along restrictNonneg is contained in shiftInvariantSigmaℤ.

This follows from the fact that preimages of shift-invariant sets are shiftℤ-invariant,
using `restrictNonneg_shiftℤ : restrictNonneg (shiftℤ ω) = shift (restrictNonneg ω)`. -/
lemma comap_restrictNonneg_shiftInvariantSigma_le :
    MeasurableSpace.comap (restrictNonneg (α := α)) (shiftInvariantSigma (α := α))
      ≤ shiftInvariantSigmaℤ (α := α) := by
  intro t ht
  -- t is of the form restrictNonneg⁻¹' s for some s ∈ shiftInvariantSigma
  rcases ht with ⟨s, hs, rfl⟩
  -- hs : isShiftInvariant s, i.e., MeasurableSet s ∧ shift⁻¹' s = s
  constructor
  · -- Measurability: restrictNonneg⁻¹' s is measurable
    exact measurable_restrictNonneg hs.1
  · -- Shift-invariance: shiftℤ⁻¹' (restrictNonneg⁻¹' s) = restrictNonneg⁻¹' s
    ext ω
    simp only [Set.mem_preimage]
    -- Goal: shiftℤ ω ∈ restrictNonneg⁻¹' s ↔ ω ∈ restrictNonneg⁻¹' s
    -- i.e., restrictNonneg (shiftℤ ω) ∈ s ↔ restrictNonneg ω ∈ s
    rw [restrictNonneg_shiftℤ]
    -- Now: shift (restrictNonneg ω) ∈ s ↔ restrictNonneg ω ∈ s
    -- This follows from s being shift-invariant
    have h_inv : shift ⁻¹' s = s := hs.2
    rw [← Set.mem_preimage, h_inv]

/-- Pulling an almost-everywhere equality back along the natural extension.

**Proof**: Uses `ae_map_iff` from mathlib: since `μ = map restrictNonneg ext.μhat`,
we have `(∀ᵐ ω ∂μ, F ω = G ω) ↔ (∀ᵐ ωhat ∂ext.μhat, F (restrictNonneg ωhat) = G (restrictNonneg ωhat))`.
The hypothesis `h` gives the RHS, so we conclude the LHS. -/
lemma naturalExtension_pullback_ae
    {μ : Measure (Ω[α])} [IsProbabilityMeasure μ] [StandardBorelSpace α]
    (ext : NaturalExtensionData (μ := μ))
    {F G : Ω[α] → ℝ} (hF : AEMeasurable F μ) (hG : AEMeasurable G μ)
    (h : (fun ωhat => F (restrictNonneg (α := α) ωhat))
        =ᵐ[ext.μhat]
        (fun ωhat => G (restrictNonneg (α := α) ωhat))) :
    F =ᵐ[μ] G := by
  haveI := ext.μhat_isProb
  rw [ae_pullback_iff (restrictNonneg (α := α)) measurable_restrictNonneg
    ext.restrict_pushforward hF hG]
  exact h

/-- Two-sided version of `condexp_precomp_iterate_eq`.

**Proof strategy**: For any k iterations of shiftℤ, the conditional expectation
is unchanged because:
1. shiftℤ^[k] is measure-preserving (composition of measure-preserving maps)
2. shiftℤ^[k] leaves shiftInvariantSigmaℤ-measurable sets invariant
3. Set-integrals over invariant sets are preserved by measure-preserving maps -/
lemma condexp_precomp_iterate_eq_twosided
    {μhat : Measure (Ωℤ[α])} [IsProbabilityMeasure μhat]
    (hσ : MeasurePreserving (shiftℤ (α := α)) μhat μhat) {k : ℕ}
    {f : Ωℤ[α] → ℝ} (hf : Integrable f μhat) :
    μhat[(fun ω => f ((shiftℤ (α := α))^[k] ω))
        | shiftInvariantSigmaℤ (α := α)]
      =ᵐ[μhat] μhat[f | shiftInvariantSigmaℤ (α := α)] := by
  -- Key property: shiftInvariantSigmaℤ-measurable sets are shiftℤ-invariant by definition
  have h_inv : ∀ s, MeasurableSet[shiftInvariantSigmaℤ (α := α)] s →
      (shiftℤ (α := α)) ⁻¹' s = s := fun s hs => hs.2
  -- Proof by induction on k
  induction k with
  | zero => simp
  | succ k ih =>
    -- f ∘ shiftℤ^[k+1] = (f ∘ shiftℤ^[k]) ∘ shiftℤ
    have h_comp : (fun ω => f ((shiftℤ (α := α))^[k+1] ω)) =
        (fun ω => f ((shiftℤ (α := α))^[k] ω)) ∘ (shiftℤ (α := α)) := by
      ext ω
      simp only [Function.comp_apply]
      -- Goal: f (shiftℤ^[k+1] ω) = f (shiftℤ^[k] (shiftℤ ω))
      -- Use: shiftℤ^[k+1] ω = shiftℤ^[k] (shiftℤ ω) by iterate_succ_apply
      rw [Function.iterate_succ_apply]
    -- shiftℤ^[k] is measure-preserving
    have hσ_k : MeasurePreserving ((shiftℤ (α := α))^[k]) μhat μhat := hσ.iterate k
    -- f ∘ shiftℤ^[k] is integrable
    have hf_k : Integrable (fun ω => f ((shiftℤ (α := α))^[k] ω)) μhat := by
      have : (fun ω => f ((shiftℤ (α := α))^[k] ω)) = f ∘ ((shiftℤ (α := α))^[k]) := rfl
      rw [this, hσ_k.integrable_comp hf.aestronglyMeasurable]
      exact hf
    -- Use uniqueness of conditional expectation for the base step
    have h_base : μhat[(fun ω => f ((shiftℤ (α := α))^[k] ω)) ∘ (shiftℤ (α := α))
        | shiftInvariantSigmaℤ (α := α)]
          =ᵐ[μhat] μhat[(fun ω => f ((shiftℤ (α := α))^[k] ω))
              | shiftInvariantSigmaℤ (α := α)] := by
      symm
      apply MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq
        (shiftInvariantSigmaℤ_le (α := α))
      -- Integrability of f ∘ shiftℤ^[k] ∘ shiftℤ
      · rw [hσ.integrable_comp hf_k.aestronglyMeasurable]
        exact hf_k
      -- IntegrableOn for the condExp
      · intro s _ _
        exact MeasureTheory.integrable_condExp.integrableOn
      -- Set integral equality: ∫_s E[g|m] = ∫_s g ∘ T when T⁻¹' s = s
      · intro s hs hμs
        -- First use setIntegral_condExp: ∫_s E[g|m] dμ = ∫_s g dμ
        rw [MeasureTheory.setIntegral_condExp (shiftInvariantSigmaℤ_le (α := α)) hf_k hs]
        -- Now show: ∫_s g dμ = ∫_s (g ∘ T) dμ using T⁻¹'s = s and MeasurePreserving
        let g := fun ω => f ((shiftℤ (α := α))^[k] ω)
        have h_s_inv : (shiftℤ (α := α)) ⁻¹' s = s := h_inv s hs
        -- Apply setIntegral_map_preimage in reverse with h_s_inv
        have h_map_eq : Measure.map (shiftℤ (α := α)) μhat = μhat := hσ.map_eq
        rw [← MeasureTheory.setIntegral_map_preimage (shiftℤ (α := α)) measurable_shiftℤ h_map_eq
            g s (shiftInvariantSigmaℤ_le (α := α) s hs) hf_k.aemeasurable]
        -- Now goal: ∫_s g = ∫_{T⁻¹'s} (g ∘ T), rewrite T⁻¹'s = s
        rw [h_s_inv]
      -- AE strong measurability
      · exact MeasureTheory.stronglyMeasurable_condExp.aestronglyMeasurable
    -- Combine: E[f ∘ T^{k+1} | m] = E[(f ∘ T^k) ∘ T | m] = E[f ∘ T^k | m] = E[f | m]
    calc μhat[(fun ω => f ((shiftℤ (α := α))^[k+1] ω)) | shiftInvariantSigmaℤ (α := α)]
        = μhat[(fun ω => f ((shiftℤ (α := α))^[k] ω)) ∘ (shiftℤ (α := α))
            | shiftInvariantSigmaℤ (α := α)] := by rw [h_comp]
      _ =ᵐ[μhat] μhat[(fun ω => f ((shiftℤ (α := α))^[k] ω))
            | shiftInvariantSigmaℤ (α := α)] := h_base
      _ =ᵐ[μhat] μhat[f | shiftInvariantSigmaℤ (α := α)] := ih

/-- Invariance of conditional expectation under the inverse shift.

**Proof strategy**: Similar to `condexp_precomp_iterate_eq_twosided`, but using
that shiftℤInv also preserves the measure and leaves the invariant σ-algebra fixed. -/
lemma condexp_precomp_shiftℤInv_eq
    {μhat : Measure (Ωℤ[α])} [IsProbabilityMeasure μhat]
    (hσInv : MeasurePreserving (shiftℤInv (α := α)) μhat μhat)
    {f : Ωℤ[α] → ℝ} (hf : Integrable f μhat) :
    μhat[(fun ω => f (shiftℤInv (α := α) ω))
        | shiftInvariantSigmaℤ (α := α)]
      =ᵐ[μhat] μhat[f | shiftInvariantSigmaℤ (α := α)] := by
  -- Key property: shiftInvariantSigmaℤ-measurable sets are shiftℤInv-invariant too
  -- Proof: If shiftℤ⁻¹' s = s then shiftℤInv⁻¹' s = s (since they're inverses)
  have h_inv : ∀ s, MeasurableSet[shiftInvariantSigmaℤ (α := α)] s →
      (shiftℤInv (α := α)) ⁻¹' s = s := by
    intro s hs
    -- hs.2 gives shiftℤ⁻¹' s = s
    -- Need: shiftℤInv⁻¹' s = s, i.e., ∀ ω, shiftℤInv ω ∈ s ↔ ω ∈ s
    ext ω
    constructor
    · -- shiftℤInv ω ∈ s → ω ∈ s
      intro h
      -- shiftℤInv ω ∈ s means ω = shiftℤ (shiftℤInv ω) ∈ shiftℤ '' s
      -- Since shiftℤ⁻¹' s = s, we have shiftℤ '' s = s (bijection)
      have hω' : shiftℤ (α := α) (shiftℤInv (α := α) ω) ∈ shiftℤ (α := α) '' s :=
        Set.mem_image_of_mem _ h
      simp only [shiftℤ_comp_shiftℤInv] at hω'
      -- Use that shiftℤ '' s = s (from shiftℤ⁻¹' s = s and bijectivity)
      have h_surj : shiftℤ (α := α) '' s = s := by
        ext x
        simp only [Set.mem_image, Set.mem_preimage]
        constructor
        · rintro ⟨y, hy, rfl⟩
          -- y ∈ s, want shiftℤ y ∈ s
          -- hs.2 : shiftℤ⁻¹' s = s means y ∈ s ↔ y ∈ shiftℤ⁻¹' s ↔ shiftℤ y ∈ s
          have h : y ∈ shiftℤ (α := α) ⁻¹' s := by rw [hs.2]; exact hy
          exact Set.mem_preimage.mp h
        · intro hx
          use shiftℤInv (α := α) x
          constructor
          · rw [← hs.2]
            simp [shiftℤ_comp_shiftℤInv, hx]
          · simp
      rw [h_surj] at hω'
      exact hω'
    · -- ω ∈ s → shiftℤInv ω ∈ s
      intro h
      -- ω ∈ s and shiftℤ⁻¹' s = s means shiftℤ⁻¹ ω ∈ s
      -- shiftℤ⁻¹' s = s means: ∀ x, shiftℤ x ∈ s ↔ x ∈ s
      -- Apply with x = shiftℤInv ω: shiftℤ (shiftℤInv ω) ∈ s ↔ shiftℤInv ω ∈ s
      rw [← hs.2]
      simp [h]
  -- Now prove the main result using ae_eq_condExp_of_forall_setIntegral_eq
  have hf_inv : Integrable (fun ω => f (shiftℤInv (α := α) ω)) μhat := by
    exact (hσInv.integrable_comp hf.aestronglyMeasurable).mpr hf
  symm
  apply MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq
    (shiftInvariantSigmaℤ_le (α := α))
  -- Integrability
  · exact hf_inv
  -- IntegrableOn for the condExp
  · intro s _ _
    exact MeasureTheory.integrable_condExp.integrableOn
  -- Set integral equality
  · intro s hs hμs
    rw [MeasureTheory.setIntegral_condExp (shiftInvariantSigmaℤ_le (α := α)) hf hs]
    -- Need: ∫_s (f ∘ shiftℤInv) = ∫_s f
    have h_s_inv : (shiftℤInv (α := α)) ⁻¹' s = s := h_inv s hs
    -- Use measure-preserving property
    rw [← MeasureTheory.integral_indicator (shiftInvariantSigmaℤ_le (α := α) s hs)]
    rw [← MeasureTheory.integral_indicator (shiftInvariantSigmaℤ_le (α := α) s hs)]
    -- Rewrite indicator: (1_s · f) ∘ shiftℤInv vs 1_s · (f ∘ shiftℤInv)
    -- Since shiftℤInv⁻¹' s = s, we have 1_s (shiftℤInv ω) = 1_s ω
    have h_ind : ∀ ω, s.indicator (fun ω => f (shiftℤInv (α := α) ω)) ω =
        s.indicator f (shiftℤInv (α := α) ω) := by
      intro ω
      simp only [Set.indicator]
      split_ifs with h1 h2 h2
      · rfl
      · exfalso
        rw [← Set.mem_preimage, h_s_inv] at h2
        exact h2 h1
      · exfalso
        rw [← h_s_inv] at h1
        exact h1 (Set.mem_preimage.mpr h2)
      · rfl
    rw [show (∫ x, s.indicator (fun ω => f (shiftℤInv (α := α) ω)) x ∂μhat) =
        (∫ x, s.indicator f (shiftℤInv (α := α) x) ∂μhat)
      from MeasureTheory.integral_congr_ae (ae_of_all μhat h_ind)]
    -- Now use measure-preserving: ∫ g ∘ T dμ = ∫ g dμ
    -- Since hσInv.map_eq : μhat.map shiftℤInv = μhat,
    -- we have ∫ g ∘ shiftℤInv dμhat = ∫ g d(μhat.map shiftℤInv) = ∫ g dμhat
    -- This is exactly ∫ (s.indicator f) ∘ shiftℤInv dμhat = ∫ s.indicator f dμhat
    have h_map_eq : Measure.map (shiftℤInv (α := α)) μhat = μhat := hσInv.map_eq
    have h_ae : AEStronglyMeasurable (s.indicator f) μhat := by
      refine (hf.aestronglyMeasurable.indicator ?_)
      exact shiftInvariantSigmaℤ_le (α := α) s hs
    -- Convert h_ae to AEStronglyMeasurable for the map measure
    have h_ae_map : AEStronglyMeasurable (s.indicator f) (μhat.map (shiftℤInv (α := α))) := by
      rw [h_map_eq]; exact h_ae
    rw [← MeasureTheory.integral_map measurable_shiftℤInv.aemeasurable h_ae_map, h_map_eq]
  -- AE strong measurability
  · exact MeasureTheory.stronglyMeasurable_condExp.aestronglyMeasurable

/-- Helper: Integrability of a bounded function on a finite measure space. -/
private lemma integrable_of_bounded_helper {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {f : Ω → ℝ} (hf : Measurable f) (hbd : ∃ C, ∀ ω, |f ω| ≤ C) :
    Integrable f μ := by
  obtain ⟨C, hC⟩ := hbd
  exact ⟨hf.aestronglyMeasurable, HasFiniteIntegral.of_bounded (ae_of_all μ hC)⟩

/-- Helper: Integrability of a bounded product on a finite measure space. -/
private lemma integrable_of_bounded_mul_helper
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ] [Nonempty Ω]
    {φ ψ : Ω → ℝ}
    (hφ_meas : Measurable φ) (hφ_bd : ∃ Cφ, ∀ ω, |φ ω| ≤ Cφ)
    (hψ_meas : Measurable ψ) (hψ_bd : ∃ Cψ, ∀ ω, |ψ ω| ≤ Cψ) :
    Integrable (fun ω => φ ω * ψ ω) μ := by
  classical
  obtain ⟨Cφ, hCφ⟩ := hφ_bd
  obtain ⟨Cψ, hCψ⟩ := hψ_bd
  have hCφ_nonneg : 0 ≤ Cφ := by
    have h := hCφ (Classical.arbitrary Ω)
    exact (abs_nonneg _).trans h
  have hCψ_nonneg : 0 ≤ Cψ := by
    have h := hCψ (Classical.arbitrary Ω)
    exact (abs_nonneg _).trans h
  have h_bound : ∀ ω, |φ ω * ψ ω| ≤ Cφ * Cψ := by
    intro ω
    have hφ := hCφ ω
    have hψ := hCψ ω
    have hmul :=
      mul_le_mul hφ hψ (abs_nonneg _) hCφ_nonneg
    simpa [abs_mul] using hmul
  have h_meas : Measurable fun ω => φ ω * ψ ω := hφ_meas.mul hψ_meas
  exact integrable_of_bounded_helper h_meas ⟨Cφ * Cψ, h_bound⟩

/-- Integrability of `f * g` when `g` is integrable and `|f| ≤ C`.

This shows that multiplying an integrable function by a bounded function preserves integrability.
The bound `|f * g| ≤ C * |g|` follows from `|f| ≤ C`. -/
lemma Integrable.of_abs_bounded {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f g : Ω → ℝ} (hg : Integrable g μ) (C : ℝ) (hC : 0 ≤ C)
    (h_bound : ∀ ω, |f ω| ≤ C)
    (hfg_meas : AEStronglyMeasurable (fun ω => f ω * g ω) μ) :
    Integrable (fun ω => f ω * g ω) μ := by
  have h_norm_bound : ∀ᵐ ω ∂μ, ‖f ω * g ω‖ ≤ C * ‖g ω‖ := by
    apply Filter.Eventually.of_forall
    intro ω
    simp only [Real.norm_eq_abs]
    calc |f ω * g ω| = |f ω| * |g ω| := abs_mul _ _
      _ ≤ C * |g ω| := mul_le_mul_of_nonneg_right (h_bound ω) (abs_nonneg _)
  -- Use Integrable.mono' with dominating function C * |g|
  refine Integrable.mono' (hg.norm.const_mul C) hfg_meas ?_
  filter_upwards with ω
  simp only [Real.norm_eq_abs, Pi.mul_apply, abs_of_nonneg hC]
  calc |f ω * g ω| = |f ω| * |g ω| := abs_mul _ _
    _ ≤ C * |g ω| := mul_le_mul_of_nonneg_right (h_bound ω) (abs_nonneg _)

/-- **Generalized lag-constancy for products** (extends `condexp_lag_constant_from_exchangeability`).

For EXCHANGEABLE measures μ on path space, if P = ∏_{i<n} f_i(ω_i) is a product of
the first n coordinates and g : α → ℝ is bounded measurable, then for k ≥ n:
  CE[P · g(ω_{k+1}) | mSI] = CE[P · g(ω_k) | mSI]

**Proof**: Uses transposition τ = swap(k, k+1). Since k ≥ n, τ fixes all indices < n.
Therefore P is unchanged by reindex τ, while g(ω_{k+1}) becomes g(ω_k).
Exchangeability then gives the result.

**Key insight**: This generalizes the pair case where P = f(ω_0) and n = 1. -/
lemma condexp_lag_constant_product
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α]
    {μ : Measure (ℕ → α)} [IsProbabilityMeasure μ]
    (hExch : ∀ π : Equiv.Perm ℕ, Measure.map (Exchangeability.reindex π) μ = μ)
    (n : ℕ) (fs : Fin n → α → ℝ)
    (hfs_meas : ∀ i, Measurable (fs i))
    (hfs_bd : ∀ i, ∃ C, ∀ x, |fs i x| ≤ C)
    (g : α → ℝ) (hg_meas : Measurable g) (hg_bd : ∃ Cg, ∀ x, |g x| ≤ Cg)
    (k : ℕ) (hk : n ≤ k) :
    μ[(fun ω => (∏ i : Fin n, fs i (ω i)) * g (ω (k + 1))) | shiftInvariantSigma (α := α)]
      =ᵐ[μ]
    μ[(fun ω => (∏ i : Fin n, fs i (ω i)) * g (ω k)) | shiftInvariantSigma (α := α)] := by
  -- Define the transposition τ = swap k (k+1)
  let τ := Equiv.swap k (k + 1)
  -- Define the two functions
  let P : (ℕ → α) → ℝ := fun ω => ∏ i : Fin n, fs i (ω i)
  let F := fun ω : ℕ → α => P ω * g (ω (k + 1))
  let G := fun ω : ℕ → α => P ω * g (ω k)

  -- Key fact 1: τ fixes all indices < n (since k ≥ n implies k, k+1 > n-1)
  have hτ_fix : ∀ i : Fin n, τ (i : ℕ) = i := by
    intro i
    have hi : (i : ℕ) < n := Fin.is_lt i
    have hik : (i : ℕ) ≠ k := by omega
    have hik1 : (i : ℕ) ≠ k + 1 := by omega
    exact Equiv.swap_apply_of_ne_of_ne hik hik1

  -- Key fact 2: P ∘ reindex τ = P (product unchanged since τ fixes all indices < n)
  have hP_inv : (P ∘ Exchangeability.reindex τ) = P := by
    ext ω
    simp only [Function.comp_apply, P, Exchangeability.reindex]
    apply Finset.prod_congr rfl
    intro i _
    -- Goal: fs i (ω (τ ↑i)) = fs i (ω ↑i)
    -- From hτ_fix: τ ↑i = ↑i
    simp only [hτ_fix i]

  -- Key fact 3: F ∘ reindex τ = G
  have hFG : F ∘ Exchangeability.reindex τ = G := by
    ext ω
    simp only [Function.comp_apply, F, G, Exchangeability.reindex]
    congr 1
    · -- P part: unchanged
      apply Finset.prod_congr rfl
      intro i _
      -- Need: fs i (ω (τ i)) = fs i (ω i)
      -- Since τ fixes i: τ (i : ℕ) = i
      show fs i (ω (τ i)) = fs i (ω i)
      rw [hτ_fix i]
    · -- g part: ω (τ (k+1)) = ω k
      rw [Equiv.swap_apply_right]

  -- Key fact 4: μ.map (reindex τ) = μ (exchangeability)
  have hμ_inv : Measure.map (Exchangeability.reindex τ) μ = μ := hExch τ

  -- Both F and G are integrable (products of bounded measurable functions)
  have hP_meas : Measurable P :=
    Finset.measurable_prod _ (fun i _ => (hfs_meas i).comp (measurable_pi_apply (i : ℕ)))

  -- Bound for the product P
  let CP := ∏ i : Fin n, (hfs_bd i).choose
  have hCP : ∀ ω, |P ω| ≤ CP := fun ω => by
    calc |P ω| = |∏ i : Fin n, fs i (ω i)| := rfl
      _ = ∏ i : Fin n, |fs i (ω i)| := Finset.abs_prod _ _
      _ ≤ ∏ i : Fin n, (hfs_bd i).choose := by
          apply Finset.prod_le_prod
          · intro i _; exact abs_nonneg _
          · intro i _; exact (hfs_bd i).choose_spec (ω i)

  obtain ⟨Cg, hCg⟩ := hg_bd

  have hF_meas : Measurable F := hP_meas.mul (hg_meas.comp (measurable_pi_apply (k + 1)))
  have hG_meas : Measurable G := hP_meas.mul (hg_meas.comp (measurable_pi_apply k))

  have hCP_nonneg : 0 ≤ CP := by
    -- CP = ∏ (hfs_bd i).choose ≥ 0 since each bound is ≥ 0
    -- Each (hfs_bd i).choose bounds |fs i x| ≥ 0, so it must be ≥ 0
    -- Need some element of α to instantiate x
    haveI : Nonempty (ℕ → α) := ProbabilityMeasure.nonempty ⟨μ, inferInstance⟩
    have ω : ℕ → α := Classical.choice ‹Nonempty (ℕ → α)›
    apply Finset.prod_nonneg
    intro i _
    exact le_trans (abs_nonneg _) ((hfs_bd i).choose_spec (ω 0))

  have hF_bd : ∀ ω, ‖F ω‖ ≤ CP * Cg := fun ω => by
    simp only [Real.norm_eq_abs]
    calc |F ω| = |P ω * g (ω (k + 1))| := rfl
      _ = |P ω| * |g (ω (k + 1))| := abs_mul _ _
      _ ≤ CP * Cg := mul_le_mul (hCP _) (hCg _) (abs_nonneg _) hCP_nonneg

  have hG_bd : ∀ ω, ‖G ω‖ ≤ CP * Cg := fun ω => by
    simp only [Real.norm_eq_abs]
    calc |G ω| = |P ω * g (ω k)| := rfl
      _ = |P ω| * |g (ω k)| := abs_mul _ _
      _ ≤ CP * Cg := mul_le_mul (hCP _) (hCg _) (abs_nonneg _) hCP_nonneg

  have hF_int : Integrable F μ := Integrable.of_bound hF_meas.aestronglyMeasurable (CP * Cg)
    (Filter.Eventually.of_forall hF_bd)
  have hG_int : Integrable G μ := Integrable.of_bound hG_meas.aestronglyMeasurable (CP * Cg)
    (Filter.Eventually.of_forall hG_bd)

  -- Strategy: Show ∫_s F = ∫_s G for all s ∈ mSI, then μ[F|mSI] = μ[G|mSI]
  have hτ_meas : Measurable (Exchangeability.reindex (α := α) τ) :=
    Exchangeability.measurable_reindex (α := α) (π := τ)

  have h_int_eq : ∀ s, MeasurableSet[shiftInvariantSigma (α := α)] s → μ s < ⊤ →
      ∫ ω in s, F ω ∂μ = ∫ ω in s, G ω ∂μ := fun s hs _ => by
    have hs_inv : isShiftInvariant (α := α) s := (mem_shiftInvariantSigma_iff (α := α)).mp hs
    exact setIntegral_eq_of_reindex_eq τ hμ_inv F G hFG hF_meas s hs_inv.1
      (reindex_swap_preimage_shiftInvariant k s hs_inv)

  -- Show ∫_s (F - G) = 0 for all s ∈ mSI
  have h_diff_zero : ∀ s, MeasurableSet[shiftInvariantSigma (α := α)] s → μ s < ⊤ →
      ∫ ω in s, (F - G) ω ∂μ = 0 := fun s hs hμs => by
    simp only [Pi.sub_apply, integral_sub hF_int.integrableOn hG_int.integrableOn,
               h_int_eq s hs hμs, sub_self]

  exact condExp_ae_eq_of_setIntegral_diff_eq_zero hF_int hG_int h_diff_zero

/-- **Generalized lag constancy for products at arbitrary coordinates**.

This extends `condexp_lag_constant_product` to products at general coordinates k_0, ..., k_{n-1}.
For j, j+1 both larger than all k_i, the transposition τ = swap(j, j+1) fixes all coordinates
in the product, so the conditional expectation is unchanged.

**Key observation**: If M = max(k_i) + 1, then for all j ≥ M:
- τ = swap(j, j+1) fixes all indices 0, 1, ..., j-1
- In particular, τ fixes all k_i (since k_i < M ≤ j)
- Therefore P ∘ reindex τ = P
- And the lag constancy argument applies -/
lemma condexp_lag_constant_product_general
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α]
    {μ : Measure (ℕ → α)} [IsProbabilityMeasure μ]
    (hExch : ∀ π : Equiv.Perm ℕ, Measure.map (Exchangeability.reindex π) μ = μ)
    (n : ℕ) (fs : Fin n → α → ℝ) (coords : Fin n → ℕ)
    (hfs_meas : ∀ i, Measurable (fs i))
    (hfs_bd : ∀ i, ∃ C, ∀ x, |fs i x| ≤ C)
    (g : α → ℝ) (hg_meas : Measurable g) (hg_bd : ∃ Cg, ∀ x, |g x| ≤ Cg)
    (j : ℕ) (hj : ∀ i : Fin n, coords i < j) :
    μ[(fun ω => (∏ i : Fin n, fs i (ω (coords i))) * g (ω (j + 1))) | shiftInvariantSigma (α := α)]
      =ᵐ[μ]
    μ[(fun ω => (∏ i : Fin n, fs i (ω (coords i))) * g (ω j)) | shiftInvariantSigma (α := α)] := by
  -- Define the transposition τ = swap j (j+1)
  let τ := Equiv.swap j (j + 1)
  -- Define the product P at coordinates
  let P : (ℕ → α) → ℝ := fun ω => ∏ i : Fin n, fs i (ω (coords i))
  let F := fun ω : ℕ → α => P ω * g (ω (j + 1))
  let G := fun ω : ℕ → α => P ω * g (ω j)

  -- Key fact 1: τ fixes all coords(i) (since coords(i) < j and τ swaps j, j+1)
  have hτ_fix : ∀ i : Fin n, τ (coords i) = coords i := by
    intro i
    have hi : coords i < j := hj i
    have hne1 : coords i ≠ j := by omega
    have hne2 : coords i ≠ j + 1 := by omega
    exact Equiv.swap_apply_of_ne_of_ne hne1 hne2

  -- Key fact 2: P ∘ reindex τ = P (product unchanged since τ fixes all coords)
  have hP_inv : (P ∘ Exchangeability.reindex τ) = P := by
    ext ω
    simp only [Function.comp_apply, P, Exchangeability.reindex]
    apply Finset.prod_congr rfl
    intro i _
    simp only [hτ_fix i]

  -- Key fact 3: τ(j+1) = j and τ(j) = j+1
  have hτ_j1 : τ (j + 1) = j := Equiv.swap_apply_right j (j + 1)
  have hτ_j : τ j = j + 1 := Equiv.swap_apply_left j (j + 1)

  -- Key fact 4: F ∘ reindex τ = G
  have hFG : (F ∘ Exchangeability.reindex τ) = G := by
    ext ω
    simp only [Function.comp_apply, F, G, Exchangeability.reindex]
    congr 1
    · -- P part
      simp only [P]
      apply Finset.prod_congr rfl
      intro i _
      show fs i (ω (τ (coords i))) = fs i (ω (coords i))
      rw [hτ_fix i]
    · -- g part
      show g (ω (τ (j + 1))) = g (ω j)
      rw [hτ_j1]

  -- Integrability bounds
  have hP_bd : ∃ Cp, ∀ ω, |P ω| ≤ Cp := by
    choose Cs hCs using hfs_bd
    use ∏ i : Fin n, Cs i
    intro ω
    calc |P ω| = |∏ i : Fin n, fs i (ω (coords i))| := rfl
      _ = ∏ i : Fin n, |fs i (ω (coords i))| := Finset.abs_prod _ _
      _ ≤ ∏ i : Fin n, Cs i := by
          apply Finset.prod_le_prod
          · intro i _; exact abs_nonneg _
          · intro i _; exact hCs i (ω (coords i))

  obtain ⟨Cp, hCp⟩ := hP_bd
  obtain ⟨Cg, hCg⟩ := hg_bd

  have hP_meas : Measurable P := by
    apply Finset.measurable_prod
    intro i _
    exact (hfs_meas i).comp (measurable_pi_apply (coords i))

  have hCp_nonneg : 0 ≤ Cp := by
    haveI : Nonempty (ℕ → α) := ProbabilityMeasure.nonempty ⟨μ, inferInstance⟩
    have ω : ℕ → α := Classical.choice ‹Nonempty (ℕ → α)›
    exact le_trans (abs_nonneg _) (hCp ω)

  have hF_meas : Measurable F := hP_meas.mul (hg_meas.comp (measurable_pi_apply (j + 1)))
  have hF_bd : ∀ ω, ‖F ω‖ ≤ Cp * Cg := fun ω => by
    simp only [Real.norm_eq_abs, F]
    calc |P ω * g (ω (j + 1))| = |P ω| * |g (ω (j + 1))| := abs_mul _ _
      _ ≤ Cp * Cg := mul_le_mul (hCp _) (hCg _) (abs_nonneg _) hCp_nonneg
  have hF_int : Integrable F μ := Integrable.of_bound hF_meas.aestronglyMeasurable (Cp * Cg)
    (Filter.Eventually.of_forall hF_bd)

  have hG_meas : Measurable G := hP_meas.mul (hg_meas.comp (measurable_pi_apply j))
  have hG_bd : ∀ ω, ‖G ω‖ ≤ Cp * Cg := fun ω => by
    simp only [Real.norm_eq_abs, G]
    calc |P ω * g (ω j)| = |P ω| * |g (ω j)| := abs_mul _ _
      _ ≤ Cp * Cg := mul_le_mul (hCp _) (hCg _) (abs_nonneg _) hCp_nonneg
  have hG_int : Integrable G μ := Integrable.of_bound hG_meas.aestronglyMeasurable (Cp * Cg)
    (Filter.Eventually.of_forall hG_bd)

  -- μ.map (reindex τ) = μ (exchangeability)
  have hμ_inv : Measure.map (Exchangeability.reindex τ) μ = μ := hExch τ

  -- Now apply the exchange argument (same pattern as condexp_lag_constant_product)
  have h_int_eq : ∀ s, MeasurableSet[shiftInvariantSigma (α := α)] s → μ s < ⊤ →
      ∫ ω in s, F ω ∂μ = ∫ ω in s, G ω ∂μ := fun s hs _ => by
    have hs_inv : isShiftInvariant (α := α) s := (mem_shiftInvariantSigma_iff (α := α)).mp hs
    exact setIntegral_eq_of_reindex_eq τ hμ_inv F G hFG hF_meas s hs_inv.1
      (reindex_swap_preimage_shiftInvariant j s hs_inv)

  have h_diff_zero : ∀ (s : Set (ℕ → α)), MeasurableSet[shiftInvariantSigma (α := α)] s
      → μ s < ⊤ →
      ∫ ω in s, (F - G) ω ∂μ = 0 := fun s hs hμs => by
    simp only [Pi.sub_apply, integral_sub hF_int.integrableOn hG_int.integrableOn,
               h_int_eq s hs hμs, sub_self]

  exact condExp_ae_eq_of_setIntegral_diff_eq_zero hF_int hG_int h_diff_zero

end Exchangeability.DeFinetti.ViaKoopman

