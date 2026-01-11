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
  |x / y| = |x| / y := by simp [abs_div, abs_of_nonneg hy]

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
lemma measurable_restrictNonneg : Measurable (restrictNonneg (α := α)) :=
  measurable_pi_lambda _ fun n => measurable_pi_apply (Int.ofNat n)

@[measurability, fun_prop]
lemma measurable_shiftℤ : Measurable (shiftℤ (α := α)) :=
  measurable_pi_lambda _ fun n => measurable_pi_apply (n + 1)

@[measurability, fun_prop]
lemma measurable_shiftℤInv : Measurable (shiftℤInv (α := α)) :=
  measurable_pi_lambda _ fun n => measurable_pi_apply (n - 1)

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

omit [MeasurableSpace Ω] [MeasurableSpace Ω'] in
/-- Indicator pulls through a preimage under composition. -/
lemma indicator_preimage_comp {B : Set Ω} (K : Ω → ℝ) :
    (Set.indicator (g ⁻¹' B) (K ∘ g))
  = (fun x' => Set.indicator B K (g x')) := by
  ext x'; by_cases hx : g x' ∈ B <;> simp [Set.indicator, hx]

end Helpers

/-! ## Infrastructure Lemmas for Conditional Expectation Pullback

This section contains infrastructure lemmas needed for the Koopman approach to de Finetti's
theorem. These lemmas handle the interaction between conditional expectation, factor maps, and
measure-preserving transformations.

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

/-- CE is a.e.-strongly measurable w.r.t. the *sub* σ-algebra, with ambient locked. -/
lemma aestronglyMeasurable_condExp'
    {Ω β} [mΩ : MeasurableSpace Ω] [NormedAddCommGroup β] [NormedSpace ℝ β] [CompleteSpace β]
    {μ : Measure Ω} (m : MeasurableSpace Ω) (_hm : m ≤ mΩ)
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
    ∀ x, |s.indicator f x| ≤ |f x| := fun x => by
  by_cases hx : x ∈ s <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx, abs_nonneg]

lemma norm_indicator_le_norm_self
    {Ω E} [SeminormedAddCommGroup E] (s : Set Ω) (f : Ω → E) :
    ∀ x, ‖s.indicator f x‖ ≤ ‖f x‖ := fun x => by
  by_cases hx : x ∈ s <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx]

/-- Indicator ↔ product with a 0/1 mask (for ℝ). -/
lemma indicator_as_mul_one {Ω} (s : Set Ω) (f : Ω → ℝ) :
    s.indicator f = fun x => f x * s.indicator (fun _ => (1 : ℝ)) x := by
  ext x; by_cases hx : x ∈ s <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx]

lemma integral_indicator_as_mul {Ω} [MeasurableSpace Ω] {μ : Measure Ω}
    (s : Set Ω) (f : Ω → ℝ) :
    ∫ x, s.indicator f x ∂μ = ∫ x, f x * s.indicator (fun _ => (1 : ℝ)) x ∂μ := by
  simp [indicator_as_mul_one s f]

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

**Note**: Mathlib API candidates for this standard result:
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

end Exchangeability.DeFinetti.ViaKoopman
