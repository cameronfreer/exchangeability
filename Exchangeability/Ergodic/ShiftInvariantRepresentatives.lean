/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Data.EReal.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Function.AEEqFun
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Exchangeability.Ergodic.ShiftInvariantSigma

/-!
# Shift-invariant representatives via limsup construction

This file constructs canonical shift-invariant representatives for functions that are
almost shift-invariant (i.e., `g ∘ shift = g` a.e.).

## Main definitions

* `gRep`: Canonical shift-invariant representative via limsup along the orbit.
* `mkShiftInvariantRep`: Given an a.e. shift-invariant function, construct a representative
  that is literally shift-invariant and measurable with respect to `shiftInvariantSigma`.
* `exists_shiftInvariantRepresentative`: Existence theorem for shift-invariant representatives.

## Main results

* `gRep_measurable`: The limsup representative is measurable.
* `gRep_shiftInvariant`: The limsup representative is pointwise shift-invariant.
* `gRep_ae_eq_of_constant_orbit`: The representative agrees with the original a.e.
* `exists_shiftInvariantFullMeasureSet`: Construction of shift-invariant full-measure sets.

## Mathematical idea

For each `ω`, consider the orbit sequence `g0(ω), g0(shift ω), g0(shift² ω), ...`.
If `g0` is almost invariant, then this sequence is eventually constant on a full-measure set.
Taking the limsup gives a well-defined function that is:
1. **Shift-invariant**: `gRep g0 (shift ω) = gRep g0 ω` for all `ω` (not just a.e.)
2. **Measurable**: Inherits measurability from `g0`
3. **Almost equal**: `gRep g0 =ᵐ[μ] g0` when `g0` is almost invariant

This construction avoids the Axiom of Choice by using a canonical limit process rather than
selecting arbitrary representatives from equivalence classes.

## References

* Olav Kallenberg (2005), *Probabilistic Symmetries and Invariance Principles*,
  Springer, Chapter 1.

-/

noncomputable section

open scoped Classical Topology

namespace Exchangeability.DeFinetti

open MeasureTheory Filter Topology
open Exchangeability.PathSpace

variable {α : Type*} [MeasurableSpace α]

/-! ### Limsup construction for shift-invariant representatives

Given a function `g0 : Ω[α] → ℝ` that is almost shift-invariant
(i.e., `g0 ∘ shift = g0` a.e.), we construct a pointwise shift-invariant
representative `gRep g0` using a limsup along the orbit.

**Key property**: If `g0 (shift^[n] ω) = g0 ω` for all `n`, then `gRep g0 ω = g0 ω`.
-/
section LimsupConstruction

/-- **Limsup along shift orbit (extended real valued).**

For a function `g0 : Ω[α] → ℝ`, this computes the limsup of the sequence
`g0(ω), g0(shift ω), g0(shift² ω), ...` in the extended reals.

This is the first step in constructing a shift-invariant representative.
-/
private def gLimsupE (g0 : Ω[α] → ℝ) (ω : Ω[α]) : EReal :=
  limsup (fun n : ℕ => (g0 (shift^[n] ω) : EReal)) atTop

/-- **Canonical shift-invariant representative via limsup.**

Given `g0 : Ω[α] → ℝ`, this constructs a shift-invariant function `gRep g0` by taking
the limsup along the shift orbit and converting back to ℝ.

**Properties**:
- If `g0` is measurable, so is `gRep g0` (see `gRep_measurable`)
- `gRep g0 (shift ω) = gRep g0 ω` for all `ω` (see `gRep_shiftInvariant`)
- If `g0 (shift^[n] ω) = g0 ω` for all `n`, then `gRep g0 ω = g0 ω`
  (see `gRep_eq_of_constant_orbit`)
- If `g0 ∘ shift =ᵐ[μ] g0`, then `gRep g0 =ᵐ[μ] g0`
  (see `gRep_ae_eq_of_constant_orbit`)
-/
def gRep (g0 : Ω[α] → ℝ) : Ω[α] → ℝ :=
  fun ω => (gLimsupE g0 ω).toReal


lemma gRep_measurable {g0 : Ω[α] → ℝ} (hg0 : Measurable g0) :
    Measurable (gRep g0) := by
  have hstep : ∀ n : ℕ, Measurable fun ω => (g0 (shift^[n] ω) : EReal) := by
    intro n
    have hreal : Measurable fun ω => g0 (shift^[n] ω) :=
      hg0.comp (shift_iterate_measurable (α := α) n)
    exact measurable_coe_real_ereal.comp hreal
  have h_meas_ereal : Measurable fun ω => gLimsupE g0 ω := by
    simpa [gLimsupE] using (Measurable.limsup hstep)
  have : Measurable fun ω => (gLimsupE g0 ω).toReal := by
    fun_prop
  simpa [gRep, gLimsupE] using this

omit [MeasurableSpace α] in
lemma gRep_shiftInvariant {g0 : Ω[α] → ℝ} :
    ∀ ω, gRep g0 (shift ω) = gRep g0 ω := by
  intro ω
  have hlimsupEq :
      limsup (fun n : ℕ => (g0 (shift^[n + 1] ω) : EReal)) atTop
        = limsup (fun n : ℕ => (g0 (shift^[n] ω) : EReal)) atTop := by
    simpa [Function.iterate_succ_apply, Nat.succ_eq_add_one]
      using (limsup_nat_add (fun n => (g0 (shift^[n] ω) : EReal)) 1)
  simpa [gRep, gLimsupE, Function.iterate_succ_apply, Nat.succ_eq_add_one]
    using congrArg EReal.toReal hlimsupEq

omit [MeasurableSpace α] in
lemma gRep_eq_of_constant_orbit {g0 : Ω[α] → ℝ} {ω : Ω[α]}
    (hconst : ∀ n : ℕ, g0 (shift^[n] ω) = g0 ω) :
    gRep g0 ω = g0 ω := by
  have hlim :
      limsup (fun n : ℕ => (g0 (shift^[n] ω) : EReal)) atTop
        = (g0 ω : EReal) := by
    have hfunext :
        (fun n : ℕ => (g0 (shift^[n] ω) : EReal))
          = fun _ => (g0 ω : EReal) := by
      funext n; simpa using congrArg (fun y : ℝ => (y : EReal)) (hconst n)
    simp [hfunext, limsup_const]
  simpa [gRep, gLimsupE] using congrArg EReal.toReal hlim

lemma gRep_ae_eq_of_constant_orbit {g0 : Ω[α] → ℝ}
    {μ : Measure (Ω[α])}
    (hconst : ∀ᵐ ω ∂μ, ∀ n : ℕ, g0 (shift^[n] ω) = g0 ω) :
    gRep g0 =ᵐ[μ] g0 := by
  classical
  filter_upwards [hconst] with ω hω
  exact gRep_eq_of_constant_orbit (g0 := g0) hω


lemma ae_shift_invariance_on_rep
    {μ : Measure (Ω[α])} [IsProbabilityMeasure μ]
    (hσ : MeasurePreserving shift μ μ)
    {f g : Ω[α] → ℝ}
    (hfg : g =ᵐ[μ] f)
    (hshift : (fun ω => f (shift ω)) =ᵐ[μ] f) :
    (fun ω => g (shift ω)) =ᵐ[μ] g := by
  classical
  have h1 : (fun ω => g (shift ω)) =ᵐ[μ] fun ω => f (shift ω) := by
    simpa [Function.comp] using
      (hσ.quasiMeasurePreserving.ae_eq_comp (μ := μ) (ν := μ)
        (f := shift) (g := g) (g' := f) hfg)
  have h2 : (fun ω => f (shift ω)) =ᵐ[μ] f := by
    simpa [Function.comp] using hshift
  have h3 : f =ᵐ[μ] g := hfg.symm
  exact h1.trans (h2.trans h3)

end LimsupConstruction

/-! ### Construction of shift-invariant representatives

The main challenge in working with shift-invariant functions is that almost-everywhere
equality `g ∘ shift =ᵐ[μ] g` doesn't immediately give a pointwise invariant function.

**Goal**: Given `g : Ω[α] → ℝ` with `g ∘ shift =ᵐ[μ] g`, construct
`g' : Ω[α] → ℝ` such that:
1. `g' (shift ω) = g' ω` for ALL `ω` (pointwise, not just a.e.)
2. `g' =ᵐ[μ] g` (almost equal to the original)
3. `g'` is measurable with respect to `shiftInvariantSigma`

**Strategy**:
1. Find a shift-invariant full-measure set `S` where `g` is constant along orbits
2. Use `gRep` to construct a pointwise invariant representative
3. Prove the representative agrees with `g` almost everywhere

This avoids Choice by using the canonical `gRep` construction instead of selecting
arbitrary representatives.
-/

/-- **Existence of shift-invariant full-measure sets.**

Build a shift-invariant full-measure set on which `g ∘ shift = g` holds pointwise.
The construction iterates the equality set and intersects all pullbacks to obtain a
forward-invariant set on which the equality holds everywhere. -/
private lemma exists_shiftInvariantFullMeasureSet
    {μ : Measure (Ω[α])} [IsProbabilityMeasure μ]
    (hσ : MeasurePreserving shift μ μ)
    (g : Ω[α] → ℝ) (hg : Measurable g)
    (hinv : (fun ω => g (shift ω)) =ᵐ[μ] g) :
    ∃ Sinf : Set (Ω[α]),
      MeasurableSet Sinf ∧
      μ (symmDiff (shift ⁻¹' Sinf) Sinf) = 0 ∧
      μ Sinfᶜ = 0 ∧
      Sinf ⊆ shift ⁻¹' Sinf ∧
      ∀ ω ∈ Sinf, g (shift ω) = g ω := by
  classical
  -- Build the basic equality set where the orbit agrees pointwise.
  set S0 : Set (Ω[α]) := {ω | g (shift ω) = g ω} with hS0_def

  -- This set is measurable because it arises as the `{0}`-preimage of a measurable function.
  have hS0_meas : MeasurableSet S0 := by
    have hdiff : Measurable fun ω => g (shift ω) - g ω :=
      (hg.comp measurable_shift).sub hg
    have hsingleton : MeasurableSet ({0} : Set ℝ) := by
      simp
    have :
        MeasurableSet ((fun ω => g (shift ω) - g ω) ⁻¹' ({0} : Set ℝ)) :=
      hdiff hsingleton
    simpa [S0, Set.preimage, Set.mem_setOf_eq, Set.mem_singleton_iff, sub_eq_zero] using this

  -- `S0` has full measure thanks to the `ae` equality.
  have hS0_full : μ S0ᶜ = 0 := by
    have hS0_ae : ∀ᵐ ω ∂μ, g (shift ω) = g ω := hinv
    simpa [S0, ae_iff] using hS0_ae

  -- All forward preimages of `S0` also have full measure via measure-preservation.
  have hpre_full : ∀ n : ℕ, μ (((shift^[n]) ⁻¹' S0)ᶜ) = 0 := by
    intro n
    have hσn : MeasurePreserving (shift^[n]) μ μ := hσ.iterate n
    have hpre : μ ((shift^[n]) ⁻¹' S0ᶜ) = μ S0ᶜ := by
      rw [hσn.measure_preimage hS0_meas.compl.nullMeasurableSet]
    simpa [Set.preimage_compl] using hpre.trans hS0_full

  -- Intersect the forward preimages to obtain a forward-invariant full-measure set.
  set Sinf : Set (Ω[α]) := ⋂ n : ℕ, (shift^[n]) ⁻¹' S0 with hSinf_def

  have hSinf_meas : MeasurableSet Sinf := by
    refine MeasurableSet.iInter ?_;
    intro n
    simpa using (shift_iterate_measurable (α := α) n) hS0_meas

  have hSinf_full : μ Sinfᶜ = 0 := by
    have h_forall : ∀ n : ℕ, ∀ᵐ ω ∂μ, ω ∈ (shift^[n]) ⁻¹' S0 := by
      intro n
      have : μ (((shift^[n]) ⁻¹' S0)ᶜ) = 0 := hpre_full n
      simpa [ae_iff] using this
    have hSinf_ae : ∀ᵐ ω ∂μ, ω ∈ Sinf := by
      simpa [Sinf, hSinf_def, Set.mem_iInter] using (ae_all_iff.mpr h_forall)
    simpa [ae_iff] using hSinf_ae

  -- Close the forward-invariant set under further pullbacks to target exact invariance.
  set Sstar : Set (Ω[α]) := ⋂ k : ℕ, (shift^[k]) ⁻¹' Sinf with hSstar_def

  have hSstar_meas : MeasurableSet Sstar := by
    refine MeasurableSet.iInter ?_;
    intro k
    simpa using (shift_iterate_measurable (α := α) k) hSinf_meas

  have hSstar_full : μ Sstarᶜ = 0 := by
    have h_forall : ∀ k : ℕ, ∀ᵐ ω ∂μ, ω ∈ (shift^[k]) ⁻¹' Sinf := by
      intro k
      have hσk : MeasurePreserving (shift^[k]) μ μ := hσ.iterate k
      have hpre : μ ((shift^[k]) ⁻¹' Sinfᶜ) = μ Sinfᶜ := by
        rw [hσk.measure_preimage hSinf_meas.compl.nullMeasurableSet]
      have : μ (((shift^[k]) ⁻¹' Sinf)ᶜ) = 0 := by
        simpa [Set.preimage_compl] using hpre.trans hSinf_full
      simpa [ae_iff] using this
    have hSstar_ae : ∀ᵐ ω ∂μ, ω ∈ Sstar := by
      simpa [Sstar, hSstar_def, Set.mem_iInter] using (ae_all_iff.mpr h_forall)
    simpa [ae_iff] using hSstar_ae

  -- Membership in `Sstar` ensures all forward iterates land back in `Sinf`.
  have hSstar_mem_Sinf : ∀ {ω}, ω ∈ Sstar → ω ∈ Sinf := by
    intro ω hω
    have hmem : ∀ k : ℕ, ω ∈ (shift^[k]) ⁻¹' Sinf := by
      simpa [Sstar, hSstar_def, Set.mem_iInter] using hω
    have hzero : ω ∈ (shift^[0]) ⁻¹' Sinf := hmem 0
    simpa [Function.iterate_zero, Set.preimage_id] using hzero

  -- Forward invariance: points in `Sstar` stay inside under the shift.
  have hSstar_forward : Sstar ⊆ shift ⁻¹' Sstar := by
    intro ω hω
    have hmem : ∀ k : ℕ, shift^[k] ω ∈ Sinf := by
      simpa [Sstar, hSstar_def, Set.mem_iInter, Set.mem_preimage] using hω
    have hshift_mem : ∀ k : ℕ, shift^[k] (shift ω) ∈ Sinf := by
      intro k
      have hk : shift^[k.succ] ω ∈ Sinf := hmem (Nat.succ k)
      simpa [Function.iterate_succ_apply, Nat.succ_eq_add_one] using hk
    have hshift : shift ω ∈ Sstar := by
      simpa [Sstar, hSstar_def, Set.mem_iInter, Set.mem_preimage, Function.iterate_succ_apply]
        using hshift_mem
    simpa [Set.mem_preimage] using hshift

  -- Pointwise equality holds on `Sstar` thanks to the base case in `Sinf`.
  have hSstar_pointwise : ∀ ω ∈ Sstar, g (shift ω) = g ω := by
    intro ω hω
    have hω_Sinf : ω ∈ Sinf := hSstar_mem_Sinf hω
    have hω_S0 : ω ∈ S0 := by
      have hmem : ∀ n : ℕ, ω ∈ (shift^[n]) ⁻¹' S0 := by
        simpa [Sinf, hSinf_def, Set.mem_iInter] using hω_Sinf
      have hzero : ω ∈ (shift^[0]) ⁻¹' S0 := hmem 0
      simpa [Function.iterate_zero, Set.preimage_id] using hzero
    simpa [S0, Set.mem_setOf_eq] using hω_S0

  -- The symmetric difference between `Sstar` and its pullback has measure zero.
  have hSstar_symmDiff_zero :
      μ (symmDiff (shift ⁻¹' Sstar) Sstar) = 0 := by
    have hsubset_diff : ((shift ⁻¹' Sstar) \ Sstar) ⊆ Sstarᶜ := by
      intro ω hω; exact hω.2
    have hmeasure_diff : μ ((shift ⁻¹' Sstar) \ Sstar) = 0 :=
      measure_mono_null hsubset_diff hSstar_full
    have hsubset : Sstar ⊆ shift ⁻¹' Sstar := hSstar_forward
    have hzero : Sstar \ shift ⁻¹' Sstar = (∅ : Set (Ω[α])) := by
      ext ω; constructor
      · intro hω
        have : ω ∈ shift ⁻¹' Sstar := hsubset hω.1
        exact False.elim (hω.2 this)
      · intro hω; simpa using hω.elim
    have hsymm :
        symmDiff (shift ⁻¹' Sstar) Sstar
          = ((shift ⁻¹' Sstar) \ Sstar) ∪ (Sstar \ shift ⁻¹' Sstar) := rfl
    simpa [hsymm, hzero] using hmeasure_diff

  -- Package all components.
  refine ⟨Sstar, hSstar_meas, hSstar_symmDiff_zero, hSstar_full, hSstar_forward,
    hSstar_pointwise⟩

/-- Given an `AEStronglyMeasurable` function whose shift agrees with it almost
everywhere, construct a representative that is literally shift-invariant and
measurable with respect to the invariant σ-algebra. -/
lemma mkShiftInvariantRep
    {μ : Measure (Ω[α])} [IsProbabilityMeasure μ]
    (hσ : MeasurePreserving shift μ μ)
    (g : Ω[α] → ℝ) (hg : AEStronglyMeasurable g μ)
    (hshift : (fun ω => g (shift ω)) =ᵐ[μ] g) :
    ∃ g',
      AEStronglyMeasurable[shiftInvariantSigma (α := α)] g' μ ∧
      (∀ᵐ ω ∂μ, g' ω = g ω) ∧
      (∀ ω, g' (shift ω) = g' ω) := by
  classical
  rcases hg with ⟨g0, hg0_sm, hg0_ae⟩
  have hshift_g0 : (fun ω => g0 (shift ω)) =ᵐ[μ] g0 :=
    ae_shift_invariance_on_rep (μ := μ) hσ hg0_ae.symm hshift
  have hg0_meas : Measurable g0 := hg0_sm.measurable
  obtain ⟨S, hS_meas, _hSymm, hS_null, hS_subset, hS_point⟩ :=
    exists_shiftInvariantFullMeasureSet (μ := μ) hσ g0 hg0_meas hshift_g0
  have hforward : ∀ ω ∈ S, shift ω ∈ S := by
    intro ω hω
    have : ω ∈ shift ⁻¹' S := hS_subset hω
    simpa [Set.mem_preimage] using this
  have hS_ae : ∀ᵐ ω ∂μ, ω ∈ S := by
    simpa [ae_iff] using hS_null
  have hconst_on_S : ∀ ω ∈ S, ∀ n : ℕ, g0 (shift^[n] ω) = g0 ω := by
    intro ω hω
    have hmem : ∀ n : ℕ, shift^[n] ω ∈ S := by
      intro n
      induction n with
      | zero => simp [Function.iterate_zero_apply]; exact hω
      | succ n ih =>
        have := hforward _ ih
        simp only [Function.iterate_succ_apply']
        exact this
    refine Nat.rec (by simp [Function.iterate_zero_apply]) ?_
    intro n ih
    have hstep : g0 (shift^[n.succ] ω) = g0 (shift^[n] ω) := by
      have := hS_point (shift^[n] ω) (hmem n)
      simp only [Function.iterate_succ_apply']
      exact this
    exact hstep.trans ih
  have hconst : ∀ᵐ ω ∂μ, ∀ n : ℕ, g0 (shift^[n] ω) = g0 ω := by
    filter_upwards [hS_ae] with ω hω using hconst_on_S ω hω
  let g' := gRep g0
  have hg'_meas : Measurable g' :=
    gRep_measurable (α := α) (g0 := g0) hg0_meas
  have hg'_ae_g0 : g' =ᵐ[μ] g0 := gRep_ae_eq_of_constant_orbit (g0 := g0) hconst
  have hg'_inv : ∀ ω, g' (shift ω) = g' ω :=
    gRep_shiftInvariant (α := α) (g0 := g0)
  have hg'_tail : Measurable[shiftInvariantSigma (α := α)] g' :=
    shiftInvariant_implies_shiftInvariantMeasurable (α := α) g' hg'_meas hg'_inv
  refine ⟨g', hg'_tail.aestronglyMeasurable, ?_, hg'_inv⟩
  exact hg'_ae_g0.trans hg0_ae.symm

/-- Main construction: given a function that agrees with its shift a.e.,
    produce a shift-invariant representative. -/
lemma exists_shiftInvariantRepresentative
    {μ : Measure (Ω[α])} [IsProbabilityMeasure μ]
    (hσ : MeasurePreserving shift μ μ)
    (g : Ω[α] → ℝ)
    (hg : AEStronglyMeasurable g μ)
    (hinv : (fun ω => g (shift ω)) =ᵐ[μ] g) :
    ∃ g',
      AEStronglyMeasurable[shiftInvariantSigma (α := α)] g' μ ∧
      (∀ᵐ ω ∂μ, g' ω = g ω) ∧
      (∀ ω, g' (shift ω) = g' ω) := by
  classical
  simpa using mkShiftInvariantRep (μ := μ) hσ g hg hinv

end Exchangeability.DeFinetti
