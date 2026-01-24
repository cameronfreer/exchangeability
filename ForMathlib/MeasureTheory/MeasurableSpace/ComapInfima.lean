/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.MeasureTheory.MeasurableSpace.Basic

open MeasureTheory

/-!
# Comap and Infima of Measurable Spaces

This file provides lemmas about how `MeasurableSpace.comap` interacts with infima (`⨅`).

## Main Results

* `iInf_comap_eq_comap_iInf_of_surjective`: With a surjective function `f` and nonempty index type,
  `comap` commutes with `⨅`:
  ```
  ⨅ i, MeasurableSpace.comap f (m i) = MeasurableSpace.comap f (⨅ i, m i)
  ```

## Supporting Lemmas

* `preimage_injective_of_surjective`: Preimage is injective on sets when `f` is surjective
* `map_comap_eq_of_surjective`: If `f` is surjective, then `map f (comap f m) = m`
* `comap_iInf_le`: The inequality `comap f (⨅ i, m i) ≤ ⨅ i, comap f (m i)` holds unconditionally

## Mathematical Context

The main result is crucial for proving that tail σ-algebras on path space can be characterized
either as pullbacks of the path-space tail, or as infima of coordinate-wise σ-algebras.

## Suggested Mathlib Location

`Mathlib.MeasureTheory.MeasurableSpace.Basic` (near existing comap/map API)

## References

* Kallenberg (2005), *Probabilistic Symmetries and Invariance Principles*
-/

namespace MeasurableSpace

/-- Preimage is injective on sets when `f` is surjective. -/
lemma preimage_injective_of_surjective {α β : Type*} {f : α → β}
    (hf : Function.Surjective f) :
    Function.Injective (fun (s : Set β) => f ⁻¹' s) :=
  hf.preimage_injective

/-- If `f` is surjective, then `map f (comap f m) = m`. -/
lemma map_comap_eq_of_surjective {α β : Type*} {f : α → β}
    (hf : Function.Surjective f) (m : MeasurableSpace β) :
    MeasurableSpace.map f (MeasurableSpace.comap f m) = m := by
  classical
  ext S; constructor
  · intro hS
    change MeasurableSet[MeasurableSpace.comap f m] (f ⁻¹' S) at hS
    rcases hS with ⟨T, hT, hpre⟩
    have hinj := preimage_injective_of_surjective (α := α) (β := β) hf
    have : S = T := by apply hinj; exact hpre.symm
    simpa [this]
  · intro hS
    change MeasurableSet[MeasurableSpace.comap f m] (f ⁻¹' S)
    exact ⟨S, hS, rfl⟩

/-- `comap` distributes over `iInf` unconditionally (≤ direction only).

The inequality `comap f (⨅ i, m i) ≤ ⨅ i, comap f (m i)` holds by monotonicity.
The reverse inequality (and hence equality) requires `f` to be surjective.
See `iInf_comap_eq_comap_iInf_of_surjective` for the surjective case. -/
lemma comap_iInf_le {ι : Sort*} {α β : Type*} (f : α → β) (m : ι → MeasurableSpace β) :
    MeasurableSpace.comap f (iInf m) ≤ iInf (fun i => MeasurableSpace.comap f (m i)) := by
  refine le_iInf (fun i => ?_)
  exact MeasurableSpace.comap_mono (iInf_le m i)

-- Extract witnesses for each comap and choose them uniformly
private lemma comap_iInf_witnesses {ι : Type*} {α β : Type*} {f : α → β}
    (m : ι → MeasurableSpace β) (s : Set α)
    (hs_all : ∀ i, MeasurableSet[MeasurableSpace.comap f (m i)] s) :
    ∃ (T : ι → Set β), (∀ i, MeasurableSet[m i] (T i)) ∧ (∀ i, s = f ⁻¹' (T i)) := by
  have : ∀ i, ∃ (T : Set β), MeasurableSet[m i] T ∧ s = f ⁻¹' T := by
    intro i
    have hi := hs_all i
    rw [MeasurableSpace.measurableSet_comap] at hi
    rcases hi with ⟨T, hT, hpre⟩
    exact ⟨T, hT, hpre.symm⟩
  choose T hTmeas hspre using this
  exact ⟨T, hTmeas, hspre⟩

-- All witnesses are equal when f is surjective
private lemma comap_witnesses_eq_of_surjective {ι : Type*} {α β : Type*} {f : α → β}
    (hf : Function.Surjective f) (T : ι → Set β) (s : Set α)
    (hspre : ∀ i, s = f ⁻¹' (T i)) :
    ∀ i j, T i = T j := by
  intro i j
  have hinj := preimage_injective_of_surjective (α := α) (β := β) hf
  have : f ⁻¹' T i = f ⁻¹' T j := by rw [← hspre i, ← hspre j]
  exact hinj this

-- A set is measurable in comap f (iInf m) if it's the preimage of a canonically measurable set
private lemma measurableSet_comap_iInf_of_canonical {ι : Type*} [Nonempty ι]
    {α β : Type*} {f : α → β} (m : ι → MeasurableSpace β)
    (T0 : Set β) (hT0 : ∀ i, MeasurableSet[m i] T0) (s : Set α) (hs : s = f ⁻¹' T0) :
    MeasurableSet[MeasurableSpace.comap f (iInf m)] s := by
  refine ⟨T0, ?_, hs.symm⟩
  rw [MeasurableSpace.measurableSet_iInf]
  exact hT0

/-- With `f` surjective and a nonempty index type, `comap` commutes with `⨅`.

This is the key lemma for showing that tail σ-algebras defined via coordinate pullbacks
equal tail σ-algebras defined as pullbacks of path-space tails. -/
theorem iInf_comap_eq_comap_iInf_of_surjective {ι : Type*} [Nonempty ι] {α β : Type*} {f : α → β}
    (hf : Function.Surjective f) (m : ι → MeasurableSpace β) :
    iInf (fun i => MeasurableSpace.comap f (m i)) = MeasurableSpace.comap f (iInf m) := by
  classical
  -- (≥) direction holds unconditionally (monotonicity)
  have hge :
      MeasurableSpace.comap f (iInf m) ≤ iInf (fun i => MeasurableSpace.comap f (m i)) := by
    refine le_iInf (fun i => ?_)
    exact MeasurableSpace.comap_mono (iInf_le _ i)

  -- (≤) direction uses surjectivity to unify witnesses
  have hle :
      iInf (fun i => MeasurableSpace.comap f (m i)) ≤ MeasurableSpace.comap f (iInf m) := by
    intro s hs
    -- For each i, s is measurable in comap f (m i)
    have hs_all : ∀ i, MeasurableSet[MeasurableSpace.comap f (m i)] s := by
      rw [MeasurableSpace.measurableSet_iInf] at hs
      exact hs

    -- Extract witnesses Tᵢ such that s = f ⁻¹' Tᵢ for each i
    obtain ⟨T, hTmeas, hspre⟩ := comap_iInf_witnesses m s hs_all

    -- All witnesses are equal by surjectivity
    have Tall := comap_witnesses_eq_of_surjective hf T s hspre

    -- Pick canonical witness T₀
    rcases ‹Nonempty ι› with ⟨i₀⟩
    let T0 : Set β := T i₀
    have T_all : ∀ i, T i = T0 := fun i => Tall i i₀
    have s_pre : s = f ⁻¹' T0 := by simpa [T_all i₀] using hspre i₀
    have T0_meas_all : ∀ i, MeasurableSet[m i] T0 := fun i => by simpa [T_all i] using hTmeas i

    -- Conclude measurability
    exact measurableSet_comap_iInf_of_canonical m T0 T0_meas_all s s_pre

  exact le_antisymm hle hge

end MeasurableSpace
