/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Logic.Equiv.Fintype
import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Tactic.Measurability

/-!
# Prefix Cylinders and Finite Marginal Uniqueness

This file provides infrastructure for working with "prefix cylinders" - cylinder sets
determined by initial segments of ℕ - and proves that finite measures on `ℕ → α` are
determined by their finite-dimensional marginals.

## Main Definitions

* `prefixProj α n`: Projection from `ℕ → α` to `Fin n → α` (first n coordinates)
* `prefixCylinder S`: Cylinder set determined by first n coordinates lying in S
* `prefixCylinders α`: Collection of all prefix cylinders (forms a π-system)

## Main Results

* `isPiSystem_prefixCylinders`: Prefix cylinders form a π-system
* `generateFrom_prefixCylinders`: Prefix cylinders generate the product σ-algebra
* `measure_eq_of_fin_marginals_eq`: Finite measures agreeing on all finite marginals are equal

## Mathematical Context

The key result `measure_eq_of_fin_marginals_eq` is a Kolmogorov extension-type theorem:
if two finite measures on `ℕ → α` induce the same distribution on each finite projection
`Fin n → α`, then they are equal. This is proved via the π-system uniqueness theorem.

This infrastructure is used in proving de Finetti's theorem to show that exchangeability
(invariance under finite permutations) implies full exchangeability (invariance under
all permutations of ℕ).

## Suggested Mathlib Location

`Mathlib.MeasureTheory.Constructions.Pi.Cylinders` or `Mathlib.MeasureTheory.Measure.FinMarginals`

## References

* Kallenberg (2005), *Probabilistic Symmetries and Invariance Principles*, Section 1.1
-/

open scoped BigOperators
open Equiv MeasureTheory Set

namespace PrefixCylinders

variable {α : Type*} [MeasurableSpace α]

/-! ### Prefix Projection -/

/-- Projection to the first `n` coordinates. -/
def prefixProj (α : Type*) (n : ℕ) (x : ℕ → α) : Fin n → α :=
  fun i => x i

omit [MeasurableSpace α] in
@[simp]
lemma prefixProj_apply {n : ℕ} (x : ℕ → α) (i : Fin n) :
    prefixProj (α := α) n x i = x i := rfl

lemma measurable_prefixProj {n : ℕ} :
    Measurable (prefixProj (α := α) n) :=
  measurable_pi_lambda _ (fun i => measurable_pi_apply (↑i : ℕ))

/-! ### Prefix Cylinders -/

/-- Cylinder set determined by the first `n` coordinates. -/
def prefixCylinder {n : ℕ} (S : Set (Fin n → α)) : Set (ℕ → α) :=
  (prefixProj (α := α) n) ⁻¹' S

omit [MeasurableSpace α] in
@[simp]
lemma mem_prefixCylinder {n : ℕ} {S : Set (Fin n → α)} {x : ℕ → α} :
    x ∈ prefixCylinder (α := α) S ↔ prefixProj (α := α) n x ∈ S := Iff.rfl

omit [MeasurableSpace α] in
@[simp]
lemma prefixCylinder_univ {n : ℕ} :
    prefixCylinder (α := α) (Set.univ : Set (Fin n → α)) = Set.univ := by
  simp [prefixCylinder]

omit [MeasurableSpace α] in
@[simp]
lemma prefixCylinder_empty {n : ℕ} :
    prefixCylinder (α := α) (∅ : Set (Fin n → α)) = ∅ := rfl

/-- The collection of all prefix cylinders. -/
def prefixCylinders (α : Type*) [MeasurableSpace α] : Set (Set (ℕ → α)) :=
  {A | ∃ n, ∃ S : Set (Fin n → α), MeasurableSet S ∧ A = prefixCylinder (α := α) S}

lemma prefixCylinder_mem_prefixCylinders {n : ℕ} {S : Set (Fin n → α)}
    (hS : MeasurableSet S) :
    prefixCylinder (α := α) S ∈ prefixCylinders α :=
  ⟨n, S, hS, rfl⟩

lemma measurable_of_mem_prefixCylinders {A : Set (ℕ → α)}
    (hA : A ∈ prefixCylinders α) : MeasurableSet A := by
  classical
  rcases hA with ⟨n, S, hS, rfl⟩
  exact (measurable_prefixProj (α := α) (n := n)) hS

/-! ### Restriction and Extension -/

section Extend

variable {m n : ℕ}

/-- Restrict a finite tuple to its first `m` coordinates. -/
def takePrefix (hmn : m ≤ n) (x : Fin n → α) : Fin m → α :=
  fun i => x (Fin.castLE hmn i)

omit [MeasurableSpace α] in
@[simp]
lemma takePrefix_apply {hmn : m ≤ n} (x : Fin n → α) (i : Fin m) :
    takePrefix (α := α) hmn x i = x (Fin.castLE hmn i) := rfl

omit [MeasurableSpace α] in
@[simp]
lemma takePrefix_prefixProj {hmn : m ≤ n} (x : ℕ → α) :
    takePrefix (α := α) hmn (prefixProj (α := α) n x) = prefixProj (α := α) m x := by
  ext i; simp [takePrefix]

/-- Extend a set from `Fin m → α` to `Fin n → α` by ignoring extra coordinates. -/
def extendSet (hmn : m ≤ n) (S : Set (Fin m → α)) : Set (Fin n → α) :=
  {x | takePrefix (α := α) hmn x ∈ S}

omit [MeasurableSpace α] in
lemma prefixCylinder_inter {m n : ℕ} {S : Set (Fin m → α)} {T : Set (Fin n → α)} :
    prefixCylinder (α := α) S ∩ prefixCylinder (α := α) T =
      prefixCylinder (α := α)
        (extendSet (α := α) (Nat.le_max_left _ _) S ∩
          extendSet (α := α) (Nat.le_max_right _ _) T) := by
  ext x
  simp only [Set.mem_inter_iff, mem_prefixCylinder, extendSet, Set.mem_setOf_eq,
             takePrefix_prefixProj]

-- Disable false-positive linter warnings: Measurable (Fin n → α) depends on [MeasurableSpace α]
set_option linter.unusedSectionVars false

@[nolint unusedArguments]
lemma takePrefix_measurable (hmn : m ≤ n) :
    Measurable (takePrefix (α := α) hmn) :=
  measurable_pi_lambda _ (fun i => measurable_pi_apply (Fin.castLE hmn i))

@[nolint unusedArguments]
lemma extendSet_measurable {S : Set (Fin m → α)} {hmn : m ≤ n}
    (hS : MeasurableSet S) : MeasurableSet (extendSet (α := α) hmn S) :=
  (takePrefix_measurable (α := α) hmn) hS

end Extend

/-! ### π-System Property -/

set_option linter.unusedSectionVars false

/-- The prefix cylinders form a π-system. -/
@[nolint unusedArguments]
lemma isPiSystem_prefixCylinders :
    IsPiSystem (prefixCylinders α) := by
  classical
  rintro A ⟨m, S, hS, rfl⟩ B ⟨n, T, hT, rfl⟩ hAB
  use max m n
  use extendSet (α := α) (Nat.le_max_left m n) S ∩
      extendSet (α := α) (Nat.le_max_right m n) T
  exact ⟨MeasurableSet.inter (extendSet_measurable (α := α) (hmn := Nat.le_max_left m n) hS)
      (extendSet_measurable (α := α) (hmn := Nat.le_max_right m n) hT),
    prefixCylinder_inter (α := α)⟩

/-- Any cylinder set belongs to the σ-algebra generated by prefix cylinders. -/
@[nolint unusedArguments]
lemma cylinder_subset_prefixCylinders {s : Finset ℕ} {S : Set (∀ _ : s, α)}
    (hS : MeasurableSet S) :
    MeasureTheory.cylinder (α := fun _ : ℕ => α) s S ∈ prefixCylinders α := by
  classical
  let N := s.sup id + 1
  have h_mem : ∀ i ∈ s, i < N := by
    intro i hi
    have hle : i ≤ s.sup id := by convert Finset.le_sup (f := id) hi
    omega
  let ι : s → Fin N := fun x => ⟨x.1, h_mem x.1 x.2⟩
  let pull : (Fin N → α) → (∀ i : s, α) := fun x => fun y => x (ι y)
  have hpull_meas : Measurable pull := by measurability
  have hs_eq :
      MeasureTheory.cylinder (α := fun _ : ℕ => α) s S =
        prefixCylinder (α := α) (pull ⁻¹' S) := by
    ext x
    classical
    have hpull : pull (prefixProj (α := α) N x) = s.restrict x := by
      funext y
      rcases y with ⟨y, hy⟩
      simp only [pull, prefixProj, Finset.restrict]
      rfl
    simp [MeasureTheory.cylinder, prefixCylinder, hpull]
  refine hs_eq ▸ prefixCylinder_mem_prefixCylinders (α := α) ?_
  exact hpull_meas hS

/-- The σ-algebra generated by prefix cylinders is the product σ-algebra. -/
@[nolint unusedArguments]
lemma generateFrom_prefixCylinders :
    MeasurableSpace.generateFrom (prefixCylinders α) =
      (inferInstance : MeasurableSpace (ℕ → α)) := by
  classical
  refine le_antisymm ?_ ?_
  · refine MeasurableSpace.generateFrom_le ?_
    rintro A hA
    exact measurable_of_mem_prefixCylinders (α := α) hA
  · have h_subset :
      MeasurableSpace.generateFrom (MeasureTheory.measurableCylinders fun _ : ℕ => α)
        ≤ MeasurableSpace.generateFrom (prefixCylinders α) := by
      refine MeasurableSpace.generateFrom_mono ?_
      intro A hA
      obtain ⟨s, S, hS, rfl⟩ :=
        (MeasureTheory.mem_measurableCylinders (α := fun _ : ℕ => α) A).1 hA
      exact cylinder_subset_prefixCylinders (α := α) hS
    simpa [MeasureTheory.generateFrom_measurableCylinders (α := fun _ : ℕ => α)] using h_subset

/-! ### Finite Marginal Uniqueness -/

private lemma totalMass_eq_of_fin_marginals_eq {μ ν : Measure (ℕ → α)}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ n (S : Set (Fin n → α)) (_hS : MeasurableSet S),
        Measure.map (prefixProj (α := α) n) μ S =
        Measure.map (prefixProj (α := α) n) ν S) :
    μ Set.univ = ν Set.univ := by
  classical
  simpa [Measure.map_apply_of_aemeasurable
    ((measurable_prefixProj (α := α) (n := 1)).aemeasurable)]
    using h 1 Set.univ MeasurableSet.univ

private lemma prefixCylinders_eq_of_fin_marginals_eq {μ ν : Measure (ℕ → α)}
    (h : ∀ n (S : Set (Fin n → α)) (_hS : MeasurableSet S),
        Measure.map (prefixProj (α := α) n) μ S =
        Measure.map (prefixProj (α := α) n) ν S)
    (A : Set (ℕ → α)) (hA : A ∈ prefixCylinders α) :
    μ A = ν A := by
  classical
  obtain ⟨n, S, hS, rfl⟩ := hA
  simp only [prefixCylinder, ← Measure.map_apply_of_aemeasurable
    ((measurable_prefixProj (α := α) (n := n)).aemeasurable) hS]
  exact h n S hS

/--
**Kolmogorov Extension-Type Uniqueness:** Finite measures with matching finite-dimensional
marginals are equal.

If two finite measures on `ℕ → α` induce the same distribution on each
finite-dimensional projection `Fin n → α`, then they are equal. This is a
consequence of the π-system uniqueness theorem applied to prefix cylinders.

**Proof structure:**
1. Measures agree on total mass (via 1-dimensional marginal)
2. Measures agree on all prefix cylinders (direct from marginals)
3. Apply π-system uniqueness to extend agreement to all measurable sets
-/
@[nolint unusedArguments]
theorem measure_eq_of_fin_marginals_eq {μ ν : Measure (ℕ → α)}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ n (S : Set (Fin n → α)) (_hS : MeasurableSet S),
        Measure.map (prefixProj (α := α) n) μ S =
        Measure.map (prefixProj (α := α) n) ν S) : μ = ν := by
  classical
  apply MeasureTheory.ext_of_generate_finite (C := prefixCylinders α)
  · simp [generateFrom_prefixCylinders (α := α)]
  · exact isPiSystem_prefixCylinders (α := α)
  · exact prefixCylinders_eq_of_fin_marginals_eq (α := α) h
  · exact totalMass_eq_of_fin_marginals_eq (α := α) h

/-- Convenience wrapper for probability measures. -/
@[nolint unusedArguments]
theorem measure_eq_of_fin_marginals_eq_prob {μ ν : Measure (ℕ → α)}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : ∀ n (S : Set (Fin n → α)) (_hS : MeasurableSet S),
        Measure.map (prefixProj (α := α) n) μ S =
        Measure.map (prefixProj (α := α) n) ν S) : μ = ν := by
  classical
  exact measure_eq_of_fin_marginals_eq (α := α) (μ := μ) (ν := ν) h

end PrefixCylinders
