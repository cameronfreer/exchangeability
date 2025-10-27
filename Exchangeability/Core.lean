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
import Exchangeability.Contractability

/-!
# Exchangeability and Full Exchangeability

This file proves that **exchangeability** (invariance under finite permutations)
and **full exchangeability** (invariance under all permutations of ℕ) are
equivalent for probability measures on sequence spaces.

## Main results

* `exchangeable_iff_fullyExchangeable`: For a probability measure and a
  measurable stochastic process, exchangeability is equivalent to full
  exchangeability.
* `measure_eq_of_fin_marginals_eq`: Two finite measures on `ℕ → α` that agree
  on all finite-dimensional marginals are equal.

## Technical approach

The proof uses the **π-system uniqueness theorem** for finite measures rather than
directly invoking Kolmogorov extension or Ionescu-Tulcea. While mathlib provides
these powerful tools (`Measure.infinitePi` for Kolmogorov extension and
`ProbabilityTheory.Kernel.traj` for Ionescu-Tulcea), applying them here would
require first constructing the measure from exchangeability data, which is
circular when proving that finite exchangeability implies full exchangeability.

Instead, we use a **uniqueness-based approach**:

1. Cylinder sets determined by initial segments form a π-system that generates
   the product σ-algebra on `ℕ → α`.
2. Two measures with matching finite marginals must be equal (by π-system
   uniqueness, `Measure.ext_of_generate_finite`).
3. Any infinite permutation can be approximated by a finite permutation on a
   sufficiently large initial segment, allowing us to transfer exchangeability
   to full exchangeability via the uniqueness result.

This approach directly proves the equivalence without requiring measure
construction machinery.
-/

noncomputable section

open scoped BigOperators

open Equiv MeasureTheory Set

namespace Exchangeability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-!
## π-system of prefix cylinders

A **prefix cylinder** is a measurable subset of `ℕ → α` determined by the first
`n` coordinates. Formally, it is the preimage of a measurable set under the
projection to `Fin n → α`.

**Key properties:**
* Prefix cylinders form a π-system (closed under finite intersections).
* They generate the product σ-algebra on `ℕ → α`.
* This allows us to apply the π-system uniqueness theorem: two finite measures
  that agree on all prefix cylinders must be equal.
-/

/-- Projection to the first `n` coordinates. -/
def prefixProj (α : Type*) (n : ℕ) (x : ℕ → α) : Fin n → α :=
  fun i => x i

omit [MeasurableSpace α] in
@[simp]
lemma prefixProj_apply {n : ℕ} (x : ℕ → α) (i : Fin n) :
    prefixProj (α:=α) n x i = x i := rfl

lemma measurable_prefixProj {n : ℕ} :
    Measurable (prefixProj (α:=α) n) := by
  measurability

/--
Cylinder set determined by the first `n` coordinates.

Given a set `S ⊆ Fin n → α`, the prefix cylinder `prefixCylinder n S` is the
set of all sequences `x : ℕ → α` whose first `n` coordinates lie in `S`.
-/
def prefixCylinder {n : ℕ} (S : Set (Fin n → α)) : Set (ℕ → α) :=
  (prefixProj (α:=α) n) ⁻¹' S

omit [MeasurableSpace α] in
@[simp]
lemma mem_prefixCylinder {n : ℕ} {S : Set (Fin n → α)} {x : ℕ → α} :
    x ∈ prefixCylinder (α:=α) S ↔ prefixProj (α:=α) n x ∈ S := Iff.rfl

omit [MeasurableSpace α] in
@[simp]
lemma prefixCylinder_univ {n : ℕ} :
    prefixCylinder (α:=α) (Set.univ : Set (Fin n → α)) = (Set.univ) := by
  ext x; simp [prefixCylinder]

omit [MeasurableSpace α] in
@[simp]
lemma prefixCylinder_empty {n : ℕ} :
    prefixCylinder (α:=α) (∅ : Set (Fin n → α)) = (∅) := rfl

/--
The collection of all prefix cylinders.

A set `A ⊆ ℕ → α` belongs to `prefixCylinders` if it is the preimage of some
measurable set `S ⊆ Fin n → α` under projection to the first `n` coordinates,
for some `n`.

**Key property:** This forms a π-system that generates the product σ-algebra.
-/
def prefixCylinders : Set (Set (ℕ → α)) :=
  {A | ∃ n, ∃ S : Set (Fin n → α), MeasurableSet S ∧ A = prefixCylinder (α:=α) S}

lemma prefixCylinder_mem_prefixCylinders {n : ℕ} {S : Set (Fin n → α)}
    (hS : MeasurableSet S) :
    prefixCylinder (α:=α) S ∈ prefixCylinders (α:=α) :=
  ⟨n, S, hS, rfl⟩

lemma measurable_of_mem_prefixCylinders {A : Set (ℕ → α)}
    (hA : A ∈ prefixCylinders (α:=α)) : MeasurableSet A := by
  classical
  rcases hA with ⟨n, S, hS, rfl⟩
  exact (measurable_prefixProj (α:=α) (n:=n)) hS

section Extend

variable {m n : ℕ}

/--
Restrict a finite tuple to its first `m` coordinates.

Given a function `x : Fin n → α` and a proof that `m ≤ n`, returns the
restriction to `Fin m → α`.
-/
def takePrefix (hmn : m ≤ n) (x : Fin n → α) : Fin m → α :=
  fun i => x (Fin.castLE hmn i)

omit [MeasurableSpace α] in
@[simp]
lemma takePrefix_apply {hmn : m ≤ n} (x : Fin n → α) (i : Fin m) :
    takePrefix (α:=α) hmn x i = x (Fin.castLE hmn i) := rfl

omit [MeasurableSpace α] in
@[simp]
lemma takePrefix_prefixProj {hmn : m ≤ n} (x : ℕ → α) :
    takePrefix (α:=α) hmn (prefixProj (α:=α) n x) = prefixProj (α:=α) m x := by
  ext i; simp [takePrefix]

@[simp]
lemma castLE_coe_nat {hmn : m ≤ n} (i : Fin m) :
    ((Fin.castLE hmn i : Fin n) : ℕ) = i :=
  Eq.refl i.1

/--
Extend a set from `Fin m → α` to `Fin n → α` by ignoring extra coordinates.

Given a set `S ⊆ Fin m → α` and `m ≤ n`, the extended set consists of all
`x : Fin n → α` whose first `m` coordinates lie in `S`.
-/
def extendSet (hmn : m ≤ n) (S : Set (Fin m → α)) : Set (Fin n → α) :=
  {x | takePrefix (α:=α) hmn x ∈ S}

omit [MeasurableSpace α] in
lemma prefixCylinder_inter {m n : ℕ} {S : Set (Fin m → α)} {T : Set (Fin n → α)} :
    prefixCylinder (α:=α) S ∩ prefixCylinder (α:=α) T =
      prefixCylinder (α:=α)
        (extendSet (α:=α) (Nat.le_max_left _ _) S ∩
          extendSet (α:=α) (Nat.le_max_right _ _) T) := by
  ext x
  simp only [Set.mem_inter_iff, mem_prefixCylinder, extendSet, Set.mem_setOf_eq, takePrefix_prefixProj]

end Extend

section Measurable

variable [MeasurableSpace α]

-- Disable false-positive linter warnings in this section:
-- Many theorems use `Measurable (Fin n → α)` which transitively depends on
-- `[MeasurableSpace α]` via `Pi.measurableSpace`, but the linter doesn't track
-- this transitive dependency and incorrectly suggests omitting `[MeasurableSpace α]`.
set_option linter.unusedSectionVars false

lemma takePrefix_measurable {m n : ℕ} (hmn : m ≤ n) :
    Measurable (takePrefix (α:=α) hmn) := by
  measurability

lemma extendSet_measurable {m n : ℕ} {S : Set (Fin m → α)} {hmn : m ≤ n}
    (hS : MeasurableSet S) : MeasurableSet (extendSet (α:=α) hmn S) :=
  (takePrefix_measurable (α:=α) hmn) hS

/--
The prefix cylinders form a π-system.

A π-system is a collection of sets closed under finite intersections. This
property is crucial for applying the uniqueness theorem for finite measures.
-/
lemma isPiSystem_prefixCylinders :
    IsPiSystem (prefixCylinders (α:=α)) := by
  classical
  rintro A ⟨m, S, hS, rfl⟩ B ⟨n, T, hT, rfl⟩ hAB
  use max m n
  use extendSet (α:=α) (Nat.le_max_left m n) S ∩
      extendSet (α:=α) (Nat.le_max_right m n) T
  constructor
  · exact MeasurableSet.inter
      (extendSet_measurable (α:=α) (hmn:=Nat.le_max_left m n) hS)
      (extendSet_measurable (α:=α) (hmn:=Nat.le_max_right m n) hT)
  · exact prefixCylinder_inter (α:=α)

/-- Helper: any cylinder determined by a finite set of coordinates belongs to the
σ-algebra generated by prefix cylinders. -/
lemma cylinder_subset_prefixCylinders {s : Finset ℕ} {S : Set (∀ _ : s, α)}
    (hS : MeasurableSet S) :
    MeasureTheory.cylinder (α:=fun _ : ℕ => α) s S ∈ prefixCylinders (α:=α) := by
  classical
  -- Choose an initial segment that covers `s`.
  let N := s.sup id + 1
  have h_mem : ∀ i ∈ s, i < N := by
    intro i hi
    have hle : i ≤ s.sup id := by convert Finset.le_sup (f := id) hi
    omega
  -- Transport `S` along the inclusion into the initial segment.
  let ι : s → Fin N := fun x => ⟨x.1, h_mem x.1 x.2⟩
  let pull : (Fin N → α) → (∀ i : s, α) := fun x => fun y => x (ι y)
  have hpull_meas : Measurable pull := by
    measurability
  have hs_eq :
      MeasureTheory.cylinder (α:=fun _ : ℕ => α) s S =
        prefixCylinder (α:=α) (pull ⁻¹' S) := by
    ext x
    classical
    have hpull : pull (prefixProj (α:=α) N x) = s.restrict x := by
      funext y
      rcases y with ⟨y, hy⟩
      simp only [pull, prefixProj, Finset.restrict]
      rfl
    simp [MeasureTheory.cylinder, prefixCylinder, hpull]
  refine hs_eq ▸ prefixCylinder_mem_prefixCylinders (α:=α) ?_
  exact hpull_meas hS

/--
The σ-algebra generated by prefix cylinders is the product σ-algebra.

This shows that prefix cylinders generate the full product σ-algebra on `ℕ → α`,
which means any measurable set can be approximated by prefix cylinders.
-/
lemma generateFrom_prefixCylinders :
    MeasurableSpace.generateFrom (prefixCylinders (α:=α)) =
      (inferInstance : MeasurableSpace (ℕ → α)) := by
  classical
  refine le_antisymm ?_ ?_
  · refine MeasurableSpace.generateFrom_le ?_
    rintro A hA
    exact measurable_of_mem_prefixCylinders (α:=α) hA
  · have h_subset :
      MeasurableSpace.generateFrom
          (MeasureTheory.measurableCylinders fun _ : ℕ => α)
        ≤ MeasurableSpace.generateFrom (prefixCylinders (α:=α)) := by
      refine MeasurableSpace.generateFrom_mono ?_
      intro A hA
      obtain ⟨s, S, hS, rfl⟩ :=
        (MeasureTheory.mem_measurableCylinders (α:=fun _ : ℕ => α) A).1 hA
      exact cylinder_subset_prefixCylinders (α:=α) hS
    simpa [MeasureTheory.generateFrom_measurableCylinders
      (α:=fun _ : ℕ => α)] using h_subset

/--
Helper lemma: Measures agree on total mass if they agree on all finite marginals.

The key insight is that the 1-dimensional marginal determines the total measure
of the entire space.
-/
private lemma totalMass_eq_of_fin_marginals_eq {μ ν : Measure (ℕ → α)}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ n (S : Set (Fin n → α)) (_hS : MeasurableSet S),
        Measure.map (prefixProj (α:=α) n) μ S =
        Measure.map (prefixProj (α:=α) n) ν S) :
    μ Set.univ = ν Set.univ := by
  classical
  simpa [Measure.map_apply_of_aemeasurable
    ((measurable_prefixProj (α:=α) (n:=1)).aemeasurable)]
    using h 1 Set.univ MeasurableSet.univ

/--
Helper lemma: Measures agree on prefix cylinders if they agree on finite marginals.

Any prefix cylinder is the preimage of a measurable set under a finite projection,
so agreement on marginals implies agreement on cylinders.
-/
private lemma prefixCylinders_eq_of_fin_marginals_eq {μ ν : Measure (ℕ → α)}
    (h : ∀ n (S : Set (Fin n → α)) (_hS : MeasurableSet S),
        Measure.map (prefixProj (α:=α) n) μ S =
        Measure.map (prefixProj (α:=α) n) ν S)
    (A : Set (ℕ → α)) (hA : A ∈ prefixCylinders (α:=α)) :
    μ A = ν A := by
  classical
  obtain ⟨n, S, hS, rfl⟩ := hA
  simp only [prefixCylinder, ← Measure.map_apply_of_aemeasurable
    ((measurable_prefixProj (α:=α) (n:=n)).aemeasurable) hS]
  exact h n S hS

/--
Finite measures with matching finite-dimensional marginals are equal.

If two finite measures on `ℕ → α` induce the same distribution on each
finite-dimensional projection `Fin n → α`, then they are equal. This is a
consequence of the π-system uniqueness theorem applied to prefix cylinders.

**Mathematical content:** This is a Kolmogorov extension-type result showing
that infinite-dimensional measures are determined by their finite marginals.

**Proof structure:** The proof decomposes into three steps:
1. Measures agree on total mass (via 1-dimensional marginal)
2. Measures agree on all prefix cylinders (direct from marginals)
3. Apply π-system uniqueness to extend agreement to all measurable sets
-/
theorem measure_eq_of_fin_marginals_eq {μ ν : Measure (ℕ → α)}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ n (S : Set (Fin n → α)) (_hS : MeasurableSet S),
        Measure.map (prefixProj (α:=α) n) μ S =
        Measure.map (prefixProj (α:=α) n) ν S) : μ = ν := by
  classical
  apply MeasureTheory.ext_of_generate_finite (C:=prefixCylinders (α:=α))
  · simp [generateFrom_prefixCylinders (α:=α)]
  · exact isPiSystem_prefixCylinders (α:=α)
  · exact prefixCylinders_eq_of_fin_marginals_eq (α:=α) h
  · exact totalMass_eq_of_fin_marginals_eq (α:=α) h

/-- Convenience wrapper of `measure_eq_of_fin_marginals_eq` for probability measures. -/
theorem measure_eq_of_fin_marginals_eq_prob {μ ν : Measure (ℕ → α)}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : ∀ n (S : Set (Fin n → α)) (_hS : MeasurableSet S),
        Measure.map (prefixProj (α:=α) n) μ S =
        Measure.map (prefixProj (α:=α) n) ν S) : μ = ν := by
  classical
  exact measure_eq_of_fin_marginals_eq (α:=α) (μ:=μ) (ν:=ν) h

end Measurable

/-!
## Exchangeability versus full exchangeability

This section proves that exchangeability (invariance under finite permutations)
implies full exchangeability (invariance under all permutations of ℕ) for
probability measures.

**Strategy:** Given an arbitrary permutation π of ℕ and a finite index n, we
construct a finite permutation that agrees with π on the first n coordinates.
Exchangeability ensures the finite marginals match, and by the previous
uniqueness result, the full measures are equal.
-/

section Probability

variable [MeasurableSpace Ω] [MeasurableSpace α]

-- Disable false-positive linter warnings in this section:
-- Many theorems use types like `Measurable (ℕ → α → β)` or `Measure (ℕ → α)` which
-- transitively depend on `[MeasurableSpace α]` via `Pi.measurableSpace`, but the
-- linter doesn't track this transitive dependency and incorrectly suggests omitting
-- `[MeasurableSpace Ω]` or `[MeasurableSpace α]`.
set_option linter.unusedSectionVars false

/--
Reindex a sequence by applying a permutation to the indices.

Given a permutation `π` of ℕ and a sequence `x : ℕ → α`, returns the sequence
`i ↦ x (π i)`.
-/
def reindex (π : Equiv.Perm ℕ) (x : ℕ → α) : ℕ → α := fun i => x (π i)

@[simp]
lemma reindex_apply {π : Equiv.Perm ℕ} (x : ℕ → α) (i : ℕ) :
    reindex (α:=α) π x i = x (π i) := rfl

lemma measurable_reindex {π : Equiv.Perm ℕ} :
    Measurable (reindex (α:=α) π) := by
  measurability

attribute [measurability] measurable_prefixProj takePrefix_measurable measurable_reindex

/--
The path law (or joint distribution) of a stochastic process.

Given a measure `μ` on `Ω` and a process `X : ℕ → Ω → α`, the path law is the
pushforward measure on `ℕ → α` obtained by mapping each `ω` to its sample path
`i ↦ X i ω`.
-/
def pathLaw (μ : Measure Ω) (X : ℕ → Ω → α) : Measure (ℕ → α) :=
  Measure.map (fun ω => fun i => X i ω) μ

lemma pathLaw_map_prefix (μ : Measure Ω) (X : ℕ → Ω → α)
    (hX : ∀ i, Measurable (X i)) (n : ℕ) :
    Measure.map (prefixProj (α:=α) n) (pathLaw (α:=α) μ X) =
      Measure.map (fun ω => fun i : Fin n => X i ω) μ := by
  classical
  have hmeas : Measurable fun ω => fun i : ℕ => X i ω := by
    fun_prop
  refine Measure.map_map (μ:=μ)
    (f:=fun ω => fun i : ℕ => X i ω)
    (g:=prefixProj (α:=α) n)
    (measurable_prefixProj (α:=α) (n:=n))
    hmeas

lemma pathLaw_map_prefix_perm (μ : Measure Ω) (X : ℕ → Ω → α)
    (hX : ∀ i, Measurable (X i)) (π : Equiv.Perm ℕ) (n : ℕ) :
    Measure.map (prefixProj (α:=α) n)
        (Measure.map (reindex (α:=α) π) (pathLaw (α:=α) μ X)) =
      Measure.map (fun ω => fun i : Fin n => X (π i) ω) μ := by
  classical
  have hreindex :
      Measurable fun x : ℕ → α => reindex (α:=α) π x := measurable_reindex (α:=α) (π:=π)
  have hmeas : Measurable fun ω => fun i : ℕ => X i ω := by
    fun_prop
  calc
    Measure.map (prefixProj (α:=α) n)
        (Measure.map (reindex (α:=α) π) (pathLaw (α:=α) μ X))
      = Measure.map (prefixProj (α:=α) n ∘ reindex (α:=α) π) (pathLaw (α:=α) μ X) := by
        rw [Measure.map_map (measurable_prefixProj (α:=α) (n:=n)) hreindex]
    _ = Measure.map (prefixProj (α:=α) n ∘ reindex (α:=α) π)
        (Measure.map (fun ω => fun i : ℕ => X i ω) μ) := by rw [pathLaw]
    _ = Measure.map ((prefixProj (α:=α) n ∘ reindex (α:=α) π) ∘ fun ω => fun i : ℕ => X i ω) μ :=
        Measure.map_map ((measurable_prefixProj (α:=α) (n:=n)).comp hreindex) hmeas
    _ = Measure.map (fun ω => fun i : Fin n => X (π i) ω) μ := rfl

/--
Full exchangeability is equivalent to invariance of the path law.

A process is fully exchangeable if and only if its path law is invariant under
all permutations of the index set ℕ. This provides a measure-theoretic
characterization of full exchangeability.
-/
lemma fullyExchangeable_iff_pathLaw_invariant {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : ℕ → Ω → α}
    (hX : ∀ i, Measurable (X i)) :
    FullyExchangeable μ X ↔
      ∀ π, Measure.map (reindex (α:=α) π) (pathLaw (α:=α) μ X)
        = pathLaw (α:=α) μ X := by
  classical
  simp only [pathLaw]
  constructor
  · intro hFull π
    rw [Measure.map_map (measurable_reindex (α:=α) (π:=π))
      (measurable_pi_lambda _ (fun i => hX i))]
    exact hFull π
  · intro hPath π
    have := hPath π
    rwa [Measure.map_map (measurable_reindex (α:=α) (π:=π))
      (measurable_pi_lambda _ (fun i => hX i))] at this

/-!
### Auxiliary combinatorics: approximating infinite permutations

To prove that exchangeability implies full exchangeability, we need to show that
any infinite permutation π of ℕ can be approximated by a finite permutation on
a sufficiently large initial segment.

The key construction: given π and n, we find a bound `m = permBound π n` such
that both `{0,...,n-1}` and `{π(0),...,π(n-1)}` lie in `{0,...,m-1}`. Then we
extend π to a permutation of `Fin m` by choosing an arbitrary permutation on the
remaining indices.
-/

section Approximation

variable (π : Equiv.Perm ℕ) (n : ℕ)

/--
A finite bound containing both `{0,...,n-1}` and `{π(0),...,π(n-1)}`.

This is the maximum of `n` and the supremum of `π(i) + 1` for `i < n`.
-/
def permBound : ℕ :=
  max n ((Finset.range n).sup fun i : ℕ => π i + 1)

lemma le_permBound : n ≤ permBound π n := le_max_left _ _

lemma lt_permBound_of_lt {i : ℕ} (hi : i < n) :
    π i < permBound π n := by
  classical
  have h_mem : i ∈ Finset.range n := by simp [hi]
  have hsup : π i + 1 ≤ (Finset.range n).sup fun j => π j + 1 := by
    apply Finset.le_sup (f := fun j => π j + 1) h_mem
  have : π i < (Finset.range n).sup fun j => π j + 1 :=
    lt_of_lt_of_le (Nat.lt_succ_self _) hsup
  exact lt_of_lt_of_le this (Nat.le_max_right _ _)

lemma lt_permBound_fin {i : Fin n} :
    π i < permBound π n := lt_permBound_of_lt (π:=π) (n:=n) i.isLt

def approxEquiv :
    {x : Fin (permBound π n) // (x : ℕ) < n} ≃
      {x : Fin (permBound π n) // ∃ j : Fin n, (x : ℕ) = π j} :=
  by
    classical
    refine
      { toFun := ?_, invFun := ?_, left_inv := ?_, right_inv := ?_ }
    · intro x
      have hx := x.property
      let i : Fin n := ⟨x.1, hx⟩
      have hi : (π i : ℕ) < permBound π n := lt_permBound_fin (π:=π) (n:=n) (i:=i)
      refine ⟨⟨π i, hi⟩, ?_⟩
      exact ⟨i, rfl⟩
    · intro y
      let j := Classical.choose y.property
      have hj := Classical.choose_spec y.property
      have hj_lt : (j : ℕ) < n := j.isLt
      have hj_eq : π.symm y.1 = j := by
        apply π.symm_apply_eq.2
        exact hj
      have hjm : (π.symm y.1 : ℕ) < permBound π n :=
        lt_of_lt_of_le (by simp [hj_eq, hj_lt])
          (le_permBound (π:=π) (n:=n))
      refine ⟨⟨π.symm y.1, hjm⟩, ?_⟩
      simp [hj_eq]
    · intro x
      ext
      simp
    · intro y
      rcases y with ⟨y, hy⟩
      rcases hy with ⟨j, hj⟩
      ext
      simp [hj]

/--
A finite permutation of `Fin (permBound π n)` that agrees with `π` on `{0,...,n-1}`.

This extends the restriction of π to an equivalence on the finite type
`Fin (permBound π n)` by choosing an arbitrary permutation on the indices
outside the range of π restricted to `{0,...,n-1}`.
-/
def approxPerm : Equiv.Perm (Fin (permBound π n)) :=
  (approxEquiv (π:=π) (n:=n)).extendSubtype

lemma approxPerm_apply_cast {i : Fin n} :
    approxPerm (π:=π) (n:=n)
        (Fin.castLE (le_permBound (π:=π) (n:=n)) i)
      = ⟨π i, lt_permBound_fin (π:=π) (n:=n) (i:=i)⟩ := by
  classical
  have hmem : ((Fin.castLE (le_permBound (π:=π) (n:=n)) i) : ℕ) < n :=
    i.2
  have := Equiv.extendSubtype_apply_of_mem
      (e:=approxEquiv (π:=π) (n:=n))
      (x:=Fin.castLE (le_permBound (π:=π) (n:=n)) i)
      hmem
  simpa using this

@[simp]
lemma approxPerm_apply_cast_coe {i : Fin n} :
    ((approxPerm (π:=π) (n:=n)
        (Fin.castLE (le_permBound (π:=π) (n:=n)) i)) : ℕ) = π i := by
  classical
  have := congrArg (fun x : Fin (permBound π n) => (x : ℕ))
    (approxPerm_apply_cast (π:=π) (n:=n) (i:=i))
  simpa using this

end Approximation

/--
Exchangeability implies invariance of all finite marginals under arbitrary permutations.

If a process `X` is exchangeable (invariant under finite permutations), then
each finite marginal is invariant under *any* permutation of ℕ, not just finite
ones. This is the key step in proving exchangeability implies full exchangeability.

**Proof idea:** Given an arbitrary permutation π and dimension n, construct a
finite permutation that agrees with π on the first n coordinates using
`approxPerm`. Exchangeability ensures this finite permutation preserves the
n-dimensional marginal, hence so does π.
-/
lemma marginals_perm_eq {μ : Measure Ω} (X : ℕ → Ω → α)
    (hX : ∀ i, Measurable (X i)) (hμ : Exchangeable μ X)
    (π : Equiv.Perm ℕ) (n : ℕ) :
    Measure.map (fun ω => fun i : Fin n => X (π i) ω) μ =
      Measure.map (fun ω => fun i : Fin n => X i ω) μ := by
  classical
  by_cases hn : n = 0
  · subst hn
    congr
    funext ω
    ext i
    exact Fin.elim0 i
  · set m := permBound (π:=π) n with hm_def
    have hm : n ≤ m := le_permBound (π:=π) (n:=n)
    set σ := approxPerm (π:=π) (n:=n) with hσ_def
    have hσ := hμ m σ
    have hX₁ : Measurable fun ω => fun i : Fin m => X i ω :=
      measurable_pi_lambda _ (fun i => hX i)
    have hX₂ : Measurable fun ω => fun i : Fin m => X (σ i) ω :=
      measurable_pi_lambda _ (fun i => hX _)
    have hproj : Measurable (takePrefix (α:=α) hm) := takePrefix_measurable (α:=α) hm
    have hmap₁ :=
      Measure.map_map (μ:=μ)
        (f:=fun ω => fun i : Fin m => X (σ i) ω)
        (g:=takePrefix (α:=α) hm) hproj hX₂
    have hmap₂ :=
      Measure.map_map (μ:=μ)
        (f:=fun ω => fun i : Fin m => X i ω)
        (g:=takePrefix (α:=α) hm) hproj hX₁
    have hσ' := congrArg (fun ν => Measure.map (takePrefix (α:=α) hm) ν) hσ
    have hσ'' :
        Measure.map ((takePrefix (α:=α) hm) ∘ fun ω => fun i : Fin m => X (σ i) ω) μ =
          Measure.map ((takePrefix (α:=α) hm) ∘ fun ω => fun i : Fin m => X i ω) μ := by
      rw [← hmap₁, ← hmap₂]
      exact hσ'
    have hcomp₁ :
        ((takePrefix (α:=α) hm) ∘ fun ω => fun i : Fin m => X (σ i) ω)
          = fun ω => fun i : Fin n => X (π i) ω := by
      funext ω i
      simp [Function.comp, takePrefix, hσ_def,
        approxPerm_apply_cast_coe (π:=π) (n:=n) (i:=i)]
    have hcomp₂ :
        ((takePrefix (α:=α) hm) ∘ fun ω => fun i : Fin m => X i ω)
          = fun ω => fun i : Fin n => X i ω := by
      funext ω i
      simp [Function.comp, takePrefix]
    simpa [Function.comp, hcomp₁, hcomp₂] using hσ''

/--
**Main theorem:** Exchangeability and full exchangeability are equivalent.

For a probability measure and a measurable stochastic process, invariance under
finite permutations (exchangeability) is equivalent to invariance under all
permutations of ℕ (full exchangeability).

**Mathematical significance:** This shows that the seemingly stronger condition
of full exchangeability is automatic once exchangeability holds. This is a
consequence of the Kolmogorov extension principle: infinite-dimensional
measures are determined by their finite-dimensional marginals.

**Proof strategy:**
- (⇒) Use `marginals_perm_eq` to show all finite marginals are invariant under
  arbitrary permutations, then apply `measure_eq_of_fin_marginals_eq`.
- (⇐) Full exchangeability trivially implies exchangeability by restriction.
-/
theorem exchangeable_iff_fullyExchangeable {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : ℕ → Ω → α}
    (hX : ∀ i, Measurable (X i)) :
    Exchangeable μ X ↔ FullyExchangeable μ X := by
  classical
  constructor
  · intro hEx π
    let μX := pathLaw (α:=α) μ X
    have hμ_univ : μ Set.univ = 1 := measure_univ
    have hμX_univ : μX Set.univ = 1 := by
      simp [μX, pathLaw, Measure.map_apply_of_aemeasurable,
        (measurable_pi_lambda _ (fun i => hX i)).aemeasurable, hμ_univ]
    haveI : IsProbabilityMeasure μX := ⟨by simpa using hμX_univ⟩
    have hμXπ_univ :
        Measure.map (reindex (α:=α) π) μX Set.univ = 1 := by
      simp [Measure.map_apply_of_aemeasurable,
        (measurable_reindex (α:=α) (π:=π)).aemeasurable, hμX_univ]
    haveI : IsProbabilityMeasure (Measure.map (reindex (α:=α) π) μX) :=
      ⟨by simpa using hμXπ_univ⟩
    have hMarg : ∀ n (S : Set (Fin n → α)) (hS : MeasurableSet S),
        Measure.map (prefixProj (α:=α) n) μX S =
          Measure.map (prefixProj (α:=α) n)
            (Measure.map (reindex (α:=α) π) μX) S := by
      intro n S hS
      have h1 := pathLaw_map_prefix (α:=α) μ X hX n
      have h2 := pathLaw_map_prefix_perm (α:=α) μ X hX π n
      have hperm := marginals_perm_eq (μ:=μ) (X:=X) hX hEx π n
      have hlhs :
          Measure.map (prefixProj (α:=α) n) μX =
            Measure.map (fun ω => fun i : Fin n => X i ω) μ := h1
      have hrhs :
          Measure.map (prefixProj (α:=α) n)
              (Measure.map (reindex (α:=α) π) μX) =
            Measure.map (fun ω => fun i : Fin n => X (π i) ω) μ := h2
      rw [hlhs, hrhs]
      exact (congrArg (fun ν => ν S) hperm).symm
    have hEq :=
      measure_eq_of_fin_marginals_eq_prob (α:=α)
        (μ:=μX) (ν:=Measure.map (reindex (α:=α) π) μX) hMarg
    have hmap₁ :
        Measure.map (fun ω => fun i : ℕ => X (π i) ω) μ =
          Measure.map (reindex (α:=α) π) μX := by
      simp only [μX, pathLaw]
      rw [Measure.map_map (measurable_reindex (α:=α) (π:=π))
        (measurable_pi_lambda _ (fun i => hX i))]
      rfl
    have hmap₂ : Measure.map (fun ω => fun i : ℕ => X i ω) μ = μX := by
      simp [μX, pathLaw]
    simpa [hmap₁, hmap₂] using hEq.symm
  · intro hFull
    exact FullyExchangeable.exchangeable (μ:=μ) (X:=X) hX hFull

end Probability

end Exchangeability
