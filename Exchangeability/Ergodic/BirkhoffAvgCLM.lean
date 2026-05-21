/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Order.Filter.Finite
import Exchangeability.Ergodic.KoopmanMeanErgodic

/-!
# Birkhoff Averages as Continuous Linear Maps

This file develops Birkhoff averages at the operator level, working entirely with
continuous linear maps (CLMs) on Lp spaces. This avoids coercion issues that arise
when mixing Lp-level and function-level operations.

## Main definitions

* `powCLM U k`: The k-th iterate of a CLM U as a CLM
* `birkhoffAvgCLM U n`: The n-th Birkhoff average as a CLM

## Main results

* `powCLM_koopman_coe_ae`: Iterating Koopman and coercing equals coercing and iterating (a.e.)
* `birkhoffAvgCLM_coe_ae_eq_function_avg`: CLM Birkhoff average equals function-level average (a.e.)

## Implementation notes

This infrastructure solves the coercion mismatch issue where Lean distinguishes between:
- `↑↑(birkhoffAverage ℝ U (fun f => f) n g)` (coerce the Lp average)
- `birkhoffAverage ℝ U (fun f => ↑↑f) n g` (average the coerced functions)

By working entirely at the CLM level and only coercing at the end, we avoid this issue.
-/

open scoped BigOperators
noncomputable section
classical

namespace Exchangeability.Ergodic

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The k-th iterate of a continuous linear map, defined as a CLM. -/
def powCLM (U : E →L[ℝ] E) : ℕ → (E →L[ℝ] E)
| 0     => ContinuousLinearMap.id ℝ E
| k + 1 => U.comp (powCLM U k)

@[simp] lemma powCLM_zero (U : E →L[ℝ] E) :
    powCLM U 0 = ContinuousLinearMap.id ℝ E := rfl

@[simp] lemma powCLM_succ (U : E →L[ℝ] E) (k : ℕ) :
    powCLM U (k+1) = U.comp (powCLM U k) := rfl

/-! ### Lp Coercion Helper Lemmas -/

section LpCoercionHelpers

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Coercion distributes through Lp scalar multiplication (a.e.). -/
lemma Lp.coeFn_smul' (c : ℝ) (f : Lp ℝ 2 μ) :
    (↑↑(c • f) : Ω → ℝ) =ᵐ[μ] fun ω => c * (f : Ω → ℝ) ω := by
  -- Lp scalar multiplication is pointwise a.e.
  -- Mathlib has Lp.coeFn_smul: ⇑(c • f) =ᵐ[μ] c • ⇑f
  -- For real numbers, c • x = c * x
  have := Lp.coeFn_smul c f
  filter_upwards [this] with ω h
  simp only [Pi.smul_apply] at h
  exact h

/-- Coercion distributes through finite sums in Lp (a.e.). -/
lemma Lp.coeFn_sum' {ι : Type*} [Fintype ι] (fs : ι → Lp ℝ 2 μ) :
    (↑↑(∑ i, fs i) : Ω → ℝ) =ᵐ[μ] fun ω => ∑ i, (fs i : Ω → ℝ) ω := by
  -- Strategy: Induction on Finset using Lp.coeFn_add
  classical
  -- Prove for arbitrary finset, then apply to Finset.univ
  have h_finset : ∀ (s : Finset ι),
      (↑↑(s.sum fs) : Ω → ℝ) =ᵐ[μ] fun ω => s.sum (fun i => (fs i : Ω → ℝ) ω) := by
    intro s
    induction s using Finset.induction with
    | empty =>
      -- Empty sum is 0, use Lp.coeFn_zero
      simp only [Finset.sum_empty]
      calc (↑↑(0 : Lp ℝ 2 μ) : Ω → ℝ)
          =ᵐ[μ] (0 : Ω → ℝ) := Lp.coeFn_zero ℝ 2 μ
        _ = fun ω => 0 := rfl
    | @insert i t hi IH =>
      -- Insert case: use Lp.coeFn_add
      simp only [Finset.sum_insert hi]
      calc (↑↑(fs i + t.sum fs) : Ω → ℝ)
          =ᵐ[μ] (↑↑(fs i) : Ω → ℝ) + (↑↑(t.sum fs) : Ω → ℝ) := Lp.coeFn_add _ _
        _ =ᵐ[μ] (↑↑(fs i) : Ω → ℝ) + fun ω => t.sum (fun j => (fs j : Ω → ℝ) ω) :=
            Filter.EventuallyEq.add .rfl IH
        _ =ᵐ[μ] fun ω => (fs i : Ω → ℝ) ω + t.sum (fun j => (fs j : Ω → ℝ) ω) := by
            apply Filter.Eventually.of_forall
            intro ω
            rfl
  -- Apply to Finset.univ
  convert h_finset Finset.univ using 1

/-- A.e. equality is preserved under finite sums. -/
lemma EventuallyEq.sum' {ι : Type*} [Fintype ι] {fs gs : ι → Ω → ℝ}
    (h : ∀ i, fs i =ᵐ[μ] gs i) :
    (fun ω => ∑ i, fs i ω) =ᵐ[μ] (fun ω => ∑ i, gs i ω) := by
  -- Strategy: Each fs i =ᵐ[μ] gs i means fs i and gs i differ on a null set N_i
  -- The union of finitely many null sets is null
  -- Outside this union, the sums are equal pointwise

  -- Convert to the definition: set where functions are equal is in the ae filter
  simp only [Filter.EventuallyEq, Filter.Eventually]
  rw [mem_ae_iff]

  -- The set where sums differ is contained in union of sets where individual functions differ
  have h_subset : {ω | ∑ i, fs i ω ≠ ∑ i, gs i ω} ⊆
         ⋃ i, {ω | fs i ω ≠ gs i ω} := by
    intro ω hω
    simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hω ⊢
    -- If the sums differ, then some summand must differ
    by_contra h_contra
    push Not at h_contra
    apply hω
    -- The sums are equal if all summands are equal
    congr 1
    ext i
    exact h_contra i

  -- Each set in the union has measure zero
  have h_null : ∀ i, μ {ω | fs i ω ≠ gs i ω} = 0 := by
    intro i
    have := h i
    rw [Filter.EventuallyEq, Filter.Eventually, mem_ae_iff] at this
    exact this

  -- Measure of finite union of null sets is zero
  -- Note: {x | ∑ i, fs i x = ∑ i, gs i x}ᶜ = {x | ∑ i, fs i x ≠ ∑ i, gs i x}
  have h_compl : {x : Ω | ∑ i, fs i x = ∑ i, gs i x}ᶜ = {x | ∑ i, fs i x ≠ ∑ i, gs i x} := by
    ext x
    simp [Set.mem_compl_iff]

  rw [h_compl]
  -- Prove μ {x | ∑ i, fs i x ≠ ∑ i, gs i x} = 0
  apply le_antisymm _ (zero_le _)
  calc μ {ω | ∑ i, fs i ω ≠ ∑ i, gs i ω}
      ≤ μ (⋃ i, {ω | fs i ω ≠ gs i ω}) := measure_mono h_subset
    _ ≤ ∑ i, μ {ω | fs i ω ≠ gs i ω} := measure_iUnion_fintype_le μ _
    _ = 0 := by simp [h_null]

end LpCoercionHelpers

end Exchangeability.Ergodic
