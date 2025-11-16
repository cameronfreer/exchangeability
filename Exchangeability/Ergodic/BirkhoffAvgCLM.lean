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

lemma powCLM_apply (U : E →L[ℝ] E) (k : ℕ) (v : E) :
    (powCLM U k) v = (U^[k]) v := by
  induction k with
  | zero => simp [powCLM]
  | succ k ih =>
    simp [powCLM, Function.iterate_succ_apply']
    rw [ih]

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
  -- Lp addition is pointwise a.e., and finite sums are iterated additions
  sorry

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
    push_neg at h_contra
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

/-- Birkhoff average as a continuous linear map. -/
def birkhoffAvgCLM (U : E →L[ℝ] E) (n : ℕ) : E →L[ℝ] E :=
  if n = 0 then 0 else
    ((n : ℝ)⁻¹) • (∑ k : Fin n, powCLM U k)

lemma birkhoffAvgCLM_zero (U : E →L[ℝ] E) :
    birkhoffAvgCLM U 0 = 0 := by
  simp [birkhoffAvgCLM]

lemma birkhoffAvgCLM_apply (U : E →L[ℝ] E) (n : ℕ) (v : E) :
    (birkhoffAvgCLM U n) v =
      if n = 0 then 0
      else (n : ℝ)⁻¹ • ∑ k : Fin n, (powCLM U k) v := by
  unfold birkhoffAvgCLM
  by_cases hn : n = 0
  · simp [hn]
  · simp only [hn, if_false]
    -- The scalar multiplication and sum distribute over function application
    simp [Pi.smul_apply, Finset.sum_apply]

/-- For Lp spaces: iterating Koopman and then coercing equals
    coercing and then composing with T^[k] (almost everywhere). -/
lemma powCLM_koopman_coe_ae {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (T : Ω → Ω) (hT_meas : Measurable T) (hT_mp : MeasurePreserving T μ μ)
    (k : ℕ) (fL2 : Lp ℝ 2 μ) :
  ((powCLM (koopman T hT_mp) k) fL2 : Ω → ℝ) =ᵐ[μ]
  (fun ω => (fL2 : Ω → ℝ) (T^[k] ω)) := by
  induction k with
  | zero =>
    simp [powCLM]
  | succ k ih =>
    simp only [powCLM_succ, ContinuousLinearMap.coe_comp', Function.comp_apply]
    -- Apply koopman to the k-th iterate
    have h_koopman : ((koopman T hT_mp) ((powCLM (koopman T hT_mp) k) fL2) : Ω → ℝ) =ᵐ[μ]
      (fun ω => ((powCLM (koopman T hT_mp) k) fL2 : Ω → ℝ) (T ω)) := by
      -- koopman is defined as compMeasurePreservingₗᵢ, which corresponds to composition
      unfold koopman
      simp only [LinearIsometry.coe_toContinuousLinearMap]
      exact Lp.coeFn_compMeasurePreserving _ hT_mp
    -- Combine with inductive hypothesis using composition
    calc ((koopman T hT_mp) ((powCLM (koopman T hT_mp) k) fL2) : Ω → ℝ)
        =ᵐ[μ] (fun ω => ((powCLM (koopman T hT_mp) k) fL2 : Ω → ℝ) (T ω)) := h_koopman
      _ =ᵐ[μ] (fun ω => (fL2 : Ω → ℝ) (T^[k] (T ω))) := by
          -- The inductive hypothesis gives: powCLM k fL2 evaluates to fL2 ∘ T^[k] a.e.
          -- We need this at the point T ω, which is the image under a measure-preserving map
          -- Use MeasurePreserving.quasiMeasurePreserving to get QuasiMeasurePreserving
          have h_quasi := hT_mp.quasiMeasurePreserving
          exact h_quasi.ae_eq_comp ih
      _ = (fun ω => (fL2 : Ω → ℝ) (T^[k+1] ω)) := by
          ext ω
          rw [← Function.iterate_succ_apply]

/-- CLM Birkhoff average equals function-level average (almost everywhere).

This is the key lemma showing that coercing the Lp Birkhoff average equals
averaging the coerced functions.

**Strategy:**
1. Unfold birkhoffAvgCLM and show coercion distributes through scalar mult and sum
2. For each k, use powCLM_koopman_coe_ae to show:
   `((powCLM (koopman T hT_mp) k) fL2 : Ω → ℝ) =ᵐ[μ] (fun ω => (fL2 : Ω → ℝ) (T^[k] ω))`
3. Combine using a.e. equality for sums
4. Simplify scalar multiplication to regular multiplication

This lemma would resolve the coercion issues at ViaKoopman lines 3999-4051. -/
lemma birkhoffAvgCLM_coe_ae_eq_function_avg
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (T : Ω → Ω) (hT_meas : Measurable T) (hT_mp : MeasurePreserving T μ μ)
    (n : ℕ) (fL2 : Lp ℝ 2 μ) :
  ((birkhoffAvgCLM (koopman T hT_mp) n) fL2 : Ω → ℝ) =ᵐ[μ]
  (fun ω => if n = 0 then 0
            else (n : ℝ)⁻¹ * ∑ k : Fin n, (fL2 : Ω → ℝ) (T^[k] ω)) := by
  -- Strategy (documented in file header):
  -- 1. Unfold birkhoffAvgCLM and case split on n = 0
  -- 2. For n ≠ 0, show coercion distributes through scalar mult and sum:
  --    - Need: Lp.coeFn_smul for scalar multiplication distribution
  --    - Need: Lp.coeFn_sum for sum distribution
  --    - Need: EventuallyEq.sum to combine a.e. equalities under sums
  -- 3. For each k, use powCLM_koopman_coe_ae to relate powCLM to function iteration
  -- 4. Combine using a.e. equality transitivity

  -- Missing infrastructure: Lp coercion lemmas for algebraic operations
  sorry

end Exchangeability.Ergodic
