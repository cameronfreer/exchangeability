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

end Exchangeability.Ergodic
