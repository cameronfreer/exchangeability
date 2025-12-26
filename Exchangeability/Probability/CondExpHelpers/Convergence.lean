/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Convergence Lemmas for Conditional Expectation

This file provides convergence lemmas for conditional expectations, including
dominated convergence theorems and subsequence extraction.

## Main results

* `tendsto_condExpL1_domconv`: DCT for conditional expectation in L¹
* `exists_subseq_ae_tendsto_of_condExpL1_tendsto`: From L¹ convergence to a.e. convergence
  of a subsequence
-/

noncomputable section
open scoped MeasureTheory ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set

/-- **DCT for conditional expectation in L¹**. -/
lemma tendsto_condExpL1_domconv
    {α E : Type*} {m m₀ : MeasurableSpace α} (μ : Measure α)
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (hm : m ≤ m₀) [SigmaFinite (μ.trim hm)]
    {fs : ℕ → α → E} {f : α → E}
    (bound : α → ℝ)
    (hfs_meas : ∀ n, AEStronglyMeasurable (fs n) μ)
    (h_int : Integrable bound μ)
    (hbound : ∀ n, ∀ᵐ x ∂μ, ‖fs n x‖ ≤ bound x)
    (hpt : ∀ᵐ x ∂μ, Filter.Tendsto (fun n => fs n x) Filter.atTop (nhds (f x))) :
    Filter.Tendsto (fun n => condExpL1 hm μ (fs n)) Filter.atTop (nhds (condExpL1 hm μ f)) := by
  classical
  -- This is exactly mathlib's lemma; we just instantiate the parameters.
  simpa using
    (MeasureTheory.tendsto_condExpL1_of_dominated_convergence
      (μ := μ) (hm := hm) (fs := fs) (f := f)
      (bound_fs := bound) (hfs_meas := hfs_meas) (h_int_bound_fs := h_int)
      (hfs_bound := hbound) (hfs := hpt))

/-- From L¹ convergence of `condExpL1` to a.e. convergence of a subsequence of its representatives. -/
lemma exists_subseq_ae_tendsto_of_condExpL1_tendsto
    {α E : Type*} {m m₀ : MeasurableSpace α} (μ : Measure α)
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (hm : m ≤ m₀) [SigmaFinite (μ.trim hm)]
    {fs : ℕ → α → E} {f : α → E}
    (hL1 :
      Filter.Tendsto (fun n => condExpL1 hm μ (fs n)) Filter.atTop (nhds (condExpL1 hm μ f))) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      (∀ᵐ x ∂μ,
        Filter.Tendsto (fun n =>
          ((↑(condExpL1 hm μ (fs (ns n))) : α → E) x))
          Filter.atTop
          (nhds ((↑(condExpL1 hm μ f) : α → E) x))) := by
  classical
  -- Step 1: L¹ ⇒ convergence in measure for the (coerced) functions.
  have h_in_measure :
      TendstoInMeasure μ
        (fun n => (↑(condExpL1 hm μ (fs n)) : α → E))
        Filter.atTop
        ((↑(condExpL1 hm μ f) : α → E)) :=
    (MeasureTheory.tendstoInMeasure_of_tendsto_Lp
      (μ := μ) (p := (1 : ENNReal)) (l := Filter.atTop)
      (f := fun n => condExpL1 hm μ (fs n))
      (g := condExpL1 hm μ f)
      hL1)
  -- Step 2: convergence in measure ⇒ a.e. convergence along a subsequence.
  rcases (MeasureTheory.TendstoInMeasure.exists_seq_tendsto_ae h_in_measure)
    with ⟨ns, hmono, hAE⟩
  exact ⟨ns, hmono, hAE⟩

end
