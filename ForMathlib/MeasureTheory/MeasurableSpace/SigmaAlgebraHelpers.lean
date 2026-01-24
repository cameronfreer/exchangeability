/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.MeasureTheory.Function.AEEqFun
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.Order.Filter.Basic

/-!
# σ-Algebra Helpers for AEStronglyMeasurable

This file provides helper lemmas for establishing AEStronglyMeasurable with respect
to infima of σ-algebras and limits of sequences. These are useful for working with
tail σ-algebras and reverse martingales.

## Main Results

* `aestronglyMeasurable_iInf_antitone`: AEStronglyMeasurable is preserved under
  infimum of antitone σ-algebras
* `aestronglyMeasurable_sub_of_tendsto_ae`: AEStronglyMeasurable for sub-σ-algebras
  is preserved under a.e. pointwise limits

## Mathematical Context

These results are crucial for proving properties of tail σ-algebras, where one needs
to show that functions measurable with respect to each σ-algebra in a decreasing
sequence are also measurable with respect to the infimum.

The key technique is using liminf/limsup to construct Measurable witnesses that
agree a.e. with the original function.

## Suggested Mathlib Location

`Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic` or a new file
`Mathlib.MeasureTheory.MeasurableSpace.InfSigmaAlgebra`

## References

* Kallenberg (2005), *Foundations of Modern Probability*, for general treatment
-/

noncomputable section

open MeasureTheory Filter

/-! ## AEStronglyMeasurable for infimum of σ-algebras

For real-valued functions, if f is AEStronglyMeasurable with respect to each σ-algebra
in an antitone (decreasing) sequence, then f is AEStronglyMeasurable with respect to
their infimum.

**Mathematical justification:**
1. For each N, we have a representative g_N with StronglyMeasurable[m N] g_N and f =ᵐ[μ] g_N
2. For ℝ-valued functions, StronglyMeasurable ↔ Measurable (via Measurable.stronglyMeasurable)
3. If f is Measurable[m N] for each N, then f is Measurable[⨅ N, m N] (by measurableSet_iInf)
4. Hence f is StronglyMeasurable[⨅ N, m N], giving AEStronglyMeasurable

The technical challenge is constructing a common representative from the a.e.-equal witnesses.
-/
@[nolint unusedArguments]
lemma aestronglyMeasurable_iInf_antitone
    {α : Type*} {m₀ : MeasurableSpace α} {μ : @MeasureTheory.Measure α m₀}
    {m : ℕ → MeasurableSpace α}
    (h_anti : Antitone m)
    (_h_le : ∀ N, m N ≤ m₀)
    (f : α → ℝ)
    (hf : ∀ N, @MeasureTheory.AEStronglyMeasurable α ℝ _ (m N) m₀ f μ) :
    @MeasureTheory.AEStronglyMeasurable α ℝ _ (⨅ N, m N) m₀ f μ := by
  -- Step 1: Extract strongly measurable representatives for each N
  let g : ℕ → α → ℝ := fun N => (hf N).mk f
  have hg_sm : ∀ N, @MeasureTheory.StronglyMeasurable α ℝ _ (m N) (g N) :=
    fun N => (hf N).stronglyMeasurable_mk
  have hg_meas : ∀ N, @Measurable α ℝ (m N) _ (g N) := fun N => (hg_sm N).measurable
  have hg_ae : ∀ N, f =ᵐ[μ] g N := fun N => (hf N).ae_eq_mk

  -- Step 2: Define h as the liminf of the g N
  let h : α → ℝ := fun x => Filter.liminf (fun N => g N x) Filter.atTop

  -- Step 3: Show h is Measurable[⨅ N, m N]
  have h_meas_each : ∀ N, @Measurable α ℝ (m N) _ h := by
    intro N
    have h_shift : h = fun x => Filter.liminf (fun n => g (n + N) x) Filter.atTop := by
      funext x
      exact (Filter.liminf_nat_add (fun n => g n x) N).symm
    rw [h_shift]
    have hg_meas_shifted : ∀ n, @Measurable α ℝ (m N) _ (g (n + N)) := fun n =>
      Measurable.mono (hg_meas (n + N)) (h_anti (Nat.le_add_left N n)) le_rfl
    haveI : MeasurableSpace α := m N
    exact Measurable.liminf hg_meas_shifted

  have h_meas : @Measurable α ℝ (⨅ N, m N) _ h := by
    intro s hs
    rw [MeasurableSpace.measurableSet_iInf]
    exact fun N => h_meas_each N hs

  -- Step 4: Show f =ᵐ h
  have h_ae_eq : f =ᵐ[μ] h := by
    have h_all_eq : ∀ᵐ x ∂μ, ∀ N, f x = g N x := by
      rw [MeasureTheory.ae_all_iff]
      exact hg_ae
    filter_upwards [h_all_eq] with x hx
    simp only [h]
    have h_const : ∀ N, g N x = f x := fun N => (hx N).symm
    simp_rw [h_const]
    exact (Filter.liminf_const (f x)).symm

  -- Step 5: Convert Measurable to StronglyMeasurable (for ℝ)
  have h_sm : @MeasureTheory.StronglyMeasurable α ℝ _ (⨅ N, m N) h := by
    haveI : MeasurableSpace α := ⨅ N, m N
    exact h_meas.stronglyMeasurable

  exact ⟨h, h_sm, h_ae_eq⟩

/-- AEStronglyMeasurable for a sub-σ-algebra is preserved under a.e. pointwise limits.

If `f n` are all Measurable[m] where `m ≤ m₀`, and `f n → g` a.e. (wrt a measure on m₀),
then `g` is AEStronglyMeasurable[m] (with the witness being the limsup, which is Measurable[m]).

This is the key lemma for "closedness" of L²[m] under L² limits:
we extract an a.e.-convergent subsequence and apply this. -/
@[nolint unusedArguments]
lemma aestronglyMeasurable_sub_of_tendsto_ae
    {α : Type*} {m₀ : MeasurableSpace α} {μ : @MeasureTheory.Measure α m₀}
    {m : MeasurableSpace α} (_hm : m ≤ m₀)
    {f : ℕ → α → ℝ} {g : α → ℝ}
    (hf_meas : ∀ n, @Measurable α ℝ m _ (f n))
    (hlim : ∀ᵐ x ∂μ, Filter.Tendsto (fun n => f n x) Filter.atTop (nhds (g x))) :
    @MeasureTheory.AEStronglyMeasurable α ℝ _ m m₀ g μ := by
  -- Strategy: construct h Measurable[m] with g =ᵐ[μ] h using limsup
  let h := fun x => Filter.atTop.limsup (fun n => f n x)
  have h_meas : @Measurable α ℝ m _ h := by
    haveI : MeasurableSpace α := m
    exact Measurable.limsup hf_meas
  have h_ae_eq : h =ᵐ[μ] g := by
    filter_upwards [hlim] with x hx
    exact Filter.Tendsto.limsup_eq hx
  have h_sm : @MeasureTheory.StronglyMeasurable α ℝ _ m h := by
    haveI : MeasurableSpace α := m
    exact h_meas.stronglyMeasurable
  exact ⟨h, h_sm, h_ae_eq.symm⟩
