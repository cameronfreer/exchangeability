/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
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

## Main results

* `aestronglyMeasurable_iInf_antitone`: AEStronglyMeasurable is preserved under
  infimum of antitone σ-algebras
* `aestronglyMeasurable_sub_of_tendsto_ae`: AEStronglyMeasurable for sub-σ-algebras
  is preserved under a.e. pointwise limits

## References

* Kallenberg (2005), *Foundations of Modern Probability*, for general treatment
-/

noncomputable section

open MeasureTheory Filter

/-! ## Lemma: AEStronglyMeasurable for infimum of σ-algebras

For real-valued functions, if f is AEStronglyMeasurable with respect to each σ-algebra
in an antitone (decreasing) sequence, then f is AEStronglyMeasurable with respect to
their infimum.

**Mathematical justification:**
1. For each N, we have a representative g_N with StronglyMeasurable[m N] g_N and f =ᵐ[μ] g_N
2. For ℝ-valued functions, StronglyMeasurable ↔ Measurable (via Measurable.stronglyMeasurable)
3. If f is Measurable[m N] for each N, then f is Measurable[⨅ N, m N] (by measurableSet_iInf)
4. Hence f is StronglyMeasurable[⨅ N, m N], giving AEStronglyMeasurable

The technical challenge is constructing a common representative from the a.e.-equal witnesses.
This is a standard measure-theoretic result that requires infrastructure not readily available
in current mathlib (dealing with representatives that differ on null sets for different σ-algebras).

**References:**
- Kallenberg (2005), *Foundations of Modern Probability*, for general treatment
- The result follows from properties of L² projections onto closed subspaces
-/
lemma aestronglyMeasurable_iInf_antitone
    {α : Type*} {m₀ : MeasurableSpace α} {μ : @MeasureTheory.Measure α m₀}
    {m : ℕ → MeasurableSpace α}
    (h_anti : Antitone m)  -- m N is decreasing in N
    (_h_le : ∀ N, m N ≤ m₀)  -- each m N is a sub-σ-algebra of the ambient
    (f : α → ℝ)
    (hf : ∀ N, @MeasureTheory.AEStronglyMeasurable α ℝ _ (m N) m₀ f μ) :
    @MeasureTheory.AEStronglyMeasurable α ℝ _ (⨅ N, m N) m₀ f μ := by
  -- Strategy: Use liminf of witnesses to construct a common representative
  -- that is measurable with respect to ⨅ N, m N.

  -- Step 1: Extract strongly measurable representatives for each N
  let g : ℕ → α → ℝ := fun N => (hf N).mk f
  have hg_sm : ∀ N, @MeasureTheory.StronglyMeasurable α ℝ _ (m N) (g N) :=
    fun N => (hf N).stronglyMeasurable_mk
  have hg_meas : ∀ N, @Measurable α ℝ (m N) _ (g N) :=
    fun N => (hg_sm N).measurable
  have hg_ae : ∀ N, f =ᵐ[μ] g N := fun N => (hf N).ae_eq_mk

  -- Step 2: Define h as the liminf of the g N
  let h : α → ℝ := fun x => Filter.liminf (fun N => g N x) Filter.atTop

  -- Step 3: Show h is Measurable[⨅ N, m N]
  -- This means: for each N, h is Measurable[m N]
  have h_meas_each : ∀ N, @Measurable α ℝ (m N) _ h := by
    intro N
    -- Key: liminf (g n) = liminf (g (n + N)) by Filter.liminf_nat_add
    -- And for n ≥ 0, g (n + N) is Measurable[m (n + N)] ≤ Measurable[m N] (by antitonicity)
    have h_shift : h = fun x => Filter.liminf (fun n => g (n + N) x) Filter.atTop := by
      funext x
      exact (Filter.liminf_nat_add (fun n => g n x) N).symm
    rw [h_shift]
    -- Now show liminf of g (n + N) is Measurable[m N]
    -- Each g (n + N) is Measurable[m (n + N)], and m (n + N) ≤ m N by antitonicity
    have hg_meas_shifted : ∀ n, @Measurable α ℝ (m N) _ (g (n + N)) := by
      intro n
      have h_le_N : m (n + N) ≤ m N := h_anti (Nat.le_add_left N n)
      exact Measurable.mono (hg_meas (n + N)) h_le_N le_rfl
    haveI : MeasurableSpace α := m N
    exact Measurable.liminf hg_meas_shifted

  -- Now conclude Measurable[⨅ N, m N] h
  have h_meas : @Measurable α ℝ (⨅ N, m N) _ h := by
    intro s hs
    rw [MeasurableSpace.measurableSet_iInf]
    exact fun N => h_meas_each N hs

  -- Step 4: Show f =ᵐ h
  -- On the set where f = g N for all N, we have h = f
  have h_ae_eq : f =ᵐ[μ] h := by
    -- Countable intersection of full-measure sets is full-measure
    have h_all_eq : ∀ᵐ x ∂μ, ∀ N, f x = g N x := by
      rw [MeasureTheory.ae_all_iff]
      intro N
      exact hg_ae N
    filter_upwards [h_all_eq] with x hx
    -- At x, f x = g N x for all N, so liminf (g N x) = f x
    simp only [h]
    have h_const : ∀ N, g N x = f x := fun N => (hx N).symm
    simp_rw [h_const]
    exact (Filter.liminf_const (f x)).symm

  -- Step 5: Convert Measurable to StronglyMeasurable (for ℝ)
  have h_sm : @MeasureTheory.StronglyMeasurable α ℝ _ (⨅ N, m N) h := by
    haveI : MeasurableSpace α := ⨅ N, m N
    exact h_meas.stronglyMeasurable

  -- Step 6: Conclude AEStronglyMeasurable
  exact ⟨h, h_sm, h_ae_eq⟩

/-- AEStronglyMeasurable for a sub-σ-algebra is preserved under a.e. pointwise limits.

If `f n` are all Measurable[m] where `m ≤ m₀`, and `f n → g` a.e. (wrt a measure on m₀),
then `g` is AEStronglyMeasurable[m] (with the witness being the limsup, which is Measurable[m]).

This is the key lemma for "closedness" of L²[m] under L² limits:
we extract an a.e.-convergent subsequence and apply this. -/
lemma aestronglyMeasurable_sub_of_tendsto_ae
    {α : Type*} {m₀ : MeasurableSpace α} {μ : @MeasureTheory.Measure α m₀}
    {m : MeasurableSpace α} (_hm : m ≤ m₀)
    {f : ℕ → α → ℝ} {g : α → ℝ}
    (hf_meas : ∀ n, @Measurable α ℝ m _ (f n))
    (hlim : ∀ᵐ x ∂μ, Filter.Tendsto (fun n => f n x) Filter.atTop (nhds (g x))) :
    @MeasureTheory.AEStronglyMeasurable α ℝ _ m m₀ g μ := by
  -- Strategy: construct h Measurable[m] with g =ᵐ[μ] h
  -- Use limsup as the witness
  let h := fun x => Filter.atTop.limsup (fun n => f n x)
  -- h is Measurable[m] by Measurable.limsup
  have h_meas : @Measurable α ℝ m _ h := by
    haveI : MeasurableSpace α := m
    exact Measurable.limsup hf_meas
  -- h = g a.e. because on the convergence set, limsup = lim = g
  have h_ae_eq : h =ᵐ[μ] g := by
    filter_upwards [hlim] with x hx
    exact Filter.Tendsto.limsup_eq hx
  -- Convert Measurable[m] h to StronglyMeasurable[m] h (for ℝ)
  have h_sm : @MeasureTheory.StronglyMeasurable α ℝ _ m h := by
    haveI : MeasurableSpace α := m
    exact h_meas.stronglyMeasurable
  -- Conclude AEStronglyMeasurable[m] g using h as witness
  exact ⟨h, h_sm, h_ae_eq.symm⟩
