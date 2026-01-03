/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Probability.ConditionalExpectation
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-!
# Basic Helper Lemmas for Conditional Expectation

This file provides basic helper lemmas for working with conditional expectations,
set integration, σ-finiteness, and indicator functions.

These are foundational utilities extracted from the main CondExp.lean file to
improve compilation speed.

## Main components

### Set Integration
- `setIntegral_congr_ae'`: Congru ence for set integrals on restricted measures
- `setIntegral_congr_ae_of_ae`: Congruence for set integrals from global a.e. equality

### σ-Finiteness
- `sigmaFinite_trim_of_le`: Trimmed measure inherits σ-finiteness from finite measures

### Indicators
- `indicator_iUnion_tsum_of_pairwise_disjoint`: Union of disjoint indicators equals their sum

-/

noncomputable section
open scoped MeasureTheory ProbabilityTheory Topology
open MeasureTheory Filter Set Function

namespace Exchangeability.Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-! ### Helper lemmas for set integration -/

/-- If two functions are a.e. equal on `μ.restrict s`, their set integrals on `s` coincide. -/
lemma setIntegral_congr_ae'
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure Ω} {s : Set Ω} {f g : Ω → E}
    (hfg : f =ᵐ[μ.restrict s] g) :
    ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ :=
  integral_congr_ae hfg

/-- If two functions are a.e. equal under `μ`, their set integrals on any `s` coincide. -/
lemma setIntegral_congr_ae_of_ae
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure Ω} {s : Set Ω} {f g : Ω → E}
    (hfgμ : f =ᵐ[μ] g) :
    ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ :=
  setIntegral_congr_ae' (ae_restrict_of_ae hfgμ)

/-! ### Helper lemmas for σ-finiteness and indicators

Note: Some lemmas in this section explicitly include `{m m₀ : MeasurableSpace Ω}` as parameters
to work with multiple measurable space structures (e.g., for trimmed measures). This makes the
section variable `[MeasurableSpace Ω]` unused for those lemmas, requiring `set_option
linter.unusedSectionVars false`. -/

set_option linter.unusedSectionVars false in
/-- If `μ` is finite, then any trim of `μ` is σ-finite. -/
lemma sigmaFinite_trim_of_le {m m₀ : MeasurableSpace Ω}
    (μ : Measure Ω) [IsFiniteMeasure μ] (hm : m ≤ m₀) :
    SigmaFinite (μ.trim hm) :=
  (inferInstance : IsFiniteMeasure (μ.trim hm)).toSigmaFinite

set_option linter.unusedSectionVars false in
/-- For pairwise disjoint sets, the indicator of the union equals
the pointwise `tsum` of indicators (for ℝ-valued constants). -/
lemma indicator_iUnion_tsum_of_pairwise_disjoint
    (f : ℕ → Set Ω) (hdisj : Pairwise (Disjoint on f)) :
    (fun ω => ((⋃ i, f i).indicator (fun _ => (1 : ℝ)) ω))
      = fun ω => ∑' i, (f i).indicator (fun _ => (1 : ℝ)) ω := by
  classical
  funext ω
  by_cases h : ω ∈ ⋃ i, f i
  · -- ω ∈ ⋃ i, f i: exactly one index i has ω ∈ f i
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp h
    have huniq : ∀ j, ω ∈ f j → j = i := by
      intro j hj
      by_contra hne
      have : Disjoint (f i) (f j) := hdisj (Ne.symm hne)
      exact this.le_bot ⟨hi, hj⟩
    -- Only f i contributes, all others are 0
    calc (⋃ k, f k).indicator (fun _ => (1:ℝ)) ω
        = 1 := Set.indicator_of_mem h _
      _ = ∑' j, if j = i then (1:ℝ) else 0 := by rw [tsum_ite_eq]
      _ = ∑' j, (f j).indicator (fun _ => (1:ℝ)) ω := by
          congr 1; ext j
          by_cases hj : ω ∈ f j
          · rw [Set.indicator_of_mem hj, huniq j hj]; simp
          · rw [Set.indicator_of_notMem hj]
            by_cases hji : j = i
            · exact absurd (hji ▸ hi) hj
            · simp [hji]
  · -- ω ∉ ⋃ i, f i: all f i miss ω
    have : ∀ i, ω ∉ f i := fun i hi => h (Set.mem_iUnion.mpr ⟨i, hi⟩)
    simp [Set.indicator_of_notMem h, Set.indicator_of_notMem (this _)]

set_option linter.unusedSectionVars false in
/-- For pairwise disjoint sets, the tsum of indicators is bounded by 1 at each point.
This follows from the fact that at most one indicator is 1 at any point. -/
lemma indicator_tsum_le_one_of_pairwise_disjoint
    (f : ℕ → Set Ω) (hdisj : Pairwise (Disjoint on f)) (x : Ω) :
    ∑' i, (f i).indicator (fun _ => (1:ℝ)) x ≤ 1 := by
  by_cases hx : x ∈ ⋃ i, f i
  · obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
    have huniq : ∀ k, x ∈ f k → k = j := fun k hk => by
      by_contra hne
      have : Disjoint (f j) (f k) := hdisj (Ne.symm hne)
      exact this.le_bot ⟨hj, hk⟩
    calc ∑' i, (f i).indicator (fun _ => (1:ℝ)) x
        = ∑' i, if i = j then 1 else 0 := by
          congr 1; ext i
          by_cases hi : x ∈ f i
          · rw [Set.indicator_of_mem hi, huniq i hi]; simp
          · rw [Set.indicator_of_notMem hi]
            by_cases hij : i = j
            · exact absurd (hij ▸ hj) hi
            · simp [hij]
      _ = 1 := tsum_ite_eq j 1
      _ ≤ 1 := le_refl 1
  · have : ∀ i, x ∉ f i := fun i hi => hx (Set.mem_iUnion.mpr ⟨i, hi⟩)
    simp [Set.indicator_of_notMem (this _)]

set_option linter.unusedSectionVars false in
/-- For pairwise disjoint measurable sets, the tsum of measures equals the measure of the union. -/
lemma measure_tsum_eq_measure_iUnion {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : ℕ → Set α) (hf_meas : ∀ i, MeasurableSet (f i))
    (hdisj : Pairwise (Disjoint on f)) :
    ∑' i, μ (f i) = μ (⋃ i, f i) :=
  (measure_iUnion (fun _ _ hij => hdisj hij) hf_meas).symm

set_option linter.unusedSectionVars false in
/-- For pairwise disjoint measurable sets under a probability measure,
the tsum of measures is at most 1. -/
lemma measure_tsum_le_one_of_pairwise_disjoint {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (f : ℕ → Set α) (hf_meas : ∀ i, MeasurableSet (f i))
    (hdisj : Pairwise (Disjoint on f)) :
    ∑' i, μ (f i) ≤ 1 := by
  calc ∑' i, μ (f i) = μ (⋃ i, f i) := measure_tsum_eq_measure_iUnion μ f hf_meas hdisj
    _ ≤ μ Set.univ := measure_mono (Set.subset_univ _)
    _ = 1 := measure_univ

end Exchangeability.Probability
