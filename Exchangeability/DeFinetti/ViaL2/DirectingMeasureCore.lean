/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Exchangeability.DeFinetti.ViaL2.AlphaConvergence

/-!
# Directing Measure Core: CDF and Measure Construction

This file defines the core components of the directing measure construction:
- `cdf_from_alpha`: The regularized CDF built from alpha functions via Stieltjes extension
- `directing_measure`: The probability measure on ℝ for each ω ∈ Ω
- `directing_measure_isProbabilityMeasure`: Proof that ν(ω) is a probability measure

## Main definitions

* `cdf_from_alpha`: CDF function F(ω,t) via `stieltjesOfMeasurableRat`
* `directing_measure`: The directing measure ν : Ω → Measure ℝ

## Main results

* `cdf_from_alpha_mono`: F(ω,·) is monotone nondecreasing
* `cdf_from_alpha_rightContinuous`: F(ω,·) is right-continuous
* `cdf_from_alpha_bounds`: 0 ≤ F(ω,t) ≤ 1
* `alphaIic_ae_tendsto_zero_at_bot`: a.e. limit 0 at -∞ for alphaIic
* `alphaIic_ae_tendsto_one_at_top`: a.e. limit 1 at +∞ for alphaIic
* `directing_measure_isProbabilityMeasure`: ν(ω) is a probability measure for each ω

## References

* Kallenberg (2005), *Probabilistic Symmetries and Invariance Principles*,
  Chapter 1, "Second proof of Theorem 1.1"
-/

noncomputable section

namespace Exchangeability.DeFinetti.ViaL2

open MeasureTheory ProbabilityTheory BigOperators Filter Topology
open Exchangeability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-!
## CDF Construction

The CDF F(ω,t) is built from the rational-valued alpha functions using
mathlib's `stieltjesOfMeasurableRat` construction, which automatically:
- Patches the null set where CDF properties might fail
- Ensures right-continuity and proper limits
- Produces a valid probability measure via Carathéodory extension
-/

noncomputable def cdf_from_alpha
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ)
    (ω : Ω) (t : ℝ) : ℝ :=
  (ProbabilityTheory.stieltjesOfMeasurableRat
      (alphaIicRat X hX_contract hX_meas hX_L2)
      (measurable_alphaIicRat X hX_contract hX_meas hX_L2)
      ω) t

/-- F(ω,·) is monotone nondecreasing. -/
lemma cdf_from_alpha_mono
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ)
    (ω : Ω) :
    Monotone (cdf_from_alpha X hX_contract hX_meas hX_L2 ω) := fun s t hst =>
  (ProbabilityTheory.stieltjesOfMeasurableRat
      (alphaIicRat X hX_contract hX_meas hX_L2)
      (measurable_alphaIicRat X hX_contract hX_meas hX_L2)
      ω).mono hst

/-- Right-continuity in t: F(ω,t) = lim_{u↘t} F(ω,u). -/
lemma cdf_from_alpha_rightContinuous
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ)
    (ω : Ω) :
    ∀ t, Filter.Tendsto (cdf_from_alpha X hX_contract hX_meas hX_L2 ω)
      (𝓝[>] t) (𝓝 (cdf_from_alpha X hX_contract hX_meas hX_L2 ω t)) := by
  intro t
  -- StieltjesFunction.right_continuous gives ContinuousWithinAt at Ici t
  -- We need Tendsto at 𝓝[>] t = 𝓝[Ioi t] t
  -- continuousWithinAt_Ioi_iff_Ici provides the equivalence
  let f := ProbabilityTheory.stieltjesOfMeasurableRat
      (alphaIicRat X hX_contract hX_meas hX_L2)
      (measurable_alphaIicRat X hX_contract hX_meas hX_L2)
      ω
  have h_rc : ContinuousWithinAt f (Set.Ici t) t := f.right_continuous t
  -- Convert ContinuousWithinAt (Ici) to ContinuousWithinAt (Ioi)
  rw [← continuousWithinAt_Ioi_iff_Ici] at h_rc
  exact h_rc

/-- Bounds 0 ≤ F ≤ 1 (pointwise in ω,t). -/
lemma cdf_from_alpha_bounds
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ)
    (ω : Ω) (t : ℝ) :
    0 ≤ cdf_from_alpha X hX_contract hX_meas hX_L2 ω t
    ∧ cdf_from_alpha X hX_contract hX_meas hX_L2 ω t ≤ 1 := by
  -- The stieltjesOfMeasurableRat construction produces a function with limits 0 at -∞ and 1 at +∞.
  -- By monotonicity, all values are in [0,1].
  let f := ProbabilityTheory.stieltjesOfMeasurableRat
      (alphaIicRat X hX_contract hX_meas hX_L2)
      (measurable_alphaIicRat X hX_contract hX_meas hX_L2)
      ω
  have h_tendsto_bot : Filter.Tendsto (f ·) Filter.atBot (𝓝 0) :=
    ProbabilityTheory.tendsto_stieltjesOfMeasurableRat_atBot
      (measurable_alphaIicRat X hX_contract hX_meas hX_L2) ω
  have h_tendsto_top : Filter.Tendsto (f ·) Filter.atTop (𝓝 1) :=
    ProbabilityTheory.tendsto_stieltjesOfMeasurableRat_atTop
      (measurable_alphaIicRat X hX_contract hX_meas hX_L2) ω
  have h_mono : Monotone (f ·) := f.mono
  constructor
  · -- Lower bound: f(t) ≥ 0
    -- For any s < t, f(s) ≤ f(t) by monotonicity.
    -- As s → -∞, f(s) → 0, so 0 ≤ f(t).
    -- Proof by contradiction: if f(t) < 0, pick ε = -f(t)/2 > 0.
    -- Then eventually f(s) ∈ (-ε, ε), so f(s) > -ε = f(t)/2.
    -- But also f(s) ≤ f(t) for s ≤ t, contradicting f(s) > f(t)/2 > f(t).
    by_contra h_neg
    push_neg at h_neg
    -- f(t) < 0, so ε := -f(t)/2 > 0
    set ε := -cdf_from_alpha X hX_contract hX_meas hX_L2 ω t / 2 with hε_def
    have hε_pos : 0 < ε := by simp [hε_def]; linarith
    -- Eventually f(s) ∈ (-ε, ε)
    have h_nhds : Set.Ioo (-ε) ε ∈ 𝓝 (0 : ℝ) := Ioo_mem_nhds (by linarith) hε_pos
    have h_preimage := h_tendsto_bot h_nhds
    rw [Filter.mem_map, Filter.mem_atBot_sets] at h_preimage
    obtain ⟨N, hN⟩ := h_preimage
    -- Take s = min N t, then s ≤ N and s ≤ t
    let s := min N t
    have hs_le_N : s ≤ N := min_le_left N t
    have hs_le_t : s ≤ t := min_le_right N t
    -- f(s) ∈ (-ε, ε)
    have hs_in : f s ∈ Set.Ioo (-ε) ε := hN s hs_le_N
    simp only [Set.mem_Ioo] at hs_in
    -- f(s) ≤ f(t) by monotonicity
    have hs_mono : f s ≤ f t := h_mono hs_le_t
    -- Connect f t with cdf_from_alpha
    have h_eq_t : (f : ℝ → ℝ) t = cdf_from_alpha X hX_contract hX_meas hX_L2 ω t := rfl
    -- Now we have: f(s) > -ε = f(t)/2 and f(s) ≤ f(t) < 0
    have h1 : f s > -ε := hs_in.1
    have h2 : -ε = cdf_from_alpha X hX_contract hX_meas hX_L2 ω t / 2 := by
      simp [hε_def]; ring
    -- f(s) > f(t)/2 and f(s) ≤ f(t) < 0
    -- If f(t) < 0, then f(t)/2 > f(t), so f(s) > f(t)/2 > f(t) contradicts f(s) ≤ f(t).
    have h_contra : cdf_from_alpha X hX_contract hX_meas hX_L2 ω t / 2 >
                    cdf_from_alpha X hX_contract hX_meas hX_L2 ω t := by linarith
    linarith [h1, h2, hs_mono, h_eq_t, h_contra]
  · -- Upper bound: f(t) ≤ 1
    -- Similar argument: for any s > t, f(t) ≤ f(s) by monotonicity.
    -- As s → +∞, f(s) → 1, so f(t) ≤ 1.
    by_contra h_gt
    push_neg at h_gt
    -- f(t) > 1, so ε := (f(t) - 1)/2 > 0
    set ε := (cdf_from_alpha X hX_contract hX_meas hX_L2 ω t - 1) / 2 with hε_def
    have hε_pos : 0 < ε := by simp [hε_def]; linarith
    -- Eventually f(s) ∈ (1-ε, 1+ε)
    have h_nhds : Set.Ioo (1 - ε) (1 + ε) ∈ 𝓝 (1 : ℝ) := Ioo_mem_nhds (by linarith) (by linarith)
    have h_preimage := h_tendsto_top h_nhds
    rw [Filter.mem_map, Filter.mem_atTop_sets] at h_preimage
    obtain ⟨N, hN⟩ := h_preimage
    -- Take s = max N t, then s ≥ N and s ≥ t
    let s := max N t
    have hs_ge_N : N ≤ s := le_max_left N t
    have hs_ge_t : t ≤ s := le_max_right N t
    -- f(s) ∈ (1-ε, 1+ε)
    have hs_in : f s ∈ Set.Ioo (1 - ε) (1 + ε) := hN s hs_ge_N
    simp only [Set.mem_Ioo] at hs_in
    -- f(t) ≤ f(s) by monotonicity
    have hs_mono : f t ≤ f s := h_mono hs_ge_t
    -- Connect f t with cdf_from_alpha
    have h_eq_t : (f : ℝ → ℝ) t = cdf_from_alpha X hX_contract hX_meas hX_L2 ω t := rfl
    -- f(s) < 1 + ε = 1 + (f(t) - 1)/2 = (f(t) + 1)/2
    have h1 : f s < 1 + ε := hs_in.2
    have h2 : 1 + ε = (cdf_from_alpha X hX_contract hX_meas hX_L2 ω t + 1) / 2 := by
      simp [hε_def]; ring
    -- f(t) ≤ f(s) < (f(t) + 1)/2
    -- So f(t) < (f(t) + 1)/2, which means 2*f(t) < f(t) + 1, i.e., f(t) < 1.
    -- But we assumed f(t) > 1, contradiction.
    linarith [h1, h2, hs_mono, h_eq_t, h_gt]

/-!
## A.e. endpoint limits for alphaIic

These lemmas establish a.e. convergence of `alphaIic` at ±∞ by combining:
1. The a.e. equality `alphaIic =ᵐ alphaIicCE` (from AlphaConvergence)
2. The a.e. convergence of `alphaIicCE` (from AlphaConvergence)
-/

/-- **A.e. convergence of α_{Iic t} → 0 as t → -∞ (along integers).**

This is the a.e. version of the endpoint limit. The statement for all ω cannot be
proven from the L¹ construction since `alphaIic` is defined via existential L¹ choice.

**Proof strategy:**
Combine the a.e. equality `alphaIic =ᵐ alphaIicCE` with `alphaIicCE_ae_tendsto_zero_atBot`.
Since both are a.e. statements and we take countable intersection over integers, we
get a.e. convergence of `alphaIic` along the integer sequence `-(n:ℝ)`.
-/
lemma alphaIic_ae_tendsto_zero_at_bot
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ =>
      alphaIic X hX_contract hX_meas hX_L2 (-(n : ℝ)) ω) atTop (𝓝 0) := by
  -- Step 1: For a.e. ω, alphaIic agrees with alphaIicCE at all integers
  have h_ae_eq : ∀ᵐ ω ∂μ, ∀ n : ℕ,
      alphaIic X hX_contract hX_meas hX_L2 (-(n : ℝ)) ω =
      alphaIicCE X hX_contract hX_meas hX_L2 (-(n : ℝ)) ω := by
    rw [ae_all_iff]
    intro n
    exact alphaIic_ae_eq_alphaIicCE X hX_contract hX_meas hX_L2 (-(n : ℝ))

  -- Step 2: alphaIicCE converges to 0 as t → -∞ for a.e. ω
  have h_CE_conv := alphaIicCE_ae_tendsto_zero_atBot X hX_contract hX_meas hX_L2

  -- Step 3: Combine to get alphaIic convergence for a.e. ω
  filter_upwards [h_ae_eq, h_CE_conv] with ω h_eq h_conv
  -- At this ω, alphaIic = alphaIicCE at all integers, and alphaIicCE → 0
  exact h_conv.congr (fun n => (h_eq n).symm)

/-- **A.e. convergence of α_{Iic t} → 1 as t → +∞ (along integers).**

This is the dual of `alphaIic_ae_tendsto_zero_at_bot`. The statement for all ω cannot be
proven from the L¹ construction since `alphaIic` is defined via existential L¹ choice.

**Proof strategy:**
Combine the a.e. equality `alphaIic =ᵐ alphaIicCE` with `alphaIicCE_ae_tendsto_one_atTop`.
-/
lemma alphaIic_ae_tendsto_one_at_top
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ =>
      alphaIic X hX_contract hX_meas hX_L2 (n : ℝ) ω) atTop (𝓝 1) := by
  -- Step 1: For a.e. ω, alphaIic agrees with alphaIicCE at all positive integers
  have h_ae_eq : ∀ᵐ ω ∂μ, ∀ n : ℕ,
      alphaIic X hX_contract hX_meas hX_L2 (n : ℝ) ω =
      alphaIicCE X hX_contract hX_meas hX_L2 (n : ℝ) ω := by
    rw [ae_all_iff]
    intro n
    exact alphaIic_ae_eq_alphaIicCE X hX_contract hX_meas hX_L2 (n : ℝ)

  -- Step 2: alphaIicCE converges to 1 as t → +∞ for a.e. ω
  have h_CE_conv := alphaIicCE_ae_tendsto_one_atTop X hX_contract hX_meas hX_L2

  -- Step 3: Combine to get alphaIic convergence for a.e. ω
  filter_upwards [h_ae_eq, h_CE_conv] with ω h_eq h_conv
  exact h_conv.congr (fun n => (h_eq n).symm)

-- **Note on `cdf_from_alpha_limits`:**
-- The axiom in MoreL2Helpers.lean requires the CDF limits to hold for ALL ω.
-- However, from the L¹ construction, we can only prove a.e. convergence:
-- - `alphaIic_ae_tendsto_zero_at_bot`: a.e. convergence to 0 as t → -∞
-- - `alphaIic_ae_tendsto_one_at_top`: a.e. convergence to 1 as t → +∞
--
-- The axiom should be weakened to an a.e. statement, and the `directing_measure`
-- construction should handle the null set by using a default probability measure
-- for ω outside the "good" set. This is a standard technique in probability theory.

/-!
## Directing Measure Definition

The directing measure ν(ω) is built from the CDF via mathlib's
`stieltjesOfMeasurableRat.measure` construction. This automatically
handles the null set patching and produces a probability measure for ALL ω.
-/

/-- Build the directing measure ν from the CDF.

For each ω ∈ Ω, we construct ν(ω) as the probability measure on ℝ with CDF
given by t ↦ cdf_from_alpha X ω t.

This is defined directly using `stieltjesOfMeasurableRat.measure`, which gives a
probability measure for ALL ω (not just a.e.) because the `stieltjesOfMeasurableRat`
construction patches the null set automatically. -/
noncomputable def directing_measure
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ) :
    Ω → Measure ℝ :=
  fun ω =>
    (ProbabilityTheory.stieltjesOfMeasurableRat
        (alphaIicRat X hX_contract hX_meas hX_L2)
        (measurable_alphaIicRat X hX_contract hX_meas hX_L2)
        ω).measure

/-- The directing measure is a probability measure.

This is now trivial because `directing_measure` is defined via `stieltjesOfMeasurableRat.measure`,
which automatically has an `IsProbabilityMeasure` instance from mathlib. -/
lemma directing_measure_isProbabilityMeasure
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ)
    (ω : Ω) :
    IsProbabilityMeasure (directing_measure X hX_contract hX_meas hX_L2 ω) :=
  ProbabilityTheory.instIsProbabilityMeasure_stieltjesOfMeasurableRat
    (measurable_alphaIicRat X hX_contract hX_meas hX_L2) ω

end Exchangeability.DeFinetti.ViaL2
