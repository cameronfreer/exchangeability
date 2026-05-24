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

* `alphaIic_ae_tendsto_zero_at_bot`: a.e. limit 0 at -∞ for alphaIic
* `alphaIic_ae_tendsto_one_at_top`: a.e. limit 1 at +∞ for alphaIic
* `directing_measure_isProbabilityMeasure`: ν(ω) is a probability measure for each ω

Monotonicity, right-continuity, and bounds on the CDF are inherited directly from
mathlib's `stieltjesOfMeasurableRat`; no project-local wrappers are needed.

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

/-- CDF function constructed from the alpha conditional expectations.
This is the right-continuous version obtained via Stieltjes extension. -/
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
