/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Exchangeability.DeFinetti.ViaL2.DirectingMeasureBridge

/-!
# Directing Measure Integrals: Bridge Lemma and Conditional Expectation

This file establishes the bridge lemma connecting the directing measure to conditional
expectation: for bounded measurable `f`,

  ∫ f dν(ω) = E[f(X₀) | tail](ω)  a.e.

The proof routes through the kernel-level identification
`directing_measure_ae_eq_condExpKernel_map` plus mathlib's
`condExp_ae_eq_integral_condExpKernel`.

## Main result

* `directing_measure_integral_eq_condExp`: bridge lemma (routes through
  `DirectingMeasureBridge`).

## References

* Kallenberg (2005), *Probabilistic Symmetries and Invariance Principles*,
  Chapter 1, "Second proof of Theorem 1.1"
-/

noncomputable section

namespace Exchangeability.DeFinetti.ViaL2

open MeasureTheory ProbabilityTheory BigOperators Filter Topology
open Exchangeability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- **Bridge lemma:** For bounded measurable `f`,

`fun ω => ∫ x, f x ∂(directing_measure X … ω)` agrees a.e. with the conditional expectation
`μ[fun ω => f (X 0 ω) | tailSigma X]`.

The proof routes through the kernel-level bridge
`directing_measure_ae_eq_condExpKernel_map` and mathlib's
`condExp_ae_eq_integral_condExpKernel`, replacing what was previously a hand-built
monotone-class extension from `Iic` indicators.

The `[StandardBorelSpace Ω]` assumption comes from `condExpKernel`. -/
lemma directing_measure_integral_eq_condExp
    [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ)
    (f : ℝ → ℝ) (hf_meas : Measurable f) (hf_bdd : ∃ M, ∀ x, |f x| ≤ M) :
    (fun ω => ∫ x, f x ∂(directing_measure X hX_contract hX_meas hX_L2 ω))
      =ᵐ[μ] μ[fun ω => f (X 0 ω) | TailSigma.tailSigma X] := by
  have hm_le : TailSigma.tailSigma X ≤ (inferInstance : MeasurableSpace Ω) :=
    TailSigma.tailSigma_le X hX_meas
  obtain ⟨M, hM⟩ := hf_bdd
  -- `f ∘ X 0` is integrable on the probability space (bounded measurable).
  have hfX0_int : Integrable (fun ω => f (X 0 ω)) μ := by
    refine Integrable.mono' (integrable_const (max M 0)) ?_ ?_
    · exact (hf_meas.comp (hX_meas 0)).aestronglyMeasurable
    · filter_upwards with ω
      rw [Real.norm_eq_abs]
      exact (hM (X 0 ω)).trans (le_max_left _ _)
  -- Bridge: a.e. in ω, `directing_measure ω = (condExpKernel μ (tailSigma X) ω).map (X 0)`.
  have h_bridge := directing_measure_ae_eq_condExpKernel_map X hX_contract hX_meas hX_L2
  -- Hence the integral against `directing_measure ω` equals the integral of `f ∘ X 0`
  -- against the kernel at `ω`, by `integral_map`.
  have h_push : (fun ω => ∫ x, f x ∂(directing_measure X hX_contract hX_meas hX_L2 ω))
      =ᵐ[μ] fun ω => ∫ y, f (X 0 y)
          ∂(condExpKernel (μ := μ) (m := TailSigma.tailSigma X) ω) := by
    filter_upwards [h_bridge] with ω hω
    rw [hω]
    exact integral_map (hX_meas 0).aemeasurable hf_meas.aestronglyMeasurable
  -- The kernel integral identifies the conditional expectation.
  exact h_push.trans
    (condExp_ae_eq_integral_condExpKernel hm_le hfX0_int).symm
end Exchangeability.DeFinetti.ViaL2
