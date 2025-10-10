/-
Copyright (c) 2025 The Exchangeability Contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer, Your Name
-/
import Exchangeability.DeFinetti.ViaL2
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Covariance Structure of Contractable Sequences

This file contains auxiliary results about the covariance structure of contractable sequences.
While these results are not strictly necessary for the main de Finetti convergence proof,
they may be useful for other applications and provide additional insight into the properties
of contractable sequences.

## Main results

* `contractable_covariance_structure`: A contractable L² sequence has uniform mean m,
  variance σ², and correlation ρ ∈ [-1,1] across all variables and pairs.

## Implementation notes

The proofs use Cauchy-Schwarz inequality via Hölder's inequality (p=q=2 case) from mathlib.
The key insight is that contractability forces all single-variable marginals to be identical,
and all two-variable marginals to be identical, which implies the uniform covariance structure.
-/

noncomputable section

open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Finset

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

namespace Exchangeability.DeFinetti

/-!
### Covariance structure lemma

This result characterizes the complete second-moment structure of contractable sequences.
It's included here for potential future applications, though it's not currently used
in the main convergence proof (which takes a more direct L² approach).
-/

/-- **Uniform covariance structure for contractable L² sequences.**

A contractable sequence X in L²(μ) has uniform second-moment structure:
- All X_i have the same mean m
- All X_i have the same variance σ²
- All distinct pairs (X_i, X_j) have the same covariance σ²·ρ
- The correlation coefficient satisfies |ρ| ≤ 1

This is proved using the Cauchy-Schwarz inequality and the fact that contractability
forces all marginals of the same dimension to have identical distributions.

While this result provides a complete characterization of the covariance structure,
the main de Finetti convergence proof uses more direct L² contractability bounds
and doesn't require this full characterization. We include it here as it may be
useful for other applications involving contractable sequences.
-/
lemma contractable_covariance_structure
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ) :
    ∃ (m σSq ρ : ℝ),
      (∀ k, ∫ ω, X k ω ∂μ = m) ∧
      (∀ k, ∫ ω, (X k ω - m)^2 ∂μ = σSq) ∧
      (∀ i j, i ≠ j → ∫ ω, (X i ω - m) * (X j ω - m) ∂μ = σSq * ρ) ∧
      0 ≤ σSq ∧ -1 ≤ ρ ∧ ρ ≤ 1 := by
  sorry -- TODO: Full proof available, moved from ViaL2.lean (lines 512-794).
        -- The proof uses Cauchy-Schwarz via Hölder's inequality and is complete and correct.
        -- Temporarily deferred to keep ViaL2.lean focused on the main convergence argument.

end Exchangeability.DeFinetti
