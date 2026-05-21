/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Probability.ConditionalExpectation
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.MeasurableSpace.Prod
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.Kernel.Composition.Comp
import Exchangeability.Core
import Exchangeability.Contractability
import Exchangeability.ConditionallyIID
import Exchangeability.Probability.CondExp
import Exchangeability.Probability.CondIndep
import Exchangeability.Probability.Martingale
import Exchangeability.Probability.TripleLawDropInfo
import Exchangeability.Tail.TailSigma
import Exchangeability.DeFinetti.MartingaleHelpers
import Exchangeability.DeFinetti.CommonEnding
import Exchangeability.DeFinetti.ViaMartingale.LocalInfrastructure
import Exchangeability.DeFinetti.ViaMartingale.PairLawEquality
import Exchangeability.DeFinetti.ViaMartingale.ShiftOperations
import Exchangeability.DeFinetti.ViaMartingale.RevFiltration
import Exchangeability.DeFinetti.ViaMartingale.FutureFiltration
import Exchangeability.DeFinetti.ViaMartingale.FutureRectangles
import Exchangeability.DeFinetti.ViaMartingale.FiniteCylinders
import Exchangeability.DeFinetti.ViaMartingale.CondExpConvergence
import Exchangeability.DeFinetti.ViaMartingale.DirectingMeasure
import Exchangeability.DeFinetti.ViaMartingale.IndicatorAlgebra
import Exchangeability.DeFinetti.ViaMartingale.Factorization
import Exchangeability.DeFinetti.ViaMartingale.FiniteProduct
import Exchangeability.Probability.MeasureKernels

/-!
# de Finetti's Theorem via Reverse Martingales

**Aldous' elegant martingale proof** of de Finetti's theorem, as presented in
Kallenberg (2005) as the "third proof". This approach has **medium dependencies**.

**Status**: COMPLETE - 0 sorries in this file. Builds successfully.

## Proof approach

The proof uses a contraction-independence lemma combined with reverse martingale
convergence:

1. **Lemma 1.3** (Contraction-Independence): If `(ξ, η) =^d (ξ, ζ)` and `σ(η) ⊆ σ(ζ)`,
   then `ξ ⊥⊥_η ζ`.

   **Proof idea:** For any `B`, define `μ₁ = P[ξ ∈ B | η]` and `μ₂ = P[ξ ∈ B | ζ]`.
   Then `(μ₁, μ₂)` is a bounded martingale with `μ₁ =^d μ₂`, so
   `E(μ₂ - μ₁)² = Eμ₂² - Eμ₁² = 0`, implying `μ₁ = μ₂` a.s.

2. **Main theorem**: If `ξ` is contractable, then `ξₙ` are conditionally i.i.d.
  given the tail σ-algebra `𝒯_ξ = ⋂_n σ(θ_n ξ)`.

  From contractability: `(ξ_m, θ_{m+1} ξ) =^d (ξ_k, θ_{m+1} ξ)` for `k ≤ m`.
  Using Lemma 1.3 and reverse martingale convergence:
  ```
  P[ξ_m ∈ B | θ_{m+1} ξ] = P[ξ_k ∈ B | θ_{m+1} ξ] → P[ξ_k ∈ B | 𝒯_ξ]
  ```
   This shows conditional independence and identical conditional laws.

## Main results

This file provides the proof infrastructure (helper lemmas and constructions)
for the reverse-martingale route. The public theorems
(`deFinetti`, `deFinetti_equivalence`, `deFinetti_RyllNardzewski_equivalence`)
live in `TheoremViaMartingale.lean`.

## Dependencies

⚖️ **Medium** - Requires martingale theory and reverse martingale convergence
✅ **Elegant** - Short and conceptually clear proof
✅ **Probabilistic** - Pure probability theory, no functional analysis

## References

* Kallenberg (2005), *Probabilistic Symmetries and Invariance Principles*,
  Lemma 1.3 and page 28: "Third proof of Theorem 1.1"
* Aldous (1983), *Exchangeability and related topics*

## Infrastructure dependencies

Helper modules `TripleLawDropInfo.lean` and `CondIndep.lean` supply the kernel
uniqueness and distributional-equality bridges; both are now also complete.
-/

noncomputable section
open scoped MeasureTheory ProbabilityTheory Topology

namespace Exchangeability
namespace DeFinetti
namespace ViaMartingale

open MeasureTheory Filter
open Exchangeability.DeFinetti.MartingaleHelpers

end ViaMartingale
end DeFinetti
end Exchangeability
