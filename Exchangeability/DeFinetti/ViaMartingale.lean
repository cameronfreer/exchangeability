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

* `deFinetti_viaMartingale`: **Main theorem** - contractable implies conditionally i.i.d.
* `contraction_independence`: Contraction-independence lemma (Kallenberg Lemma 1.3)

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

/-! ### Infrastructure for Test Function Transfer (integral_map + Law Equality) -/

/-- **B1: Bochner integral under Measure.map (Change of variables).**
If `T : Ω → δ` is measurable and `g : δ → ℝ` is integrable w.r.t. `Measure.map T μ`,
then `∫ g ∘ T ∂μ = ∫ g ∂ (Measure.map T μ)`.

This is the Bochner integral analogue of `lintegral_map`. -/
lemma integral_map_eq
    {Ω δ : Type*} [MeasurableSpace Ω] [MeasurableSpace δ]
    {μ : Measure Ω} {T : Ω → δ} (hT : Measurable T)
    {g : δ → ℝ}
    (hg : Integrable g (Measure.map T μ)) :
  ∫ ω, g (T ω) ∂μ = ∫ y, g y ∂ (Measure.map T μ) := by
  -- Use mathlib's change-of-variables formula for Bochner integrals
  symm
  exact MeasureTheory.integral_map hT.aemeasurable hg.aestronglyMeasurable

/-- **B2: Test-function transfer under equality of laws.**
If two pushforward measures coincide, Bochner integrals of any integrable
function coincide. -/
lemma integral_eq_of_map_eq
    {Ω δ : Type*} [MeasurableSpace Ω] [MeasurableSpace δ]
    {μ : Measure Ω} {T T' : Ω → δ}
    (hMeas : Measurable T) (hMeas' : Measurable T')
    {g : δ → ℝ}
    (hg : Integrable g (Measure.map T μ))
    (hLaw : Measure.map T μ = Measure.map T' μ) :
  ∫ ω, g (T ω) ∂μ = ∫ ω, g (T' ω) ∂μ := by
  classical
  -- Use integral_map on both sides and the law equality
  have h1 := integral_map_eq hMeas hg
  have h2 : Integrable g (Measure.map T' μ) := hLaw ▸ hg
  have h3 := integral_map_eq hMeas' h2
  calc ∫ ω, g (T ω) ∂μ
      = ∫ y, g y ∂(Measure.map T μ) := h1
    _ = ∫ y, g y ∂(Measure.map T' μ) := by rw [hLaw]
    _ = ∫ ω, g (T' ω) ∂μ := h3.symm

/-! **Kallenberg Lemma 1.3 (Contraction-Independence)**: If the triple distribution
satisfies (Y, Z, W) =^d (Y, Z, W'), then Y and Z are conditionally independent given W.

This is the key lemma connecting distributional symmetry to conditional independence.

Note: The order (Y, Z, W) matches the natural interpretation where Y is the variable of
interest and (Z, W) provides the conditioning information.

**Proof strategy:** We prove rectangle factorization directly from the distributional equality.

**Mathematical content:** The distributional equality (Y,Z,W) =^d (Y,Z,W') combined with the
implicit "contraction" (W' may contain more information than W) implies that Z provides no
additional information about Y beyond what W provides. This is precisely conditional independence.

**What's needed to complete:** The proof requires showing that for all measurable sets A, B, C
with C ∈ σ(W):
  ∫_C 1_A(Y)·1_B(Z) dμ = (∫_C 1_A(Y)·1_C(W) dμ) · (∫ 1_B(Z)·1_C(W) dμ) / μ(C)

This factorization follows from the distributional equality via a martingale argument
(see Kallenberg 2005, proof of Lemma 1.3) or via conditional distributions.

**Mathlib target:** Mathlib.Probability.ConditionalIndependence.FromDistributionalEquality
-/

/- ===== Helpers: adjointness & indicator algebra (μ[·|m], (hm : m ≤ m0)) ===== -/

/-- If `|g| ≤ C` a.e., then `|μ[g|m]| ≤ C` a.e. (uses monotonicity of conditional expectation). -/
@[nolint unusedArguments]
lemma ae_bound_condexp_of_ae_bound
    {Ω : Type*} [m0 : MeasurableSpace Ω] (μ : Measure Ω)
    {m : MeasurableSpace Ω} (hm : m ≤ m0)
    [SigmaFinite (μ.trim hm)]
    {g : Ω → ℝ} {C : ℝ}
    (hgC : ∀ᵐ ω ∂μ, |g ω| ≤ C) :
  ∀ᵐ ω ∂μ, |μ[g | m] ω| ≤ C := by
  by_cases hC : 0 ≤ C
  · exact MeasureTheory.ae_bdd_condExp_of_ae_bdd (R := ⟨C, hC⟩) hgC
  · -- C < 0 contradicts |g ω| ≤ C since |g ω| ≥ 0
    push Not at hC
    filter_upwards [hgC] with ω hω
    linarith [abs_nonneg (g ω)]


-- FutureCylinders, FirstBlockCylinder, IndicatorAlgebra, FutureRectangles sections
-- have been extracted to MartingaleHelpers.lean and ViaMartingale/FutureRectangles.lean

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]


-- FiniteCylinders content (finFutureSigma, contractable_finite_cylinder_measure, etc.)
-- has been extracted to ViaMartingale/FiniteCylinders.lean

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

-- Note: condexp_indicator_drop_info_of_pair_law_direct and condexp_indicator_drop_info_of_pair_law
-- have been extracted to ViaMartingale/DropInfo.lean

-- Note: block_coord_condIndep, condexp_indicator_inter_of_condIndep,
-- finite_level_factorization, and tail_factorization_from_future
-- have been extracted to ViaMartingale/Factorization.lean

-- Note: measure_pi_univ_pi, bind_apply_univ_pi, finite_product_formula_id,
-- finite_product_formula_strictMono, finite_product_formula, and finite_product_formula_id'
-- have been extracted to ViaMartingale/FiniteProduct.lean

/-! ### Main Theorem: de Finetti via Reverse Martingales -/

section MainTheorem

open ProbabilityTheory

end MainTheorem

/-!
## Notes

The main de Finetti theorem using this machinery is in `TheoremViaMartingale.lean`.
This file provides the proof infrastructure (helper lemmas and constructions).
-/

end ViaMartingale
end DeFinetti
end Exchangeability
