/-
Copyright (c) 2025 The Exchangeability Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Exchangeability.DeFinetti.ViaKoopman.ContractableFactorization
import Exchangeability.DeFinetti.ViaKoopman.KernelIndependence

/-!
# de Finetti's Theorem via Contractability (Kallenberg's First Proof)

This file provides de Finetti's theorem using contractability directly, following
Kallenberg's "first proof" which uses disjoint-block averaging rather than permutations.

## Main results

* `deFinetti_viaKoopman_contractable`: de Finetti's theorem from contractability.
  For a contractable sequence on a standard Borel space, there exists a kernel ν
  such that the coordinates are conditionally i.i.d. given ν.

## Mathematical overview

The key insight of Kallenberg's first proof is that contractability (invariance under
strictly monotone subsequences) directly implies conditional i.i.d., without going
through exchangeability.

The proof proceeds as follows:

1. **Block injection**: For `m` blocks of size `n`, define strictly monotone maps
   `ρⱼ : ℕ → ℕ` that select one element from each block.

2. **Contractability application**: For each choice function `j : Fin m → Fin n`,
   the block injection `ρⱼ` is strictly monotone, so contractability gives:
   `∫ ∏ fᵢ(ωᵢ) dμ = ∫ ∏ fᵢ(ω(ρⱼ(i))) dμ`

3. **Averaging**: Sum over all `n^m` choice functions to get:
   `∫ ∏ fᵢ(ωᵢ) dμ = ∫ ∏ blockAvg_i dμ`

4. **L¹ convergence**: As `n → ∞`, block averages converge in L¹ to conditional
   expectations (using Cesàro convergence).

5. **Factorization**: Taking limits yields:
   `CE[∏ fᵢ(ωᵢ) | mSI] = ∏ CE[fᵢ(ω₀) | mSI]` a.e.

6. **Kernel construction**: The product factorization gives kernel independence,
   from which we construct the directing measure ν.

## Comparison with ViaKoopman.lean

The alternative proof in `ViaKoopman.lean` uses exchangeability, which requires:
- Extending strictly monotone maps to permutations (`exists_perm_extending_strictMono`)
- Proving exchangeability implies contractability

This file avoids that step entirely, working directly with contractability.

## References

* Kallenberg (2005), *Probabilistic Symmetries and Invariance Principles*, Chapter 1
-/

open Filter MeasureTheory

noncomputable section

namespace Exchangeability.DeFinetti

open MeasureTheory Filter Topology ProbabilityTheory
open Exchangeability.Ergodic
open Exchangeability.PathSpace
open Exchangeability.DeFinetti.ViaKoopman
open scoped BigOperators

variable {α : Type*} [MeasurableSpace α] [StandardBorelSpace α]

-- Short notation for shift-invariant σ-algebra
local notation "mSI" => shiftInvariantSigma (α := α)

/-- de Finetti's Theorem from contractability (Kallenberg's first proof).

For a contractable probability measure on path space where the shift is measure-preserving,
there exists a kernel ν (the "directing measure") such that the coordinates are
conditionally i.i.d. given ν.

**Hypotheses:**
- `hσ`: The shift map is measure-preserving
- `hContract`: The measure is contractable (invariant under strictly monotone subsequences)

**Conclusion:**
There exists a kernel `ν : Ω[α] → Measure α` such that:
1. `ν ω` is a probability measure for a.e. ω
2. For any bounded measurable functions `fs : Fin m → α → ℝ`:
   `∫ ∏ fᵢ(ωᵢ) dμ = ∫ (∫ ∏ fᵢ(x) dν(ω)) dμ(ω)`

**Mathematical content:**
This is the hard direction of de Finetti's equivalence:
  Contractable → Conditionally i.i.d.

The proof uses disjoint-block averaging (see `ContractableFactorization.lean`):
1. For each n, partition into blocks and average over block positions
2. Contractability ensures the integral is unchanged
3. As n → ∞, block averages converge to conditional expectations
4. The product factorization gives kernel independence
5. The kernel ν is constructed from the conditional expectation
-/
theorem deFinetti_viaKoopman_contractable
    {μ : Measure (Ω[α])} [IsProbabilityMeasure μ]
    (hσ : MeasurePreserving shift μ μ)
    (hContract : ∀ (m : ℕ) (k : Fin m → ℕ), StrictMono k →
        Measure.map (fun ω i => ω (k i)) μ = Measure.map (fun ω (i : Fin m) => ω i.val) μ) :
    ∃ (ν : (Ω[α]) → Measure α),
      (∀ᵐ ω ∂μ, IsProbabilityMeasure (ν ω)) ∧
      (∀ (m : ℕ) (fs : Fin m → α → ℝ),
        (∀ i, Measurable (fs i)) →
        (∀ i, ∃ C, ∀ x, |fs i x| ≤ C) →
        ∫ ω, (∏ i : Fin m, fs i (ω i.val)) ∂μ =
          ∫ ω, (∫ x, (∏ i : Fin m, fs i x) ∂(ν ω)) ∂μ) := by
  -- Step 1: Use condexp_product_factorization_contractable to get product factorization
  -- Step 2: Define ν from the conditional distribution at coordinate 0
  -- Step 3: Show the integral factorization follows from the CE factorization
  sorry -- TODO: Complete by combining ContractableFactorization with KernelIndependence

/-- Contractability implies conditional i.i.d. (Kallenberg's first proof).

This is the key implication in de Finetti's theorem: a contractable sequence
is conditionally i.i.d. given the tail σ-algebra. -/
theorem conditionallyIID_of_contractable
    {μ : Measure (Ω[α])} [IsProbabilityMeasure μ]
    (hσ : MeasurePreserving shift μ μ)
    (hContract : ∀ (m : ℕ) (k : Fin m → ℕ), StrictMono k →
        Measure.map (fun ω i => ω (k i)) μ = Measure.map (fun ω (i : Fin m) => ω i.val) μ) :
    ∃ (ν : (Ω[α]) → Measure α),
      (∀ᵐ ω ∂μ, IsProbabilityMeasure (ν ω)) ∧
      -- Identical distribution: ν ω = conditional distribution at coordinate 0
      (∀ s, MeasurableSet s →
        (fun ω => (ν ω s).toReal) =ᵐ[μ]
          μ[(fun ω' => Set.indicator s (1 : α → ℝ) (ω' 0)) | mSI]) ∧
      -- Conditional independence: joint CE factors as product
      (∀ (m : ℕ) (sets : Fin m → Set α),
        (∀ i, MeasurableSet (sets i)) →
        μ[(fun ω' => Set.indicator (⋂ (i : Fin m), (fun ω'' => ω'' i.val) ⁻¹' sets i) (1 : Ω[α] → ℝ) ω') | mSI]
          =ᵐ[μ] fun ω =>
            ∏ i : Fin m, μ[(fun ω' => Set.indicator ((fun ω'' => ω'' 0) ⁻¹' sets i) (1 : Ω[α] → ℝ) ω') | mSI] ω) :=
  sorry -- TODO: Derive from deFinetti_viaKoopman_contractable

end Exchangeability.DeFinetti
