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
   `∫ ∏ fᵢ(ωᵢ) dμ = ∫ (∏ᵢ ∫ fᵢ dν(ω)) dμ(ω)`

This is the **product factorization** form of de Finetti:
- LHS: Product at different coordinates ω(0), ω(1), ..., ω(m-1)
- RHS: Product of expectations, each ∫ fᵢ dν evaluated against same ν(ω)

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
          ∫ ω, (∏ i : Fin m, ∫ x, fs i x ∂(ν ω)) ∂μ) := by
  -- Use ν from KernelIndependence.lean (the regular conditional distribution)
  use ν (μ := μ)
  constructor
  · -- Step 1: ν ω is a probability measure for a.e. ω
    -- This follows from rcdKernel being a Markov kernel
    apply ae_of_all
    intro ω
    exact IsMarkovKernel.isProbabilityMeasure ω
  · -- Step 2: Product factorization for bounded measurable functions
    intro m fs hfs_meas hfs_bd
    -- The proof uses condexp_product_factorization_contractable to get:
    -- μ[(∏ fᵢ(ωᵢ)) | mSI] =ᵐ ∏ μ[fᵢ(ω₀) | mSI]
    --
    -- Then:
    -- LHS = ∫ (∏ fᵢ(ωᵢ)) dμ
    --     = ∫ CE[∏ fᵢ(ωᵢ) | mSI] dμ  (tower property)
    --     = ∫ (∏ CE[fᵢ(ω₀) | mSI]) dμ  (by factorization)
    --
    -- For the RHS, we need:
    -- ∫ fᵢ dν(ω) = CE[fᵢ(ω₀) | mSI](ω)  a.e.
    --
    -- This follows from the definition of ν = rcdKernel, where
    -- rcdKernel is the pushforward of condExpKernel by π₀.
    --
    -- The technical proof requires:
    -- 1. Connection between condExpKernel and ν via CE-to-kernel-integral lemmas
    -- 2. Measurability and integrability infrastructure
    -- 3. Fubini-type arguments for exchanging integrals
    --
    -- This relies on infrastructure in KernelIndependence.lean that has remaining sorries.
    -- The mathematical argument is sound but full formalization awaits completion of
    -- the conditional expectation kernel infrastructure.
    sorry

/-- Contractability implies conditional i.i.d. (Kallenberg's first proof).

This is the key implication in de Finetti's theorem: a contractable sequence
is conditionally i.i.d. given the tail σ-algebra.

This theorem provides the **standard form** of conditionally i.i.d.:
1. ν(ω) is the conditional distribution at coordinate 0 given mSI
2. The conditional expectation of the indicator of a cylinder set factors as
   a product of conditional expectations of single-coordinate indicators
-/
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
            ∏ i : Fin m, μ[(fun ω' => Set.indicator ((fun ω'' => ω'' 0) ⁻¹' sets i) (1 : Ω[α] → ℝ) ω') | mSI] ω) := by
  -- Use ν from KernelIndependence.lean
  use ν (μ := μ)
  refine ⟨?_, ?_, ?_⟩
  · -- Part 1: ν ω is a probability measure for a.e. ω
    apply ae_of_all
    intro ω
    exact IsMarkovKernel.isProbabilityMeasure ω
  · -- Part 2: Identical distribution - ν ω s = CE[1_s(ω₀) | mSI](ω) a.e.
    -- This is the definition of ν via rcdKernel (pushforward of condExpKernel by π₀)
    --
    -- By definition:
    --   ν ω = rcdKernel ω
    --       = (condExpKernel μ mSI).map π₀ ω
    --
    -- For a measurable set s ⊆ α:
    --   (ν ω) s = (condExpKernel μ mSI ω) (π₀⁻¹(s))
    --           = (condExpKernel μ mSI ω) {ω' | ω' 0 ∈ s}
    --
    -- And by condExp_ae_eq_integral_condExpKernel:
    --   CE[1_s(ω₀) | mSI] =ᵐ ∫ 1_{ω' 0 ∈ s} d(condExpKernel μ mSI ω)
    --                     = (condExpKernel μ mSI ω) {ω' | ω' 0 ∈ s}
    --                     = (ν ω) s
    --
    -- The proof requires unwinding the definitions of ν, rcdKernel, and condExpKernel.
    intro s hs
    -- The connection between ν and conditional expectation requires
    -- the kernel-integral representation of conditional expectation.
    -- This is standard but requires careful handling of measurability.
    sorry
  · -- Part 3: Conditional independence - CE factors as product for indicator functions
    -- This is exactly condexp_product_factorization_contractable applied to indicators
    intro m sets hsets
    -- Define indicator functions fs : Fin m → α → ℝ
    let fs : Fin m → α → ℝ := fun i => Set.indicator (sets i) 1
    -- These are bounded (by 1) and measurable
    have hfs_meas : ∀ i, Measurable (fs i) := fun i =>
      measurable_const.indicator (hsets i)
    have hfs_bd : ∀ i, ∃ C, ∀ x, |fs i x| ≤ C := fun i => ⟨1, fun x => by
      simp only [fs]
      by_cases hx : x ∈ sets i
      · simp [Set.indicator_of_mem hx]
      · simp [Set.indicator_of_notMem hx]⟩
    -- Apply condexp_product_factorization_contractable
    have h_fact := condexp_product_factorization_contractable hσ hContract fs hfs_meas hfs_bd
    -- The LHS indicator is the product of individual indicators
    -- 1_{∩ᵢ ωᵢ ∈ sets i} = ∏ᵢ 1_{sets i}(ωᵢ)
    have h_prod_eq : (fun ω' => Set.indicator
        (⋂ (i : Fin m), (fun ω'' => ω'' i.val) ⁻¹' sets i) (1 : Ω[α] → ℝ) ω')
        = (fun ω' => ∏ i : Fin m, fs i (ω' i.val)) := by
      ext ω'
      simp only [fs]
      by_cases h : ω' ∈ ⋂ (i : Fin m), (fun ω'' => ω'' i.val) ⁻¹' sets i
      · -- ω' is in the intersection, so each coordinate is in the corresponding set
        have h' : ∀ i : Fin m, ω' i.val ∈ sets i := by
          simpa only [Set.mem_iInter, Set.mem_preimage] using h
        rw [Set.indicator_of_mem h]
        -- Each indicator is 1
        have h_each : ∀ i, Set.indicator (sets i) (1 : α → ℝ) (ω' i.val) = 1 := by
          intro i
          rw [Set.indicator_of_mem (h' i)]
          rfl
        simp only [h_each, Finset.prod_const_one, Pi.one_apply]
      · -- ω' is not in the intersection
        rw [Set.indicator_of_notMem h]
        -- At least one indicator is 0
        simp only [Set.mem_iInter, Set.mem_preimage, not_forall] at h
        obtain ⟨i, hi⟩ := h
        symm
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        rw [Set.indicator_of_notMem hi]
    -- The RHS factors as product of CEs at coordinate 0
    -- The key is that 1_{ω' 0 ∈ s}(ω') = 1_s(ω' 0) for ω' : Ω[α]
    have h_integrands_eq : ∀ i, (fun ω' : Ω[α] => Set.indicator ((fun ω'' => ω'' 0) ⁻¹' sets i)
        (1 : Ω[α] → ℝ) ω') = (fun ω' => fs i (ω' 0)) := by
      intro i
      ext ω'
      -- Both are indicator functions that evaluate to 1 iff ω' 0 ∈ sets i
      simp only [fs]
      rfl
    have h_rhs_eq : (fun ω => ∏ i : Fin m,
        μ[(fun ω' => Set.indicator ((fun ω'' => ω'' 0) ⁻¹' sets i) (1 : Ω[α] → ℝ) ω') | mSI] ω)
        = (fun ω => ∏ i : Fin m, μ[(fun ω' => fs i (ω' 0)) | mSI] ω) := by
      ext ω
      apply Finset.prod_congr rfl
      intro i _
      simp only [h_integrands_eq i]
    -- Combine using h_fact
    rw [h_prod_eq, h_rhs_eq]
    exact h_fact

end Exchangeability.DeFinetti
