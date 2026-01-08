# ViaL2: Kallenberg's Second Proof of de Finetti's Theorem

This directory implements Kallenberg's "second proof" of de Finetti's theorem using elementary L² methods. The proof establishes that contractable sequences are conditionally i.i.d. without requiring the Mean Ergodic Theorem or martingale convergence.

## Completion Status

**Status: COMPLETE** (January 2026)

All proofs compile with only standard mathlib axioms (`propext`, `Classical.choice`, `Quot.sound`). The full project builds successfully with ~13,800 lines of Lean 4 code across 5 files.

| File | Lines | Status |
|------|-------|--------|
| `MainConvergence.lean` | 888 | Complete |
| `CesaroConvergence.lean` | 3,390 | Complete |
| `BlockAverages.lean` | 1,624 | Complete* |
| `MoreL2Helpers.lean` | 3,489 | Complete |
| `DirectingMeasure.lean` | 4,381 | Complete |

*BlockAverages contains one stub lemma due to import structure; the actual proof is in MoreL2Helpers.

## Key Insight: The Identification Chain

The central insight is the **identification chain** connecting three quantities:

```
α_f = E[f(X₀) | tail] = ∫f dν
```

where:
- `α_f` is the L¹ limit of Cesàro averages `(1/m) Σ f(X_k)`
- `E[f(X₀) | tail]` is the conditional expectation given the tail σ-algebra
- `ν(ω)` is the directing measure (conditional distribution of X₀ given tail)

### Proof Strategy

1. **L² Contractability Bound** (`CesaroConvergence.lean`)
   - For contractable sequences, Cesàro averages are Cauchy in L²
   - Uses Kallenberg's L² bound: `‖A_{m,n} - A_{m',n}‖_L² ≤ C_f/√n`

2. **L² Limit Exists** (`cesaro_to_condexp_L2`)
   - L² completeness gives limit `α_f`
   - **Key identification:** `α_f =ᵐ E[f(X₀) | tail]`

3. **Bridge Lemma** (`DirectingMeasure.lean`)
   - `directing_measure_integral_eq_condExp`: `∫f dν = E[f(X₀) | tail]` a.e.
   - The directing measure ν is the conditional distribution of X₀ given tail

4. **Chain Completion** (`directing_measure_integral_via_chain`)
   - By transitivity: `α_f = ∫f dν` a.e.
   - This bypasses the Ioc/step function approach entirely

## File Structure

| File | Purpose |
|------|---------|
| `MainConvergence.lean` | `weighted_sums_converge_L1`: L¹ convergence of Cesàro averages |
| `CesaroConvergence.lean` | `cesaro_to_condexp_L2`: L² convergence with conditional expectation identification |
| `DirectingMeasure.lean` | Directing measure construction and bridge lemmas |
| `BlockAverages.lean` | Block average machinery for the main proof |
| `MoreL2Helpers.lean` | Additional L² lemmas and technical machinery |

## Key Lemmas

### From `CesaroConvergence.lean`

```lean
lemma cesaro_to_condexp_L2 :
    ∃ (α_f : Ω → ℝ), MemLp α_f 2 μ ∧
      AEStronglyMeasurable[TailSigma.tailSigma X] α_f μ ∧
      Tendsto (fun n => eLpNorm (blockAvg f X 0 n - α_f) 2 μ) atTop (𝓝 0) ∧
      α_f =ᵐ[μ] μ[(f ∘ X 0) | TailSigma.tailSigma X]
```

### From `DirectingMeasure.lean`

```lean
-- Bridge lemma: integral against directing measure = conditional expectation
lemma directing_measure_integral_eq_condExp :
    (fun ω => ∫ x, f x ∂(directing_measure X ... ω))
      =ᵐ[μ] μ[fun ω => f (X 0 ω) | TailSigma.tailSigma X]

-- Simplified proof using identification chain
lemma directing_measure_integral_via_chain :
    ∃ (alpha : Ω → ℝ), Measurable alpha ∧ MemLp alpha 1 μ ∧
      (L¹ convergence) ∧
      (∀ᵐ ω ∂μ, alpha ω = ∫ x, f x ∂(directing_measure X ... ω))
```

## DirectingMeasure.lean: Detailed Structure

The `DirectingMeasure.lean` file (4,381 lines) is the heart of the ViaL2 proof. It establishes that the directing measure ν(ω) serves as the conditional distribution of X₀ given the tail σ-algebra.

### Construction Phases

The proof proceeds in four phases, each building on the previous:

**Phase A: Indicator functions on Iic sets**
- `integral_indicator_borel_tailAEStronglyMeasurable`: For Borel indicators, ω ↦ ∫ 1_S dν(ω) is tail-AESM
- Uses π-λ theorem starting from `{Iic t : t ∈ ℝ}` generators

**Phase B: Simple functions**
- `integral_simpleFunc_tailAEStronglyMeasurable`: Simple function integrals are tail-AESM
- Decomposes into finite sums of indicator integrals

**Phase C: Bounded measurable functions**
- `integral_bounded_measurable_tailAEStronglyMeasurable`: General bounded measurable case
- Uses `SimpleFunc.approxOn` for approximation, DCT for limit exchange
- Key technique: `StronglyMeasurable.limUnder` on tail-SM representatives

**Phase D: Set integral equality**
- `setIntegral_directing_measure_bounded_measurable_eq`: The bridge property
- Shows ∫_A (∫f dν) dμ = ∫_A f(X₀) dμ for tail-measurable A

### Key Technical Challenges Solved

1. **Tail-AESM for limits**: Proving that pointwise limits of tail-AESM functions are tail-AESM required careful use of `StronglyMeasurable.limUnder` to construct tail-SM witnesses.

2. **σ-algebra management**: The proof carefully tracks which functions are measurable with respect to the tail σ-algebra vs. the ambient σ-algebra.

3. **Simple function approximation**: Uses `SimpleFunc.approxOn` with closed bounded intervals to uniformly approximate bounded measurable functions.

## Comparison with Other Approaches

### Why Not Ioc/Step Functions?

An earlier approach attempted to prove `α = ∫f dν` via:
1. π-λ extension (Iic → Ioc → all Borel sets)
2. Step function approximation on range intervals
3. Triangle inequality combining the pieces

This approach diverges from Kallenberg and causes elaboration timeouts in Lean.

### Kallenberg's Actual Approach

1. **Existence of α_f** via L² completeness ✓
2. **Identification:** `α_f = E[f(X₀) | tail]` directly ✓
3. **Bridge:** ν is the conditional distribution, so `E[f(X₀)|tail] = ∫f dν` by definition

The identification chain approach is:
- More mathematically natural (follows Kallenberg)
- More Lean-friendly (avoids elaboration issues)
- Simpler (bypasses complex step function machinery)

## Dependencies

```
MainConvergence.lean
       ↓
CesaroConvergence.lean ← cesaro_to_condexp_L2 (α = E[f|tail])
       ↓
DirectingMeasure.lean ← directing_measure_integral_eq_condExp (∫f dν = E[f|tail])
       ↓
directing_measure_integral_via_chain (α = ∫f dν by transitivity)
       ↓
Main theorem
```

## Build Instructions

```bash
# Build the full ViaL2 proof
lake build Exchangeability.DeFinetti.ViaL2.DirectingMeasure

# Check axioms (should show only propext, Classical.choice, Quot.sound)
lake env lean -c 'import Exchangeability.DeFinetti.ViaL2.DirectingMeasure; #print axioms directing_measure_integral'
```

## History

- **Initial development**: Cesàro convergence and L² bounds
- **December 2024**: Core directing measure construction
- **January 2026**: Completed all sorries in DirectingMeasure.lean
  - Final sorry filled: `integral_bounded_measurable_tailAEStronglyMeasurable` (tail-AESM for limits)

## References

- Kallenberg, O. (2005). *Probabilistic Symmetries and Invariance Principles*, Chapter 1, Theorem 1.1
- The "second proof" uses L² methods without ergodic theory or martingales
