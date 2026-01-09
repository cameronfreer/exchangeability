# L² Proof of de Finetti's Theorem

This directory contains Kallenberg's "second proof" of de Finetti's theorem, using elementary L² contractability bounds. This proof has the **lightest dependencies** (no ergodic theory or martingale convergence required).

## Mathematical Overview

**Main result:** For contractable sequences on Borel spaces, coordinates are conditionally i.i.d. given the tail σ-algebra.

**Key insight:** The identification chain connects three quantities:
```
α_f = E[f(X₀) | tail] = ∫f dν
```
where:
- `α_f` is the L¹ limit of Cesàro averages `(1/m) Σ f(X_k)`
- `E[f(X₀) | tail]` is the conditional expectation given the tail σ-algebra
- `ν(ω)` is the directing measure (conditional distribution of X₀ given tail)

### Proof Strategy

1. **L² Contractability Bound:** For contractable sequences, Cesàro averages are Cauchy in L²
2. **L² Limit Exists:** L² completeness gives limit `α_f` with identification `α_f =ᵐ E[f(X₀) | tail]`
3. **Bridge Lemma:** The directing measure ν satisfies `∫f dν = E[f(X₀) | tail]` a.e.
4. **Chain Completion:** By transitivity, `α_f = ∫f dν` a.e.

## File Structure

| File | Purpose |
|------|---------|
| `MainConvergence.lean` | L¹ convergence of Cesàro averages |
| `CesaroConvergence.lean` | L² convergence with conditional expectation identification |
| `DirectingMeasureIntegral.lean` | Bridge lemmas connecting directing measure to CE |
| `DirectingMeasureCore.lean` | Core directing measure construction |
| `AlphaConvergence.lean` | Convergence of alpha functions |
| `AlphaIicCE.lean` | Alpha function conditional expectation properties |
| `AlphaIic.lean` | Alpha function for Iic sets |
| `MoreL2Helpers.lean` | Additional L² lemmas |
| `BlockAverages.lean` | Block average machinery |
| `WindowMachinery.lean` | Window-based averaging |
| `BlockAvgDef.lean` | Block average definitions |
| `Clip01.lean` | Clipping functions to [0,1] |

## Key Lemmas

| Lemma | Description |
|-------|-------------|
| `cesaro_to_condexp_L2` | L² limit exists and equals `E[f(X₀) \| tail]` |
| `weighted_sums_converge_L1` | L¹ convergence of Cesàro averages |
| `directing_measure_integral_eq_condExp` | `∫f dν = E[f(X₀) \| tail]` a.e. |
| `l2_bound_two_windows` | L² contractability bound for block averages |

## References

- Kallenberg (2005), *Probabilistic Symmetries and Invariance Principles*, Chapter 1, Theorem 1.1
  - Lemma 1.2: L² contractability bound
  - Page 27: "Second proof of Theorem 1.1" (L² route)
