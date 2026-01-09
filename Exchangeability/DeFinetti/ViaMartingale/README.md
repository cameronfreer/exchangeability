# Martingale Proof of de Finetti's Theorem

This directory contains Kallenberg's "third proof" of de Finetti's theorem, using reverse martingale convergence.

## Mathematical Overview

**Main result:** For contractable sequences on Borel spaces, coordinates are conditionally i.i.d. given the tail σ-algebra.

**Key insight (Kallenberg page 28):** For contractable ξ with k < m ≤ n:
```
P[ξ_k ∈ B | θ_m ξ] = P[ξ_k ∈ B | θ_n ξ]   (a.s.)
```
where θ_m ξ = (ξ_m, ξ_{m+1}, ...) is the m-shifted sequence.

### Proof Strategy

The central lemma `P[X_m ∈ B | tail] = P[X_0 ∈ B | tail]` combines:

1. **Contractability:** `CE(X_m | fut) = CE(X_0 | fut)` for the future filtration
2. **Reverse martingale convergence:** `CE(X_k | rev n) → CE(X_k | tail)` as n → ∞
3. **Chain lemma:** `CE(X_k | rev m) = CE(X_k | rev n)` for k < m ≤ n

## File Structure

| File | Purpose |
|------|---------|
| `CondExpConvergence.lean` | Main convergence lemma combining contractability with tower/chain |
| `KallenbergChain.lean` | Chain lemma and convergence to tail |
| `PairLawEquality.lean` | Pair law equality from contractability |
| `FiniteProduct.lean` | Finite product factorization |
| `Factorization.lean` | Factorization infrastructure |
| `FutureRectangles.lean` | Future rectangle sets |
| `FiniteCylinders.lean` | Finite cylinder sets |
| `LocalInfrastructure.lean` | Local definitions and helpers |
| `DirectingMeasure.lean` | Directing measure construction |
| `FutureFiltration.lean` | Future filtration definitions |
| `ShiftOperations.lean` | Shift operator θ_m (shiftRV) |
| `RevFiltration.lean` | Reverse filtration σ(θ_m ξ) |
| `IndicatorAlgebra.lean` | Indicator function algebra |

## Key Lemmas

| Lemma | Description |
|-------|-------------|
| `condexp_convergence` | CE equality at future level from contractability |
| `extreme_members_equal_on_tail` | `P[X_m ∈ B \| tail] = P[X_0 ∈ B \| tail]` |
| `condExp_indicator_revFiltration_eq_tail` | CE on revFiltration equals CE on tail |
| `pair_law_shift_eq_of_contractable` | (X_k, θ_m X) =^d (X_k, θ_n X) for k < m ≤ n |

## Notation Correspondence

| This formalization | Kallenberg |
|--------------------|------------|
| `shiftRV X m` | θ_m ξ |
| `revFiltration X m` | σ(θ_m ξ) |
| `futureFiltration X m` | σ(θ_{m+1} ξ) |
| `tailSigma X` | T_ξ = ⋂_m σ(θ_m ξ) |

## References

- Kallenberg (2005), *Probabilistic Symmetries and Invariance Principles*, Chapter 1
  - Lemma 1.3: Contraction-independence
  - Page 28: "Third proof of Theorem 1.1" (reverse martingale route)
- Aldous (1983), *Exchangeability and related topics*
