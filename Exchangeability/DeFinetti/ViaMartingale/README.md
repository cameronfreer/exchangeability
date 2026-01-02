# Martingale Proof of de Finetti's Theorem

This directory contains Kallenberg's "third proof" of de Finetti's theorem, using reverse martingale convergence.

## Mathematical Overview

**Main result:** For contractable sequences on Borel spaces, coordinates are conditionally i.i.d. given the tail σ-algebra.

**Key insight (Kallenberg page 28):** For contractable ξ with k < m ≤ n:
```
P[ξ_k ∈ B | θ_m ξ] = P[ξ_k ∈ B | θ_n ξ]   (a.s.)
```
where θ_m ξ = (ξ_m, ξ_{m+1}, ...) is the m-shifted sequence.

## Two Proof Routes for `extreme_members_equal_on_tail`

The central lemma `P[X_m ∈ B | tail] = P[X_0 ∈ B | tail]` has two proofs:

### 1. Tower Property Route (`extreme_members_equal_on_tail_via_tower`)

**File:** `CondExpConvergence.lean`

```
CE(X_m | fut) = CE(X_0 | fut)           [contractability]
CE(CE(· | fut) | tail) = CE(· | tail)   [tower property]
⟹ CE(X_m | tail) = CE(X_0 | tail)
```

**Characteristics:**
- Shorter (~24 lines)
- Uses `condExp_condExp_of_le` (tower property)
- More direct, less infrastructure

### 2. Kallenberg Route (`extreme_members_equal_on_tail`) — Default

**Files:** `KallenbergChain.lean`, `CondExpConvergence.lean`

```
CE(X_k | rev m) = CE(X_k | rev n)     [chain lemma, k < m ≤ n]
CE(X_k | rev n) → CE(X_k | tail)      [reverse martingale convergence]
⟹ CE(X_k | rev m) = CE(X_k | tail)    [constant sequence = limit]
```

Then combine:
```
CE(X_m | tail) = CE(X_m | rev(m+1))    [convergence lemma]
              = CE(X_0 | rev(m+1))      [contractability]
              = CE(X_0 | tail)          [convergence lemma]
```

**Characteristics:**
- Longer (~37 lines)
- More faithful to Kallenberg's page-28 presentation
- Explicitly uses reverse martingale convergence (`condExp_tendsto_iInf`)
- Separates "chain is constant" from "limit equals value"

## Key Lemmas

### KallenbergChain.lean

| Lemma | Description |
|-------|-------------|
| `pair_law_shift_eq_of_contractable` | (X_k, θ_m X) =^d (X_k, θ_n X) for k < m ≤ n |
| `condExp_indicator_revFiltration_eq_of_le` | CE constant along revFiltration chain |
| `condExp_indicator_revFiltration_eq_tail` | CE on revFiltration equals CE on tail |

### Supporting Infrastructure

| File | Purpose |
|------|---------|
| `RevFiltration.lean` | σ(θ_m ξ) = revFiltration X m |
| `FutureFiltration.lean` | futureFiltration X m = revFiltration X (m+1) |
| `ShiftOperations.lean` | Shift operator θ_m (shiftRV) |
| `DirectingMeasure.lean` | Directing measure construction |
| `Factorization.lean` | Finite product factorization |

## Notation Correspondence

| This formalization | Kallenberg |
|--------------------|------------|
| `shiftRV X m` | θ_m ξ |
| `revFiltration X m` | σ(θ_m ξ) |
| `futureFiltration X m` | σ(θ_{m+1} ξ) |
| `tailSigma X` | T_ξ = ⋂_m σ(θ_m ξ) |

## Dependencies

```
Martingale/Convergence.lean    ← condExp_tendsto_iInf (Lévy downward)
    ↑
KallenbergChain.lean           ← chain lemma + convergence to tail
    ↑
CondExpConvergence.lean        ← extreme_members_equal_on_tail
    ↑
DirectingMeasure.lean          ← directing measure construction
    ↑
FiniteProduct.lean             ← product formula
    ↑
ViaMartingale.lean             ← main theorem assembly
```

## References

- Kallenberg (2005), *Probabilistic Symmetries and Invariance Principles*, Chapter 1
  - Lemma 1.3: Contraction-independence
  - Page 28: "Third proof of Theorem 1.1" (reverse martingale route)
- Aldous (1983), *Exchangeability and related topics*
