# de Finetti's Theorem via Reverse Martingales

This document describes the **martingale approach** to proving de Finetti's theorem,
implemented under `Exchangeability/DeFinetti/ViaMartingale/`. This is Aldous' elegant
proof, presented by Kallenberg (2005) as the "Third proof" of Theorem 1.1.

> **Historical architecture note.** The "File Structure and Dependencies" and "Key
> Technical Lemmas" sections below describe the *monolithic* `ViaMartingale.lean`
> (a single ~5,000-line file) as it existed up through ~Jan 2026. The proof has
> since been split into a directory `Exchangeability/DeFinetti/ViaMartingale/`
> with 12 files (see `README.md` for the current structure); line-number
> references in the tables below no longer resolve. The mathematical content
> (proof strategy, time-reversal crossing bound, Kallenberg Lemma 1.3, etc.) is
> unchanged.

## Status

**COMPLETE** - All main theorems are axiom-clean:
- `conditionallyIID_of_contractable`: `propext, Classical.choice, Quot.sound`
- `deFinetti`: `propext, Classical.choice, Quot.sound`
- `deFinetti_RyllNardzewski_equivalence`: `propext, Classical.choice, Quot.sound`

No `sorryAx` dependencies remain in the main theorem chain.

## Mathematical Overview

### Main Result

For infinite sequences on standard Borel spaces:
```
Contractable ⟺ Exchangeable ⟺ Conditionally i.i.d.
```

The martingale approach proves: **Contractable ⇒ Conditionally i.i.d.**

### Proof Strategy

The proof consists of two main components:

#### 1. Contraction-Independence Lemma (Kallenberg Lemma 1.3)

**Statement**: If `(ξ, η) =^d (ξ, ζ)` (same joint distribution) and `σ(η) ⊆ σ(ζ)`
(η is coarser than ζ), then `ξ ⊥⊥_η ζ` (ξ and ζ are conditionally independent given η).

**Proof idea**: Define conditional expectations:
- `μ₁ = E[1_{ξ∈B} | η]`
- `μ₂ = E[1_{ξ∈B} | ζ]`

The tower property gives `E[μ₂ | η] = μ₁`, so `(μ₁, μ₂)` forms a bounded martingale.
From `(ξ, η) =^d (ξ, ζ)`:
```
E[μ₂²] = E[μ₁²]
```
Therefore:
```
E[(μ₂ - μ₁)²] = E[μ₂²] - 2E[μ₁μ₂] + E[μ₁²]
              = E[μ₂²] - 2E[μ₁²] + E[μ₁²]  (using E[μ₂μ₁] = E[μ₁²])
              = E[μ₂²] - E[μ₁²]
              = 0
```
So `μ₁ = μ₂` a.s., which gives conditional independence.

#### 2. Reverse Martingale Convergence

For a contractable sequence X, we have for `k ≤ m`:
```
(X_m, θ_{m+1} X) =^d (X_k, θ_{m+1} X)
```
where `θ_n X = (X_n, X_{n+1}, ...)` is the shift.

The conditional expectation `E[1_{X_k∈B} | θ_{m+1} X]` forms a reverse martingale
(antitone filtration, martingale property). By Lévy's downward theorem:
```
E[1_{X_k∈B} | θ_{m+1} X] → E[1_{X_k∈B} | 𝒯_X]  as m → ∞
```
where `𝒯_X = ⋂_m σ(θ_m X)` is the tail σ-algebra.

Using Lemma 1.3 with the contractability condition:
```
E[1_{X_m∈B} | θ_{m+1} X] = E[1_{X_k∈B} | θ_{m+1} X]
```

Taking limits: all coordinates have the same conditional law given the tail,
proving conditional i.i.d.

### Differences from Kallenberg's Original

1. **Time-Reversal Crossing Bound**: Our formalization required a technical lemma
   (`timeReversal_crossing_bound`) not explicitly stated in Kallenberg. This bounds
   the upcrossings of a time-reversed negated process, needed for reverse martingale
   convergence.

2. **Finite-Dimensional Products**: We explicitly construct the directing measure
   via `condExpKernel` and verify the product formula for finite marginals, whereas
   Kallenberg's presentation is more abstract.

3. **Doob-Dynkin Factorization**: We use explicit Doob-Dynkin factorization to show
   that conditional expectations factor through the conditioning variable, rather than
   relying on abstract measurability arguments.

4. **Hitting Time Bounds**: The formal proof uses `hitting_le_of_mem` from mathlib's
   upcrossing theory to bound crossing times, translating the bijection argument into
   explicit hitting time bounds.

## File Structure and Dependencies

### Main Files

```
ViaMartingale.lean (239KB, ~5000 lines)
├── Local infrastructure lemmas
├── Contraction-Independence (Kallenberg Lemma 1.3)
├── Pair-law equality from contractability
├── Conditional expectation convergence
├── Reverse martingale convergence
├── Directing measure construction
├── Finite-dimensional product formula
└── Main theorem assembly
```

### Dependency Graph

```
ViaMartingale.lean
├── Mathlib.Probability.Martingale.Basic
├── Mathlib.Probability.Kernel.CondDistrib
├── Mathlib.Probability.Kernel.Condexp
├── Exchangeability.Core
├── Exchangeability.Contractability
├── Exchangeability.ConditionallyIID
├── Exchangeability.Probability.Martingale
│   └── Exchangeability.Probability.TimeReversalCrossing  ← Key technical lemma
├── Exchangeability.Probability.CondIndep
├── Exchangeability.Probability.TripleLawDropInfo
├── Exchangeability.Tail.TailSigma
└── Exchangeability.DeFinetti.CommonEnding
```

### Key Technical Lemmas

| Lemma | Location | Purpose |
|-------|----------|---------|
| `timeReversal_crossing_bound` | TimeReversalCrossing.lean | Bounds upcrossings in reversed process |
| `pair_law_eq_of_contractable` | ViaMartingale.lean:1338 | Distributional equality from contractability |
| `condExp_Xr_indicator_eq_of_contractable` | ViaMartingale.lean:1636 | Conditional expectation equality |
| `finite_product_formula` | ViaMartingale.lean:4954 | Product structure for finite marginals |
| `directingMeasure_isProb` | ViaMartingale.lean:4333 | Directing measure is probability |

## The Time-Reversal Crossing Bound

The most technically involved lemma is `timeReversal_crossing_bound`:

```lean
lemma timeReversal_crossing_bound
    {Ω : Type*} (X : ℕ → Ω → ℝ) (a b : ℝ) (hab : a < b) (N k : ℕ) (ω : Ω)
    (h_k : upperCrossingTime a b X N k ω < N)
    (_h_neg : -b < -a) :
    upperCrossingTime (-b) (-a) (negProcess (revProcess X N)) (N+1) k ω ≤ N
```

### Mathematical Content

For a process X with k upcrossings [a→b] completing before time N, the time-reversed
negated process Y = -X(N-·) has its k upcrossings [-b→-a] completing at time ≤ N.

### Proof Technique

The proof uses the bijection (τ, σ) ↦ (N-σ, N-τ) between X's crossings and Y's crossings:

1. **Bijection Structure**: If X crosses from a to b at times (τ, σ), then
   Y = -X(N-·) crosses from -b to -a at times (N-σ, N-τ).

2. **Level Conditions**:
   - X(σ) ≥ b ⟹ Y(N-σ) = -X(σ) ≤ -b
   - X(τ) ≤ a ⟹ Y(N-τ) = -X(τ) ≥ -a

3. **Time Bound**: Since τ ≥ 0, we have N-τ ≤ N.

4. **Induction**: Track that Y's m-th crossing completes by time N - lowerCrossingTime X (k-m).

5. **Hitting Time Bound**: Use `hitting_le_of_mem` to show the greedy algorithm finds
   crossings at the bijected times.

### Why This Lemma is Needed

Mathlib's reverse martingale convergence requires bounds on upcrossings. The standard
upcrossing lemma gives bounds for forward martingales. For reverse martingales, we need
to relate the upcrossings of the reversed process to the original, which requires this
time-reversal bound.

## Comparison with Other Proof Approaches

### L² Approach (ViaL2.lean)

- **Dependencies**: Lighter (no martingale theory)
- **Technique**: Direct L² estimates on conditional expectations
- **Status**: Complete, used as the default public API

### Koopman/Ergodic Approach (ViaKoopman.lean)

- **Dependencies**: Heavy (ergodic theory, Koopman operator)
- **Technique**: Mean Ergodic Theorem
- **Status**: Complete

### Martingale Approach (ViaMartingale.lean)

- **Dependencies**: Medium (martingale theory, reverse convergence)
- **Technique**: Lévy's downward theorem + contraction-independence
- **Status**: Complete

## Advantages of the Martingale Approach

1. **Conceptual Clarity**: The proof naturally explains why the tail σ-algebra is the
   right conditioning object.

2. **Probabilistic**: Uses pure probability theory without functional analysis.

3. **Generalizable**: The contraction-independence lemma (Lemma 1.3) is a general result
   applicable beyond de Finetti's theorem.

4. **Historic Significance**: This is Aldous' proof, which provided new insights into
   exchangeability.

## References

- Kallenberg (2005), *Probabilistic Symmetries and Invariance Principles*, Chapter 1,
  Theorem 1.1, pages 26-28 ("Third proof")
- Aldous (1983), *Exchangeability and related topics*, École d'Été de Probabilités
  de Saint-Flour XIII
- Williams (1991), *Probability with Martingales*, Chapter 11 (for upcrossing lemmas)
- Durrett (2019), *Probability: Theory and Examples*, Section 5.5 (martingale convergence)

## Summary

The martingale proof of de Finetti's theorem is now complete in our formalization.
The key technical challenge was proving `timeReversal_crossing_bound`, which required
careful tracking of the bijection between original and reversed crossing times through
induction on the crossing index. This lemma enables the use of reverse martingale
convergence, which is central to Aldous' elegant proof.
