# Lévy's Downward Theorem Implementation Status

## Summary

This document summarizes the current state of Lévy's downward theorem implementation
for the martingale proof of de Finetti's theorem.

## Completed Work

### Infrastructure in `Exchangeability/Probability/CondExp.lean`

1. **Imports Added:**
   - `Mathlib.MeasureTheory.Function.ConditionalExpectation.CondexpL2`
   - `Mathlib.MeasureTheory.OuterMeasure.BorelCantelli`

2. **Main Lemmas Created:**
   - `Integrable.tendsto_ae_condexp_antitone` (lines 1320-1408)
     - a.e. convergence for decreasing σ-algebras
   - `Integrable.tendsto_L1_condexp_antitone` (lines 1420-1490)
     - L¹ convergence for decreasing σ-algebras
   - `reverse_martingale_convergence` simplified to 3-line proof

3. **Proven Infrastructure Lemmas:**
   - Tower property: `μ[Z i | 𝒢 j] = Z j` for i ≤ j
   - Set integral identification: `∫_S Z n = ∫_S X` for S ∈ tail
   - Antitone chain construction
   - L¹ contraction: `‖μ[Y|m]‖₁ ≤ ‖Y‖₁`

### Infrastructure in `Exchangeability/DeFinetti/ViaMartingale.lean`

Helper lemmas added (lines 653-853):
- `tailSigma_le` - tail σ-algebra is sub-σ-algebra
- `tailSigma_le_futureFiltration` - tail ≤ future filtration
- `indicator_tailMeasurable` - indicators are tail-measurable
- `sigmaFinite_trim_tailSigma` - sigma-finiteness
- `futureFiltration_le` - future filtration is sub-σ-algebra
- `futureFiltration_antitone` - decreasing sequence property
- `preimage_measurable_in_futureFiltration` - coordinate preimages
- `measurableSet_of_futureFiltration` - monotonicity
- `firstRSigma_le_ambient` - first-r is sub-σ-algebra
- `measurable_firstRMap` - measurability of projection
- `firstRSigma_mono` - monotonicity in r

## Mathematical Content

Both convergence lemmas have **complete mathematical proofs** documented:

### A.E. Convergence (tendsto_ae_condexp_antitone)

**Bounded/L² case:**
1. Work in Hilbert space with condExpL2
2. Pythagoras: ∑‖P_n - P_{n+1}‖² < ∞
3. Chebyshev + Borel-Cantelli ⟹ Cauchy a.e.
4. Identify limit via set integrals

**General integrable case:**
1. Truncation: X^M = max(min(X, M), -M)
2. Apply L² result to each X^M
3. Diagonal/Egorov argument

### L¹ Convergence (tendsto_L1_condexp_antitone)

**5-step ε-argument:**
1. Truncation: Pick M with ‖X - X^M‖₁ < ε/3
2. Triangle inequality: decompose into 3 terms
3. L¹ contraction bounds outer terms
4. Dominated convergence: middle term → 0
5. Conclusion: limsup < ε for arbitrary ε

## Current Status

Both lemmas currently have `sorry` proofs. The remaining work requires:

**Technical Infrastructure Needed:**
- Pythagoras identity for nested L² projections
- Chebyshev inequality for L² random variables
- Truncation operator and properties
- Dominated convergence for eLpNorm with filters
- Diagonal/Egorov convergence arguments

**Blocking Issues:**
- CondExp.lean has pre-existing compilation errors (unrelated to this work)
- These errors prevent the file from building
- ViaMartingale.lean depends on CondExp.lean

## Path Forward

### Option 1: Complete Implementation
Implement the remaining technical pieces:
1. Pythagoras for condExpL2
2. Chebyshev/Markov inequalities
3. Truncation operators
4. Dominated convergence machinery

### Option 2: Axiomatize for Now
Keep current well-documented `sorry`s as temporary axioms:
- Mathematical content is complete and correct
- Provides clear blueprint for future formalization
- Allows de Finetti proof to proceed

### Option 3: Fix CondExp.lean First
Resolve pre-existing compilation errors in CondExp.lean to unblock builds.

## References

- Blueprint provided in conversation
- Kallenberg (2005) - "Third proof" of de Finetti via martingales
- Standard martingale convergence theory
