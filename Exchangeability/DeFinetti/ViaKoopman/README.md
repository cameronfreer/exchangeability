# Koopman Proof of de Finetti's Theorem

This directory contains Kallenberg's "first proof" of de Finetti's theorem, using the Mean Ergodic Theorem via the Koopman operator. This proof has the **heaviest dependencies** but provides a deep connection to ergodic theory and dynamical systems.

## Mathematical Overview

**Main result:** For contractable sequences on Borel spaces, coordinates are conditionally i.i.d. given the shift-invariant σ-algebra.

**Key insight:** The Koopman operator U : L²(μ) → L²(μ) defined by (Uf)(ω) = f(shift(ω)) is unitary when shift preserves μ. The Mean Ergodic Theorem gives L² convergence of Cesàro averages to the projection onto shift-invariant functions.

### Proof Strategy

1. **Shift-invariance:** Contractability implies the path measure is shift-invariant
2. **Mean Ergodic Theorem:** Cesàro averages converge in L² to the conditional expectation given the shift-invariant σ-algebra
3. **CE Product Factorization:** For contractable sequences, conditional expectations factor as products
4. **Bridge Lemma:** Injective indices reduce to consecutive indices via sorting

## File Structure

| File | Purpose |
|------|---------|
| `ContractableFactorization.lean` | CE product factorization for contractable sequences |
| `CesaroL2ToL1.lean` | L² to L¹ bridge lemmas |
| `InfraGeneralized.lean` | Generalized infrastructure |
| `InfraCore.lean` | Core infrastructure definitions |
| `InfraLagConstancy.lean` | Lag constancy infrastructure |
| `CesaroHelpers.lean` | Cesàro average helpers |
| `BlockAverage.lean` | Block average machinery |
| `KoopmanCommutation.lean` | Koopman operator commutation properties |
| `CesaroL1Bounded.lean` | Bounded L¹ convergence helpers |
| `CesaroPairFactorization.lean` | Pair factorization for Cesàro averages |
| `BlockInjection.lean` | Block injection lemmas |
| `KernelBridge.lean` | Bridge lemma for kernel measures |
| `CylinderFunctions.lean` | Cylinder function definitions |
| `LpCondExpHelpers.lean` | Lᵖ conditional expectation helpers |
| `DirectingKernel.lean` | Directing measure from CE kernel |
| `Quantization.lean` | Quantization machinery |
| `Infrastructure.lean` | Basic definitions |
| `CesaroConvergence.lean` | Cesàro convergence |

## Key Lemmas

| Lemma | Description |
|-------|-------------|
| `condexp_product_factorization_contractable` | CE factors as product for consecutive indices |
| `indicator_product_bridge_contractable` | Injective indices → kernel measure products |
| `conditionallyIID_bind_of_contractable` | Entry point for contractable sequences |

## References

- Kallenberg (2005), *Probabilistic Symmetries and Invariance Principles*, Chapter 1, Theorem 1.1
  - Page 26: "First proof of Theorem 1.1" (Koopman/ergodic route)
- Yosida (1980), *Functional Analysis*, Mean Ergodic Theorem
