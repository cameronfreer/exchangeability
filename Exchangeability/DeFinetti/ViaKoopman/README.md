# ViaKoopman: Kallenberg's First Proof of de Finetti's Theorem

This directory implements Kallenberg's "first proof" of de Finetti's theorem using the Mean Ergodic Theorem and Koopman operator. This proof has the **heaviest dependencies** but provides a deep connection to ergodic theory and dynamical systems.

## Mathematical Overview

**Main result:** For contractable sequences on Borel spaces, coordinates are conditionally i.i.d. given the shift-invariant σ-algebra.

**Key insight:** The Koopman operator U : L²(μ) → L²(μ) defined by (Uf)(ω) = f(shift(ω)) is a unitary operator when shift preserves μ. The Mean Ergodic Theorem then gives L² convergence of Cesàro averages to the projection onto shift-invariant functions.

## Two Proof Routes

The Koopman proof has two entry points based on what hypothesis you start with:

### 1. Exchangeable Route (`ViaKoopman.lean` + `KernelIndependence.lean`)

```
Exchangeable → FullyExchangeable → path measure invariant
                                          ↓
                      MeasurePreserving shift (μ_path)
                                          ↓
                      Mean Ergodic Theorem → Cesàro convergence
                                          ↓
                      Conditional independence via indicator products
                                          ↓
                      ConditionallyIID
```

**Entry lemma:** `exchangeable_implies_ciid_modulo_bridge`

### 2. Contractable Route (`ViaKoopmanContractable.lean`) — Recommended

```
Contractable → MeasurePreserving shift (via contractability)
                          ↓
         Cesàro convergence (same as above)
                          ↓
         CE product factorization via contractability
                          ↓
         indicator_product_bridge_contractable (injective → StrictMono sort)
                          ↓
         ConditionallyIID (no permutations needed!)
```

**Entry lemma:** `conditionallyIID_bind_of_contractable`

### Why Prefer the Contractable Route?

1. **No circular dependency** - Avoids needing exchangeability to prove CIID
2. **Cleaner architecture** - Uses contractability directly without π-system machinery
3. **Kallenberg's actual approach** - Matches the "first proof" structure on page 26

## File Structure

### Core Files (top-level)

| File | Lines | Purpose |
|------|-------|---------|
| `ViaKoopman.lean` | ~6600 | Main proof via exchangeability route |
| `ViaKoopmanContractable.lean` | ~650 | **Recommended** proof via contractability |

### Supporting Infrastructure (`ViaKoopman/`)

| File | Purpose |
|------|---------|
| `Infrastructure.lean` | Shift operators, basic definitions |
| `DirectingKernel.lean` | Directing measure ν construction |
| `ContractableFactorization.lean` | CE product factorization for contractable sequences |
| `KernelIndependence.lean` | Bridge lemma for exchangeability route |
| `CesaroConvergence.lean` | L² convergence of Cesàro averages |
| `CesaroHelpers.lean` | Helper lemmas for Cesàro averages |
| `KoopmanCommutation.lean` | Koopman operator commutation properties |
| `LpCondExpHelpers.lean` | L^p conditional expectation helpers |
| `CylinderFunctions.lean` | Cylinder function definitions |
| `Quantization.lean` | Quantization machinery |
| `BlockInjection.lean` | Block injection lemmas |

## Key Lemmas

### From `ViaKoopmanContractable.lean`

```lean
-- Main bridge: injective indices → kernel measure products
lemma indicator_product_bridge_contractable
    (hσ : MeasurePreserving shift μ μ)
    (hContract : ∀ (m : ℕ) (k : Fin m → ℕ), StrictMono k → ...)
    (k : Fin m → ℕ) (hk : Function.Injective k) (B : Fin m → Set α) :
    ∫⁻ ω, ∏ i, ENNReal.ofReal ((B i).indicator 1 (ω (k i))) ∂μ
      = ∫⁻ ω, ∏ i, (ν ω) (B i) ∂μ

-- Entry point for contractable sequences
lemma conditionallyIID_bind_of_contractable
    (hσ : MeasurePreserving shift μ μ)
    (hContract : ∀ (m : ℕ) (k : Fin m → ℕ), StrictMono k → ...) :
    Exchangeability.ConditionallyIID μ (fun i ω => ω i)
```

### From `ContractableFactorization.lean`

```lean
-- CE factorizes as product for consecutive indices
lemma condexp_product_factorization_contractable
    (hσ : MeasurePreserving shift μ μ) (hContract : ...)
    (fs : Fin m → α → ℝ) :
    μ[fun ω => ∏ i, fs i (ω i.val) | shiftInvariantSigma]
      =ᵐ[μ] fun ω => ∏ i, μ[fun ω' => fs i (ω' 0) | shiftInvariantSigma] ω
```

### From `DirectingKernel.lean`

```lean
-- Directing measure from conditional expectation kernel
def ν (μ : Measure Ω[α]) : Ω[α] → Measure α

-- ν gives probability measures a.e.
lemma ν_isProbabilityMeasure (ω : Ω[α]) : IsProbabilityMeasure (ν ω)

-- Integral against ν = integral against condExpKernel
lemma integral_ν_eq_integral_condExpKernel (f : α → ℝ) :
    ∫ x, f x ∂(ν ω) = ∫ y, f (y 0) ∂(condExpKernel μ mSI ω)
```

## Proof of `indicator_product_bridge_contractable`

The key insight is sorting injective indices to reduce to the consecutive case:

1. **Sort injective k**: Use `injective_implies_strictMono_perm` to get permutation σ such that ρ := k ∘ σ is StrictMono

2. **Reindex products**: Use `Equiv.prod_comp` to rewrite:
   - `∏ i, indicator (k i) = ∏ j, indicator (ρ j)` via σ
   - `∏ i, ν(B i) = ∏ j, ν(B (σ j))` via σ

3. **Apply contractability**: Reduce from ρ-indices to consecutive indices

4. **CE factorization**: Apply `condexp_product_factorization_contractable` for consecutive indices

5. **Chain equalities**: Convert lintegral ↔ integral via `ofReal_integral_eq_lintegral_ofReal`

## Dependencies

```
Ergodic/KoopmanMeanErgodic.lean (Mean Ergodic Theorem)
        ↓
ViaKoopman/CesaroConvergence.lean
        ↓
ViaKoopman/ContractableFactorization.lean
        ↓
ViaKoopman/DirectingKernel.lean
        ↓
ViaKoopmanContractable.lean ← indicator_product_bridge_contractable
        ↓
TheoremViaKoopman.lean (main theorem)
```

The lemma `injective_implies_strictMono_perm` lives in `Exchangeability.Util.StrictMono`,
a common utilities file with no project dependencies.

## Comparison with Other Proofs

| Aspect | ViaKoopman | ViaL2 | ViaMartingale |
|--------|------------|-------|---------------|
| **Approach** | Mean Ergodic Theorem | L² bounds | Reverse martingale |
| **Dependencies** | Heavy (ergodic theory) | Light | Medium |
| **Generality** | Extends to dynamical systems | Specific to de Finetti | Specific to de Finetti |
| **Complexity** | ~7000 lines | ~2500 lines | ~2000 lines |

## Current Status

- **ViaKoopmanContractable.lean**: Complete (no sorries)
- **ContractableFactorization.lean**: Complete (no sorries)
- **DirectingKernel.lean**: Complete (no sorries)
- **ViaKoopman.lean**: 4 active sorries (in MET/factorization sections)

## References

- Kallenberg (2005), *Probabilistic Symmetries and Invariance Principles*, Chapter 1, Theorem 1.1 ("First proof")
- Yosida (1980), *Functional Analysis*, Mean Ergodic Theorem
