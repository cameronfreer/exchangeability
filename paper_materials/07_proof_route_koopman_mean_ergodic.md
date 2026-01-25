---
Repo: https://github.com/human-oriented/exchangeability
Commit: aec253b69aaabbd93dd82fe1a7d9bbf34cf90ab5
Date: 2026-01-24
Built: yes
Lean: v4.27.0-rc1
Lake: v5.0.0-src+2fcce72
---

# Proof Route: Koopman/Mean Ergodic (Kallenberg's First Proof)

## Overview

**Entry point:** `Exchangeability/DeFinetti/TheoremViaKoopman.lean`

**Reference:** Kallenberg (2005), page 26, "First proof"

**Status:** Complete

**Key technique:** Mean Ergodic Theorem via Koopman operator on L²

## Key Connection

This proof connects de Finetti's theorem to **ergodic theory**, showing that exchangeability is fundamentally about dynamical invariance.

## File Structure

```
DeFinetti/
├── TheoremViaKoopman.lean         # Main theorem
├── ViaKoopman.lean                # Proof assembly
└── ViaKoopman/
    ├── BlockAverage.lean          # Block averaging
    ├── BlockInjection.lean        # Strictly monotone block maps
    ├── CesaroConvergence.lean     # Cesàro mean convergence
    ├── CesaroL1Bounded.lean       # L¹ bounds for Cesàro
    ├── CesaroL2ToL1.lean          # L² to L¹ transfer
    ├── CesaroPairFactorization.lean  # Pair factorization
    ├── CesaroHelpers.lean         # Cesàro utilities
    ├── ContractableFactorization.lean  # Main factorization
    ├── CylinderFunctions.lean     # Cylinder set functions
    ├── DirectingKernel.lean       # Kernel construction
    ├── InfraCore.lean             # Core infrastructure
    ├── InfraGeneralized.lean      # Generalized infrastructure
    ├── InfraLagConstancy.lean     # Lag constancy
    ├── Infrastructure.lean        # General infrastructure
    ├── KernelBridge.lean          # Kernel-measure bridge
    ├── KoopmanCommutation.lean    # Koopman operator properties
    ├── LpCondExpHelpers.lean      # Lp/condExp helpers
    └── Quantization.lean          # Quantization for approximation

Ergodic/
├── KoopmanMeanErgodic.lean        # Mean Ergodic Theorem
├── BirkhoffAvgCLM.lean            # Birkhoff averages as CLM
├── InvariantSigma.lean            # Invariant σ-algebra
├── ProjectionLemmas.lean          # Projection theory
├── ShiftInvariantRepresentatives.lean
└── ShiftInvariantSigma.lean       # Shift-invariant σ-algebra
```

## Proof Skeleton

### Step 1: Path Space and Shift Operator

**File:** `PathSpace/Shift.lean`

**Definition:** For path space `Ω = ℕ → α`, define the shift:
```
T : Ω → Ω
T(ω)_n = ω_{n+1}
```

**Key property:** Contractability implies `T` is measure-preserving:
```lean
theorem shift_measurePreserving_of_contractable
    (hContract : Contractable μ X) :
    MeasurePreserving shift μ
```

### Step 2: Koopman Operator

**File:** `Ergodic/KoopmanMeanErgodic.lean`

**Definition:** The Koopman operator `U_T : L²(μ) → L²(μ)`:
```
U_T f = f ∘ T
```

**Properties:**
- `U_T` is a linear isometry (since T is measure-preserving)
- `U_T` is unitary on the invariant subspace

**Lean:**
```lean
def koopmanOp (T : Ω → Ω) (hT : MeasurePreserving T μ) :
    Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  compRightCLM hT
```

### Step 3: Mean Ergodic Theorem

**File:** `Ergodic/KoopmanMeanErgodic.lean`

**Statement:** For any `f ∈ L²(μ)`:
```
(1/n) Σᵢ₌₀ⁿ⁻¹ Uⁱ f → P f  in L²
```

where `P` is the orthogonal projection onto the `U`-invariant subspace.

**Lean signature:**
```lean
theorem mean_ergodic_L2
    (T : Ω → Ω) (hT : MeasurePreserving T μ)
    (f : Lp ℝ 2 μ) :
    Tendsto (fun n => cesaro (koopmanOp T hT) n f) atTop
      (𝓝 (invariantProjection T hT f))
```

### Step 4: Invariant Functions are Tail-Measurable

**File:** `Ergodic/InvariantSigma.lean`

**Statement:** A function `f` satisfies `U_T f = f` a.e. if and only if `f` is measurable with respect to the shift-invariant σ-algebra.

The shift-invariant σ-algebra equals the tail σ-algebra:
```
{A : T⁻¹(A) = A a.e.} = ⋂_n σ(X_n, X_{n+1}, ...)
```

### Step 5: Block Averaging via Contractability

**File:** `ViaKoopman/ContractableFactorization.lean`

**Key insight:** For `m` disjoint blocks of size `n`, define block injections `ρⱼ` that select one element from each block. Contractability gives:
```
∫ ∏ᵢ fᵢ(Xᵢ) dμ = ∫ ∏ᵢ fᵢ(X_{ρⱼ(i)}) dμ
```

Averaging over all `n^m` choices of `j`:
```
∫ ∏ᵢ fᵢ(Xᵢ) dμ = ∫ ∏ᵢ (blockAvg_n fᵢ) dμ
```

### Step 6: L¹ Convergence of Block Averages

**File:** `ViaKoopman/CesaroL1Bounded.lean`

**Statement:** As `n → ∞`, block averages converge in L¹ to conditional expectations:
```
blockAvg_n f → 𝔼[f | mSI]  in L¹
```

where `mSI` is the shift-invariant σ-algebra.

### Step 7: Product Factorization

**File:** `ViaKoopman/CesaroPairFactorization.lean`

Taking `n → ∞` in the block average formula:
```
𝔼[∏ᵢ fᵢ(Xᵢ) | mSI] = ∏ᵢ 𝔼[fᵢ(X₀) | mSI]  a.e.
```

This is conditional independence given the tail.

### Step 8: Construct Directing Measure

**File:** `ViaKoopman/DirectingKernel.lean`

From the product factorization, construct `ν : Ω → Measure α`:
```
ν(ω) = Law(X_0 | mSI)(ω)
```

### Step 9: Extension to Borel Sets

**File:** `DeFinetti/CommonEnding.lean`

Use π-system/monotone class extension.

## Key Lemmas (Spine)

| # | Lemma | File | Purpose |
|---|-------|------|---------|
| 1 | `shift_measurePreserving` | ViaKoopman.lean | Shift preserves μ |
| 2 | `koopmanOp_isometry` | KoopmanMeanErgodic.lean | Koopman is isometric |
| 3 | `mean_ergodic_L2` | KoopmanMeanErgodic.lean | Mean Ergodic Theorem |
| 4 | `invariant_iff_tailMeasurable` | InvariantSigma.lean | Invariant = tail |
| 5 | `block_avg_contractable` | ContractableFactorization.lean | Block factorization |
| 6 | `block_avg_L1_convergence` | CesaroL1Bounded.lean | L¹ convergence |
| 7 | `product_factorization_ae` | CesaroPairFactorization.lean | Cond. indep. |
| 8 | `directingKernel_construct` | DirectingKernel.lean | ν construction |

## Dependencies

### mathlib
- `Mathlib.Analysis.InnerProductSpace.Projection`
- `Mathlib.MeasureTheory.Function.LpSpace`
- Hilbert space theory

### Internal (substantial)
- `Exchangeability/Ergodic/*.lean` (6 files)
- `Exchangeability/PathSpace/Shift.lean`

## Snippet: Mean Ergodic Theorem

```lean
/-- The Mean Ergodic Theorem in L².

    For a measure-preserving transformation T, the Cesàro averages
    (1/n) Σᵢ₌₀ⁿ⁻¹ f ∘ Tⁱ converge in L² to the projection of f onto
    the T-invariant subspace.
-/
theorem mean_ergodic_L2
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (T : Ω → Ω) (hT : MeasurePreserving T μ)
    (f : Lp ℝ 2 μ) :
    Tendsto (fun n => (1 : ℝ) / n • ∑ i ∈ Finset.range n, koopmanOp T hT^i f)
      atTop (𝓝 (invariantProjection T hT f))
```

## Mathematical Significance

This proof reveals de Finetti's theorem as part of **ergodic theory**:

1. **Dynamical interpretation:** Exchangeability means the shift dynamics is measure-preserving.

2. **Ergodic decomposition:** The directing measure arises from the ergodic decomposition of the path space.

3. **Invariant functions:** Conditionally on the tail σ-algebra (= invariant σ-algebra), the coordinates are i.i.d.

4. **Connection to Birkhoff:** The Mean Ergodic Theorem (L² Birkhoff) provides the necessary convergence.

## Comparison to Other Proofs

| Aspect | Koopman | Martingale | L² |
|--------|---------|-----------|-----|
| Key tool | Mean Ergodic Thm | Reverse martingale | Correlation bounds |
| Conceptual | Ergodic theory | Probability | Analysis |
| Dependencies | Heavy | Medium | Light |
| Generality | L²-valued | General Borel | ℝ-valued |
| Elegance | ★★★★★ | ★★★★☆ | ★★★☆☆ |
