---
Repo: https://github.com/human-oriented/exchangeability
Commit: aec253b69aaabbd93dd82fe1a7d9bbf34cf90ab5
Date: 2026-01-24
Built: yes
Lean: v4.27.0-rc1
Lake: v5.0.0-src+2fcce72
---

# Proof Route: Reverse Martingale (Kallenberg's Third Proof)

## Overview

**Entry point:** `Exchangeability/DeFinetti/TheoremViaMartingale.lean`

**Reference:** Kallenberg (2005), Lemma 1.3 and page 28

**Status:** Complete

**Key technique:** Reverse martingale convergence for conditional expectations

## File Structure

```
DeFinetti/
├── TheoremViaMartingale.lean      # Main theorems (public API)
├── ViaMartingale.lean             # Proof assembly
└── ViaMartingale/
    ├── LocalInfrastructure.lean   # Local lemmas and notation
    ├── PairLawEquality.lean       # (ξ,η) =ᵈ (ξ,ζ) infrastructure
    ├── ShiftOperations.lean       # Shift operator on path space
    ├── RevFiltration.lean         # Reverse filtration ℱ_{≥n}
    ├── FutureFiltration.lean      # Future σ-algebra theory
    ├── FutureRectangles.lean      # Rectangle sets for products
    ├── FiniteCylinders.lean       # Cylinder set manipulation
    ├── CondExpConvergence.lean    # Reverse martingale convergence
    ├── DirectingMeasure.lean      # Construction of ν
    ├── IndicatorAlgebra.lean      # Indicator function algebra
    ├── Factorization.lean         # Product factorization lemmas
    ├── FiniteProduct.lean         # Finite product formula
    └── KallenbergChain.lean       # Kallenberg lemma chain
```

## Proof Skeleton

### Step 1: Contraction-Independence Lemma (Kallenberg Lemma 1.3)

**File:** `ViaMartingale/PairLawEquality.lean`

**Statement:** If `(ξ, η) =ᵈ (ξ, ζ)` and `σ(η) ⊆ σ(ζ)`, then `ξ ⊥⊥_η ζ`.

**Lean signature:**
```lean
theorem contraction_independence
    (hLaw : Law (Y, W) = Law (Y, W'))
    (hSub : σ(W) ⊆ σ(W')) :
    CondIndep Y W W'
```

**Proof idea:**
1. Define `μ₁ = 𝔼[1_B(Y) | W]` and `μ₂ = 𝔼[1_B(Y) | W']`
2. `(μ₁, μ₂)` is a bounded martingale
3. `μ₁ =ᵈ μ₂` from the law equality
4. Therefore `𝔼[(μ₂ - μ₁)²] = 𝔼[μ₂²] - 𝔼[μ₁²] = 0`
5. So `μ₁ = μ₂` a.s., giving conditional independence

### Step 2: Reverse Filtration

**File:** `ViaMartingale/RevFiltration.lean`

**Definition:** For a sequence `X : ℕ → Ω → α`, define:
- `ℱ_{≥n} = σ(X_n, X_{n+1}, X_{n+2}, ...)` (future σ-algebra from position n)
- `ℱ_∞ = ⋂_n ℱ_{≥n}` (tail σ-algebra)

**Key property:** `ℱ_{≥0} ⊇ ℱ_{≥1} ⊇ ℱ_{≥2} ⊇ ...` (decreasing)

### Step 3: Reverse Martingale Convergence

**File:** `ViaMartingale/CondExpConvergence.lean`

**Statement:** For an integrable `f`:
```
𝔼[f | ℱ_{≥n}] → 𝔼[f | ℱ_∞]  a.s. and in L¹
```

**Lean signature:**
```lean
theorem condExp_tail_convergence
    (hf : Integrable f μ) :
    Tendsto (fun n => condExp ℱ_{≥n} f) atTop
      (𝓝 (condExp ℱ_∞ f)) -- a.e. and L¹
```

### Step 4: Directing Measure Construction

**File:** `ViaMartingale/DirectingMeasure.lean`

**Construction:** Define `ν : Ω → Measure α` via the conditional distribution kernel:
```
ν(ω)(B) = 𝔼[1_{X_0 ∈ B} | ℱ_∞](ω)
```

**Key properties:**
```lean
def directingMeasure (X : ℕ → Ω → α) : Ω → Measure α := condExpKernel μ (X 0) ℱ_∞

theorem directingMeasure_isProb : ∀ ω, IsProbabilityMeasure (ν ω)

theorem directingMeasure_measurable_eval :
    ∀ B, MeasurableSet B → Measurable (fun ω => (ν ω) B)
```

### Step 5: Conditional Law Equality

**File:** `ViaMartingale/Factorization.lean`

**Key lemma:** For any index `k` and measurable `B`:
```
𝔼[1_{X_k ∈ B} | ℱ_∞] = ν(B)  a.e.
```

**Proof:** From contractability, `(X_k, θ_{k+1} X) =ᵈ (X_0, θ_{k+1} X)`, and by Lemma 1.3 this gives the equality.

### Step 6: Finite Product Formula

**File:** `ViaMartingale/FiniteProduct.lean`

**Statement:** For any strictly increasing `k : Fin m → ℕ`:
```
Law(X_{k(0)}, ..., X_{k(m-1)}) = ∫ ν^⊗m dμ
```

**Lean signature:**
```lean
theorem finite_product_formula (m : ℕ) (k : Fin m → ℕ) (hk : StrictMono k) :
    Measure.map (fun ω i => X (k i) ω) μ =
      μ.bind (fun ω => Measure.pi (fun _ => ν ω))
```

**Proof:** Uses conditional independence from Step 5.

### Step 7: Extension to Borel Sets

**File:** `DeFinetti/CommonEnding.lean`

Uses π-system/monotone class to extend from cylinder sets to all Borel sets.

## Key Lemmas (Spine)

| # | Lemma | File | Line |
|---|-------|------|------|
| 1 | `integral_map_eq` | ViaMartingale.lean | 116 |
| 2 | `integral_eq_of_map_eq` | ViaMartingale.lean | 129 |
| 3 | `condExp_tail_convergence` | CondExpConvergence.lean | ~80 |
| 4 | `contraction_independence` | PairLawEquality.lean | ~150 |
| 5 | `directingMeasure_isProb` | DirectingMeasure.lean | ~50 |
| 6 | `conditional_law_eq_directingMeasure` | Factorization.lean | ~100 |
| 7 | `finite_product_formula` | FiniteProduct.lean | ~200 |
| 8 | `conditionallyIID_of_contractable` | TheoremViaMartingale.lean | 70 |

## Dependencies

### mathlib
- `Mathlib.Probability.ConditionalExpectation`
- `Mathlib.Probability.Martingale.Basic`
- `Mathlib.Probability.Kernel.CondDistrib`
- `Mathlib.Probability.Kernel.Condexp`

### Internal
- `Exchangeability/Probability/Martingale/Reverse.lean`
- `Exchangeability/Tail/TailSigma.lean`
- `Exchangeability/Probability/CondExp.lean`

## Snippet: Directing Measure Construction

```lean
/-- The directing measure for a sequence, defined via conditional expectation kernel.
    This is the random probability measure ν such that coordinates are
    conditionally i.i.d. with distribution ν. -/
def directingMeasure
    {Ω α : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    [MeasurableSpace α] [StandardBorelSpace α]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → α) (hX_meas : ∀ i, Measurable (X i)) : Ω → Measure α :=
  condExpKernel μ (X 0) (tailSigma X)
```

## Elegance Notes

The martingale approach is particularly elegant because:

1. **Probabilistically natural:** The proof uses fundamental probabilistic tools (martingales, conditional expectations) in their natural habitat.

2. **Conceptually clear:** The key insight - that contractability implies conditional i.i.d. via the contraction-independence lemma - is intuitive.

3. **Minimal machinery:** Once reverse martingale convergence is available, the rest follows naturally.

4. **General:** Works for arbitrary standard Borel state spaces, not just ℝ.
