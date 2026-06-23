---
Repo: https://github.com/cameronfreer/exchangeability
Commit: aec253b69aaabbd93dd82fe1a7d9bbf34cf90ab5
Date: 2026-01-24
Built: yes
Lean: v4.27.0-rc1
Lake: v5.0.0-src+2fcce72
---

# Proof Route: L² Bounds (Kallenberg's Second Proof)

## Overview

**Entry point:** `Exchangeability/DeFinetti/TheoremViaL2.lean`

**Reference:** Kallenberg (2005), page 27, Lemma 1.2

**Status:** Complete

**Key technique:** Elementary L² correlation bounds from contractability

## Key Advantage

**Lightest dependencies** - no ergodic theory, minimal martingale theory. Uses only L² spaces and basic measure theory.

## File Structure

```
DeFinetti/
├── TheoremViaL2.lean              # Main theorem
├── ViaL2.lean                     # Proof assembly
└── ViaL2/
    ├── BlockAverages.lean         # Block average definitions (~1600 lines)
    ├── BlockAvgDef.lean           # Core block average type
    ├── Clip01.lean                # Clipping to [0,1]
    ├── CesaroConvergence.lean     # Cesàro convergence (~2800 lines)
    ├── AlphaConvergence.lean      # α_n → α_∞ in L²
    ├── AlphaIic.lean              # α indexed by Iic
    ├── AlphaIicCE.lean            # Conditional expectation of α
    ├── MainConvergence.lean       # Main convergence theorems (~2800 lines)
    ├── DirectingMeasureCore.lean  # ν construction core
    ├── DirectingMeasureIntegral.lean # Product formula via ν
    ├── MoreL2Helpers.lean         # Technical L² lemmas (~1400 lines)
    └── WindowMachinery.lean       # Sliding window helpers
```

## Proof Skeleton

### Step 1: Work with Bounded Random Variables

**File:** `ViaL2/Clip01.lean`

For general random variables, first clip to [0,1]:
```lean
def clip01 (x : ℝ) : ℝ := max 0 (min 1 x)
```

The general case follows by:
1. Proving the result for bounded random variables
2. Approximating general L² random variables by bounded ones

### Step 2: Block Averages

**File:** `ViaL2/BlockAverages.lean`

**Definition:** For a sequence `X : ℕ → Ω → ℝ`, define:
```
α_n(ω) = (1/n) Σᵢ₌₀ⁿ⁻¹ X_i(ω)
```

**Lean:**
```lean
def blockAvg (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (1 / n) * ∑ i ∈ Finset.range n, X i ω
```

### Step 3: Kallenberg Lemma 1.2 (Correlation Bound)

**File:** `ViaL2/CesaroConvergence.lean`

**Statement:** For contractable `X` with `X_i` bounded in [0,1]:
```
|𝔼[X_i · X_j] - 𝔼[X_i] · 𝔼[X_j]| ≤ C / min(i+1, j+1)
```

**Key Lean lemma:** `l2_contractability_bound` at L2Helpers.lean:852

**Proof idea:** From contractability:
- `(X_0, X_i) =ᵈ (X_j, X_i)` for `j ≤ i`
- This bounds cross-correlations
- Summing over indices gives the bound

### Step 4: L² Convergence of Block Averages

**File:** `ViaL2/AlphaConvergence.lean`

**Statement:** The sequence `α_n` is Cauchy in L²:
```
‖α_n - α_m‖₂ → 0  as n,m → ∞
```

**Proof:** Using the correlation bound:
```
𝔼[(α_n - α_m)²] = 𝔼[α_n²] + 𝔼[α_m²] - 2𝔼[α_n · α_m]
```
Each term is controlled by the correlation bound, giving:
```
𝔼[(α_n - α_m)²] ≤ C · (log n / n + log m / m)
```

**Lean signature:**
```lean
theorem alpha_L2_cauchy :
    CauchySeq (fun n => (⟨blockAvg X n, blockAvg_memLp X n⟩ : Lp ℝ 2 μ))
```

### Step 5: L² Limit Exists

**File:** `ViaL2/MainConvergence.lean`

**Statement:** There exists `α_∞ ∈ L²(μ)` such that:
```
α_n → α_∞  in L²
```

**Lean:**
```lean
theorem alpha_L2_limit_exists :
    ∃ α_∞ : Lp ℝ 2 μ, Tendsto (fun n => blockAvg X n) atTop (𝓝 α_∞)
```

### Step 6: Product Factorization

**File:** `ViaL2/DirectingMeasureIntegral.lean`

**Statement:** For bounded measurable `f, g : ℝ → ℝ`:
```
𝔼[f(X_i) · g(X_j)] = 𝔼[𝔼[f(X_0) | α_∞] · 𝔼[g(X_0) | α_∞]]
```

This is the key factorization showing conditional independence.

**Lean signature:**
```lean
theorem product_factorization
    (hContract : Contractable μ X)
    (hf : Bounded f) (hg : Bounded g) (i j : ℕ) :
    ∫ f (X i) * g (X j) ∂μ = ∫ (condExp f α_∞) * (condExp g α_∞) ∂μ
```

### Step 7: Construct Directing Measure

**File:** `ViaL2/DirectingMeasureCore.lean`

From the factorization, construct `ν : Ω → Measure ℝ` such that:
```
∫ f dν(ω) = 𝔼[f(X_0) | α_∞](ω)
```

### Step 8: Extension to Borel Sets

**File:** `DeFinetti/CommonEnding.lean`

Use π-system/monotone class to extend from cylinder sets to Borel sets.

## Key Lemmas (Spine)

| # | Lemma | File | Purpose |
|---|-------|------|---------|
| 1 | `blockAvg` | BlockAvgDef.lean:45 | Block average definition |
| 2 | `blockAvg_measurable` | BlockAvgDef.lean:48 | Block averages are measurable |
| 3 | `l2_contractability_bound` | L2Helpers.lean:852 | Kallenberg Lemma 1.2 (correlation bound) |
| 4 | `reverse_martingale_subsequence_convergence` | MainConvergence.lean:796 | Subsequential a.e. convergence |
| 5 | `conditionallyIID_of_contractable_viaL2` | TheoremViaL2.lean:135 | Main theorem |

*Note: The L² proof involves many helper lemmas; the above are the key ones.*

## Dependencies

### mathlib
- `Mathlib.MeasureTheory.Function.LpSpace`
- `Mathlib.Analysis.Normed.Field.Lemmas`
- `Mathlib.Topology.MetricSpace.CauchySeq`

### Internal (minimal)
- `Exchangeability/Contractability.lean`
- `Exchangeability/ConditionallyIID.lean`
- `Exchangeability/Probability/LpNormHelpers.lean`

## Snippet: L² Contractability Bound (Kallenberg Lemma 1.2)

**File:** `DeFinetti/L2Helpers.lean:852`

```lean
/-- L² bound for weighted differences of contractable random variables.
Following Kallenberg page 26, Lemma 1.2. -/
theorem l2_contractability_bound
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} (ξ : Fin n → Ω → ℝ)
    (m : ℝ) (σ ρ : ℝ)
    (_hρ_bd : -1 ≤ ρ ∧ ρ ≤ 1)
    (_hmean : ∀ k, ∫ ω, ξ k ω ∂μ = m)
    (_hL2 : ∀ k, MemLp (fun ω => ξ k ω - m) 2 μ)
    (_hvar : ∀ k, ∫ ω, (ξ k ω - m)^2 ∂μ = σ ^ 2)
    (_hcov : ∀ i j, i ≠ j → ∫ ω, (ξ i ω - m) * (ξ j ω - m) ∂μ = σ ^ 2 * ρ)
    (p q : Fin n → ℝ)
    (_hp_prob : (∑ i, p i) = 1 ∧ ∀ i, 0 ≤ p i)
    (_hq_prob : (∑ i, q i) = 1 ∧ ∀ i, 0 ≤ q i) :
    ∫ ω, (∑ i, p i * ξ i ω - ∑ i, q i * ξ i ω)^2 ∂μ ≤
      2 * σ ^ 2 * (1 - ρ) * (⨆ i, |p i - q i|)
```

## Why This Proof is "Elementary"

1. **No ergodic theory:** Does not use the Mean Ergodic Theorem or Koopman operators.

2. **No reverse martingales:** Does not use martingale convergence theorems.

3. **L² only:** Uses only Hilbert space structure of L², no deeper analysis.

4. **Explicit estimates:** All bounds are explicit and computable.

5. **Self-contained:** The correlation bound is proved from first principles using only contractability.

## Limitation

This proof works directly only for **ℝ-valued** random variables (or more generally, Hilbert spaces). For general standard Borel spaces, one must either:
- Embed into ℝ (using Borel isomorphism)
- Use the martingale proof instead
