/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer, Claude (Anthropic)
-/
import Exchangeability.Core
import Exchangeability.Contractability
import Exchangeability.DeFinetti.L2Helpers

/-!
# Contractability vs. Exchangeability: Why No Direct Implication

This file documents why `cesaro_to_condexp_L2` uses `l2_contractability_bound` instead
of `kallenberg_L2_bound`, addressing the circularity that would arise from assuming
exchangeability while trying to prove contractable → exchangeable.

## The De Finetti Equivalence

**Theorem (Kallenberg 1.1):** For infinite sequences on Borel spaces:
```
Contractable μ X  ⟺  Exchangeable μ X  ⟺  ConditionallyIID μ X
```

## Why There's No Counterexample

**Important:** There is NO counterexample showing contractability ≠ exchangeability for
infinite sequences on Borel spaces. The two concepts are equivalent!

However, establishing this equivalence requires significant work:
- `contractable_of_exchangeable` (Contractability.lean): Exchangeable → Contractable ✓
- `cesaro_to_condexp_L2` (ViaL2.lean): Contractable → ConditionallyIID → Exchangeable
  (this is the deep direction)

## The Circularity Problem

When proving `cesaro_to_condexp_L2`, we cannot assume exchangeability:
- **Given hypothesis:** `Contractable μ X`
- **Goal:** Prove X is conditionally i.i.d. (which implies exchangeable)
- **Circular if we assumed:** `Exchangeable μ X` (this is what we're trying to prove!)

## What Contractability Immediately Gives Us

### Definition
```lean
def Contractable (μ : Measure Ω) (X : ℕ → Ω → α) : Prop :=
  ∀ (n : ℕ) (k : Fin n → ℕ), StrictMono k →
    Measure.map (fun ω i => X (k i) ω) μ = Measure.map (fun ω i => X i ω) μ
```

### Immediate Consequences

**1. Uniform marginals** (via `contractable_map_single`):
All individual variables have the same distribution.
-/

namespace Exchangeability.DeFinetti.ContractabilityExamples

open MeasureTheory

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable (X : ℕ → Ω → ℝ)
variable (hX_contract : Contractable μ X)
variable (hX_meas : ∀ i, Measurable (X i))

/-- **Example 1:** Contractability gives uniform marginals.

All single variables X_i have the same distribution as X_0. -/
example (i : ℕ) :
    Measure.map (X i) μ = Measure.map (X 0) μ :=
  L2Helpers.contractable_map_single (X := X) hX_contract hX_meas (i := i)

/-- **Example 2:** Contractability gives uniform bivariate distributions for increasing pairs.

For any i < j, the pair (X_i, X_j) has the same distribution as (X_0, X_{j-i}). -/
example {i j : ℕ} (hij : i < j) :
    Measure.map (fun ω => (X i ω, X j ω)) μ =
    Measure.map (fun ω => (X 0 ω, X (j-i) ω)) μ := by
  -- Use contractability with the subsequence {i, j}
  sorry  -- Follows from definition, via appropriate reindexing

/-! ### What Contractability Doesn't Immediately Give

**Permutation invariance:**

Contractability does NOT immediately tell us that (X_0, X_1) and (X_1, X_0) have the
same distribution, because (1, 0) is not an increasing subsequence!

However, by the de Finetti theorem, contractable sequences ARE exchangeable, so this
equality DOES hold - we just can't use it while proving the theorem. -/

/-- **Non-example:** Contractability doesn't directly give permutation invariance.

We cannot prove this using only the contractability hypothesis - it requires the full
de Finetti theorem! -/
example :
    Measure.map (fun ω => (X 0 ω, X 1 ω)) μ =
    Measure.map (fun ω => (X 1 ω, X 0 ω)) μ := by
  -- This is TRUE (by de Finetti), but we can't prove it from contractability alone
  -- without going through the full de Finetti proof!
  sorry

/-! ## Why Contractability Suffices for L² Bounds

Even though contractability doesn't give permutation invariance, it DOES give:

### Uniform Covariance Structure

For centered variables Z_i = X_i - E[X_i]:
-/

/-- **Example 3:** Contractability gives uniform variance.

All variables have the same second moment. -/
example (m : ℝ) (hm : ∀ i, ∫ ω, X i ω ∂μ = m) (i : ℕ) :
    ∫ ω, (X i ω - m)^2 ∂μ = ∫ ω, (X 0 ω - m)^2 ∂μ := by
  -- Follows from contractable_map_single
  sorry

/-- **Example 4:** Contractability gives uniform pairwise covariance for increasing pairs.

For any i < j, the covariance of (X_i, X_j) equals that of (X_0, X_1). -/
example (m : ℝ) (hm : ∀ i, ∫ ω, X i ω ∂μ = m) {i j : ℕ} (hij : i < j) :
    ∫ ω, (X i ω - m) * (X j ω - m) ∂μ = ∫ ω, (X 0 ω - m) * (X 1 ω - m) ∂μ := by
  -- Follows from contractable_map_pair
  sorry

/-! ### Why This Suffices for `l2_contractability_bound`

The theorem `l2_contractability_bound` from L2Helpers.lean requires:
```lean
theorem l2_contractability_bound
    (hvar : ∀ k, ∫ ω, (ξ k ω - m)^2 ∂μ = σ ^ 2)        ← Uniform variance
    (hcov : ∀ i j, i ≠ j → ∫ ω, (ξ i ω - m) * (ξ j ω - m) ∂μ = σ ^ 2 * ρ)  ← Uniform covariance for ALL pairs
```

**Key observation:** Even though contractability only gives us covariance equality for
increasing pairs (i < j), we also need it for i > j.

**Solution:** Covariance is symmetric! If Cov(X_i, X_j) = Cov(X_0, X_1) for i < j, then:
```
Cov(X_j, X_i) = Cov(X_i, X_j)  (by symmetry of covariance)
                = Cov(X_0, X_1)  (from contractability with i < j)
```

So contractability DOES give us the uniform covariance structure needed by the L² bound!
-/

/-- **Example 5:** Covariance is symmetric, so contractability gives uniform covariance
for ALL pairs (not just increasing ones). -/
example (m : ℝ) (hm : ∀ i, ∫ ω, X i ω ∂μ = m) {i j : ℕ} (hij : i ≠ j) :
    ∫ ω, (X i ω - m) * (X j ω - m) ∂μ = ∫ ω, (X 0 ω - m) * (X 1 ω - m) ∂μ := by
  by_cases h_lt : i < j
  · -- Case i < j: use contractability directly
    sorry
  · -- Case i > j: use contractability + symmetry
    have hji : j < i := Nat.lt_of_le_of_ne (Nat.le_of_not_lt h_lt) (hij.symm)
    sorry

/-! ## Summary

| Property | Contractability | Exchangeability |
|----------|----------------|-----------------|
| **Definition** | Increasing subsequences have same distribution | Finite permutations preserve distribution |
| **Uniform marginals** | ✓ (immediate) | ✓ (immediate) |
| **Uniform covariance** | ✓ (immediate + symmetry) | ✓ (immediate) |
| **Permutation invariance** | ✓ (via de Finetti theorem) | ✓ (by definition) |
| **Needed for L² bound** | ✓ Uniform covariance suffices | ✓ But stronger than needed |

**Conclusion:**
- Contractability and exchangeability are equivalent (de Finetti theorem)
- But contractability is the weaker *assumption* (doesn't directly give permutations)
- Contractability is still *sufficient* for L² bounds (gives uniform covariance)
- Therefore: use `l2_contractability_bound` to avoid circular reasoning

The key insight is that the **uniform covariance structure** (not full permutation invariance)
is what matters for the L² Cesàro convergence argument. Contractability provides exactly this!
-/

end Exchangeability.DeFinetti.ContractabilityExamples
