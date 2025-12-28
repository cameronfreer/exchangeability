/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer, Claude (Anthropic)
-/
import Exchangeability.Core
import Exchangeability.Contractability
import Exchangeability.DeFinetti.L2Helpers
import Exchangeability.DeFinetti.ViaL2
import Mathlib.Probability.IdentDistrib

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
  -- Strategy: (X_i, X_j) ~ (X_0, X_1) ~ (X_0, X_{j-i}) by contractability
  have h1 := L2Helpers.contractable_map_pair (X := X) hX_contract hX_meas hij
  -- Now show (X_0, X_{j-i}) ~ (X_0, X_1)
  have hpos : 0 < j - i := Nat.sub_pos_of_lt hij
  have h2 := L2Helpers.contractable_map_pair (X := X) hX_contract hX_meas hpos
  exact h1.trans h2.symm

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
  classical

  -- De Finetti (proved in `Exchangeability.DeFinetti.ViaL2`):
  -- contractable sequences on Borel spaces are exchangeable.
  have hX_exch : Exchangeable μ X :=
    exchangeable_of_contractable (μ := μ) (X := X) hX_contract hX_meas

  -- Apply exchangeability to the transposition (0 1) on `Fin 2`.
  let σ : Equiv.Perm (Fin 2) := Equiv.swap (0 : Fin 2) 1
  have hσ :
      Measure.map (fun ω i : Fin 2 => X (σ i : ℕ) ω) μ =
        Measure.map (fun ω i : Fin 2 => X (i : ℕ) ω) μ :=
    hX_exch 2 σ

  -- Push forward both sides by the measurable map extracting the first two coordinates.
  let p : (Fin 2 → ℝ) → ℝ × ℝ := fun y => (y 0, y 1)
  have hp : Measurable p := by
    exact (measurable_pi_apply (0 : Fin 2)).prod_mk (measurable_pi_apply (1 : Fin 2))
  have h_meas_left : Measurable (fun ω i : Fin 2 => X (σ i : ℕ) ω) :=
    measurable_pi_lambda _ (fun i => hX_meas (σ i : ℕ))
  have h_meas_right : Measurable (fun ω i : Fin 2 => X (i : ℕ) ω) :=
    measurable_pi_lambda _ (fun i => hX_meas (i : ℕ))

  have h := congrArg (fun ν => Measure.map p ν) hσ
  rw [Measure.map_map hp h_meas_left, Measure.map_map hp h_meas_right] at h

  -- `σ` swaps the two coordinates, so the LHS becomes `(X 1, X 0)`.
  simpa [p, σ] using h.symm

/-! ## Why Contractability Suffices for L² Bounds

Even though contractability doesn't give permutation invariance, it DOES give:

### Uniform Covariance Structure

**CRITICAL INSIGHT:** The difference between:
- **Symmetry of covariance functional**: ∫ (X_i - m)(X_j - m) = ∫ (X_j - m)(X_i - m)
  (follows from commutativity of multiplication - a purely algebraic property!)
- **Symmetry of joint distribution**: (X_i, X_j) ~ (X_j, X_i)
  (requires exchangeability - the property we're proving!)

We only need the first, which we get for FREE from algebra, not the second.

For centered variables Z_i = X_i - E[X_i]:
-/

/-- **Example 3:** Contractability gives uniform variance.

All variables have the same second moment. -/
example (m : ℝ) (hm : ∀ i, ∫ ω, X i ω ∂μ = m) (i : ℕ) :
    ∫ ω, (X i ω - m)^2 ∂μ = ∫ ω, (X 0 ω - m)^2 ∂μ := by
  -- X_i and X_0 have the same distribution by contractability
  have h_map := L2Helpers.contractable_map_single (X := X) hX_contract hX_meas (i := i)
  -- Build IdentDistrib from the map equality
  have h_id : ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ :=
    { aemeasurable_fst := (hX_meas i).aemeasurable
      aemeasurable_snd := (hX_meas 0).aemeasurable
      map_eq := h_map }
  -- Apply IdentDistrib.comp with g(x) = (x - m)²
  have h_comp : ProbabilityTheory.IdentDistrib (fun ω => (X i ω - m)^2) (fun ω => (X 0 ω - m)^2) μ μ :=
    h_id.comp (by measurability : Measurable fun x => (x - m)^2)
  -- Use IdentDistrib.integral_eq
  exact h_comp.integral_eq

/-- **Example 4:** Contractability gives uniform pairwise covariance for increasing pairs.

For any i < j, the covariance of (X_i, X_j) equals that of (X_0, X_1). -/
example (m : ℝ) (hm : ∀ i, ∫ ω, X i ω ∂μ = m) {i j : ℕ} (hij : i < j) :
    ∫ ω, (X i ω - m) * (X j ω - m) ∂μ = ∫ ω, (X 0 ω - m) * (X 1 ω - m) ∂μ := by
  -- (X_i, X_j) and (X_0, X_1) have the same joint distribution by contractability
  have h_map := L2Helpers.contractable_map_pair (X := X) hX_contract hX_meas hij
  -- Build IdentDistrib from the map equality
  have h_id : ProbabilityTheory.IdentDistrib (fun ω => (X i ω, X j ω)) (fun ω => (X 0 ω, X 1 ω)) μ μ :=
    { aemeasurable_fst := ((hX_meas i).prodMk (hX_meas j)).aemeasurable
      aemeasurable_snd := ((hX_meas 0).prodMk (hX_meas 1)).aemeasurable
      map_eq := h_map }
  -- Apply IdentDistrib.comp with g(x,y) = (x - m)(y - m)
  have h_comp : ProbabilityTheory.IdentDistrib
      (fun ω => (X i ω - m) * (X j ω - m))
      (fun ω => (X 0 ω - m) * (X 1 ω - m)) μ μ :=
    h_id.comp (by measurability : Measurable fun p : ℝ × ℝ => (p.1 - m) * (p.2 - m))
  -- Use IdentDistrib.integral_eq
  exact h_comp.integral_eq

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
for ALL pairs (not just increasing ones).

**KEY INSIGHT:** This avoids circularity! We use:
1. Contractability (for i < j)
2. Symmetry of covariance (mathematical property, NOT requiring exchangeability)
3. Together these give uniform covariance for all i ≠ j, as needed by Kallenberg's Lemma 1.2

We do NOT need to assume exchangeability or prove that (X_i, X_j) ~ (X_j, X_i). -/
example (m : ℝ) (hm : ∀ i, ∫ ω, X i ω ∂μ = m) {i j : ℕ} (hij : i ≠ j) :
    ∫ ω, (X i ω - m) * (X j ω - m) ∂μ = ∫ ω, (X 0 ω - m) * (X 1 ω - m) ∂μ := by
  by_cases h_lt : i < j
  · -- Case i < j: use contractability directly (Example 4)
    have h_map := L2Helpers.contractable_map_pair (X := X) hX_contract hX_meas h_lt
    have h_id : ProbabilityTheory.IdentDistrib (fun ω => (X i ω, X j ω)) (fun ω => (X 0 ω, X 1 ω)) μ μ :=
      { aemeasurable_fst := ((hX_meas i).prodMk (hX_meas j)).aemeasurable
        aemeasurable_snd := ((hX_meas 0).prodMk (hX_meas 1)).aemeasurable
        map_eq := h_map }
    have h_comp : ProbabilityTheory.IdentDistrib
        (fun ω => (X i ω - m) * (X j ω - m))
        (fun ω => (X 0 ω - m) * (X 1 ω - m)) μ μ :=
      h_id.comp (by measurability : Measurable fun p : ℝ × ℝ => (p.1 - m) * (p.2 - m))
    exact h_comp.integral_eq
  · -- Case i > j: use contractability with j < i, then symmetry of multiplication
    have hji : j < i := Nat.lt_of_le_of_ne (Nat.le_of_not_lt h_lt) (hij.symm)
    -- By contractability: (X_j, X_i) ~ (X_0, X_1)
    have h_map := L2Helpers.contractable_map_pair (X := X) hX_contract hX_meas hji
    have h_id : ProbabilityTheory.IdentDistrib (fun ω => (X j ω, X i ω)) (fun ω => (X 0 ω, X 1 ω)) μ μ :=
      { aemeasurable_fst := ((hX_meas j).prodMk (hX_meas i)).aemeasurable
        aemeasurable_snd := ((hX_meas 0).prodMk (hX_meas 1)).aemeasurable
        map_eq := h_map }
    -- Apply IdentDistrib.comp with g(x,y) = (y - m)(x - m) [note the swap!]
    have h_comp : ProbabilityTheory.IdentDistrib
        (fun ω => (X j ω - m) * (X i ω - m))
        (fun ω => (X 0 ω - m) * (X 1 ω - m)) μ μ :=
      h_id.comp (by measurability : Measurable fun p : ℝ × ℝ => (p.1 - m) * (p.2 - m))
    -- Use commutativity to swap: (X_i - m)(X_j - m) = (X_j - m)(X_i - m)
    calc ∫ ω, (X i ω - m) * (X j ω - m) ∂μ
        = ∫ ω, (X j ω - m) * (X i ω - m) ∂μ := by simp only [mul_comm]
      _ = ∫ ω, (X 0 ω - m) * (X 1 ω - m) ∂μ := h_comp.integral_eq

/-! ## Understanding the Circularity Issue

### What Would Be Circular

If we tried to prove uniform covariance by showing (X_i, X_j) ~ (X_j, X_i), that WOULD be circular:

```lean
-- ❌ CIRCULAR: We can't prove this from contractability alone!
have h_swap : Measure.map (fun ω => (X i ω, X j ω)) μ =
              Measure.map (fun ω => (X j ω, X i ω)) μ := sorry
```

This would require exchangeability, which is what we're trying to prove!

### What Is NOT Circular

But we don't need (X_i, X_j) ~ (X_j, X_i). We only need:

```lean
-- ✓ NOT CIRCULAR: This follows from contractability + symmetry of *
∫ ω, (X i ω - m) * (X j ω - m) ∂μ = ∫ ω, (X 0 ω - m) * (X 1 ω - m) ∂μ
```

For i > j, we use:
1. j < i, so by contractability: ∫ (X_j - m)(X_i - m) = ∫ (X_0 - m)(X_1 - m)
2. By commutativity of multiplication: (X_i - m)(X_j - m) = (X_j - m)(X_i - m)
3. Therefore: ∫ (X_i - m)(X_j - m) = ∫ (X_0 - m)(X_1 - m)

The key: **Symmetry of the covariance functional** (not symmetry of the joint distribution!)

### Why This Matters for Kallenberg's Lemma 1.2

Kallenberg's Lemma 1.2 requires: cov(ξᵢ, ξⱼ) = σ²ρ for ALL i ≠ j

- We get this for i < j from contractability (Example 4)
- We get this for i > j from contractability + symmetry (Example 5)
- We do NOT need exchangeability!

This is the subtlety that makes the L² proof work without circularity.
-/

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
