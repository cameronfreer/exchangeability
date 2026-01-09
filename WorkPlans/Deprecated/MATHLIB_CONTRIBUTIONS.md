# Mathlib Contribution Opportunities from CondExpDeprecated.lean

This document outlines opportunities to contribute to mathlib based on the sorries in
CondExpDeprecated.lean. Each represents a genuine gap in mathlib's conditional expectation API.

## 1. Generalized Set Integral Property for Conditional Expectation

**Location:** [CondExpDeprecated.lean:103](Exchangeability/Probability/CondExpDeprecated.lean#L103)
**Difficulty:** Medium
**Estimated effort:** 1-2 weeks

### The Gap

Currently, `setIntegral_condExp` requires the integration set S to be measurable in the
conditioning σ-algebra m. However, the property holds for ANY measurable set S in the
ambient σ-algebra m₀.

**Current mathlib:**
```lean
lemma setIntegral_condExp {m m₀ : MeasurableSpace Ω} (hm : m ≤ m₀)
    {f : Ω → ℝ} (hf : Integrable f μ)
    {S : Set Ω} (hS : MeasurableSet[m] S) :  -- Requires S ∈ m
    ∫ ω in S, μ[f|m] ω ∂μ = ∫ ω in S, f ω ∂μ
```

**Proposed addition:**
```lean
lemma setIntegral_condExp_of_measurableSet {m m₀ : MeasurableSpace Ω} (hm : m ≤ m₀)
    {f : Ω → ℝ} (hf : Integrable f μ)
    {S : Set Ω} (hS : MeasurableSet[m₀] S) :  -- Only requires S ∈ m₀
    ∫ ω in S, μ[f|m] ω ∂μ = ∫ ω in S, f ω ∂μ
```

### Why It's Needed

This generalization is required for Dynkin system arguments where we need to integrate
over sets that are measurable in a larger σ-algebra but not in the conditioning σ-algebra.

**Use case:** In the proof of `condIndep_iff_condexp_eq`, we have:
- S measurable in mF ⊔ mG (the joint σ-algebra)
- Want to integrate μ[f|mG] over S
- But S is not necessarily measurable in mG

### Proof Strategy

Three possible approaches:

**Approach 1: Indicator functions**
- Convert ∫ in S, g to ∫ S.indicator * g
- Show μ[(S.indicator * f)|m] = S.indicator * μ[f|m]
- Requires generalizing `condExp_indicator` to work when S ∉ m

**Approach 2: Approximation**
- Approximate S by simple functions measurable in m
- Use dominated convergence to pass to the limit
- Requires careful construction of approximating sequence

**Approach 3: Direct from characterization**
- μ[f|m] is characterized by ∫ in T, μ[f|m] = ∫ in T, f for all T ∈ m
- Use measure-theoretic arguments (Fubini, product measures)
- Show this extends to all T ∈ m₀

**Recommended:** Approach 3, using the uniqueness characterization of conditional expectation

### Dependencies

- Good understanding of conditional expectation API in mathlib
- Familiarity with `ae_eq_condExp_of_forall_setIntegral_eq`
- Knowledge of measure theory (dominated convergence, Fubini)

### Value to Mathlib

- Makes conditional expectation more flexible for Dynkin/π-system arguments
- Enables more natural proofs in probability theory
- Removes artificial restrictions on integration domains

---

## 2. Conditional Variance Decomposition Formula

**Location:** [CondExpDeprecated.lean:805](Exchangeability/Probability/CondExpDeprecated.lean#L805)
**Difficulty:** Medium
**Estimated effort:** 1-2 weeks

### The Gap

Mathlib lacks the standard variance decomposition formula for conditional expectation:
```
E[(X - E[X|m])²] = E[X²] - E[(E[X|m])²]
```

Or in conditional form:
```
E[(X - E[X|m])² | m] = E[X² | m] - (E[X | m])²
```

### Why It's Needed

This is a fundamental formula in probability theory, used for:
- L² martingale theory
- Variance calculations
- Proving orthogonality properties
- Bounding moments

**Use case:** In `bounded_martingale_l2_eq`, we want to show that if X₁ =ᵐ E[X₂|m₁]
and ∫ X₁² = ∫ X₂², then X₁ =ᵐ X₂. The variance decomposition gives:
```
∫ (X₂ - X₁)² = ∫ X₂² - ∫ X₁² = 0
```

### Proof Strategy

The variance decomposition follows from:
1. Expand (X - E[X|m])² = X² - 2X·E[X|m] + (E[X|m])²
2. Apply conditional expectation: E[· | m]
3. Use tower property: E[E[X|m]|m] = E[X|m]
4. Use pull-out property: E[E[X|m]·g|m] = E[X|m]·g for m-measurable g

**Key steps:**
```lean
E[(X - E[X|m])² | m]
  = E[X² - 2X·E[X|m] + (E[X|m])² | m]
  = E[X²|m] - 2E[X·E[X|m]|m] + E[(E[X|m])²|m]
  = E[X²|m] - 2E[X|m]·E[X|m] + (E[X|m])²     (by pull-out)
  = E[X²|m] - (E[X|m])²
```

### Dependencies

- `condExp_sub`, `condExp_add` (linearity)
- `condExp_stronglyMeasurable_mul` (pull-out property)
- `condExp_condExp_of_le` (tower property)
- Good understanding of Lp spaces

### Value to Mathlib

- Standard probability theory result
- Enables clean martingale proofs
- Useful for many probability applications
- Natural companion to existing conditional expectation API

---

## 3. Lévy's Downward Theorem (Reverse Martingale Convergence)

**Location:** [CondExpDeprecated.lean:817](Exchangeability/Probability/CondExpDeprecated.lean#L817)
**Difficulty:** Hard
**Estimated effort:** 4-8 weeks

### The Gap

Mathlib has Lévy's upward theorem (convergence for increasing σ-algebras) but lacks
the downward version for decreasing σ-algebras.

**Theorem:** For a decreasing sequence 𝒢ₙ ↓ 𝒢∞ := ⨅ n, 𝒢ₙ and integrable X:
```
μ[X | 𝒢ₙ] → μ[X | 𝒢∞]  almost everywhere
```

### Why It's Needed

Reverse martingales appear in:
- Exchangeable sequences (de Finetti's theorem)
- Bayesian statistics (posterior convergence)
- Ergodic theory
- Stationary processes

### Proof Strategy

Standard approach via martingale theory:

**Step 1: A.e. convergence**
1. Show (μ[X|𝒢ₙ])ₙ is a reverse martingale
2. Use L² projection properties and Doob's reverse martingale theorem
3. Apply Borel-Cantelli to control fluctuations
4. Show limit equals μ[X|𝒢∞] by uniqueness

**Step 2: L¹ convergence**
1. Use a.e. convergence from Step 1
2. Apply dominated convergence (μ[X|𝒢ₙ] dominated by integrable function)
3. Or use L¹ contraction property of conditional expectation

### Dependencies

**Major infrastructure needed:**
- Truncation operators and stopping times
- Doob's maximal inequalities
- Upcrossing inequalities
- Borel-Cantelli lemmas
- Reverse martingale convergence theory

**Existing mathlib to build on:**
- `MeasureTheory.condexp_*` (conditional expectation basics)
- `MeasureTheory.Martingale.*` (forward martingale theory)
- Convergence theorems (dominated, monotone)

### Value to Mathlib

- Completes the martingale convergence picture
- Essential for de Finetti's theorem
- Widely used in probability theory
- Natural counterpart to existing Lévy upward theorem

### Subtasks

If attempting this contribution, break it down:
1. ✅ Basic reverse martingale definition (may already exist)
2. ⬜ Doob's reverse martingale convergence theorem
3. ⬜ Infimum σ-algebra properties
4. ⬜ L² approximation lemmas
5. ⬜ A.e. convergence (main theorem)
6. ⬜ L¹ convergence (corollary)

---

## General Recommendations

### For Contributors

1. **Start small**: Begin with #1 (generalized setIntegral) before tackling #2 or #3
2. **Check existing mathlib**: APIs change frequently - verify gaps still exist
3. **Coordinate**: Check Zulip/GitHub for ongoing work
4. **Follow conventions**: Match mathlib naming and proof style
5. **Add tests**: Include examples showing the value of the new API

### For Maintainers

These contributions would significantly strengthen mathlib's probability theory library:
- #1 and #2 are natural extensions of existing API
- #3 is a substantial addition but highly valuable
- All have clear use cases in downstream applications

### Testing Ground

The file `CondExpDeprecated.lean` serves as a testing ground:
- Contains concrete use cases for each contribution
- Shows how the API would be used
- Provides motivation and context
- Can be used to validate proposed lemmas

---

## Current Status Summary

| Contribution | Difficulty | Effort | Dependencies | Impact |
|--------------|------------|--------|--------------|--------|
| Generalized setIntegral (#1) | Medium | 1-2 weeks | Basic measure theory | High |
| Variance decomposition (#2) | Medium | 1-2 weeks | Lp spaces | High |
| Lévy's downward theorem (#3) | Hard | 4-8 weeks | Martingale theory | Very High |

**Total estimated effort for all three:** 6-12 weeks for experienced contributor

**Priority:** #1 > #2 > #3 (based on difficulty and dependencies)

---

*Document created: 2025-10-12*
*Based on: CondExpDeprecated.lean (commit 0731b75)*
*Maintained by: Exchangeability project*
