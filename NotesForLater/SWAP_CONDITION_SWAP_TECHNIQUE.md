# Swap-Condition-Swap Back Technique for Non-Circular Conditional Independence Proofs

## Context

**File:** `Exchangeability/DeFinetti/ViaMartingale.lean`, line 1051
**Goal:** Prove `∫_s (φ * μ[ψ | 𝔾]) = ∫_s (φ * ψ)` for 𝔾-measurable sets s
**Challenge:** φ is NOT 𝔾-measurable, so standard pull-out properties don't apply
**Circularity Issue:** This equality is needed to PROVE the rectangle factorization `μ[φ*ψ|𝔾] = μ[φ|𝔾]*μ[ψ|𝔾]`, so we can't use the factorization in the proof

## The Technique

### High-Level Idea

Use the triple law (Y,Z,W) =^d (Y,Z,W') to "swap" between W and W', conditioning out dependencies along the way. The key insight: even though φ depends on Y (not W), we can still use the triple law to transfer properties between σ(W) and σ(W').

### Step-by-Step Strategy

For a 𝔾-measurable set s (where 𝔾 = σ(W)):

**Step 1: Express as preimage**
- s is 𝔾-measurable ⟹ s = W⁻¹(B) for some measurable B ⊆ γ
- Let h = indicator_B, so h∘W = indicator_s

**Step 2: Swap to W' using triple law**
```lean
∫ φ*ψ*(h∘W) = ∫ φ*ψ*(h∘W')
```
This follows from the triple law with test function F(y,z,w) = φ(y)*ψ(z)*h(w)

**Step 3: Condition ψ on σ(W')**
```lean
∫ φ*ψ*(h∘W') = ∫ φ*V'*(h∘W')  where V' := μ[ψ | σ(W')]
```
This is the standard tower property: ∫ f*ψ = ∫ f*μ[ψ|σ(W')] for σ(W')-measurable f

**Step 4: Common version**
From equality of pair laws (Z,W) and (Z,W') (which is a marginal of the triple law), there exists v : γ → ℝ such that:
- V = v∘W  where V = μ[ψ | σ(W)]
- V' = v∘W'  where V' = μ[ψ | σ(W')]

**Step 5: Swap back with function of W only**
```lean
∫ φ*(v*h)∘W' = ∫ φ*(v*h)∘W
```
Key: Now we apply the triple law to F(y,z,w) = φ(y)*(v*h)(w), which doesn't involve ψ!

**Step 6: Identify with goal**
```lean
∫ φ*(v*h)∘W = ∫ φ*V*(h∘W) = ∫_s φ*V
```
Using V = v∘W and h∘W = indicator_s

**Chaining:** Steps 2+3+5+6 give: `∫_s φ*ψ = ∫_s φ*V`

## Required Lemmas

### 1. Common Version Lemma ⭐
**Statement:** If Law(Z,W) = Law(Z,W') and V := μ[ψ(Z) | σ(W)], V' := μ[ψ(Z) | σ(W')], then ∃v : γ → ℝ with V = v∘W and V' = v∘W' a.e.

**Proof sketch:**
- By Doob-Dynkin, V = v₁∘W and V' = v₂∘W' for some v₁, v₂
- For any bounded Borel h:
  ```
  ∫ (v₁*h)∘W = ∫ ψ(Z)*(h∘W) = ∫ ψ(Z)*(h∘W') = ∫ (v₂*h)∘W'
  ```
  (using the defining property of conditional expectation)
- Since Law(W) = Law(W'), this implies ∫ v₁*h = ∫ v₂*h for all h
- Therefore v₁ = v₂ a.e. w.r.t. Law(W)

**Status:** Not in mathlib; requires proof from first principles using Doob-Dynkin + uniqueness of CE

### 2. Generalized Triple Law
**Current:** h_test_fn only handles F(y,z,w) = φ(y)*ψ(z)*h(w)
**Needed:** Version for F(y,z,w) = φ(y)*g(w) (no ψ factor)

**Derivation:** Pair laws (Y,W) and (Y,W') coincide (marginal of triple law)

### 3. Conditioning with σ(W')-Measurable Test Functions
**Statement:** ∫ f*ψ = ∫ f*μ[ψ|σ(W')] when f is σ(W')-measurable

**Status:** Standard tower property; should exist in mathlib conditional expectation API

### 4. σ(W)-Measurability Characterization
**Statement:** s is σ(W)-measurable ⟺ s = W⁻¹(B) for some measurable B

**Status:** Standard Doob-Dynkin; likely `measurableSet_comap` in mathlib

## Why This Avoids Circularity

The key is that we NEVER use the rectangle factorization μ[φ*ψ|𝔾] = μ[φ|𝔾]*μ[ψ|𝔾]:
- Step 2 uses only the triple law (given hypothesis)
- Step 3 uses only standard CE tower property
- Step 4 uses only equality of pair laws (marginal of triple law) + Doob-Dynkin
- Step 5 uses the triple law again, but with a function that doesn't involve ψ

The proof establishes the integral equality WITHOUT assuming the factorization, then the factorization follows by feeding this equality into `ae_eq_condExp_of_forall_setIntegral_eq`.

## Implementation Status

**Current blocker:** Lines 1029-1051 in ViaMartingale.lean

**Challenges:**
1. Nested proof structure makes it hard to access the generality needed
2. h_test_fn is too specialized (requires φ*ψ*h form)
3. Common version lemma not in mathlib

**Recommended next steps:**
1. Extract the integral equality as a separate top-level lemma
2. Prove the common version lemma separately
3. Generalize h_test_fn to handle functions of (Y,W) only
4. Assemble the full swap-condition-swap back proof

## Mathematical Significance

This technique shows how to use distributional equalities (triple laws) to establish conditional independence properties without circular reasoning. The key insight is:
- **Going around the circle:** W → W' → W transfers information even when variables (like φ) don't directly factor through the conditioning σ-algebra
- **Common version bridges the gap:** V and V' live in different probability spaces but represent the "same" regression function via the shared law

This pattern should generalize to other settings where:
- You have distributional equalities involving multiple random elements
- You need to prove conditional independence but can't use factorization properties (circularity)
- Standard pull-out lemmas don't apply (conditioning on "wrong" σ-algebra)

## References

- **Source:** User feedback in session (2025-11-02)
- **Mathematical background:** Kallenberg (2005), Theorem 1.1, proof via L² methods
- **Related:** `MATHLIB_PR_CANDIDATES.md` - common version lemma might be PR-worthy
