# Final Sorry at Line 1330: W-Side Equality Challenge

## Context

**File:** `Exchangeability/DeFinetti/ViaMartingale.lean`, line 1330
**Status:** 8/9 sorries filled (89% complete)
**Last updated:** 2025-11-02

## What's Needed

Prove for σ(W)-measurable set W⁻¹(B_set):
```lean
∫ x in W ⁻¹' B_set, φ x * ψ x ∂μ = ∫ x in W ⁻¹' B_set, φ x * V x ∂μ
```
where V = μ[ψ | σ(W)] and φ is NOT σ(W)-measurable.

## The Circularity Problem

This appears circular with the main goal:
- **Outer goal:** Prove `μ[φ*ψ|𝔾] = μ[φ*V|𝔾]` a.e. by showing `∫_s φ*ψ = ∫_s φ*V` for all 𝔾-measurable sets s
- **This sorry:** Prove `∫_{W⁻¹B} φ*ψ = ∫_{W⁻¹B} φ*V` for the specific 𝔾-measurable set W⁻¹(B_set)

Standard approaches that fail:
1. **setIntegral_condExp:** Only gives `∫_s ψ = ∫_s V`, missing the φ factor
2. **Defining property of V:** Only applies to 𝔾-measurable functions, but φ*1_s is not 𝔾-measurable
3. **Tower property for products:** Reduces to proving `μ[φ*ψ|𝔾] = μ[φ*V|𝔾]`, which is the main goal (circular!)

## Analysis

The fundamental issue:
- We're trying to prove "for all 𝔾-measurable sets s, ∫_s φ*ψ = ∫_s φ*V"
- But to prove it for one specific set W⁻¹(B_set), we seem to need the full statement

Possible resolutions:
1. **Proof reorganization:** Extract this as a separate top-level lemma proved using swap technique independently
2. **Different proof strategy:** Avoid this calc step entirely by restructuring the swap-condition-swap proof
3. **Weaker statement:** Maybe we only need this for indicator functions, not general φ?

## Current Documentation (line 1310-1330)

The sorry has extensive comments explaining:
- How it reduces to proving μ[φ*ψ|𝔾] = μ[φ*V|𝔾] a.e.
- Why this appears circular with the main goal
- That the swap-condition-swap technique should resolve it using distributional equalities
- That this is "one instance" of proving the set integral equality for ALL sets

## Attempted Approaches

### Approach 1: Direct use of setIntegral_condExp
```lean
have h_base : ∫ x in W ⁻¹' B_set, ψ x ∂μ = ∫ x in W ⁻¹' B_set, V x ∂μ
```
This works but only gives the base case without φ.

### Approach 2: Pointwise equality
Tried to prove `(W ⁻¹' B_set).indicator (φ * ψ) = (W ⁻¹' B_set).indicator (φ * V)` pointwise.
Failed: The equality is only a.e., not pointwise.

### Approach 3: Tower property decomposition
Tried to use `∫_s φ*ψ = ∫ 1_s * μ[φ*ψ|𝔾]` and similarly for φ*V.
Failed: Reduces to the circular μ[φ*ψ|𝔾] = μ[φ*V|𝔾] again.

## Compilation Status

- File compiles successfully with the sorry
- Only pre-existing type class warnings at lines 1171-1172
- No new errors introduced

## Files Modified

- Enhanced `common_version_condExp_with_props` (lines 817-853) ✅
- Filled measurability/boundedness sorries (lines 1298-1308) ✅
- Implemented 5-step swap-based proof (lines 1259-1348) ✅
- Remaining: Line 1330 sorry (this issue)

## Recommendation

**This requires user guidance.** Possible options:
1. Accept that this step uses the rectangle factorization being proved (document carefully why it's not circular)
2. Restructure the proof to avoid this step
3. Prove a separate helper lemma using the swap technique before the main calc chain

The mathematical content is sound (the swap-condition-swap technique is valid), but the Lean proof structure may need reorganization to avoid the appearance of circularity.
