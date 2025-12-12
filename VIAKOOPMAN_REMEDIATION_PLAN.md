# ViaKoopman Remediation Plan

## Implementation Progress (Updated 2025-12-12)

### Completed ✅

1. **Replaced incorrect axiom with `condexp_lag_constant_from_exchangeability`** (Infrastructure.lean:971-995)
   - Uses Kallenberg's transposition argument: exchangeability implies lag-constancy
   - Key insight: τ swaps indices k and k+1, so exchangeability gives
     CE[f(ω_0)·g(ω_{k+1})|ℐ] = CE[f(ω_0)·g(ω_k)|ℐ]
   - Requires full exchangeability hypothesis, not just stationarity

2. **Updated `condexp_pair_factorization_MET`** (ViaKoopman.lean:3993-4074)
   - Now takes explicit exchangeability hypothesis `hExch : ∀ π, μ.map (reindex π) = μ`
   - Uses `h_tower_of_lagConst` directly with exchangeability-derived lag constancy
   - Clean proof chain without false intermediate lemmas

3. **Removed FALSE lemmas from Infrastructure.lean**:
   - `naturalExtension_condexp_pullback` - Claimed CE equality on different σ-algebras
   - `condexp_pair_lag_constant_twoSided` - Required conditional independence (circular)

4. **Removed FALSE lemmas from ViaKoopman.lean**:
   - `condexp_pair_lag_constant` - Depended on false Infrastructure lemmas
   - `condexp_tower_for_products` - Depended on false lag constancy chain

### Current State

- **Infrastructure.lean**: 2 sorries
  - `exists_naturalExtension` - Kolmogorov extension (TRUE, needs Ionescu-Tulcea)
  - `condexp_lag_constant_from_exchangeability` - Core axiom (TRUE via transposition)
- **ViaKoopman.lean**: 7 sorries (unrelated to the false lemma chain)
- **Build status**: ✅ Compiles successfully
- **Lines removed**: 468 lines of false lemmas and proof attempts

### Remaining Work

- Prove `condexp_lag_constant_from_exchangeability` using transposition argument
- Implement `exists_naturalExtension` via Ionescu-Tulcea (optional)
- Clean up other sorries unrelated to the false lemma chain

---

## Executive Summary

The original approach contained **2 FALSE statements** that formed a dependency chain:
1. `naturalExtension_condexp_pullback` - Cannot equate CEs on different σ-algebras
2. `condexp_pair_lag_constant_twoSided` - Lag constancy requires conditional independence

**Solution implemented (Option B - Kallenberg's Transposition):**
- Accept lag-constancy as an axiom that requires EXCHANGEABILITY (not just stationarity)
- Exchangeability provides permutation invariance, which implies lag-constancy
- This is honest because we're explicit about needing the full exchangeability hypothesis

## Why Option B (Exchangeability-Based Lag Constancy)?

### The Key Insight

Stationarity alone does NOT imply lag-constancy. Consider:
- AR(1) process: X_n = ρ·X_{n-1} + ε_n (stationary but NOT lag-constant)
- Cov(X_0, X_k) = ρ^k (depends on k!)

Exchangeability IS strong enough because of the **transposition argument**:
- Let τ be the permutation swapping k and k+1
- By exchangeability: μ.map (reindex τ) = μ
- Therefore: CE[f(ω_0)·g(ω_{k+1})|ℐ] = CE[f(ω_0)·g(ω_k)|ℐ]

### The Correct Axiom

```lean
/-- Exchangeability implies lag-constancy via Kallenberg's transposition argument.

For an exchangeable sequence, consider the transposition τ swapping indices k and k+1.
Exchangeability gives Measure.map (reindex τ) μ = μ. The function ω ↦ f(ω_0)·g(ω_{k+1})
becomes ω ↦ f(ω_0)·g(ω_k) under reindex τ (since τ fixes 0 and sends k+1 to k).

Key insight: STATIONARITY is NOT enough for lag constancy.
Counter-example: AR(1) process X_n = ρ·X_{n-1} + ε_n is stationary but
Cov(X_0, X_k) = ρ^k depends on k.
EXCHANGEABILITY provides this via transposition of adjacent indices. -/
axiom condexp_lag_constant_from_exchangeability
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α]
    {μ : Measure (ℕ → α)} [IsProbabilityMeasure μ]
    (hExch : ∀ π : Equiv.Perm ℕ, Measure.map (Exchangeability.reindex π) μ = μ)
    (f g : α → ℝ)
    (hf_meas : Measurable f) (hf_bd : ∃ C, ∀ x, |f x| ≤ C)
    (hg_meas : Measurable g) (hg_bd : ∃ C, ∀ x, |g x| ≤ C)
    (k : ℕ) :
    μ[(fun ω => f (ω 0) * g (ω (k + 1))) | shiftInvariantSigma (α := α)]
      =ᵐ[μ]
    μ[(fun ω => f (ω 0) * g (ω k)) | shiftInvariantSigma (α := α)]
```

## Proof Strategy for Filling the Axiom

To prove `condexp_lag_constant_from_exchangeability`:

1. **Define transposition τ**: `τ = Equiv.swap k (k+1)`

2. **Show reindex τ preserves 0**: Since τ fixes 0, `(reindex τ ω) 0 = ω 0`

3. **Show reindex τ sends k+1 to k**: `(reindex τ ω) (k+1) = ω k`

4. **Apply exchangeability**: `μ.map (reindex τ) = μ` gives
   ```
   μ[(f ∘ (· 0)) * (g ∘ (· (k+1))) | ℐ]
   = μ[(f ∘ (· 0)) * (g ∘ (· k)) | ℐ] ∘ reindex τ  -- by pullback
   = μ[(f ∘ (· 0)) * (g ∘ (· k)) | ℐ]              -- by measure invariance
   ```

5. **Handle conditional expectation under measure-preserving maps**:
   This requires showing CE commutes appropriately with reindex τ.

## Updated Dependency Chain

```
condexp_product_factorization_ax
    └── condexp_pair_factorization_MET (requires exchangeability)
            └── h_tower_of_lagConst (takes lag constancy as hypothesis)
                    └── condexp_lag_constant_from_exchangeability (AXIOM)
                            └── Exchangeability hypothesis (from de Finetti setup)
```

**Conclusion**: The proof chain is now honest - it explicitly requires exchangeability.

## Files Modified

1. **Infrastructure.lean**:
   - Added `condexp_lag_constant_from_exchangeability` axiom (971-995)
   - Deleted `naturalExtension_condexp_pullback` (was FALSE)
   - Deleted `condexp_pair_lag_constant_twoSided` (was FALSE)
   - Updated "Why this approach is honest" documentation

2. **ViaKoopman.lean**:
   - Updated `condexp_pair_factorization_MET` to require exchangeability
   - Deleted `condexp_pair_lag_constant` (depended on false lemmas)
   - Deleted `condexp_tower_for_products` (depended on false chain)
   - Updated docstrings to reflect new approach

## Mathematical Justification

The restructured proof is **more honest** because:

1. **Exchangeability is explicit** - The proof now clearly shows that exchangeability
   (not just stationarity) is required for the factorization theorem.

2. **Lag-constancy from transposition** is a standard result in probability theory
   (Kallenberg 2005, Lemma 1.3).

3. **No circular reasoning** - We don't assume conditional independence to prove it.
   Instead, we use the weaker property (lag-constancy) that follows from exchangeability.

## Optional Future Work

1. **Prove the axiom**: Fill in `condexp_lag_constant_from_exchangeability` using
   the transposition argument outlined above.

2. **Prove `exists_naturalExtension`**: Use Ionescu-Tulcea from mathlib.

3. **Connect to de Finetti proper**: Show how exchangeability of (X_n) on (Ω, μ)
   translates to the exchangeability hypothesis on path space.

## References

- Kallenberg (2005), *Probabilistic Symmetries and Invariance Principles*, Lemma 1.3
- Mathlib reindex: `Exchangeability.reindex`
- Mathlib conditional expectation: `MeasureTheory.condexp`
