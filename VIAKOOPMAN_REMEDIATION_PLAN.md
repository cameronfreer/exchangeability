# ViaKoopman Remediation Plan

## Critical Finding (2025-12-12 Session)

### Issue with k=0 Case of Lag Constancy Axiom

**Problem**: The axiom `condexp_lag_constant_from_exchangeability` claims:
```
CE[f(ω₀)·g(ω_{k+1}) | ℐ] = CE[f(ω₀)·g(ω_k) | ℐ]  for ALL k ≥ 0
```

**Analysis**:
- **k ≥ 1**: TRUE via transposition. τ = swap(k, k+1) fixes 0, so the argument works.
- **k = 0**: POTENTIALLY FALSE. τ = swap(0, 1) does NOT fix 0.

**Counterexample for k=0**: For i.i.d. Bernoulli(1/2) (which is exchangeable):
- CE[ω₀·ω₁ | ℐ] = E[ω₀]·E[ω₁] = 1/4 (by independence)
- CE[ω₀² | ℐ] = E[ω₀] = 1/2 (since ω₀² = ω₀ for Bernoulli)
- These are NOT equal!

### CRITICAL CORRECTION: Proof Restructuring to Avoid k=0

**The k=0 case is FALSE and cannot be proven.** The axiom's docstring incorrectly claims
τ = swap(k, k+1) fixes 0 for all k, but for k=0, τ = swap(0, 1) does NOT fix 0.

**Current proof flow** (BROKEN at step 1):
```
Step 1: CE[f·g₁] = CE[f·g₀]  ← Uses k=0 lag constancy (FALSE!)
Step 2: CE[f·g₀] = CE[f·CE[g₀|ℐ]]  (h_tower_of_lagConst)
Step 3: = CE[f|ℐ]·CE[g₀|ℐ]  (pullout)
```

**Restructured proof** (VALID, avoids k=0):
```
Step 1: Define A'_n = (1/n)·Σ_{j=1}^n g(ω_j)  ← Cesàro starting from j=1
Step 2: CE[f·A'_n] = CE[f·g₁] for all n  ← Uses only k≥1 lag constancy!
        (Because: CE[f·g_j] = CE[f·g_1] via induction using k=j-1 ≥ 1)
Step 3: A'_n → CE[g₀|ℐ] in L¹  ← MET + shift invariance
Step 4: L¹-Lipschitz: CE[f·A'_n] → CE[f·CE[g₀|ℐ]]
Step 5: ∴ CE[f·g₁] = CE[f·CE[g₀|ℐ]] (limit)
Step 6: = CE[f|ℐ]·CE[g₀|ℐ]  (pullout)
Step 7: = CE[f|ℐ]·CE[g₁|ℐ]  (shift invariance: CE[g₀|ℐ] = CE[g₁|ℐ])
```

**Why this works**:
- `product_ce_constant_of_lag_const` currently uses induction that terminates at g₀
- Modified to terminate at g₁ instead, avoiding the k=0 step
- The MET convergence A'_n → CE[g₀|ℐ] still holds by shift invariance

**Conclusion**: The final product factorization CE[f·g₁|ℐ] = CE[f|ℐ]·CE[g₁|ℐ] IS TRUE,
but the proof path must be restructured to avoid k=0. The axiom should be restricted
to k ≥ 1 (or renamed to make this explicit).

---

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

**HIGH PRIORITY (k=0 fix)**:
1. Modify axiom to require `k ≥ 1` (add `hk : 0 < k` hypothesis)
2. Restructure `condexp_pair_factorization_MET` to avoid k=0:
   - Modify `h_tower_of_lagConst` to use Cesàro from index 1
   - Update `product_ce_constant_of_lag_const` to terminate at g₁ not g₀
   - Remove direct usage of k=0 lag constancy
3. Prove the modified axiom (k≥1 only) using transposition argument

**MEDIUM PRIORITY**:
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

### The Corrected Axiom (k ≥ 1 only)

**NOTE**: The original axiom allowed k=0, which is FALSE. The corrected version requires k ≥ 1.

```lean
/-- Exchangeability implies lag-constancy via Kallenberg's transposition argument.

For an exchangeable sequence, consider the transposition τ swapping indices k and k+1.
Exchangeability gives Measure.map (reindex τ) μ = μ. The function ω ↦ f(ω_0)·g(ω_{k+1})
becomes ω ↦ f(ω_0)·g(ω_k) under reindex τ (since τ fixes 0 and sends k+1 to k).

**CRITICAL**: This only works for k ≥ 1. For k=0, τ = swap(0,1) does NOT fix 0.

Key insight: STATIONARITY is NOT enough for lag constancy.
Counter-example: AR(1) process X_n = ρ·X_{n-1} + ε_n is stationary but
Cov(X_0, X_k) = ρ^k depends on k.
EXCHANGEABILITY provides this via transposition of adjacent indices (for k≥1). -/
axiom condexp_lag_constant_from_exchangeability
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α]
    {μ : Measure (ℕ → α)} [IsProbabilityMeasure μ]
    (hExch : ∀ π : Equiv.Perm ℕ, Measure.map (Exchangeability.reindex π) μ = μ)
    (f g : α → ℝ)
    (hf_meas : Measurable f) (hf_bd : ∃ C, ∀ x, |f x| ≤ C)
    (hg_meas : Measurable g) (hg_bd : ∃ C, ∀ x, |g x| ≤ C)
    (k : ℕ) (hk : 0 < k) :  -- ← ADDED: k must be positive
    μ[(fun ω => f (ω 0) * g (ω (k + 1))) | shiftInvariantSigma (α := α)]
      =ᵐ[μ]
    μ[(fun ω => f (ω 0) * g (ω k)) | shiftInvariantSigma (α := α)]
```

## Proof Strategy for Filling the Axiom

**IMPORTANT**: This strategy only works for k ≥ 1. The k=0 case is FALSE (see Critical Finding above).

To prove `condexp_lag_constant_from_exchangeability` for **k ≥ 1**:

1. **Define transposition τ**: `τ = Equiv.swap k (k+1)`

2. **Show reindex τ preserves 0**: Since k ≥ 1, τ fixes 0:
   - `Equiv.swap_apply_of_ne_of_ne : k ≠ 0 → k+1 ≠ 0 → τ 0 = 0`
   - Therefore `(reindex τ ω) 0 = ω (τ 0) = ω 0` ✓

3. **Show reindex τ sends k+1 to k**: `(reindex τ ω) (k+1) = ω (τ (k+1)) = ω k`
   - `Equiv.swap_apply_right : τ (k+1) = k`

4. **Apply exchangeability**: `μ.map (reindex τ) = μ` gives
   ```
   μ[(f ∘ (· 0)) * (g ∘ (· (k+1))) | ℐ]
   = μ[(f ∘ (· 0)) * (g ∘ (· k)) | ℐ] ∘ reindex τ  -- by pullback
   = μ[(f ∘ (· 0)) * (g ∘ (· k)) | ℐ]              -- by measure invariance
   ```

5. **Handle conditional expectation under measure-preserving maps**:
   This requires showing CE commutes appropriately with reindex τ.

**Why k=0 fails**: When k=0, τ = swap(0, 1) does NOT fix 0 (τ 0 = 1), so step 2 fails.

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
