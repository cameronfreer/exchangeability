# Simplification Plan for `block_coord_condIndep`

## Current Status
The `block_coord_condIndep` proof (lines 1612-2735, ~1123 lines) contains a massive `finite_approx` section using Dynkin's π-λ theorem with cylinder sets. This is overly complex.

## Proposed Simplified Approach (10-20 lines)

Replace the `finite_approx` block starting at line 1651 with:

```lean
-- Simplified proof using contractability and bridge lemmas
-- For any measurable B ⊆ α, show:
-- E[1_{X_r∈B} | σ(Z_r, θ_{m+1}X)] = E[1_{X_r∈B} | σ(θ_{m+1}X)] a.e.

-- Step 1: From contractable_triple_pushforward (or contractable_dist_eq_on_rectangles_future),
-- we have: Law(Z_r, X_r, θ_{m+1}X) = Law(Z_r, X_r, θ_{r+1}X)

-- Step 2: Apply condexp_indicator_eq_of_pair_law_eq bridge to the pairs:
-- (Y, Z) := (X_r, (Z_r, θ_{m+1}X)) and (Y', Z) := (X_r, (Z_r, θ_{r+1}X))
-- This gives: E[1_{X_r∈B} | σ(Z_r, θ_{m+1}X)] = E[1_{X_r∈B} | σ(Z_r, θ_{r+1}X)] a.e.

-- Step 3: Note that σ(Z_r, θ_{r+1}X) = σ(Z_r) ⊔ σ(θ_{r+1}X)
-- and σ(θ_{m+1}X) ≤ σ(θ_{r+1}X) since r < m

-- Step 4: Use tower property to lower both sides to σ(θ_{m+1}X):
-- E[1_{X_r∈B} | σ(θ_{m+1}X)] = E[E[1_{X_r∈B} | σ(Z_r) ⊔ σ(θ_{r+1}X)] | σ(θ_{m+1}X)]
--                              = E[E[1_{X_r∈B} | σ(Z_r, θ_{m+1}X)] | σ(θ_{m+1}X)]  [by step 2]
--                              = E[1_{X_r∈B} | σ(Z_r, θ_{m+1}X)]  [tower property]

-- This establishes the projection property needed

-- Step 5: Apply condIndep_of_indicator_condexp_eq bridge to conclude
```

## Implementation Strategy

1. **Find contractability lemma** that gives the triple/pair distributional equality
2. **Import needed bridges**: `condexp_indicator_eq_of_pair_law_eq` and `condIndep_of_indicator_condexp_eq` 
3. **Replace lines 1651-2735** with the ~20 line proof above
4. **Verify it compiles** with the existing infrastructure

## Benefits

- **Reduces proof from 1123 lines to ~20 lines** (98% reduction)
- **Eliminates Dynkin π-λ machinery** (GoodSets, monotone class arguments)
- **Uses existing bridge lemmas** already imported from CondExp.lean
- **Clearer mathematical reasoning** - directly uses contractability distributional equality

## Files to Check

- `Exchangeability/Probability/CondExp.lean` - for bridge lemma signatures
- Current file has imports at top for these bridges
- Look for `contractable_triple_pushforward` or similar lemma
