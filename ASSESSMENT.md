# Project Assessment - December 18, 2025

## Build Status

| Component | Status | Notes |
|-----------|--------|-------|
| Main project | ✅ BUILDS | 6434 jobs |
| ViaL2/CesaroConvergence.lean | ❌ ERRORS | Unknown identifiers, type mismatches |
| ViaKoopman approach | ⚠️ BUILDS | Has 2 custom axioms |

## Main Theorem Status

**Theorem:** `conditionallyIID_of_contractable` (ViaMartingale approach)

**Axioms:**
```
[propext, sorryAx, Classical.choice, Quot.sound]
```

**Status:** INCOMPLETE (depends on `sorryAx`)

## Critical Path Sorries

These 2 sorries block the main theorem completion:

### 1. TripleLawDropInfo.lean:197 (LINE UPDATED)
- **Declaration:** `condExp_indicator_eq_of_law_eq_of_comap_le`
- **Purpose:** Core Kallenberg 1.3 lemma (L² argument)
- **Proof outline:**
  1. Tower property: E[μ₂|mW] = μ₁
  2. Boundedness: 0 ≤ μ₁, μ₂ ≤ 1 a.e.
  3. Cross term: E[μ₂·μ₁] = E[μ₁²]
  4. Square equality: E[μ₁²] = E[μ₂²] (from pair law via RN derivative)
  5. L² computation: E[(μ₂-μ₁)²] = 0
  6. Conclusion: μ₂ = μ₁ a.e.
- **Helper lemmas COMPLETE:**
  - `marginal_law_eq_of_pair_law`
  - `joint_measure_eq_of_pair_law`
  - `pair_law_of_triple_law`
  - `condExp_eq_of_triple_law_direct`
- **Key missing piece:** Step 4 requires Doob-Dynkin factorization or RN derivative uniqueness

### 2. ViaMartingale.lean:1723
- **Declaration:** `h_CI_UXrW` inside `condExp_Xr_indicator_eq_of_contractable`
- **Purpose:** Establishes conditional independence `CondIndep μ U (X r) W`
- **Depends on:** Item 1 above

## Recently Completed

### ✅ CondIndep.lean:1637 (COMPLETED)
- **Declaration:** `condIndep_indicator_of_dropInfoY`
- **Purpose:** Convert drop-info property to conditional independence
- **Full 4-step proof implemented:**
  1. Pull-out for mZW (indB is mZW-measurable)
  2. Apply dropY hypothesis to substitute condExp
  3. Tower property application
  4. Pull-out for mW (condExp is mW-measurable)

## Other Sorries (Not Blocking Main Theorem)

| File | Line | Declaration |
|------|------|-------------|
| CondIndep.lean | 604 | `tendsto_condexp_L1` |
| CondIndep.lean | 677 | `approx_bounded_measurable` |
| CondIndep.lean | 757 | `condIndep_simpleFunc_left` |
| CondIndep.lean | 1084 | `condIndep_bddMeas_extend_left` |
| CondIndepHelpers.lean | 77, 106, 141, 175, 228 | Various helpers |
| TimeReversalCrossing.lean | 115 | `timeReversal_crossing_bound` |
| KernelEvalEquality.lean | 118 | `kernel_eval_ae_eq_of_kernel_eq` |
| ShiftInvariance.lean | 1327 | Blocked by circular import |

## Custom Axioms (ViaKoopman Only)

| File | Line | Axiom |
|------|------|-------|
| ViaKoopman/Infrastructure.lean | 805 | `condexp_precomp_iterate_eq_of_invariant` |
| ViaKoopman/Infrastructure.lean | 920 | `naturalExtension_exists` |

## Summary Statistics

| Category | Count |
|----------|-------|
| Critical path sorries | 2 |
| Custom axioms | 2 (ViaKoopman only) |
| Files with build errors | 1 |

## Next Steps

To complete the ViaMartingale proof:

1. **Fill `condExp_indicator_eq_of_law_eq_of_comap_le`** (TripleLawDropInfo.lean:197)
   - The key blocking step is proving E[μ₁²] = E[μ₂²] from pair law
   - Two approaches:
     a) Doob-Dynkin: Factor μ₁ = g ∘ W, μ₂ = g' ∘ W', show g = g' ρ-a.e.
     b) RN derivative: Use ∫_B g dρ = ν(B) characterization
   - Helper lemmas `hρ_eq` and `hν_eq` are proved

2. **Fill `h_CI_UXrW`** (ViaMartingale.lean:1723)
   - Should follow once item 1 is complete

## Technical Notes

The key mathematical insight for step 1 is:
- Let ρ = map W μ = map W' μ (proved in `hρ_eq`)
- Let ν = map W (μ.restrict (X⁻¹'A)) = map W' (μ.restrict (X⁻¹'A)) (proved in `hν_eq`)
- Conditional expectation E[1_{X∈A}|σ(W)] factors through W as g ∘ W
- The function g satisfies ∫_B g dρ = ν(B) for all measurable B
- By RN derivative uniqueness, g is unique ρ-a.e.
- Since both μ₁ and μ₂ are characterized by the same ν and ρ, they use the same g
- Therefore ∫ μ₁² dμ = ∫ g² dρ = ∫ μ₂² dμ

This argument requires Doob-Dynkin factorization for conditional expectation, which may need additional infrastructure in mathlib.
