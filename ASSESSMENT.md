# Project Assessment - December 17, 2025

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

These 3 sorries block the main theorem completion:

### 1. ViaMartingale.lean:1723
- **Declaration:** `h_CI_UXrW` inside `condExp_Xr_indicator_eq_of_contractable`
- **Purpose:** Establishes conditional independence `CondIndep μ U (X r) W`
- **Depends on:** Items 2 and 3 below

### 2. TripleLawDropInfo.lean:122
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

### 3. CondIndep.lean:1637
- **Declaration:** `condIndep_indicator_of_dropInfoY`
- **Purpose:** Convert drop-info property to conditional independence

## Other Sorries (Not Blocking Main Theorem)

| File | Line | Declaration |
|------|------|-------------|
| CondIndep.lean | 581 | `tendsto_condexp_L1` |
| CondIndep.lean | 606 | `approx_bounded_measurable` |
| CondIndep.lean | 706 | `condIndep_simpleFunc_left` |
| CondIndep.lean | 760 | `condIndep_bddMeas_extend_left` |
| TimeReversalCrossing.lean | 79 | `timeReversal_crossing_bound` |
| KernelEvalEquality.lean | 80 | `kernel_eval_ae_eq_of_kernel_eq` |

## Custom Axioms (ViaKoopman Only)

| File | Line | Axiom |
|------|------|-------|
| ViaKoopman/Infrastructure.lean | 805 | `condexp_precomp_iterate_eq_of_invariant` |
| ViaKoopman/Infrastructure.lean | 920 | `naturalExtension_exists` |

## Admits in Code

| File | Lines |
|------|-------|
| CondExpExtras.lean | 1535, 1540, 1545 |
| ViaKoopman.lean | 1690 |

## Summary Statistics

| Category | Count |
|----------|-------|
| Total sorries in compiled code | 9 |
| Critical path sorries | 3 |
| Custom axioms | 2 (ViaKoopman only) |
| Admits | 4 |
| Files with build errors | 1 |

## Next Steps

To complete the ViaMartingale proof:

1. **Fill `condExp_indicator_eq_of_law_eq_of_comap_le`** (TripleLawDropInfo.lean:122)
   - Complete the L² argument using the existing helper lemmas
   - Key technical pieces: tower property, pull-out lemma, integral equality

2. **Fill `condIndep_indicator_of_dropInfoY`** (CondIndep.lean:1637)
   - Convert the drop-info result to CondIndep factorization

3. **Fill `h_CI_UXrW`** (ViaMartingale.lean:1723)
   - Should follow once items 1 and 2 are complete

## Recent Commits

```
eebeda6 refactor(TripleLawDropInfo): Fix helper lemmas and simplify main proof
ddb463a refactor: Remove 1538 lines of dead code from ViaMartingale.lean
```
