# Sorry and Axiom Summary Report

## Overview

- **Total sorries**: 39
- **Total axioms**: 47

## Sorry Distribution by File

| File | Sorries | Status |
|------|---------|--------|
| ViaL2.lean | 19 | Type class and L¹ convergence infrastructure |
| ViaKoopman.lean | 16 | 6 type class sorries (compilation fixes), 10 strategic sorries |
| ViaMartingale.lean | 4 | Conditional independence and measure extension |

### ViaKoopman.lean Sorries (16 total)

#### Type Class Compilation Fixes (6 sorries - Stream 1b)
These were added to fix compilation errors. All have detailed OLD PROOF documentation.

1. **Line 481** - `condexp_pullback_factor` - Type class instance conflict
2. **Line 518** - `hm'` helper - MeasurableSpace.comap instance issue
3. **Line 522** - `hHg'` helper - integrable_map_measure instance issue
4. **Line 530** - `condexp_pullback_factor` conclusion - ae_eq_condExp application
5. **Line 553** - `condexp_precomp_iterate_eq_of_invariant` - Full proof with multiple instance errors
6. **Line 779** - `h_unshifted_eq` - funext and type mismatch issues

**Fix time estimate**: 3-6 hours (documented in VIAKOOPMAN_PARALLEL_WORK_PLAN.md)

#### Strategic Sorries (10 sorries - Streams 2-4)
These require substantive mathematical work.

7. **Line 1822** - Mean Ergodic Theorem application - depends on birkhoffAverage_tendsto_condexp_L2 (line 1188)
8. **Line 2120** - `condexp_tower_for_products` - Lag-constancy axiom dependency
9. **Line 2225** - `h_shift_inv` - Shift invariance of conditional expectation
10. **Line 2328** - Conditional independence chain (Stream 2)
11. **Line 2437** - Inductive step for conditional independence
12. **Line 2485** - Product factorization induction
13. **Line 3225** - `birkhoffCylinder_tendsto_condexp` - Main convergence theorem
14. **Line 3255** - `extremeMembers_agree` - Extreme point characterization
15. **Line 3334** - `ν_measurable_tail` - ν evaluation measurability
16. **Line 4716** - Kernel independence composition

**Fix time estimate**: 8-12 hours (documented in work plan)

### ViaL2.lean Sorries (19 total)

All relate to:
- L¹ convergence infrastructure (7 sorries)
- Measurability of conditional expectations (4 sorries)
- Directing measure construction (5 sorries)
- Monotone class theorem application (3 sorries)

**Key blockers**:
- Line 2424: `alpha_is_conditional_expectation` - Main theorem
- Lines 2718-2747: L¹ limit uniqueness chain (4 connected sorries)
- Lines 3839-3911: Directing measure measurability (3 connected sorries)
- Lines 4039-4098: Monotone class API application (2 connected sorries)

### ViaMartingale.lean Sorries (4 total)

1. **Line 87** - Main theorem placeholder
2. **Line 446** - `condexp_convergence_fwd` - Requires measure_ext_of_future_rectangles
3. **Line 1963** - Conditional independence from contractability (Kallenberg Lemma 1.3)
4. **Line 2206** - iSup/join commutation

## Axiom Distribution by File

| File | Axioms | Purpose |
|------|--------|---------|
| ViaL2/SorryFreeHelpers.lean | 17 | Interface stubs for L² approach |
| ViaKoopman.lean | 14 | Koopman/ergodic theory infrastructure |
| ViaL2.lean | 11 | Duplicate axioms from SorryFreeHelpers |
| Probability/Martingale.lean | 7 | Reverse martingale convergence |
| Axioms.lean | 5 | Shared axioms across proofs |
| TheoremViaKoopman.lean | 1 | Main theorem axiom |

### Critical Axioms (Need Elimination Plans)

#### Koopman/Ergodic Axioms (14 in ViaKoopman.lean)
1. `condexpL2_koopman_comm` - L² conditional expectation commutes with Koopman operator
2. `condindep_pair_given_tail` - Conditional independence given tail σ-algebra
3. `kernel_integral_product_factorization` - Kernel integral factorization
4. `Kernel.IndepFun.ae_measure_indepFun` - Kernel independence theorem
5. `quantize_tendsto` - Dyadic approximation convergence
6. `condexp_mul_condexp` - Conditional expectation product rule
7. `condexp_precomp_iterate_eq_twosided` - Two-sided shift conditional expectation
8. `condexp_precomp_shiftℤInv_eq` - ℤ-shift invariance
9. `condexp_product_factorization_ax` - Product factorization axiom
10. `condexp_product_factorization_general` - General product factorization
11. `exchangeable_implies_ciid_modulo_bridge_ax` - Main bridge to conditional i.i.d.
12. `exists_naturalExtension` - Natural extension existence
13. `naturalExtension_condexp_pullback` - Natural extension pullback property
14. `naturalExtension_pullback_ae` - Natural extension pullback a.e. equality

#### L² Axioms (11 in ViaL2.lean, 17 in SorryFreeHelpers.lean)
Core infrastructure:
- `alphaFrom` - Define alpha function from contractability
- `alphaIic` - Indicator-based alpha construction
- `cdf_from_alpha` - CDF from alpha function
- `directing_measure` - Directing measure construction
- `tailSigma` - Tail σ-algebra definition

Convergence and limits:
- `cesaro_to_condexp_L1` - Cesàro averages converge to conditional expectation
- `alphaIic_tendsto_one_at_top` - Alpha limits at +∞
- `alphaIic_tendsto_zero_at_bot` - Alpha limits at -∞
- `l1_convergence_under_clip01` - L¹ convergence preservation under clipping
- `subseq_ae_of_L1` - Subsequence a.e. convergence from L¹
- `tendsto_integral_indicator_Iic` - Integral convergence for indicators

#### Martingale Axioms (7 in Probability/Martingale.lean)
- `reverseMartingale_convergence_ae` - Reverse martingale a.e. convergence
- `reverseMartingaleLimit` - Reverse martingale limit definition
- `reverseMartingaleLimit_eq` - Limit equals conditional expectation
- `reverseMartingaleLimit_measurable` - Limit measurability
- `reverseMartingaleLimitNat` - Natural number version
- `reverseMartingaleLimitNat_eq` - Nat version equals conditional expectation
- `reverseMartingaleNat_convergence` - Nat version convergence

### Acceptable Axioms (Standard Mathlib)
When checking with `#print axioms`, these are expected:
- `propext` - Propositional extensionality
- `quot.sound` - Quotient soundness
- `Classical.choice` - Axiom of choice

## Work Plan Status

### Completed
✅ **Stream 1**: ViaKoopman.lean compiles (20 errors → 0 errors)
✅ **Milestone 1**: All three proof files build successfully
✅ **Milestone 2**: Documentation of all sorries and axioms

### In Progress
🚧 User is "still refactoring other parts"

### Pending (Do NOT start yet)
⏸️ **Stream 1b**: Fix 6 type class sorries (3-6 hours)
⏸️ **Stream 2**: Conditional independence theorem (3-4 hours)
⏸️ **Stream 3**: Mean Ergodic Theorem connection (2-3 hours)
⏸️ **Stream 4**: Natural extension lemmas (3-5 hours)

**Total estimated time for all pending work**: 11-18 hours

## Recommendations

1. **Immediate**: Continue refactoring work (per user's instruction)

2. **After refactoring complete**:
   - Start with Stream 1b (type class fixes) - highest impact, clearest fix path
   - Then Stream 2 (conditional independence) - unlocks multiple downstream sorries
   - Then Stream 3 (Mean Ergodic) - connects ergodic theory to convergence
   - Finally Stream 4 (natural extension) - most mathematically involved

3. **Axiom elimination**:
   - Many L² axioms have implementations in ViaL2.lean with sorries
   - Focus on converting axioms to theorems with complete proofs
   - Some axioms (reverse martingale) may need mathlib PRs

4. **Testing**:
   - Use `#print axioms theorem_name` to verify only standard axioms after fixes
   - Run `lake build` frequently during Stream 1b work
   - Use `sorry_analyzer.py` to track progress
