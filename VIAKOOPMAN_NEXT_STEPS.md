# ViaKoopman.lean - Comprehensive Status

**Updated: 2025-12-09**

---

## Current State Summary

| File | Axioms | Sorries | Status |
|------|--------|---------|--------|
| ViaKoopman.lean | 3 | 5 | Main proof file |
| ViaKoopman/Infrastructure.lean | 5 | 1 | Dependencies |
| TheoremViaKoopman.lean | 1 | 0 | Final theorem wrapper |
| **Total** | **9** | **6** | |

---

## ViaKoopman.lean - 3 Axioms

| Line | Name | Difficulty | Notes |
|------|------|------------|-------|
| 1465 | `condexp_product_factorization_ax` | Medium | CE product factorization |
| 1506 | `condexp_product_factorization_general` | Medium | General CE product |
| 1844 | `exchangeable_implies_ciid_modulo_bridge_ax` | Hard | **Main bridge** to CIID |

## ViaKoopman/Infrastructure.lean - 5 Active Axioms

| Line | Name | Notes |
|------|------|-------|
| 889 | `exists_naturalExtension` | Natural extension existence (construction needed) |
| 901 | `naturalExtension_condexp_pullback` | CE pullback property |
| 934 | `condexp_precomp_iterate_eq_twosided` | Two-sided iteration |
| 947 | `condexp_precomp_shiftℤInv_eq` | Shift invariance |
| 1030 | `condexp_pair_lag_constant_twoSided` | Pair lag constant |

**Note**: Several axioms are commented out (lines 805, 969) due to type class elaboration issues.

---

## Recently Completed Conversions

### 2025-12-09

- **`Kernel.IndepFun.ae_measure_indepFun`**: Converted from axiom to lemma
  - Proved kernel independence implies integral factorization
  - Key techniques:
    - π-λ theorem via `IndepSets.indep'` to extend from generators
    - Rational intervals as generators for Borel σ-algebra
    - `ae_all_iff` for countable rational quantification
    - `IndepFun.integral_fun_mul_eq_mul_integral` for the final step
  - Added `Measurable X` and `Measurable Y` hypotheses for measurability requirements

- **`naturalExtension_pullback_ae`**: Converted from axiom to lemma
  - Proves AE-equalities transport through the natural extension
  - Key techniques:
    - Added `measurable_restrictNonneg` to show restriction map is measurable
    - Uses `ae_pullback_iff` (already proved in Infrastructure.lean)
    - Added `AEMeasurable` hypotheses (hF, hG) for the functions
    - Updated usage site with `stronglyMeasurable_condExp.mono` for CE measurability

### 2025-12-04

- **Removed dead axioms** (reduces axiom count from 7 to 5):
  - `condindep_pair_given_tail` - was a placeholder returning `True`, never used
  - `kernel_integral_product_factorization` - only used in dead code
  - Also removed dead lemma `condexp_pair_factorization`
  - All bypassed by `condexp_pair_factorization_MET` which uses Mean Ergodic Theorem

- **`condexpL2_koopman_comm`**: Converted from axiom to theorem
  - Used Koopman operator commutation with conditional expectation
  - Key insight: `condExp_comp_mfderiv` pattern

- **`condexp_mul_condexp`**: Converted from axiom to lemma
  - Proved: `μ[X * μ[Y | m] | m] =ᵐ[μ] μ[Y | m] * μ[X | m]`
  - Key techniques:
    - `StronglyMeasurable.mono hm` to handle two MeasurableSpace instances
    - `Integrable.mul_of_top_right` for bounded × integrable products
    - `condExp_mul_of_aestronglyMeasurable_right` for pull-out property

- **`optionB_L1_convergence_bounded_fwd`**: Eliminated via file reorganization (5 → 4 axioms)
  - Forward-declared axiom pattern: axiom at line 1293, proof at line 3809
  - Moved 1006 lines of code that used the axiom to after the proof
  - Changed call from axiom to real theorem
  - No mathematical proof needed - just code reorganization

---

## Technical Notes

### Two MeasurableSpace Instance Pattern

When a lemma has signature:
```lean
{Ω : Type*} [mΩ : MeasurableSpace Ω] {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
```

Lean's instance resolution can pick `m` instead of `mΩ` for methods like `.stronglyMeasurable`.

**Solution**: Use `StronglyMeasurable.mono hm` to convert from inferred `StronglyMeasurable[m]` to desired `StronglyMeasurable[mΩ]`.

### π-λ Theorem for Independence Proofs

For kernel independence results:
1. Define π-systems (e.g., preimages of `{Iic q | q : ℚ}`)
2. Prove `IndepSets` on the π-systems
3. Use `IndepSets.indep'` to extend to generated σ-algebras
4. Connect via `comap_generateFrom` and `borel_eq_generateFrom_Iic_rat`

### Useful Mathlib Lemmas for CE Proofs

- `stronglyMeasurable_condExp`: CE is m-strongly measurable
- `condExp_mul_of_aestronglyMeasurable_right`: Pull-out property
- `integrable_condExp`: CE of integrable is integrable
- `memLp_top_of_bound`: Bounded function is in L∞
- `Integrable.mul_of_top_right`: L¹ × L∞ → L¹
- `ae_all_iff`: `∀ᵐ x, ∀ i, P i x ↔ ∀ i, ∀ᵐ x, P i x` for countable i
- `IndepFun.integral_fun_mul_eq_mul_integral`: Independence implies integral factorization

---

## Recommended Next Steps

### High Value but Complex Targets
1. **`naturalExtension_condexp_pullback`** - Can potentially be derived from `condexp_pullback_factor` but requires proving `comap restrictNonneg shiftInvariantSigma = shiftInvariantSigmaℤ`
2. **`condexp_product_factorization_ax`** - Needs conditional independence machinery for inductive step

### Lower Priority
- `exists_naturalExtension` - Requires construction of natural two-sided extension
- `condexp_precomp_iterate_eq_twosided` - Depends on commented-out `condexp_precomp_iterate_eq_of_invariant`
- `exchangeable_implies_ciid_modulo_bridge_ax` - Main theorem bridge (very hard)

---

## Other Files (Not on Critical Path for Koopman)

- **Probability/Martingale.lean**: 5 sorries (reverse martingale convergence)
- **Probability/MartingaleUnused.lean**: 13 axioms, 8 sorries (marked "Unused")
- **Probability/CesaroHelpers.lean**: 1 sorry
- **Probability/CondExpUnneeded.lean**: 4 sorries (marked "Unneeded")

These are either unused or for alternative proof approaches.
