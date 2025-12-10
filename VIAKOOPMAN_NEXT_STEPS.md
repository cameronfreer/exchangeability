# ViaKoopman.lean - Comprehensive Status

**Updated: 2025-12-09 (Session 2)**

---

## Current State Summary

| File | Axioms | Sorries | Status |
|------|--------|---------|--------|
| ViaKoopman.lean | 0 | ~22 | Main proof file |
| ViaKoopman/Infrastructure.lean | 0 | 7 | Dependencies |
| TheoremViaKoopman.lean | 0 | 1 | Final theorem wrapper |
| **Total** | **0** | **~30** | All axioms converted to sorries |

**Major milestone**: All axioms in the ViaKoopman proof path have been converted to lemmas with sorry.
This makes the proof structure explicit and allows incremental progress on each component.

---

## ViaKoopman.lean - Sorries (formerly axioms)

| Line | Name | Difficulty | Notes |
|------|------|------------|-------|
| ~1477 | `condexp_product_factorization_ax` | Medium | CE product factorization (induction) |
| ~1520 | `condexp_product_factorization_general` | Medium | General CE product (reduce to above) |
| ~1856 | `exchangeable_implies_ciid_modulo_bridge_ax` | Hard | **Main bridge** to CIID |

## ViaKoopman/Infrastructure.lean - Sorries (formerly axioms)

| Line | Name | Notes |
|------|------|-------|
| ~903 | `exists_naturalExtension` | Natural extension existence (construction needed) |
| ~961 | `naturalExtension_condexp_pullback` | CE pullback property |
| ~997 | `condexp_precomp_iterate_eq_twosided` | Two-sided iteration |
| ~1011 | `condexp_precomp_shiftℤInv_eq` | Shift invariance |
| ~1106 | `condexp_pair_lag_constant_twoSided` | Pair lag constant |

**Note**: Several axioms remain commented out (lines 805, 1027) due to type class elaboration issues.

---

## Recently Completed Conversions

### 2025-12-09 (Session 2) - Axiom Elimination

**All axioms converted to lemmas with sorry**, making proof structure explicit:

- **ViaKoopman.lean axioms → sorries**:
  - `condexp_product_factorization_ax` - CE product factorization (induction needed)
  - `condexp_product_factorization_general` - reduces to above via shift invariance
  - `exchangeable_implies_ciid_modulo_bridge_ax` - main bridge theorem

- **Infrastructure.lean axioms → sorries**:
  - `exists_naturalExtension` - natural two-sided extension construction
  - `naturalExtension_condexp_pullback` - CE pullback property
  - `condexp_precomp_iterate_eq_twosided` - two-sided iteration
  - `condexp_precomp_shiftℤInv_eq` - inverse shift invariance
  - `condexp_pair_lag_constant_twoSided` - lag constancy

- **TheoremViaKoopman.lean**:
  - `deFinetti_RyllNardzewski_equivalence_viaKoopman` - final theorem wrapper

### 2025-12-09 (Session 1)

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

All axioms are now sorries. Next steps are to fill in the actual proofs.

### High Value Targets (filling sorries)
1. **`naturalExtension_condexp_pullback`** - Can potentially be derived from `condexp_pullback_factor` but requires proving `comap restrictNonneg shiftInvariantSigma = shiftInvariantSigmaℤ`. Helper `comap_restrictNonneg_shiftInvariantSigma_le` already proves the ≤ direction.
2. **`condexp_product_factorization_ax`** - Needs conditional independence machinery for inductive step. Base case (m=0) is already sketched in comments.
3. **`condexp_precomp_iterate_eq_twosided`** - Similar to `condexp_precomp_iterate_eq_of_invariant` but for ℤ indexing

### Lower Priority
- `exists_naturalExtension` - Requires construction of natural two-sided extension (Kolmogorov extension)
- `condexp_pair_lag_constant_twoSided` - Uses shift invariance + inverse shift argument
- `exchangeable_implies_ciid_modulo_bridge_ax` - Main theorem bridge (very hard, depends on all others)

---

## Other Files (Not on Critical Path for Koopman)

- **Probability/Martingale.lean**: 5 sorries (reverse martingale convergence)
- **Probability/MartingaleUnused.lean**: 13 axioms, 8 sorries (marked "Unused")
- **Probability/CesaroHelpers.lean**: 1 sorry
- **Probability/CondExpUnneeded.lean**: 4 sorries (marked "Unneeded")

These are either unused or for alternative proof approaches.
