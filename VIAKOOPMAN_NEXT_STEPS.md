# ViaKoopman.lean - Comprehensive Status

**Updated: 2025-12-09 (Session 3)**

---

## Current State Summary

| File | Axioms | Sorries | Status |
|------|--------|---------|--------|
| ViaKoopman.lean | 0 | ~22 | Main proof file |
| ViaKoopman/Infrastructure.lean | 0 | 5 | Dependencies (2 sorries proven!) |
| TheoremViaKoopman.lean | 0 | 1 | Final theorem wrapper |
| **Total** | **0** | **~28** | Incremental progress |

**Major milestone**: All axioms converted to lemmas with sorry, and two key lemmas now proven.

---

## ViaKoopman.lean - Sorries (formerly axioms)

| Line | Name | Difficulty | Notes |
|------|------|------------|-------|
| ~1477 | `condexp_product_factorization_ax` | Medium | CE product factorization (induction) |
| ~1520 | `condexp_product_factorization_general` | Medium | General CE product (reduce to above) |
| ~1856 | `exchangeable_implies_ciid_modulo_bridge_ax` | Hard | **Main bridge** to CIID |

## ViaKoopman/Infrastructure.lean - Sorries (formerly axioms)

| Line | Name | Status | Notes |
|------|------|--------|-------|
| ~491 | (commented out helper) | N/A | Dead code in comment block |
| ~785 | `condexp_pullback_factor` | Sorry | AE strong measurability transfer |
| ~903 | `exists_naturalExtension` | Sorry | Natural extension existence (Kolmogorov construction) |
| ~961 | `naturalExtension_condexp_pullback` | Sorry | CE pullback property |
| ~997 | `condexp_precomp_iterate_eq_twosided` | **PROVEN** | Two-sided iteration via induction |
| ~1105 | `condexp_precomp_shiftℤInv_eq` | **PROVEN** | Inverse shift invariance |
| ~1289 | `condexp_pair_lag_constant_twoSided` | Sorry | Requires deeper ergodic theory (lag independence) |

**Note**: Several axioms remain commented out (lines 805, 1027) due to type class elaboration issues.

---

## Recently Completed Conversions

### 2025-12-09 (Session 3) - Proving Sorries

**Two Infrastructure.lean sorries proven:**

- **`condexp_precomp_iterate_eq_twosided`**: Proved!
  - E[f ∘ T^k | m] =ᵐ E[f | m] for measure-preserving T and T-invariant σ-algebra m
  - Proof by induction on k using `ae_eq_condExp_of_forall_setIntegral_eq`
  - Key insight: m-measurable sets satisfy T⁻¹' s = s by definition
  - Uses indicator function approach for set integral rewriting

- **`condexp_precomp_shiftℤInv_eq`**: Proved!
  - E[f ∘ T⁻¹ | m] =ᵐ E[f | m] for the inverse shift
  - Similar proof structure to iterate case
  - Key insight: T⁻¹' s = s implies (T⁻¹)⁻¹' s = s for bijective T

- **`condexp_pair_lag_constant_twoSided`**: Analyzed (still sorry)
  - This lemma requires deeper ergodic theory than just shift-invariance
  - The claim is that CE[f(ω₀)·g(ωₖ) | m] doesn't depend on k
  - Shift-invariance only shows CE[F ∘ T^k | m] =ᵐ CE[F | m]
  - But changing k changes the "lag" between coordinates, not just the starting point
  - Proof likely needs mixing/ergodicity properties or conditional independence

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

Two sorries have been proven; remaining sorries are harder.

### High Value Targets (filling sorries)
1. **`naturalExtension_condexp_pullback`** - Can potentially be derived from `condexp_pullback_factor` but requires proving `comap restrictNonneg shiftInvariantSigma = shiftInvariantSigmaℤ`. Helper `comap_restrictNonneg_shiftInvariantSigma_le` already proves the ≤ direction.
2. **`condexp_product_factorization_ax`** - Needs conditional independence machinery for inductive step. Base case (m=0) is already sketched in comments.
3. **`condexp_pullback_factor`** - AE strong measurability transfer; has a TODO note in comments about type class issues

### Lower Priority
- `exists_naturalExtension` - Requires construction of natural two-sided extension (Kolmogorov extension)
- `condexp_pair_lag_constant_twoSided` - Requires deeper ergodic theory; shift-invariance alone is insufficient (see analysis in code comments)
- `exchangeable_implies_ciid_modulo_bridge_ax` - Main theorem bridge (very hard, depends on all others)

---

## Other Files (Not on Critical Path for Koopman)

- **Probability/Martingale.lean**: 5 sorries (reverse martingale convergence)
- **Probability/MartingaleUnused.lean**: 13 axioms, 8 sorries (marked "Unused")
- **Probability/CesaroHelpers.lean**: 1 sorry
- **Probability/CondExpUnneeded.lean**: 4 sorries (marked "Unneeded")

These are either unused or for alternative proof approaches.
