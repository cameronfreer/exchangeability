# ViaKoopman.lean - Comprehensive Status

**Updated: 2025-12-04**

---

## Current State Summary

| File | Axioms | Sorries | Status |
|------|--------|---------|--------|
| ViaKoopman.lean | 7 | 5 | Main proof file |
| ViaKoopman/Infrastructure.lean | 8 | 2 | Dependencies |
| TheoremViaKoopman.lean | 1 | 0 | Final theorem wrapper |
| **Total** | **16** | **7** | |

---

## ViaKoopman.lean - 7 Axioms

| Line | Name | Difficulty | Notes |
|------|------|------------|-------|
| 296 | `Kernel.IndepFun.ae_measure_indepFun` | Medium | Conditional independence via kernels |
| 557 | `condindep_pair_given_tail` | Easy? | **Placeholder returning True** - needs investigation |
| 577 | `kernel_integral_product_factorization` | Medium | Kernel integral factorization |
| 1355 | `optionB_L1_convergence_bounded_fwd` | Hard | L¹ Cesàro convergence for bounded functions |
| 2442 | `condexp_product_factorization_ax` | Medium | CE product factorization |
| 2483 | `condexp_product_factorization_general` | Medium | General CE product |
| 2821 | `exchangeable_implies_ciid_modulo_bridge_ax` | Hard | **Main bridge** to CIID |

## ViaKoopman.lean - 5 Sorries

| Line | Context | Issue |
|------|---------|-------|
| 1019 | `birkhoffAverage_tendsto_condexp_L2` | Type class synthesis issues |
| 2471 | inside `condexp_product_factorization_ax` | Part of axiom body |
| 2519 | inside `condexp_product_factorization_general` | Part of axiom body |
| 4184 | `extreme_condexp_self` | May not be necessary |
| 5589 | `condindep_components_given_invSubalgebra` | Kernel.IndepFun autoparam issues |

---

## ViaKoopman/Infrastructure.lean - 8 Axioms

| Line | Name | Notes |
|------|------|-------|
| 798 | `condexp_precomp_iterate_eq_of_invariant` | CE invariance under iteration |
| 882 | `exists_naturalExtension` | Natural extension existence |
| 894 | `naturalExtension_condexp_pullback` | CE pullback property |
| 909 | `naturalExtension_pullback_ae` | AE pullback property |
| 924 | `condexp_precomp_iterate_eq_twosided` | Two-sided iteration |
| 937 | `condexp_precomp_shiftℤInv_eq` | Shift invariance |
| 959 | `condexp_pair_lag_constant_twoSided` | Pair lag constant |
| 1020 | `condexp_pair_lag_constant_twoSided` | (duplicate at different line) |

## ViaKoopman/Infrastructure.lean - 2 Sorries

| Line | Context |
|------|---------|
| 484 | Unknown |
| 778 | Unknown |

---

## Recently Completed Conversions

### 2025-12-04
- **`condexpL2_koopman_comm`**: Converted from axiom to theorem
  - Used Koopman operator commutation with conditional expectation
  - Key insight: `condExp_comp_mfderiv` pattern

- **`condexp_mul_condexp`**: Converted from axiom to lemma
  - Proved: `μ[X * μ[Y | m] | m] =ᵐ[μ] μ[Y | m] * μ[X | m]`
  - Key techniques:
    - `StronglyMeasurable.mono hm` to handle two MeasurableSpace instances
    - `Integrable.mul_of_top_right` for bounded × integrable products
    - `condExp_mul_of_aestronglyMeasurable_right` for pull-out property

---

## Technical Notes

### Two MeasurableSpace Instance Pattern

When a lemma has signature:
```lean
{Ω : Type*} [mΩ : MeasurableSpace Ω] {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
```

Lean's instance resolution can pick `m` instead of `mΩ` for methods like `.stronglyMeasurable`.

**Solution**: Use `StronglyMeasurable.mono hm` to convert from inferred `StronglyMeasurable[m]` to desired `StronglyMeasurable[mΩ]`.

### Useful Mathlib Lemmas for CE Proofs

- `stronglyMeasurable_condExp`: CE is m-strongly measurable
- `condExp_mul_of_aestronglyMeasurable_right`: Pull-out property
- `integrable_condExp`: CE of integrable is integrable
- `memLp_top_of_bound`: Bounded function is in L∞
- `Integrable.mul_of_top_right`: L¹ × L∞ → L¹

---

## Recommended Next Steps

### High Value Targets
1. **`condindep_pair_given_tail`** (line 557) - Placeholder returning True, may be easy
2. **`condexp_product_factorization_ax`** (line 2442) - Has clear mathlib path
3. **`kernel_integral_product_factorization`** (line 577) - Kernel theory

### Lower Priority
- Infrastructure axioms (may need mathlib contributions)
- `optionB_L1_convergence_bounded_fwd` (complex convergence argument)
- `exchangeable_implies_ciid_modulo_bridge_ax` (main theorem bridge)

---

## Other Files (Not on Critical Path for Koopman)

- **Probability/Martingale.lean**: 5 sorries (reverse martingale convergence)
- **Probability/MartingaleUnused.lean**: 13 axioms, 8 sorries (marked "Unused")
- **Probability/CesaroHelpers.lean**: 1 sorry
- **Probability/CondExpUnneeded.lean**: 4 sorries (marked "Unneeded")

These are either unused or for alternative proof approaches.
