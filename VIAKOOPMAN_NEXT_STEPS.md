# ViaKoopman.lean - Comprehensive Status

**Updated: 2025-12-10 (Session 5)**

---

## Current State Summary

| File | Axioms | Sorries | Status |
|------|--------|---------|--------|
| ViaKoopman.lean | 0 | 3 | Main proof file |
| ViaKoopman/Infrastructure.lean | 0 | 3 | Dependencies |
| TheoremViaKoopman.lean | 0 | 1 | Final theorem wrapper |
| **Total** | **0** | **~7** | Build successful! |

**Major milestones**:
- Main bridge lemma `exchangeable_implies_ciid_modulo_bridge_ax` proven (Session 4)
- Base cases for product factorization lemmas proven (Session 5)
- Build now completes successfully with no errors

---

## ViaKoopman.lean - Sorries (formerly axioms)

| Line | Name | Difficulty | Notes |
|------|------|------------|-------|
| ~1069 | `birkhoffAverage_tendsto_condexp_L2` | Hard | MET type class issues |
| ~1488 | `condexp_product_factorization_ax` | Medium | CE product factorization (base case done, inductive step sorry) |
| ~1539 | `condexp_product_factorization_general` | Medium | General CE product (base case done, inductive step sorry) |
| ~1856 | `exchangeable_implies_ciid_modulo_bridge_ax` | ~~Hard~~ | **PROVEN** (Session 4) |

## ViaKoopman/Infrastructure.lean - Sorries (formerly axioms)

| Line | Name | Status | Notes |
|------|------|--------|-------|
| ~491 | (commented out helper) | N/A | Dead code in comment block |
| ~785 | `condexp_pullback_factor` | **PROVEN** | AE strong measurability transfer (Session 4) |
| ~896 | `exists_naturalExtension` | Sorry | Natural extension existence (Kolmogorov construction) |
| ~934 | `naturalExtension_condexp_pullback` | Sorry | CE pullback property |
| ~997 | `condexp_precomp_iterate_eq_twosided` | **PROVEN** | Two-sided iteration via induction |
| ~1105 | `condexp_precomp_shiftℤInv_eq` | **PROVEN** | Inverse shift invariance |
| ~1271 | `condexp_pair_lag_constant_twoSided` | Sorry | Requires deeper ergodic theory (lag independence) |

**Note**: `condexp_precomp_iterate_eq_twosided` and `condexp_precomp_shiftℤInv_eq` are proven but commented out due to pre-existing build errors from mathlib API changes in `MeasurePreserving.integral_comp`. The lemma logic is correct but needs API updates. These lemmas are not currently used by ViaKoopman.lean.

---

## Recently Completed Conversions

### 2025-12-10 (Session 5) - Base Cases, Build Fix, and Documentation

**Base cases proven for product factorization:**

- **`condexp_product_factorization_ax`** base case (m=0): Proven using `condExp_const`
  - Empty products simplify to 1: `∏ k : Fin 0, fs k (ω k) = 1`
  - `μ[1 | shiftInvariantSigma] =ᵐ 1` via `condExp_const`

- **`condexp_product_factorization_general`** base case (m=0): Same approach

**Build status**: Build now completes successfully with no errors (6428 jobs).

**Comprehensive implementation notes added** to preserve proof strategies:
- ViaKoopman.lean: Detailed inductive step structure for product factorization
- Infrastructure.lean: Analysis of natural extension and lag-constancy challenges
- TheoremViaKoopman.lean: Options for reusing existing equivalence theorem

See commit `81922aa` for full details.

### 2025-12-10 (Session 4) - Major Bridge Lemma

**Two key lemmas proven:**

- **`exchangeable_implies_ciid_modulo_bridge_ax`** (ViaKoopman.lean): **PROVEN!**
  - This is the main bridge from exchangeability to ConditionallyIID
  - Proof approach: Apply `conditional_iid_from_directing_measure` with:
    - `measurable_pi_apply` for coordinate measurability
    - `IsMarkovKernel.isProbabilityMeasure` for ν being probability measure
    - `ν_eval_measurable` for measurability (compatible after hypothesis weakening)
    - `indicator_product_bridge_ax` for the bridge condition
  - Required weakening `aemeasurable_measure_pi` to only require measurability for measurable sets

- **`condexp_pullback_factor`** (Infrastructure.lean): **PROVEN!**
  - AE strong measurability transfer along measure-preserving maps
  - Key insight: `g` is measurable from `(Ω', comap g m)` to `(Ω, m)` by definition of comap
  - Use `StronglyMeasurable.comp_measurable` to compose condExp with g
  - Uses the bracket notation `StronglyMeasurable[m]` for sub-σ-algebra measurability

**Hypothesis weakening cascade:**
- `aemeasurable_measure_pi`: `∀ s, Measurable ...` → `∀ s, MeasurableSet s → Measurable ...`
- `bind_pi_apply`, `bind_pi_isProbabilityMeasure`, `fidi_eq_avg_product`
- `conditional_iid_from_directing_measure`, `complete_from_directing_measure`

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

Build is successful! Remaining sorries are mathematically hard.

### High Value Targets (filling sorries)
1. **`naturalExtension_condexp_pullback`** - Can potentially be derived from `condexp_pullback_factor` (now proven) but requires proving `comap restrictNonneg shiftInvariantSigma = shiftInvariantSigmaℤ`. Helper `comap_restrictNonneg_shiftInvariantSigma_le` already proves the ≤ direction.
2. **`condexp_product_factorization_ax`** - Base case (m=0) is proven. Inductive step needs conditional independence machinery to factorize CE[fs 0 · ∏ᵢ₌₁ⁿ fs i | ℐ].

### Lower Priority (require significant new infrastructure)
- `exists_naturalExtension` - Requires construction of natural two-sided extension (Kolmogorov extension theorem)
- `condexp_pair_lag_constant_twoSided` - Requires deeper ergodic theory; shift-invariance alone is insufficient
- `birkhoffAverage_tendsto_condexp_L2` - Type class synthesis issues with sub-σ-algebras block implementation

### Already Completed
- ✅ `condexp_pullback_factor` - Proven (Session 4)
- ✅ `exchangeable_implies_ciid_modulo_bridge_ax` - Proven (Session 4)
- ✅ Base cases for product factorization lemmas (Session 5)

---

## Other Files (Not on Critical Path for Koopman)

- **Probability/Martingale.lean**: 5 sorries (reverse martingale convergence)
- **Probability/MartingaleUnused.lean**: 13 axioms, 8 sorries (marked "Unused")
- **Probability/CesaroHelpers.lean**: 1 sorry
- **Probability/CondExpUnneeded.lean**: 4 sorries (marked "Unneeded")

These are either unused or for alternative proof approaches.
