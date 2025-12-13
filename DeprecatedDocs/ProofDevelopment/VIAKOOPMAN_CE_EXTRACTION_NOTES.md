# ViaKoopman CE Extraction Attempt - 2025-10-19

## Summary

Attempted to extract conditional expectation utilities from ViaKoopman.lean to create a reusable `Probability/CondExpHelpers.lean` file. **Deferred** due to type class complexity.

## Identified CE Lemmas (General-Purpose)

1. **`condExp_abs_le_of_abs_le`** - Absolute value bound preservation (Jensen's inequality)
2. **`condExp_L1_lipschitz`** - L¹-Lipschitz continuity  
3. **`condExp_mul_pullout`** - Pull-out property for m-measurable functions
4. **`condExp_const_mul`** - Constant multiplication commutativity
5. **`condExp_sum_finset`** - Finite sum linearity
6. **`integrable_of_bounded_measurable`** - Bounded functions are integrable on finite measures
7. **`integrable_mul_of_ae_bdd_left`** - Product integrability from bounded factor

**Estimated impact**: ~120 lines reduction when completed.

## Technical Blockers

### 1. Measure Space Coercion Issues
The lemmas use anonymous measurable space binding `{_ : MeasurableSpace Ω}` combined with explicit sub-σ-algebra parameters `{m : MeasurableSpace Ω}`. This creates type class synthesis complexity when extracting to a generic file.

**Example error**:
```
invalid binder annotation, type is not a class instance
  ?m.5
```

### 2. AEStronglyMeasurable Topology Requirements
The `condExp_mul_pullout` lemma requires `TopologicalSpace` instances that are context-dependent:

```lean
@AEStronglyMeasurable _ _ m _ Z μ
```

This fails when `m` is a generic σ-algebra parameter without ambient context.

### 3. Tight Coupling with shiftInvariantSigma
Many lemmas are specialized to `shiftInvariantSigma` in ViaKoopman, making generic extraction non-trivial:

```lean
μ[Z | shiftInvariantSigma (α := α)]
```

Generic version requires additional type parameters and measurability assumptions.

## Recommendations

### Short-term (Current State)
**Action**: **DEFER extraction** until ViaKoopman proof is fully complete (all sorries resolved).

**Rationale**:
- ViaKoopman builds successfully with 3 remaining sorries  
- CE lemmas are `private` and not exported, so no namespace pollution
- Extraction complexity outweighs current benefits
- Better to stabilize proof first, then extract when requirements are clear

### Medium-term (After Proof Completion)
Once ViaKoopman has zero sorries:

1. **Identify actual reuse** - Check if ViaL2/ViaMartingale would benefit from these lemmas
2. **Generalize carefully** - Add necessary type class constraints incrementally
3. **Test in isolation** - Ensure extracted file builds independently
4. **Update imports** - Replace `private lemma` with imports from CondExpHelpers

**Estimated effort after completion**: Half day (as originally projected).

### Long-term (Mathlib Contribution)
Some lemmas (e.g., `condExp_L1_lipschitz`, `condExp_mul_pullout`) are mathematically general and could be contributed to mathlib's conditional expectation API after proper generalization and documentation.

## Lesson Learned

**Principle**: Extract utilities from **completed, stable** code, not from **in-progress** proofs.

**Why**:
- Proof development reveals actual usage patterns
- Type class requirements emerge naturally from use cases
- Premature extraction creates maintenance burden
- Completed proofs have clear, stable APIs

This aligns with the original refactoring notes that deferred ViaKoopman CE extraction.

## Current Status

- ✅ CE lemmas identified and documented
- ✅ Extraction attempted and technical blockers understood
- ✅ Decision to defer extraction documented with clear rationale
- ⏸️ Extraction deferred until ViaKoopman proof completion

**Next action**: Focus on completing ViaKoopman proof (resolve 3 remaining sorries), then revisit extraction.
