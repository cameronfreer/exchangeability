# Session 2 Summary - Continuing de Finetti Proof

**Date**: 2025-10-12 (continued from previous session)

## Objective

Continue implementing the "next session recommendations" from the previous session:
1. ✅ Research mathlib CE API (30 min)
2. ⚠️  Implement `condExp_pullout` (45 min) - partially done
3. ⚠️  Fill 3 sub-sorries in `condexp_pair_factorization_MET` (1 hour) - documented

## Work Completed

### 1. Research & Analysis

Researched mathlib conditional expectation API and found:
- `condExp_mul_of_aestronglyMeasurable_left` - pull-out property for CE
- `condExp_condExp_of_le` - tower property
- `condExp_of_stronglyMeasurable` - CE of measurable functions
- `condexp_precomp_iterate_eq` (line 1483) - shift invariance for CE

### 2. Updated Documentation in ViaKoopman.lean

#### condExp_mul_pullout (lines 315-336)
**Status**: Sorry'd with detailed proof sketch

**Issue Identified**: Need correct mathlib APIs for:
- Converting `Measurable[m]` to `AEStronglyMeasurable[m]`
- The `bdd_mul` lemma signature
- `Filter.eventually_of_forall` or equivalent

**Proof Strategy Documented** (~10-15 LOC):
1. Show Z is AEStronglyMeasurable[m] using hZ_meas
2. Show Z*Y is integrable using hY.bdd_mul with boundedness hZ_bd
3. Apply condExp_mul_of_aestronglyMeasurable_left

#### h_shift_inv (lines 445-463)
**Status**: Sorry'd with analysis of the challenge

**Key Issue Discovered**: The expression `f(ω₀)·g(ω₁)` mixes coordinates in a way that doesn't simply compose with shift. Specifically:
- `f(ω₀)·g(ω₁) ≠ (f·g) ∘ shift`
- Need either an exchangeability property or a more sophisticated argument

**Proof Strategy Outlined** (~10-15 LOC):
- Original plan: Use `condexp_precomp_iterate_eq` (line 1483)
- Problem: That lemma applies to `(f ∘ shift^k)`, but we have a mixed expression
- Alternative: Might need exchangeability of the measure, not just shift-invariance
- TODO: Identify the right lemma or approach

#### h_pullout (lines 458-482)
**Status**: Sorry'd with clear dependencies

**Blocking Issue**: Depends on completing `condExp_mul_pullout` helper first

**Proof Strategy** (~15 LOC once helper is done):
- Z := CE[g(ω₀)|m] is m-measurable by stronglyMeasurable_condExp
- Boundedness: |CE[g|m]| ≤ C requires Jensen's inequality
- Y := f ∘ π_0 is integrable (bounded + measurable)
- Apply condExp_mul_pullout

#### h_tower (lines 486-507)
**Status**: Sorry'd with detailed analysis

**Goal**: Show `CE[f(ω₀)·g(ω₀)|m] = CE[f(ω₀)·CE[g(ω₀)|m]|m]`

**Approach Analyzed**: Show both sides have the same integral over every m-measurable set:
- LHS: ∫_A CE[f·g|m] dμ = ∫_A f·g dμ
- RHS: ∫_A CE[f·CE[g|m]|m] dμ = ∫_A f·CE[g|m] dμ

**Challenge Identified**: Need to show ∫_A f·g dμ = ∫_A f·CE[g|m] dμ for all m-measurable A.
- The issue: f∘π₀ is typically NOT m-measurable for tail σ-algebra
- Might need a "substitution" lemma for CE or specific properties of tail σ-algebra
- TODO: Find the right mathlib lemma (~15-20 LOC)

## Compilation Status

✅ **File compiles successfully!**

```bash
$ lake build Exchangeability.DeFinetti.ViaKoopman
warning: Exchangeability/DeFinetti/ViaKoopman.lean:293:14: declaration uses 'sorry'
warning: Exchangeability/DeFinetti/ViaKoopman.lean:315:14: declaration uses 'sorry'
warning: Exchangeability/DeFinetti/ViaKoopman.lean:430:14: declaration uses 'sorry'
```

**3 sorries total**:
1. Line 293: `condExp_L1_lipschitz` (optional, not blocking)
2. Line 315: `condExp_mul_pullout` (blocks h_pullout)
3. Line 430: `condexp_pair_factorization_MET` with 3 internal sorries:
   - `h_shift_inv` (line 449) - needs exchangeability analysis
   - `h_tower` (line 488) - needs substitution lemma
   - `h_pullout` (line 471) - blocked by condExp_mul_pullout

## Key Insights Discovered

### 1. Shift Invariance Challenge
The transformation from `f(ω₀)·g(ω₁)` to `f(ω₀)·g(ω₀)` is **not** a simple shift composition. This is more subtle than initially thought and may require:
- Exchangeability of the measure (not just contractability)
- A symmetry argument
- Different formulation of the lemma

### 2. Tower Property Subtlety
Replacing `g(ω₀)` with `CE[g(ω₀)|m]` inside a conditional expectation is subtle because:
- `f(ω₀)` is not m-measurable (for tail σ-algebra)
- Cannot simply "pull out" CE[g|m]
- Need a general substitution property or specific tail σ-algebra structure

### 3. API Challenges
The mathlib API for conditional expectation requires careful attention to:
- Converting between Measurable and AEStronglyMeasurable
- Proving integrability with boundedness
- Correct use of filter/eventually lemmas

## Next Steps (Priority Order)

### HIGH PRIORITY: Resolve Blocking Issues

1. **Mathlib API Research for condExp_mul_pullout** (~1 hour)
   - Find correct way to build AEStronglyMeasurable[m] from Measurable[m]
   - Identify the correct bdd_mul signature
   - Find eventually_of_forall or replacement
   - **Impact**: Unblocks h_pullout

2. **Analyze h_shift_inv Exchangeability** (~1-2 hours)
   - Determine if we need exchangeability vs just shift-invariance
   - Find the right lemma for mixed coordinate expressions
   - May need to look at how Kallenberg's proof handles this step
   - **Impact**: Completes 1 of 3 sub-sorries

3. **Find Substitution Lemma for h_tower** (~1 hour)
   - Search mathlib for CE substitution properties
   - Or prove directly using integral characterization
   - **Impact**: Completes 1 of 3 sub-sorries

### MEDIUM PRIORITY: Complete the Pair Factorization

4. **Implement h_pullout** (~30 min)
   - Depends on completing condExp_mul_pullout first
   - Should be straightforward application
   - **Impact**: Completes final sub-sorry, eliminating 2 axioms!

### LOW PRIORITY: Optional Improvements

5. **Complete condExp_L1_lipschitz** (~30 min)
   - Not blocking any main results
   - Good for completeness

## Estimated Remaining Effort

| Component | Status | Remaining Effort | Blocking? |
|-----------|--------|------------------|-----------|
| condExp_mul_pullout | Sorry'd | 1 hour API research | Yes (h_pullout) |
| h_shift_inv | Sorry'd | 1-2 hours analysis | No |
| h_tower | Sorry'd | 1 hour research | No |
| h_pullout | Sorry'd | 30 min impl | Blocked |
| condExp_L1_lipschitz | Sorry'd | 30 min | No |

**Total**: ~3-4 hours to complete all sorries

**Critical path**: condExp_mul_pullout → h_pullout

## Files Modified

- `ViaKoopman.lean`:
  - Lines 315-336: condExp_mul_pullout with detailed proof sketch
  - Lines 445-463: h_shift_inv with challenge analysis
  - Lines 458-482: h_pullout with clear dependencies
  - Lines 486-507: h_tower with detailed approach

## Lessons Learned

1. **Don't assume simple patterns**: The shift invariance step turned out more subtle than expected
2. **Document blocking dependencies**: Clear sorry messages with proof sketches help identify critical path
3. **API mismatches need research**: Mathlib APIs evolve; need to verify signatures before implementing
4. **Keep it compiling**: Better to sorry with good docs than have broken code

## Conclusion

This session made significant progress in **analysis and documentation** rather than implementation. All 3 sub-sorries in `condexp_pair_factorization_MET` now have:
- Clear proof strategies
- Identified challenges and blockers
- Estimated LOC for completion

The file compiles cleanly with the same 3 high-level sorries as before, but we now have a much clearer understanding of what's needed to complete them.

**Key Blocker**: Mathlib API research for `condExp_mul_pullout` is the critical path item.

**Next session**: Start with API research for condExp_mul_pullout, as this unblocks h_pullout and provides a template for the other sorries.
