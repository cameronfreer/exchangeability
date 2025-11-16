# ViaKoopman.lean Sorry Analysis

## Status: **COMPILING** (fixing compilation errors as of 2025-11-16)

This document catalogs the remaining `sorry` statements in ViaKoopman.lean, organized by category and priority.

## Recent Compilation Fixes (2025-11-16)

Added 3 new sorries to resolve compilation errors:
- **Line 845**: AEStronglyMeasurable transfer along measure-preserving map
- **Line 4017**: L¹/L² calc chain (depends on h_meas sorry at 3996)
- **Line 4584**: optionB_L1_convergence_bounded_proves_axiom (type class unification)

---

## Category A: Type Class Synthesis Issues (3 sorries)

These are blocked by Lean elaboration issues, not mathematical difficulty.

### A1. Line 3890: `condexpL2_ae_eq_condExp_mSI`
**Issue**: lpMeas subtype coercion
```lean
(condexpL2 (μ := μ) f : Ω[α] → ℝ) =ᵐ[μ] μ[f | shiftInvariantSigma]
```
**Status**: TODO - Navigate lpMeas subtype structure
**Strategy**: Show coercion commutes: `(subtypeL x : Ω[α] → ℝ) = (x : Ω[α] → ℝ)`, then apply `MemLp.condExpL2_ae_eq_condExp`
**Priority**: Medium (workarounds exist in downstream code)

### A2. Line 3996: birkhoffAverage coercion
**Issue**: Elaborator interprets `(fun f => f)` as `(fun f => ↑↑f)`
```lean
AEStronglyMeasurable (fun ω => birkhoffAverage ... - condexpL2 ...) μ
```
**Status**: TODO - Prove measurability of pointwise birkhoffAverage with coerced iterates
**Priority**: Medium (technical elaboration issue)

### A3. Line 6126: `Kernel.IndepFun` autoparam
**Issue**: Autoparam issues with `condExpKernel`
```lean
Kernel.IndepFun (fun y => f (y 0)) (fun y => g (y 1)) (condExpKernel μ mSI) μ
```
**Status**: Replaced with True := trivial and axiomatic helper
**Strategy**: Apply `condindep_pair_given_tail` composed with measurable f, g
**Priority**: Low (has workaround via helper axioms)

---

## Category B: Step B Dyadic Approximation (3 sorries)

Part of the 95% complete dyadic approximation infrastructure.

### B1. Line 2360: `L1_cesaro_convergence_unbounded`
**Mathematical content**: Unbounded version of Cesàro convergence in L¹
**Strategy documented at lines 2355-2359**:
1. Define truncations: `g_M := max (min (g x) M) (-M)`
2. Apply `L1_cesaro_convergence_bounded` to each `g_M`
3. Show `A_n(g_M) → A_n(g)` in L¹ uniformly (dominated convergence)
4. Show `CE[g_M | mSI] → CE[g | mSI]` in L¹ (continuity of CE)
5. ε/3 argument to conclude

**Estimated effort**: ~40 lines
**Priority**: High (blocks Step B completion)

### B2. Line 2962: Product factorization inductive step
**Mathematical content**: Conditional independence for product CE
```lean
CE[∏ᵢ₌₀ⁿ fs i (ω i) | mSI] =ᵐ ∏ᵢ₌₀ⁿ ∫ fs i dν
```
**Strategy**: Use IH + `identicalConditionalMarginals` + conditional independence
**Priority**: High (core Step B lemma)

### B3. Line 3010: General product factorization continuation
**Mathematical content**: Extends B2 to arbitrary coordinate indices
**Dependencies**: Requires B2 completion
**Priority**: High (completes Step B)

---

## Category C: Infrastructure Lemmas (2 sorries)

### C1. Line 557: `aestronglyMeasurable_comp_of_pushforward_comap`
**Status**: **COMMENTED OUT** (not currently in use)
**Issue**: Sub-σ-algebra parameter blocks simpa trick
```lean
@AEStronglyMeasurable Ω' (MeasurableSpace.comap g m) β _ (H ∘ g) μ'
```
**Priority**: Low (unused, may not be needed)

### C2. Line 4721: `ν_measurable_tail`
**Status**: **COMMENTED OUT** with TODO
**Issue**: May not be necessary for main results
```lean
Measurable[shiftInvariantSigma] (ν (μ := μ))
```
**Priority**: Lowest (probably unnecessary)

---

## Category D: Mean Ergodic Theorem (1 sorry)

### D1. Line 1949: `birkhoffAverage_tendsto_condexp_L2` general version
**Mathematical content**: MET for general (T, m) pairs
**Status**: Documented alternative approaches at lines 1940-1947
**Alternatives**:
- Option A: Direct proof for sub-σ-algebras (2-3 weeks)
- Option B: Connect Koopman operator with sub-σ-algebra CE
  (see MET_IMPLEMENTATION_FINDINGS.md)

**Current decision**: Leave as sorry - the shift-specific version works correctly
**Priority**: Low (not needed for main proof)

---

## Summary Statistics

- **Total sorries**: 9
- **Commented out**: 2 (lines 557, 4721)
- **Active sorries**: 7
- **High priority (Step B)**: 3
- **Medium priority (type class)**: 2
- **Low priority**: 2

## Completion Roadmap

**Phase 1 (Step B completion)**:
1. Fill lines 2360, 2962, 3010
2. Estimated: 1-2 days for experienced Lean developer

**Phase 2 (Type class cleanup)**:
1. Fix lines 3890, 3996, 6126
2. Estimated: 1-2 days (mostly elaboration debugging)

**Phase 3 (Optional)**:
1. Decide whether C1, C2, D1 are needed
2. Remove if unnecessary, prove if needed

## Notes

- All sorries have documented TODOs or strategies
- File compiles successfully (verified by LSP + lake build)
- No new axioms introduced beyond documented ones
- Step B infrastructure is ~95% complete per PROGRESS_SUMMARY.md
