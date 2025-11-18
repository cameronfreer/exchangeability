# ViaKoopman.lean Refactoring Analysis

## File Statistics
- **Total lines**: 6650
- **Declarations**: ~85 (theorems, lemmas, defs, axioms)
- **Active sorries**: ~8-10
- **Build status**: Compiles with pre-existing errors at lines 2362, 2376

## Current Structure

### Major Sections (identified by `/-! ###` markers)

1. **Lines 1-26**: Imports and opening statements
2. **Lines 27-33**: API compatibility aliases (EMPTY - removed alias)
3. **Lines 35-53**: Reusable micro-lemmas (private utility functions)
4. **Lines 54-77**: Lp coercion lemmas (private, measure theory)
5. **Lines 78-167**: **HUGE documentation block** (90 lines of module-level docs)
6. **Lines 168-170**: Namespace opening
7. **Lines 172-322**: Two-sided natural extension infrastructure
8. **Lines 323-372**: Helpers section (50 lines)
9. **Lines 560-701**: Instance-locking shims for conditional expectation (142 lines)
10. **Lines 1625-1728**: Lp norm helpers + conditional expectation linearity
11. **Lines 1729-1903**: Option A: Projected Mean Ergodic Theorem (COMMENTED OUT)
12. **Lines 1904-2275**: Mean Ergodic Theorem for General (T, m) (372 lines, has sorry)
13. **Lines 2276-3101**: Option B: Density + Uniform Integrability Approach (826 lines, has sorries)
14. **Lines 3102-3359**: Helper lemmas for indicator_product_bridge_ax
15. **Lines 3360-3439**: MeasureTheory namespace extension
16. **Lines 3441-3543**: CylinderFunctions section (103 lines)
17. **Lines 3545-3896**: MainConvergence section (352 lines, has sorries)
18. **Lines 3898-4637**: Option B: L¹ Convergence via Cylinder Functions (740 lines, has sorries)
19. **Lines 4639-6554**: **ExtremeMembers section** (1916 lines! 29% of file)
20. **Lines 6609-6628**: Bridge Lemma
21. **Lines 6629-6650**: Main theorem + namespace closing

## Refactoring Proposal

### Option 1: Split by Logical Proof Approach (RECOMMENDED)

**Goal**: Separate the two independent proof approaches (Option A vs Option B) and extract completed infrastructure.

#### New File Structure

```
DeFinetti/ViaKoopman/
├── Infrastructure.lean        (Lines 1-701: imports, utilities, helpers)
│   ├── Imports and API aliases
│   ├── Micro-lemmas
│   ├── Lp coercion lemmas
│   ├── Two-sided shift infrastructure
│   ├── Instance-locking shims
│   └── Status: ✅ COMPLETE (no sorries)
│
├── MeanErgodicTheorem.lean    (Lines 1904-2275: general MET)
│   ├── birkhoffAverage_tendsto_condexp for general (T, m)
│   ├── Status: ⚠️ Has 1 sorry (line 1952)
│   └── Depends: Infrastructure.lean
│
├── OptionB_DensityUI.lean     (Lines 2276-3101: density approach)
│   ├── L1_cesaro_convergence_bounded
│   ├── L1_cesaro_convergence (unbounded version)
│   ├── Status: ⚠️ Has 1 sorry (line 2403)
│   └── Depends: Infrastructure.lean, MeanErgodicTheorem.lean
│
├── CylinderFunctions.lean     (Lines 3102-3543: cylinder machinery)
│   ├── Helper lemmas for indicator_product_bridge_ax
│   ├── MeasureTheory namespace extensions
│   ├── CylinderFunctions section
│   ├── Status: ✅ COMPLETE (no sorries)
│   └── Depends: Infrastructure.lean
│
├── MainConvergence.lean       (Lines 3545-3896: convergence results)
│   ├── birkhoffAverage_tendsto_condexp (specialized for shift)
│   ├── Helper lemmas for condexpL2_koopman_comm
│   ├── Status: ⚠️ Has sorries (line 3934)
│   └── Depends: Infrastructure.lean, CylinderFunctions.lean
│
├── OptionB_L1Convergence.lean (Lines 3898-4637: L¹ convergence)
│   ├── Option B: L¹ Convergence via Cylinder Functions
│   ├── OptionB_L1Convergence section
│   ├── Status: ⚠️ Has sorries (lines 4065, 4081)
│   └── Depends: MainConvergence.lean, OptionB_DensityUI.lean
│
├── ExtremeMembers.lean        (Lines 4639-6554: conditional independence)
│   ├── **LARGEST SECTION** (1916 lines)
│   ├── Mathlib infrastructure for conditional independence
│   ├── Kernel independence and integral factorization
│   ├── OLD PROOF (kept for reference)
│   ├── Pair factorization for conditional expectation
│   ├── Use axiomatized product factorization
│   ├── Status: ⚠️ Has sorries (line 6165)
│   └── Depends: Infrastructure.lean, CylinderFunctions.lean
│
└── Theorem.lean               (Lines 6609-6650: main theorem)
    ├── Bridge Lemma
    ├── Main theorem: exchangeable_implies_conditionallyIID_viaKoopman
    ├── Status: ✅ COMPLETE (uses all above pieces)
    └── Depends: ALL above files
```

#### Benefits of Option 1
1. **Clear separation of concerns**: Infrastructure vs proof approaches vs main theorem
2. **Incremental work**: Can work on one proof approach at a time
3. **Independent compilation**: Infrastructure compiles clean, work on sorries in isolation
4. **Easier testing**: Each file can be built independently
5. **Better documentation**: Each file gets focused documentation
6. **Reusability**: Infrastructure can be reused for other proofs

#### Migration Strategy
1. **Phase 1** (1-2 hours): Create Infrastructure.lean, verify it compiles
2. **Phase 2** (1 hour each): Extract completed sections (CylinderFunctions, etc.)
3. **Phase 3** (2-3 hours): Extract sections with sorries, fix imports
4. **Phase 4** (1 hour): Create Theorem.lean, verify full build
5. **Phase 5** (30 min): Update imports in other files, deprecate ViaKoopman.lean

**Total estimated time**: 8-12 hours

### Option 2: Extract Only Completed Infrastructure (MINIMAL)

**Goal**: Quick win - extract only the parts with no sorries.

#### New Files
1. **ViaKoopman/Infrastructure.lean**: Lines 1-701 (utilities, helpers)
2. **ViaKoopman/CylinderFunctions.lean**: Lines 3102-3543 (completed cylinder machinery)

Keep everything else in ViaKoopman.lean for now.

**Benefits**: Immediate reduction from 6650 → ~5200 lines, no imports to fix.

**Estimated time**: 2-3 hours

### Option 3: No Refactoring (STATUS QUO)

**Keep current structure if**:
- File will be cleaned up/deleted soon after sorries are resolved
- Refactoring overhead > benefit
- Prefer monolithic files for proof navigation

## Recommendation: **Option 1 (Full Split)**

### Why Option 1?

1. **File is massive** (6650 lines) - difficult to navigate
2. **Clear logical boundaries** - sections are well-documented and independent
3. **Active development** - multiple sorries being worked on simultaneously
4. **Long-term value** - infrastructure will be reused
5. **ExtremeMembers section is huge** - 29% of file, deserves its own file
6. **Parallel work enabled** - different developers can work on different proof approaches

### Immediate Next Steps (if Option 1 chosen)

1. **Create directory**: `mkdir -p Exchangeability/DeFinetti/ViaKoopman`
2. **Extract Infrastructure.lean** (lines 1-701):
   - Includes all imports
   - All utility lemmas
   - Two-sided shift infrastructure
   - Instance-locking shims
   - **Verify**: Should compile with no errors
3. **Update ViaKoopman.lean** to import Infrastructure.lean
4. **Verify**: Full project still builds
5. **Iterate**: Extract next section (CylinderFunctions.lean)

## Sorries Summary by Section

| Section | Sorries | Lines | Status |
|---------|---------|-------|--------|
| Infrastructure | 0 | 701 | ✅ Complete |
| MeanErgodicTheorem | 1 | 372 | ⚠️ Active |
| OptionB_DensityUI | 1 | 826 | ⚠️ Active |
| CylinderFunctions | 0 | 441 | ✅ Complete |
| MainConvergence | 1 | 352 | ⚠️ Active |
| OptionB_L1Convergence | 2 | 740 | ⚠️ **Current work** |
| ExtremeMembers | 1 | 1916 | ⚠️ Large section |
| Theorem | 0 | 42 | ✅ Complete |

**Total active sorries**: ~6-8 (some are TODOs in comments)

## Build Impact Analysis

### Current Build Errors (Unrelated to Refactoring)
- Line 2362: Application type mismatch (in OptionB_DensityUI section)
- Line 2376: Unknown identifier `optionB_L1_convergence_bounded`

**Note**: These errors won't be affected by refactoring - they're pre-existing.

### Refactoring Risk Assessment
- **Low risk**: Infrastructure extraction (no dependencies on rest of file)
- **Medium risk**: Cylinder/Convergence extraction (some cross-dependencies)
- **High risk**: ExtremeMembers extraction (largest section, many internal references)

## Alternative: Directory Structure Without Splitting

Keep ViaKoopman.lean monolithic, but add companion files:

```
DeFinetti/
├── ViaKoopman.lean                    (monolithic, 6650 lines)
├── ViaKoopman/
│   ├── STRUCTURE.md                   (this analysis)
│   ├── SORRIES.md                     (detailed sorry tracking)
│   ├── Infrastructure/                (documentation only)
│   │   ├── TwoSidedShift.md
│   │   └── InstanceLocking.md
│   └── Proofs/
│       ├── OptionA_MET.md
│       └── OptionB_DensityUI.md
```

**Benefits**: Documentation without code changes.

## Conclusion

**Immediate recommendation**: Start with **Option 2** (extract completed infrastructure only) to get quick wins and test the refactoring workflow. If successful, proceed with full Option 1.

**Time commitment**:
- Option 2: 2-3 hours (minimal risk)
- Option 1: 8-12 hours (high value, medium risk)
- Option 3: 0 hours (status quo)

**Next session**: If user agrees, start with Infrastructure.lean extraction (estimated 1.5 hours for extraction + verification).

---

**Created**: 2025-11-16
**Analysis of**: ViaKoopman.lean (6650 lines, ~85 declarations, ~8 sorries)
