# Option A (Quick Win) Summary - 2025-10-19

**Date:** 2025-10-19
**Task:** Fix simp recursion errors in ViaL2.lean and ViaMartingale.lean
**Goal:** Get both proof files building cleanly

## Summary

**Good News:** ViaL2.lean already builds successfully! The "simp recursion errors" mentioned in the background bash summary were from an earlier session and have already been fixed.

**Partial Success:** ViaMartingale.lean has type-level issues that need more investigation. The file has compilation errors at lines 230 and 236 related to integration with the new `Tail/TailSigma.lean` helper file.

---

## Results

### ✅ ViaL2.lean - Already Building!

**Status:** Builds successfully
**Sorries:** 19 (as documented in SORRY_AXIOM_ANALYSIS.md)
**Errors:** 0
**Warnings:** Minor linter warnings only (unused variables, unused simp arguments)

**Build verification:**
```bash
lake build Exchangeability.DeFinetti.ViaL2
# Result: Build completed successfully (2559 jobs)
```

**Conclusion:** ViaL2 needs no fixes - it's ready for proof completion work.

### ⚠️ ViaMartingale.lean - Type Integration Issues

**Status:** Does not build
**Errors:** 2 compilation errors at lines 230 and 236
**Root Cause:** Type-level mismatches when integrating with `Tail/TailSigma.lean`

#### Error 1: Line 230 - `comap_shift_eq_iSup_comap_coords` Application

**Error Message:**
```
Type mismatch
  Tail.comap_shift_eq_iSup_comap_coords m
has type
  Eq (MeasurableSpace.comap (fun ω k => ω (m + k)) inferInstance)
     (⨆ k, MeasurableSpace.comap (fun ω => ω (m + k)) inferInstance)
but is expected to have type
  Eq (MeasurableSpace.comap (shiftRV X m) inferInstance)
     (⨆ k, MeasurableSpace.comap (fun ω => X (m + k) ω) inferInstance)
```

**Problem:** The library lemma `comap_shift_eq_iSup_comap_coords` expects functions on path space `(ℕ → α)`, but ViaMartingale uses `shiftRV X m` which has type `Ω → (ℕ → α)`.

**Attempted fixes:**
1. Added type parameter `(α := α)`
2. Changed `simp` to `unfold`
3. All failed due to fundamental type mismatch

**Root issue:** ViaMartingale's definitions (`shiftRV`, `revFiltration`) work on a process `X : ℕ → Ω → α`, while the library lemma works on path space `ℕ → α` directly.

#### Error 2: Line 236 - `tailProcess_eq_iInf_revFiltration` Application

**Error Message:**
```
Application type mismatch: The argument
  revFiltration_eq_tailFamily
```

**Attempted fix:** Changed signature to match the expected form:
```lean
Exchangeability.Tail.tailProcess_eq_iInf_revFiltration X (revFiltration X) (revFiltration_eq_tailFamily X)
```

**Status:** Still failing due to dependency on line 230 error.

---

## Analysis

### Why ViaL2 Works But ViaMartingale Doesn't

**ViaL2.lean:**
- Was fixed in a previous session (likely before context was lost)
- Uses compatible definitions with Tail/TailSigma.lean
- 19 sorries but 0 compilation errors

**ViaMartingale.lean:**
- Uses its own `shiftRV` and `revFiltration` definitions
- These definitions have a different type structure than the canonical `Tail/TailSigma.lean` helpers
- Needs bridge lemmas that handle the type coercion

### The Type Structure Problem

**Canonical (Tail/TailSigma.lean):**
```lean
comap_shift_eq_iSup_comap_coords :
  (n : ℕ) →
  MeasurableSpace.comap (fun (ω : ℕ → α) => fun k => ω (n + k)) inferInstance
  = ⨆ k, MeasurableSpace.comap (fun ω => ω (n + k)) inferInstance
```
Works directly on path space `ℕ → α`.

**ViaMartingale approach:**
```lean
shiftRV (X : ℕ → Ω → α) (m : ℕ) : Ω → (ℕ → α) :=
  fun ω n => X (m + n) ω

revFiltration X m :=
  MeasurableSpace.comap (shiftRV X m) inferInstance
```
Works on a process via `shiftRV` which produces path space from `Ω`.

**The gap:** We need a version of the lemma that works for processes, or we need to instantiate the path-space lemma with `Ω = ℕ → α` and `X = coordinate projections`.

---

## Recommended Fix Strategy

### Option 1: Add Process-Specific Lemma to Tail/TailSigma.lean

Add a version of `comap_shift_eq_iSup_comap_coords` that works for processes:

```lean
/-- Process version of comap_shift_eq_iSup_comap_coords. -/
lemma process_comap_shift_eq_iSup (X : ℕ → Ω → α) (m : ℕ) :
    MeasurableSpace.comap (fun ω n => X (m + n) ω) inferInstance
    = ⨆ k, MeasurableSpace.comap (fun ω => X (m + k) ω) inferInstance := by
  -- Instantiate comap_shift_eq_iSup_comap_coords with Ω and X
  sorry
```

Then use this in ViaMartingale.lean:
```lean
lemma revFiltration_eq_tailFamily (X : ℕ → Ω → α) (m : ℕ) :
    revFiltration X m =
    ⨆ k : ℕ, MeasurableSpace.comap (fun ω => X (m + k) ω) inferInstance := by
  unfold revFiltration shiftRV
  exact Exchangeability.Tail.process_comap_shift_eq_iSup X m
```

### Option 2: Use Path Space Instantiation

Instantiate the existing lemma with `Ω = ℕ → α` and use the fact that `shiftRV X m` is just composition:

```lean
lemma revFiltration_eq_tailFamily (X : ℕ → Ω → α) (m : ℕ) :
    revFiltration X m =
    ⨆ k : ℕ, MeasurableSpace.comap (fun ω => X (m + k) ω) inferInstance := by
  unfold revFiltration shiftRV
  -- Need to show: shiftRV X m relates to the coordinate shift on path space
  sorry
```

### Option 3: Simplify by Using sorry (Quickest)

Since the lemma is meant to be a bridge to prove `tailSigma_eq_canonical`, and we have 4 sorries already in ViaMartingale, the quickest fix is:

```lean
lemma revFiltration_eq_tailFamily (X : ℕ → Ω → α) (m : ℕ) :
    revFiltration X m =
    ⨆ k : ℕ, MeasurableSpace.comap (fun ω => X (m + k) ω) inferInstance := by
  sorry  -- TODO: Instantiate Tail.comap_shift_eq_iSup_comap_coords for processes
```

This would allow the file to build and moves the issue to the "proof completion" phase.

---

## Current Project Build Status

### Building Successfully ✅

- Core.lean
- Contractability.lean
- ConditionallyIID.lean
- All Ergodic/* files
- Tail/TailSigma.lean
- PathSpace/CylinderHelpers.lean
- Util/StrictMono.lean
- Probability/IntegrationHelpers.lean (4 sorries)
- **ViaKoopman.lean** (16 sorries, 0 errors!)
- **ViaL2.lean** (19 sorries, 0 errors!)

### Not Building ❌

- **ViaMartingale.lean** - 2 type-level errors at lines 230, 236

---

## Time Spent

**Total time on Option A:** ~30 minutes

**Breakdown:**
- Verifying ViaL2 builds: 5 min
- Attempting ViaMartingale fixes: 20 min
- Analysis and documentation: 5 min

**Estimated time to complete ViaMartingale fixes:**
- Option 1 (add process lemma): 1-2 hours
- Option 2 (path space instantiation): 1-2 hours
- Option 3 (sorry): 5 minutes

---

## Recommendation

### Short-term (Now):

**Use Option 3 (sorry)** to unblock the file and move forward:
- Time: 5 minutes
- Impact: ViaMartingale builds with 5 sorries instead of 4
- Benefit: Can proceed with other work

### Medium-term (Next Session):

**Implement Option 1 (process lemma)** when doing proof completion work:
- Add `process_comap_shift_eq_iSup` to Tail/TailSigma.lean
- This is more valuable than fixing just for ViaMartingale
- Other process-based code may benefit

### Alternative Path:

**Switch focus** to other high-value work:
- ViaL2 proof completion (19 sorries, file builds)
- ViaKoopman Stream 1b type class fixes (6 sorries, file builds)
- See REFACTORING_UPDATE_2025-10-19.md § 3-4 for detailed strategies

---

## Key Learnings

1. **Background bash summaries can be outdated** - ViaL2 and ViaKoopman both build despite showing errors in the summary

2. **Type-level integration is subtle** - The path-space vs. process formulation creates type mismatches that aren't immediately obvious

3. **Quick wins aren't always quick** - What seemed like "simp recursion errors" turned out to be fundamental type structure issues in ViaMartingale

4. **Prioritize what builds** - ViaL2 and ViaKoopman both build and have more sorries to work on than the time spent debugging ViaMartingale

---

## Next Steps

**Immediate (User's Choice):**

1. **Apply Option 3 sorry fix** to ViaMartingale (5 min) - Get all three proof files building
2. **Start ViaL2 proof work** - File builds, 19 sorries documented with decomposition strategies
3. **Start ViaKoopman Stream 1b** - File builds, 6 type class sorries with fix strategies

**Medium-term:**

- Add process-specific lemmas to Tail/TailSigma.lean
- Complete ViaMartingale bridge proofs properly
- See REFACTORING_UPDATE_2025-10-19.md for comprehensive proof completion plan

---

## Files Modified This Session

1. **Exchangeability/DeFinetti/ViaMartingale.lean** (lines 230, 236)
   - Added type parameter `(α := α)` to `comap_shift_eq_iSup_comap_coords`
   - Fixed signature of `tailProcess_eq_iInf_revFiltration` call
   - Changed `simp` to `unfold` for `revFiltration` and `shiftRV`
   - **Status:** Still has compilation errors (type-level issues)

2. **OPTION_A_SUMMARY.md** (this file)
   - Documents findings and recommendations

---

**Generated:** 2025-10-19
**Session Duration:** ~30 minutes
**Outcome:** Partial success (ViaL2 verified building, ViaMartingale needs more work)
