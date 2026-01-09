# ViaKoopman.lean Refactoring: Step-by-Step Execution Plan

## Session Summary (2025-11-16)
- **Documentation added** ✅ File structure now documented in ViaKoopman.lean
- **Ready for refactoring** ✅ Directory created: `Exchangeability/DeFinetti/ViaKoopman/`
- **Next**: Execute Option 2 refactoring (extract completed infrastructure)

## Option 2: Extract Completed Infrastructure (Estimated: 2-3 hours)

### Step 1: Extract Infrastructure.lean (60-90 min)

**Extract lines**: 1-701 + namespace setup

**File**: `Exchangeability/DeFinetti/ViaKoopman/Infrastructure.lean`

**Contents**:
```lean
/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.SimpleFuncDense
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.Independence.Kernel
import Exchangeability.Ergodic.KoopmanMeanErgodic
import Exchangeability.Ergodic.InvariantSigma
import Exchangeability.Ergodic.ProjectionLemmas
import Exchangeability.Ergodic.BirkhoffAvgCLM
import Exchangeability.DeFinetti.CommonEnding
import Exchangeability.DeFinetti.MartingaleHelpers
import Exchangeability.ConditionallyIID
import Exchangeability.Probability.CondExp
import Exchangeability.PathSpace.Shift
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp

open Filter MeasureTheory

/-! # Infrastructure for ViaKoopman Proof

This file contains completed infrastructure for the Koopman-based de Finetti proof:
- Reusable micro-lemmas
- Lp coercion lemmas
- Two-sided natural extension infrastructure
- Helper lemmas for shift operations
- Instance-locking shims for conditional expectation

All lemmas in this file are proved (no sorries).

**Extracted from**: ViaKoopman.lean lines 1-701
**Status**: ✅ COMPLETE (no sorries)
-/

noncomputable section

namespace Exchangeability.DeFinetti.ViaKoopman

open MeasureTheory Filter Topology ProbabilityTheory
open Exchangeability.Ergodic
open Exchangeability.PathSpace
open Exchangeability.DeFinetti.MartingaleHelpers (comap_comp_le)
open scoped BigOperators RealInnerProductSpace

variable {α : Type*} [MeasurableSpace α]

-- Short notation for shift-invariant σ-algebra
local notation "mSI" => shiftInvariantSigma (α := α)

/-! ### Reusable micro-lemmas -/

[INSERT LINES 38-53 FROM ViaKoopman.lean]

/-! ### Lp coercion lemmas -/

[INSERT LINES 56-77 FROM ViaKoopman.lean]

/-! ### Two-sided natural extension infrastructure -/

[INSERT LINES 288-701 FROM ViaKoopman.lean]

end Exchangeability.DeFinetti.ViaKoopman
```

**Action items**:
1. Create Infrastructure.lean with above structure
2. Copy lines 1-25 (imports), 38-53 (micro-lemmas), 56-77 (Lp coercion), 275-701 (two-sided infrastructure)
3. Build: `lake build Exchangeability.DeFinetti.ViaKoopman.Infrastructure`
4. Verify: No errors, no sorries

### Step 2: Update ViaKoopman.lean to import Infrastructure (15-20 min)

**Modify**: `Exchangeability/DeFinetti/ViaKoopman.lean`

**Changes**:
1. After existing imports (line 23), add:
   ```lean
   import Exchangeability.DeFinetti.ViaKoopman.Infrastructure
   ```

2. Delete lines 27-77 (now in Infrastructure.lean)

3. Delete lines 288-701 (now in Infrastructure.lean)

4. Keep namespace opening at line 275:
   ```lean
   namespace Exchangeability.DeFinetti.ViaKoopman
   ```
   (But the micro-lemmas and two-sided infrastructure are now imported)

**Action items**:
1. Add import statement
2. Delete extracted sections
3. Build: `lake build Exchangeability.DeFinetti.ViaKoopman`
4. Verify: File now ~6000 lines instead of 6650

### Step 3: Extract CylinderFunctions.lean (30-45 min)

**Extract lines**: 3102-3543

**File**: `Exchangeability/DeFinetti/ViaKoopman/CylinderFunctions.lean`

**Contents**:
```lean
/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Exchangeability.DeFinetti.ViaKoopman.Infrastructure

/-! # Cylinder Functions Infrastructure

Helper lemmas for indicator_product_bridge_ax, MeasureTheory namespace extensions,
and cylinder function machinery for the Koopman de Finetti proof.

**Extracted from**: ViaKoopman.lean lines 3102-3543
**Status**: ✅ COMPLETE (no sorries)
-/

noncomputable section

namespace Exchangeability.DeFinetti.ViaKoopman

open MeasureTheory Filter Topology ProbabilityTheory
open Exchangeability.Ergodic
open Exchangeability.PathSpace
open scoped BigOperators

variable {α : Type*} [MeasurableSpace α]

/-! ### Helper lemmas for indicator_product_bridge_ax -/

[INSERT LINES 3102-3359 FROM ViaKoopman.lean]

namespace MeasureTheory

[INSERT LINES 3360-3439 FROM ViaKoopman.lean]

end MeasureTheory

section CylinderFunctions

[INSERT LINES 3441-3543 FROM ViaKoopman.lean]

end CylinderFunctions

end Exchangeability.DeFinetti.ViaKoopman
```

**Action items**:
1. Create CylinderFunctions.lean with above structure
2. Copy lines 3102-3543
3. Build: `lake build Exchangeability.DeFinetti.ViaKoopman.CylinderFunctions`
4. Verify: No errors, no sorries

### Step 4: Update ViaKoopman.lean to import CylinderFunctions (10-15 min)

**Modify**: `Exchangeability/DeFinetti/ViaKoopman.lean`

**Changes**:
1. After Infrastructure import, add:
   ```lean
   import Exchangeability.DeFinetti.ViaKoopman.CylinderFunctions
   ```

2. Delete lines 3102-3543 (now in CylinderFunctions.lean)

**Action items**:
1. Add import statement
2. Delete extracted section
3. Build: `lake build Exchangeability.DeFinetti.ViaKoopman`
4. Verify: File now ~5200 lines instead of ~6000

### Step 5: Verification and Documentation (15-20 min)

**Action items**:
1. Build full project: `lake build`
2. Verify: All builds successful
3. Run diagnostics:
   ```bash
   wc -l Exchangeability/DeFinetti/ViaKoopman.lean
   wc -l Exchangeability/DeFinetti/ViaKoopman/*.lean
   ```
4. Update VIAKOOPMAN_REFACTORING_ANALYSIS.md with completion status
5. Commit with message: `refactor: Extract completed infrastructure from ViaKoopman (Option 2)`

### Step 6: Document Next Steps (5 min)

**Update**: ViaKoopman.lean module documentation

**Changes**: Update "File Structure" section to reflect extracted files:
```markdown
## File Structure (Originally 6650 lines, now ~5200 lines)

**Extracted to separate files** (Option 2 complete):
- `ViaKoopman/Infrastructure.lean` (lines 1-701) ✅
- `ViaKoopman/CylinderFunctions.lean` (lines 3102-3543) ✅

**Remaining in ViaKoopman.lean**:
- Section 2: Lp Norm Helpers (Lines 1625-1728)
- Section 3: Mean Ergodic Theorem (Lines 1904-2275) ⚠️ 1 sorry
- Section 4: Option B - Density Approach (Lines 2276-3101) ⚠️ 1 sorry
- Section 6: Main Convergence (Lines 3545-3896) ⚠️ 1 sorry
- Section 7: Option B - L¹ Convergence (Lines 3898-4637) ⚠️ 2 sorries
- Section 8: Extreme Members (Lines 4639-6554) ⚠️ 1 sorry
- Section 9: Main Theorem (Lines 6609-6650) ✅ COMPLETE

**Next**: Option 1 full split (when ready)
```

## Estimated Timeline

| Step | Description | Time | Cumulative |
|------|-------------|------|------------|
| 1 | Extract Infrastructure.lean | 60-90 min | 60-90 min |
| 2 | Update ViaKoopman imports | 15-20 min | 75-110 min |
| 3 | Extract CylinderFunctions.lean | 30-45 min | 105-155 min |
| 4 | Update ViaKoopman imports | 10-15 min | 115-170 min |
| 5 | Verification | 15-20 min | 130-190 min |
| 6 | Documentation | 5 min | 135-195 min |

**Total**: 2.25-3.25 hours

## Success Criteria

✅ Infrastructure.lean builds without errors
✅ CylinderFunctions.lean builds without errors
✅ ViaKoopman.lean builds without errors
✅ Full project builds without errors
✅ ViaKoopman.lean reduced from 6650 → ~5200 lines
✅ No new errors introduced
✅ All existing sorries still compile

## Rollback Plan

If refactoring causes issues:
1. `git stash` or `git reset --hard HEAD~1`
2. Review errors and adjust extraction boundaries
3. Retry with smaller increments

## After Option 2 Complete

**Decision point**: Proceed with Option 1 (full split) or continue working on sorries?

**Option 1 advantages**:
- ExtremeMembers (1916 lines) gets own file
- Each sorry section isolated
- Parallel development enabled
- **Estimated**: 6-9 more hours (8 files total)

**Continue with sorries advantages**:
- Faster path to completion
- Less refactoring overhead
- Can always refactor later

**Recommendation**: Complete Option 2, fix high-priority sorries (lines 4065, 4081), then decide.

---

**Created**: 2025-11-16
**Status**: Ready for execution
**Next session**: Execute Steps 1-6 above
