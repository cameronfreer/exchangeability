# ViaL2.lean Refactoring Plan: Extract Helper Modules

## Summary

ViaL2.lean is currently **3804 lines**. We can safely extract **~540 lines** (~14%) of complete, working code into a separate `L2Helpers.lean` file.

## Extraction Candidates (All Complete, No Sorries)

### 1. **CovarianceHelpers** (Lines 84-287, ~204 lines)
**Purpose**: Helper lemmas about contractable sequences and their covariance structure

**Key lemmas**:
- `contractable_map_single`: All marginals have same distribution
- `contractable_map_pair`: All bivariate marginals have same joint distribution  
- `contractable_comp`: Contractability preserved under measurable postcomposition
- `abs_mul_le_half_sq_add_sq`: Young's inequality for products

**Dependencies**: Only uses `Contractable`, `Measurable`, basic measure theory

**Status**: ✅ Complete, no sorries, builds cleanly

---

### 2. **Lp Utility Lemmas** (Lines 289-499, ~210 lines)
**Purpose**: Standard lemmas for working with Lp spaces and ENNReal conversions

**Key lemmas**:
- ENNReal conversion lemmas
- MemLp properties
- Measurability helpers
- Integration lemmas

**Dependencies**: Basic Lp space theory from mathlib

**Status**: ✅ Complete, no sorries, builds cleanly

---

### 3. **FinIndexHelpers** (Lines 892-1021, ~130 lines)
**Purpose**: Helper lemmas for Fin index gymnastics in two-window bounds

**Key lemmas**:
- `sum_filter_fin_val_lt_eq_sum_fin`: Reindexing filtered sums
- `sum_filter_fin_val_ge_eq_sum_fin`: Another reindexing variant
- Various Fin arithmetic helpers

**Dependencies**: Basic `Fin` and `Finset` theory

**Status**: ✅ Complete, no sorries, builds cleanly

---

## Proposed File Structure

```
Exchangeability/DeFinetti/
├── ViaL2.lean              (main proof, ~3260 lines after extraction)
├── L2Helpers.lean          (extracted helpers, ~540 lines)
└── L2Approach.lean         (existing, already separate)
```

### New file: `L2Helpers.lean`

```lean
/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Exchangeability.Contractability
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# Helper Lemmas for L² de Finetti Proof

This file contains auxiliary lemmas used in the L² approach to de Finetti's theorem
(`ViaL2.lean`). All lemmas here are complete (no sorries) and compile cleanly.

## Contents

1. **CovarianceHelpers**: Lemmas about contractable sequences and covariance structure
2. **Lp Utility Lemmas**: Standard Lp space and ENNReal conversion helpers
3. **FinIndexHelpers**: Fin reindexing lemmas for two-window bounds

-/

noncomputable section

namespace Exchangeability.DeFinetti.L2Helpers

[... extracted content ...]

end Exchangeability.DeFinetti.L2Helpers
```

### Modified: `ViaL2.lean`

Add import at top:
```lean
import Exchangeability.DeFinetti.L2Helpers
```

Replace the three extracted sections with:
```lean
-- CovarianceHelpers, Lp utilities, and FinIndexHelpers
-- are now in L2Helpers.lean
open L2Helpers
```

---

## Benefits

1. **Reduced main file size**: 3804 → ~3260 lines (14% reduction)
2. **Better modularity**: Helper lemmas separated from main proof logic
3. **Easier maintenance**: Changes to helpers don't require rebuilding entire proof
4. **Cleaner structure**: Main file focuses on proof steps, not technical lemmas
5. **No risk**: All extracted code is complete and working

---

## Implementation Steps

1. Create `L2Helpers.lean` with proper imports and namespace
2. Copy the three sections (CovarianceHelpers, Lp utils, FinIndexHelpers)
3. Adjust visibility (`private` → `public` where needed for export)
4. Add import to `ViaL2.lean`
5. Remove extracted sections from `ViaL2.lean`
6. Add `open L2Helpers` to expose the lemmas
7. Test build: `lake build Exchangeability.DeFinetti.ViaL2`
8. Commit with clear message

---

## Alternative: Phased Extraction

If you prefer a more cautious approach:

**Phase 1**: Extract just `FinIndexHelpers` (~130 lines, most self-contained)
**Phase 2**: Extract `CovarianceHelpers` (~204 lines)
**Phase 3**: Extract `Lp utilities` (~210 lines)

This allows testing after each phase.

---

## Notes

- All extracted code has **zero sorries**
- All extracted code **builds without warnings** (after recent linting fixes)
- The extracted lemmas are **not** main theorem statements - they're pure helpers
- No circular dependencies (helpers don't depend on main proof)
