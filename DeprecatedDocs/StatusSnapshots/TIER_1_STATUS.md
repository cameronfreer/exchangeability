# Tier 1 Refactoring Status

**Date:** 2025-10-19
**Status:** Partial completion - checkpoint commit created

## Overview

Tier 1 focused on creating two helper files to eliminate duplication:
1. **IntegrationHelpers.lean** - Integration theory wrappers
2. **StrictMono.lean** - Strictly monotone function utilities

This document tracks progress on both components.

## Completed Work

### IntegrationHelpers.lean ✅ (Partial)

**File:** `Exchangeability/Probability/IntegrationHelpers.lean` (91 lines)
**Commit:** b497aac

**Working lemmas (3/4):**

1. ✅ `integral_pushforward_id` - Identity function under pushforward
   ```lean
   ∫ x, x ∂(Measure.map f μ) = ∫ ω, f ω ∂μ
   ```

2. ✅ `integral_pushforward_sq_diff` - Squared difference under pushforward
   ```lean
   ∫ x, (x - c)² ∂(Measure.map f μ) = ∫ ω, (f ω - c)² ∂μ
   ```

3. ✅ `integral_pushforward_continuous` - General continuous function
   ```lean
   ∫ x, g x ∂(Measure.map f μ) = ∫ ω, g (f ω) ∂μ
   ```

**Deferred lemma (1/4):**

❌ `abs_integral_mul_le_L2` - Cauchy-Schwarz inequality for L²
   - **Reason:** Mathlib Hölder inequality API complexity
   - **Status:** Has `sorry` placeholder
   - **Blocking:** Full ViaL2.lean integration (18 call sites need this)

**Impact:**
- Eliminates ~54 `integral_map` boilerplate call sites across three proofs
- Clean namespace: `Exchangeability.Probability.IntegrationHelpers`
- No project dependencies - pure mathlib wrapper

### Proof Decomposition Documentation ✅

**File:** `PROOF_DECOMPOSITION_OPPORTUNITIES.md` (326 lines)
**Commit:** b497aac

**Documented opportunities:**

**High Priority (already compiling files):**
1. Core.lean `measure_eq_of_fin_marginals_eq` (~80 lines → 4 lemmas)
2. Contractability.lean `exists_perm_extending_strictMono` (~60 lines → 3 lemmas)
3. TailSigma.lean `tailProcess_eq_iInf_revFiltration` (~40 lines → 2 lemmas)

**Tier 2-4 refactoring ideas:**
- Tier 2: CE utilities extraction from ViaKoopman (~120 lines, ~half day)
- Tier 3: Ergodic theory to mathlib (~774 lines, 1-2 weeks, community contribution)
- Tier 4: CDF/Stieltjes infrastructure (~300 lines, conditional on need)

**Implementation guidelines:**
- When to decompose (>50 lines, multiple steps, independent interest)
- How to decompose (identify break points, name clearly, test independently)
- Success metrics (50% reduction in >50 line proofs)

## Deferred Work

### StrictMono.lean ❌ (Not started)

**Planned file:** `Exchangeability/Util/StrictMono.lean`
**Status:** Not created

**Planned content:**
- Extract Fin-specific strictly monotone utilities from Contractability.lean
- `strictMono_implies_injective`
- `strictMono_range_card`
- Helper lemmas for permutation extension

**Impact:** ~20 lines of reusable utilities

**Why deferred:** Focused on IntegrationHelpers first (higher impact)

### Cauchy-Schwarz Proof ⚠️ (Blocked)

**Location:** `IntegrationHelpers.lean:44`
**Blocker:** Mathlib Hölder inequality API complexity

**Technical challenges:**
- `IsConjExponent` deprecated → `HolderConjugate`
- Complex type requirements for conjugate exponents
- API mismatch between L² and Hölder formulations

**Impact if unresolved:**
- ViaL2.lean cannot use IntegrationHelpers fully
- 18 Hölder call sites remain verbose
- File compiles with `sorry` but not axiom-free

## Build Status

**IntegrationHelpers.lean:** ✅ Compiles (with 1 sorry)
```bash
lake build Exchangeability.Probability.IntegrationHelpers
# Success: 1596 jobs
```

**No integration yet:** ViaL2.lean still uses old patterns
- Waiting for Cauchy-Schwarz completion
- ~54 call sites ready to refactor

## Next Steps

### Option 1: Complete Tier 1 Fully
1. Resolve Cauchy-Schwarz proof using mathlib L² inner product API
2. Create StrictMono.lean with Fin utilities
3. Update ViaL2.lean to use new helpers
4. Verify build and performance

**Estimated time:** 2-3 hours
**Blocker:** Mathlib API research needed

### Option 2: Move to Proof Decomposition
1. Defer Tier 1 completion
2. Execute high-priority proof decompositions:
   - Core.lean `measure_eq_of_fin_marginals_eq`
   - Contractability.lean `exists_perm_extending_strictMono`
   - TailSigma.lean polish
3. Return to Tier 1 later

**Estimated time:** 3-4 hours total
**Benefit:** Immediate quality improvement to compiling files

### Option 3: Hybrid Approach
1. Complete StrictMono.lean (low-hanging fruit, ~30 min)
2. Do Core.lean decomposition (~1-2 hours)
3. Research Cauchy-Schwarz solution asynchronously

**Estimated time:** 2-3 hours
**Benefit:** Balanced progress across multiple improvements

## Success Metrics

**Tier 1 completion criteria:**
- ✅ IntegrationHelpers.lean created (partial)
- ❌ All 4 lemmas proven without sorries (3/4)
- ❌ StrictMono.lean created (0/1)
- ✅ Documentation complete (1/1)
- ❌ ViaL2.lean integrated (0/1)

**Current score:** 2.75/5 criteria met (55%)

## Recommendations

**For immediate value:**
1. **Complete StrictMono.lean** - Easy win, clear extraction path
2. **Core.lean decomposition** - High impact, already compiles
3. **Defer Cauchy-Schwarz** - Needs deeper mathlib research

**For long-term quality:**
1. Research mathlib L² inner product space API
2. Consider asking mathlib Zulip for Cauchy-Schwarz pattern
3. Complete full Tier 1 integration once unblocked

## Conclusion

Tier 1 achieved **partial completion** with immediate documentation value:
- ✅ 3 working integration helpers
- ✅ Comprehensive proof decomposition roadmap
- ✅ Clean foundation for future refactoring

**Key blocker:** Cauchy-Schwarz proof requires mathlib API expertise

**Recommended path:** Proceed with proof decomposition (Option 2) while deferring Cauchy-Schwarz research to async task.

---

**Status:** Checkpoint commit b497aac
**Next decision:** User choice of Option 1, 2, or 3
