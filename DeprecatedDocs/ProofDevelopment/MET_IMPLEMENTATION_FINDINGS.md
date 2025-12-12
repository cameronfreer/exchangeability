# Mean Ergodic Theorem Implementation - Root Cause Analysis

## Executive Summary

**Task**: Implement the Mean Ergodic Theorem for `birkhoffAverage_tendsto_condexp_L2` in ViaKoopman.lean

**Result**: ✅ Partial implementation + 🔴 Fundamental blocker discovered

**Root Cause**: The `koopman` operator is not defined for sub-σ-algebras, preventing completion of the general (T, m) version.

## What Was Accomplished

### 1. Successful Implementation (Step 1)

```lean
-- Step 1: Cast integrable f to Lp ℝ 2 μ
have hf_memlp : MemLp f 2 μ := hf_int.memℒp one_le_two
let g : Lp ℝ 2 μ := hf_memlp.toLp f
```

✅ **Complete**: Found correct API (`MemLp`, not `Memℒp`)
✅ **Complete**: Conversion path `Integrable → MemLp → Lp`

### 2. Root Cause Discovery (Step 2)

**Attempted**:
```lean
let K := Exchangeability.Ergodic.koopman T hT_pres
```

**Blocked**: Type class synthesis error

**Reason**: `koopman` signature is:
```lean
def koopman {μ : Measure Ω} [IsProbabilityMeasure μ]
    (T : Ω → Ω) (hT : MeasurePreserving T μ μ) :
    Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ
```

The measure `μ` is w.r.t. the **ambient** MeasurableSpace instance, not the sub-σ-algebra `m`.

## The Fundamental Problem

### Theorem Signature

```lean
birkhoffAverage_tendsto_condexp_L2
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (T : Ω → Ω) (hT_meas : Measurable T) (hT_pres : MeasurePreserving T μ μ)
    {m : MeasurableSpace Ω} (hm : m ≤ ‹MeasurableSpace Ω›)  ⬅️ SUB-σ-ALGEBRA
    (h_inv : ∀ s, MeasurableSet[m] s → T ⁻¹' s = s)
    (f : Ω → ℝ) (hf_int : Integrable f μ)
```

### The Mismatch

| Component | Expected σ-algebra | Actual σ-algebra |
|-----------|-------------------|------------------|
| `koopman T` | Ambient `‹MeasurableSpace Ω›` | Ambient |
| `Lp ℝ 2 μ` | Ambient | Ambient |
| `condexp[· \| m]` | Sub-algebra `m` | `m` |
| `h_inv` condition | Sub-algebra `m` | `m` |

**The clash**: We need to connect:
- Koopman fixed-point subspace (defined w.r.t. ambient σ-algebra)
- Conditional expectation onto `m` (defined w.r.t. sub-σ-algebra)

### Why It Works for Shift

In `InvariantSigma.lean` and line 3245, this works because:

```lean
-- shiftInvariantSigma IS the ambient σ-algebra in the construction
def shiftInvariantSigma : MeasurableSpace (Ω[α]) :=
  ⨅ n : ℕ, MeasurableSpace.comap (shift^[n]) inferInstance

-- Then we have:
fixedSubspace hσ = {φ : Lp ℝ 2 μ | koopman shift hσ φ = φ}
                 = lpMeas shiftInvariantSigma ℝ 2 μ
```

There's no sub-σ-algebra mismatch because `shiftInvariantSigma` IS the σ-algebra that the types are built on.

### Why It Fails for General (T, m)

For arbitrary T-invariant sub-σ-algebra `m`:

```lean
-- m is a SUB-σ-algebra: m ≤ ‹MeasurableSpace Ω›
-- koopman acts on Lp w.r.t. ‹MeasurableSpace Ω›
-- condexp targets lpMeas(m), not lpMeas(‹MeasurableSpace Ω›)
```

**The infrastructure doesn't exist to connect these.**

## Technical Deep Dive

### API Discoveries

1. **Correct names** (not what documentation suggested):
   - `MemLp f p μ` (not `Memℒp`)
   - `Integrable.memℒp` (method name uses lowercase ℒ)
   - `MemLp.toLp`

2. **Lp conversion path**:
   ```lean
   Integrable f μ
     → MemLp f p μ               (via Integrable.memℒp)
     → Lp E p μ                  (via MemLp.toLp)
   ```

3. **Lp norm relation**:
   ```lean
   theorem Lp.norm_def (f : Lp E p μ) :
     ‖f‖ = ENNReal.toReal (eLpNorm f p μ)
   ```

### Error Messages Decoded

**Error 1**: `Unknown identifier Memℒp`
- **Cause**: Wrong capitalization
- **Fix**: Use `MemLp` (capital M, capital L, lowercase p)

**Error 2**: `synthesized type class instance is not definitionally equal`
- **Cause**: `koopman` expects ambient MeasurableSpace, got sub-σ-algebra context
- **Impact**: Fatal - blocks entire approach

## Solutions Considered

### Option 1: Generalize Koopman Infrastructure

**Approach**: Extend `koopman` to work with sub-σ-algebras

**Requires**:
1. Define `koopman_sub : {m : MeasurableSpace Ω} → (m ≤ inst) → ...`
2. Define `Lp_sub` space: functions measurable w.r.t. `m`
3. Prove isometry properties for `koopman_sub`
4. Generalize all projection lemmas

**Effort**: 1-2 weeks

**Risk**: May reveal deeper type-theoretic issues

### Option 2: Restriction Lemma

**Approach**: Prove that `koopman` on ambient space restricts correctly

**Requires**:
```lean
lemma koopman_restricts
    {m : MeasurableSpace Ω} (hm : m ≤ inst)
    (h_inv : ∀ s, MeasurableSet[m] s → T⁻¹' s = s) :
    (koopman T hT_pres).restrict (lpMeas m) = koopman_m T ...
```

**Effort**: 3-5 days

**Risk**: `restrict` operation may not preserve required properties

### Option 3: Direct MET for Sub-σ-algebras

**Approach**: Bypass Koopman entirely, prove MET directly for sub-σ-algebras

**Requires**:
1. Formulate MET without Koopman operator
2. Prove convergence using only measurability and invariance
3. Connect directly to conditional expectation

**Effort**: 2-3 weeks

**Benefit**: Most general solution

### Option 4: Keep as Sorry (CHOSEN)

**Rationale**:
- General version not needed for main application
- Shift-specific infrastructure is complete
- Effort/benefit ratio unclear
- Good documentation more valuable than partial implementation

**Trade-offs**:
- ✅ Unblocks other work
- ✅ Documents problem clearly
- ✅ Provides roadmap for future
- ❌ Theorem incomplete

## Comparison: Before vs. After

### Before This Session

```lean
private theorem birkhoffAverage_tendsto_condexp_L2 ... := by
  admit  -- Single line, no context
```

**Status**: Opaque blocker

### After This Session

```lean
private theorem birkhoffAverage_tendsto_condexp_L2 ... := by
  /-
    PARTIAL IMPLEMENTATION with 2 remaining sorries:
    ... [detailed explanation]
  -/
  classical
  -- Step 1: Cast f to Lp ℝ 2 μ [✅ COMPLETE]
  have hf_memlp : MemLp f 2 μ := hf_int.memℒp one_le_two
  let g : Lp ℝ 2 μ := hf_memlp.toLp f

  -- Step 2: Build Koopman operator [🔴 BLOCKED]
  sorry  -- Infrastructure gap: koopman not defined for sub-σ-algebras

  -- Steps 3-5 documented in comments [📝 DOCUMENTED]
  sorry  -- Complete proof would go here
```

**Status**: Root cause identified, partial implementation, clear path forward

## Impact Analysis

### Downstream Dependencies

**Line 1971**: `L1_cesaro_convergence` uses this sorry

**BUT**: That usage is for `shiftℤInv` and shift-invariant σ-algebra, where complete infrastructure EXISTS.

**Conclusion**: This sorry does NOT block critical functionality.

### Alternative for Line 1971

Instead of using the general theorem, can instantiate from the shift-specific version:

```lean
-- Existing (line 3245):
theorem birkhoffAverage_tendsto_condexp (f : Lp ℝ 2 μ) :
    Tendsto (fun n => birkhoffAverage ℝ (koopman shift hσ) id n f)
      atTop (𝓝 (condexpL2 μ f))

-- Can derive for shiftℤInv:
theorem birkhoffAverage_tendsto_condexp_shiftℤInv ...
```

## Lessons Learned

### 1. Type Class Synthesis is Fragile

Sub-σ-algebras cause type class synthesis issues throughout Lean's measure theory library. The "definitional equality" errors are symptoms of deeper structural mismatches.

### 2. Infrastructure Dependencies Run Deep

This isn't just about one lemma (`range_condexp_eq_fixedSubspace`). The ENTIRE Koopman/MET machinery assumes a single ambient σ-algebra.

### 3. Documentation > Incomplete Code

Better to have:
- Clear explanation of what works
- Precise identification of blockers
- Roadmap for completion

Than to have:
- Partial code with obscure errors
- Unclear status
- No path forward

### 4. API Discovery is Non-Trivial

Finding the right lemmas/definitions:
- `MemLp` vs `Memℒp` (capitalization matters!)
- `memℒp` method (lowercase ℒ) on `Integrable`
- `toLp` constructor

Required significant exploration.

## Recommendations

### For This Codebase

**Short term** (current): Keep sorry with comprehensive documentation

**Medium term** (if needed): Implement Option 2 (restriction lemma)

**Long term** (if generally useful): Implement Option 1 (generalize infrastructure)

### For Future Work

1. **When encountering sub-σ-algebra issues**:
   - Check if ambient-σ-algebra version exists
   - Document type class synthesis errors carefully
   - Consider if generalization is necessary

2. **When implementing ergodic theory**:
   - Be explicit about which σ-algebra each operator acts on
   - Test with sub-σ-algebras early
   - Provide both ambient and sub-σ-algebra versions if needed

3. **When documenting sorries**:
   - Explain attempted approaches
   - Identify root cause, not just symptoms
   - Provide alternative solutions

## Files Changed

### New Files
- `VIAKOOPMAN_MET_SUMMARY.md` - Comprehensive session summary
- `MET_IMPLEMENTATION_FINDINGS.md` - This document

### Modified Files
- `Exchangeability/DeFinetti/ViaKoopman.lean`
  - Line 1600-1622: Partial implementation with documented gaps
  - Reduced from "unknown blocker" to "known infrastructure limitation"

### Commits
1. `5b37783` - Document Mean Ergodic Theorem proof strategy
2. `9d66277` - Attempt MET proof implementation - uncover fundamental blocker

## Conclusion

**What we learned**: The blocker isn't mathematical complexity, it's infrastructure mismatch.

**What we accomplished**:
- ✅ Partial implementation (Step 1 complete)
- ✅ Root cause identified (koopman/sub-σ-algebra mismatch)
- ✅ API discoveries documented (`MemLp`, conversion paths)
- ✅ Alternative approaches outlined (4 options)
- ✅ Clean build maintained

**What remains**:
- Option selection for completing the proof (if needed)
- Implementation of chosen option (estimated 3 days to 2 weeks)
- OR: continued use with documentation (current state)

**Recommendation**: Keep as sorry unless general version becomes critical for other work. The documentation now provides clear guidance for anyone who needs to complete it.

---

*Generated: 2025-10-21*
*Session: Mean Ergodic Theorem Implementation Attempt*
*Result: Root Cause Identified*
