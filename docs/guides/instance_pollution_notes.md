# Instance Pollution in CondIndep.lean - Session Notes

**Date**: 2025-10-28
**File**: `Exchangeability/Probability/CondIndep.lean`
**Issue**: Measurable space instance selection problems in rectangle case

---

## Summary

Successfully completed Section 4 and Section 5 fixes from the user-provided guidance. However, encountered fundamental **instance pollution** issues where Lean's typeclass inference selects local sub-σ-algebra instances (`mZW`, `mW`) instead of the ambient `MeasurableSpace Ω` instance when elaborating predicates like `MeasurableSet` and `Measurable`.

---

## Completed Work

### ✅ Section 4: condIndep_of_indep_pair Fixes

**Lines 263-266** (Product indicator case):
```lean
· rw [Set.indicator_of_mem hY, Set.indicator_of_mem hZ]
  have : (Y ω, Z ω) ∈ A ×ˢ B := Set.mk_mem_prod hY hZ
  rw [Set.indicator_of_mem this]
  norm_num
```

**Lines 294-297** (Intersection indicator case):
```lean
· rw [Set.indicator_of_mem hY, Set.indicator_of_mem hZ]
  have : ω ∈ Y ⁻¹' A ∩ Z ⁻¹' B := ⟨hY, hZ⟩
  rw [Set.indicator_of_mem this]
  norm_num
```

**Result**: Both errors at original lines 263 and 292 are **RESOLVED** ✅

---

### ✅ Section 5: NNReal Elaboration

Checked for NNReal elaboration errors mentioned in summary documents.

**Result**: No NNReal errors present - Section 5 not needed ✅

---

## Instance Pollution Problem

### Root Cause

When you have multiple `MeasurableSpace Ω` instances in scope:
1. **Ambient instance**: `inst✝⁴ : MeasurableSpace Ω` (from theorem signature)
2. **Local instances**: `mW := MeasurableSpace.comap W ...` and `mZW := MeasurableSpace.comap (fun ω => (Z ω, W ω)) ...`

Lean's elaborator **preferentially selects recently-defined local instances** over the ambient typeclass instance.

### Manifestation

**Lines 527-528** (Preimage measurability):
```lean
have hBpre : MeasurableSet (Z ⁻¹' B) := hB.preimage hZ
have hCpre : MeasurableSet (W ⁻¹' C) := hC.preimage hW
```

**Error**:
```
Application type mismatch: The argument
  hZ
has type
  @Measurable Ω β inst✝⁴ inst✝² Z
but is expected to have type
  @Measurable Ω β mZW inst✝² Z
```

**Explanation**: When elaborating `MeasurableSet (Z ⁻¹' B)`, Lean infers `@MeasurableSet Ω mZW (Z ⁻¹' B)` instead of `@MeasurableSet Ω inst✝⁴ (Z ⁻¹' B)`.

---

## Pattern A Investigation

### Attempt 1: Using `‹MeasurableSpace Ω›`

```lean
set m0 : MeasurableSpace Ω := ‹MeasurableSpace Ω› with hm0
```

**Result**: ❌ Failed
**Reason**: The `‹...›` notation picks up `mZW` from the local context instead of the ambient instance.

**Evidence**: Goal state after `set` showed:
```
m0 : MeasurableSpace Ω := mZW
hm0 : m0 = mZW
```

### Attempt 2: Using `inferInstance`

```lean
set m0 : MeasurableSpace Ω := inferInstance with hm0
```

**Result**: ❌ Failed
**Reason**: `inferInstance` elaborates in a context where `mZW` is the most recently mentioned instance, so Lean picks that.

### Attempt 3: Explicit `@` notation with `inst✝⁴`

```lean
have hBpre : @MeasurableSet Ω inst✝⁴ (Z ⁻¹' B) := hB.preimage hZ
```

**Result**: ❌ Syntax error
**Reason**: `inst✝⁴` is pretty-printer notation, not valid source syntax. Cannot write auto-generated instance names directly.

---

## Current Error Summary

**Total Errors**: 16

### Type 1: Application Type Mismatches (5 errors)

**Lines**: 527, 528, 548, 604, 609

**Pattern**: Function expects argument with type using `inst✝⁴`, but got argument with type using `mZW`.

**Examples**:
- Line 527: `hB.preimage hZ` - `hZ` has ambient type, but `.preimage` expects `mZW` type
- Line 548: `hInt_ce.indicator hBpre` - `hBpre` has `mZW` type, but `.indicator` expects ambient type
- Line 604: Type mismatch for `hBpre` in some context
- Line 609: `hC.preimage hW` - similar to line 527

### Type 2: Deterministic Timeouts (10+ errors)

**Lines**: Starting at 618, 625, 630, 653, 656, 660, 673, 411

**Pattern**: Lean's unification engine hits 200,000 heartbeat limit when trying to unify predicates across different measurable space instances.

**Example**:
```
(deterministic) timeout at `isDefEq`, maximum number of heartbeats (200000) has been reached
```

**Likely Cause**: Lean is trying to prove `@MeasurableSet Ω mZW s = @MeasurableSet Ω inst✝⁴ s` or similar, which requires walking through comap definitions and gets stuck in unification loops.

### Type 3: Unknown Constant (1 error)

**Line**: 735

**Error**: `(kernel) unknown constant 'condExp_project_of_condIndep'`

**Cause**: Downstream error - the theorem failed to compile due to earlier errors.

---

## Key Learnings

### 1. Instance Notation Limitations

- **`‹MeasurableSpace Ω›`**: Picks "best match" from context, not necessarily ambient instance
- **`inferInstance`**: Same issue - elaborates to whatever Lean thinks is default in current context
- **`inst✝⁴`**: Cannot be written in source code - only for pretty-printing
- **`_`**: Same as `inferInstance` - will pick local instance over ambient

### 2. The `set` Tactic Creates New Instances

The `set m0 := X with hm0` pattern:
- Creates a **NEW local constant** `m0` (not just an alias)
- Provides equality `hm0 : m0 = X`
- Does NOT prevent instance pollution - it just gives you an equality to work with

### 3. Pattern A Requires Full Conversion Infrastructure

User's Pattern A guidance requires:
1. `set m0 := ... with hm0` to get named equality
2. Helper lemmas like:
   ```lean
   have measurable_domain_congr {m₁ m₂ : MeasurableSpace Ω} (hm : m₁ = m₂) {f : Ω → β} :
       @Measurable Ω β m₁ _ f ↔ @Measurable Ω β m₂ _ f := by simp [hm]
   ```
3. Using `.mpr`/`.mp` to convert ALL facts between instances
4. Being extremely careful about which instance is used where

### 4. Simplified Approach Still Has Issues

Even removing all Pattern A machinery and using simple:
```lean
have hBpre : MeasurableSet (Z ⁻¹' B) := hB.preimage hZ
```

Still fails because Lean elaborates `MeasurableSet` with `mZW` instead of ambient instance.

---

## Options for Resolution

### Option A: Pattern A (Full Implementation)

Implement user's complete Pattern A:
1. Actually freeze the ambient instance correctly (not yet solved!)
2. Create conversion helpers for all predicates needed
3. Convert all ambient facts to `m0` versions using helpers
4. Explicitly manage which instance is used everywhere

**Pros**: Robust once working
**Cons**: Complex, requires solving the initial freezing problem

### Option B: Pattern B (abbrev approach)

User mentioned this as "simpler alternative":
```lean
abbrev m0 : MeasurableSpace Ω := <somehow get ambient>
```

**Question**: How to get the ambient instance for the abbrev without it picking up `mZW`?

### Option C: Explicit `@` Annotations Everywhere

Force the correct instance using `@` notation:
```lean
have hBpre : @MeasurableSet Ω _ (Z ⁻¹' B) := @MeasurableSet.preimage Ω β _ _ B hB Z (@hZ _ _)
```

**Pros**: Direct control
**Cons**: Extremely verbose, error-prone

### Option D: Restructure to Avoid Local Instances

Don't define `mW` and `mZW` as local constants. Instead:
- Use `MeasurableSpace.comap W inferInstance` inline everywhere
- Or use section variables with explicit instance management

**Pros**: Avoids pollution entirely
**Cons**: May break existing proof structure

### Option E: Increase Heartbeat Limits

For the timeout errors:
```lean
set_option maxHeartbeats 500000 in
theorem ...
```

**Note**: This only helps with timeouts, not the underlying type mismatches.

---

## Questions for User

1. **Pattern A Initialization**: How do you correctly "freeze" the ambient instance when `‹MeasurableSpace Ω›` and `inferInstance` both pick up `mZW`?

2. **Pattern B Details**: Can you provide a concrete example of the `abbrev` approach for this situation?

3. **Preferred Solution**: Given the current state, which option would you recommend?

4. **Instance Management**: Is there a way to temporarily "hide" `mW` and `mZW` from typeclass inference while defining `m0`?

---

## Current File State

**Rectangle case prelude (lines 524-529)**:
```lean
classical

-- Preimage measurability in the ambient σ-algebra
have hBpre : MeasurableSet (Z ⁻¹' B) := hB.preimage hZ
have hCpre : MeasurableSet (W ⁻¹' C) := hC.preimage hW
```

**Status**: Simplified from Pattern A attempts, but still has instance selection errors.

**All Section 4 and 5 fixes**: ✅ Successfully applied

**Remaining work**: Resolve the 16 instance-related errors, or await user guidance on preferred approach.

---

## Related Files and Context

**Previous Session Summaries**:
- `/tmp/rectangle_case_fixes_complete.md` - Complete fix application summary
- `/tmp/condindep_session_summary.md` - Initial Dynkin framework work
- `/tmp/dynkin_framework_complete.md` - Framework completion

**User Guidance Provided**:
- Pattern A: Use `set ... with` and conversion helpers
- Pattern B: Use `abbrev` (simpler alternative)
- Never use `letI` for domain measurable spaces
- Section 4: Use `Set.mk_mem_prod` for product membership
- Section 5: Handle NNReal elaboration if needed

**User's Expected Responsibility**:
From `rectangle_case_fixes_complete.md`:
> "Remaining: measurable space mismatches and NNReal errors (user will handle)"

This suggests the user anticipated these instance issues and planned to resolve them personally.

---

**Generated**: 2025-10-28
**Session**: Instance pollution investigation (continuation from rectangle case fixes)
**Status**: Sections 4 and 5 complete ✅, instance issues remain ⚠️
