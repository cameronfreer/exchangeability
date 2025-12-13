# CondIndep.lean Error Analysis

**Status:** File has compilation errors blocking ViaMartingale.lean build
**Date:** 2025-10-29
**Blocker:** Lines 554-602 (primary), cascading parse errors, measurable space mismatches

---

## Error Summary (14 errors)

### **Chunk 1: Lines 554-602** (Primary blocker - structural issues)

#### **Line 554**: Type class instance error in `tendsto_condexp_L1`

```lean
lemma tendsto_condexp_L1 (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m : MeasurableSpace Ω) (hm : m ≤ inferInstance)  -- ← Line 554: inferInstance problematic
```

**Error:** `type class instance expected ?m.4`
**Issue:** `inferInstance` in argument position causes type class synthesis failure
**Fix:** Change to explicit type annotation or remove the constraint

---

#### **Lines 566-570**: Multiple synthesis errors in `approx_bounded_measurable`

```lean
lemma approx_bounded_measurable (μ : Measure Ω) [IsProbabilityMeasure μ]
    {f : α → ℝ} (M : ℝ) (hf_meas : Measurable f)
    (hf_bdd : ∀ᵐ ω ∂μ.map (fun x => x), |f ω| ≤ M) :  -- ← Wrong measure type
```

**Errors:**
- Line 566: `failed to synthesize FunLike (Measure Ω) (Set α) ℝ≥0∞`
- Line 568: Same FunLike synthesis failure
- Line 569: Same FunLike synthesis failure
- Line 570: Application type mismatch (twice)

**Issue:** `μ : Measure Ω` but trying to use `μ.map (fun x => x)` with `α` types
- The lemma is parameterized over `μ : Measure Ω` but operates on `f : α → ℝ`
- `μ.map (fun x => x)` doesn't type-check: identity map from `Ω → Ω` doesn't help
- Should be `μ : Measure α` or different approach entirely

**Fix Options:**
1. Change signature to `μ : Measure α` (simplest)
2. Rework to use pushforward measure `Measure.map Y μ` where `Y : Ω → α`
3. Make lemma work on `Ω` directly instead of abstract `α`

---

#### **Line 602**: Unsolved goals (proof block incomplete)

```lean
    μ[ (φ ∘ Y) | MeasurableSpace.comap W inferInstance ]
      * μ[ (ψ ∘ Z) | MeasurableSpace.comap W inferInstance ] := by  -- ← Line 602
  classical  -- ← Proof body starts but never closes
  set mW := MeasurableSpace.comap W inferInstance

  /-! ### Step 0: build real-valued simple-function approximation ... -/
  -- ... extensive scaffolding code follows ...
```

**Error:** `unsolved goals` - proof block never completes
**Issue:** The `by` block at line 602 starts with:
- `classical`
- Several `set` declarations
- Long commented scaffolding for eapprox-based approximation
- **But no closing tactic** - proof is incomplete

**Fix:** Either:
1. Add `sorry` to complete the proof block
2. Complete the approximation proof (complex - see inline comments)
3. Remove the `:= by` and make it an `axiom` temporarily

---

### **Chunk 2: Lines 609, 739, 778, 923** (Cascading parse errors)

**Line 609**: `unexpected identifier; expected command`
**Line 739**: `unexpected token 'have'; expected command`
**Line 778**: `unexpected token 'have'; expected command`
**Line 923**: `unexpected identifier; expected command`

**Root cause:** All these are cascade failures from the unclosed proof at line 602.
The parser loses track of context and interprets subsequent definitions as malformed.

**Fix:** These will auto-resolve once line 602 is fixed.

---

### **Chunk 3: Lines 1138-1139, 1156** (Measurable space type mismatches)

#### **Lines 1138-1139**: Wrong measurable space inference

```lean
-- Inside proof of condExp_project_of_condIndep, in rectangle case
have hBpre : MeasurableSet (Z ⁻¹' B) := hBpre_m0
have hCpre : MeasurableSet (W ⁻¹' C) := hCpre_m0
```

**Errors:**
```
Line 1138: Type mismatch
  hBpre_m0 has type: @MeasurableSet Ω m0 (Z ⁻¹' B)
  but is expected to have type: @MeasurableSet Ω mZW (Z ⁻¹' B)

Line 1139: Type mismatch
  hCpre_m0 has type: @MeasurableSet Ω m0 (W ⁻¹' C)
  but is expected to have type: @MeasurableSet Ω mZW (W ⁻¹' C)
```

**Context:**
- `m0 := ‹MeasurableSpace Ω›` (ambient instance, line 1027)
- `mZW := MeasurableSpace.comap (fun ω => (Z ω, W ω)) inferInstance` (line 1031)
- `hBpre_m0 : @MeasurableSet Ω m0 (Z ⁻¹' B)` (line 1130)

**Issue:** Inside the rectangle case subproof, Lean infers `mZW` as the expected
measurable space, but `hBpre_m0` provides `m0`-measurability. While `m0` is the ambient
instance and should work everywhere, the local context expects `mZW`.

**Previous fix attempts:**
1. ✗ Direct assignment: `hBpre := hBpre_m0` (type mismatch)
2. ✗ Explicit annotation: `@MeasurableSet Ω inferInstance (...)` (still wrong context)
3. ✗ Using `simpa [m0]` to rewrite (rewrite fails to find pattern)

**Correct fix:** Need to explicitly convert or reprove with ambient measurability:
```lean
have hBpre : MeasurableSet (Z ⁻¹' B) :=
  hB.preimage hZ  -- Reprove directly with ambient measurable functions
have hCpre : MeasurableSet (W ⁻¹' C) :=
  hC.preimage hW
```

---

#### **Line 1156**: Wrong σ-algebra ordering

```lean
have haesm_ce : AEStronglyMeasurable (μ[f | mW]) μ :=
  hsm_ce_mW.mono hmW_le |>.aestronglyMeasurable
```

**Error:**
```
Type mismatch
  StronglyMeasurable.aestronglyMeasurable (StronglyMeasurable.mono hsm_ce_mW hmW_le)
has type: @AEStronglyMeasurable Ω ℝ ... m0 ?m.963 μ[f|mW] ?m.964
but is expected to have type: @AEStronglyMeasurable Ω ℝ ... mZW inst✝⁴ μ[f|mW] μ
```

**Context:**
- `hsm_ce_mW : @StronglyMeasurable Ω ℝ _ mW (μ[f | mW])`
- `hmW_le : mW ≤ m0` (line 1134)
- `hle : mW ≤ mZW` (line 1035, outer scope)

**Issue:** Using `hmW_le : mW ≤ m0` but the context expects `mZW`-measurability.
Should use `hle : mW ≤ mZW` from the outer scope.

**Fix:**
```lean
have haesm_ce : AEStronglyMeasurable (μ[f | mW]) μ :=
  hsm_ce_mW.mono hle |>.aestronglyMeasurable  -- Use hle, not hmW_le
```

---

## Fix Priority

### 🔴 **Critical** (blocks everything): Lines 554-602

1. **Line 554**: Fix `inferInstance` in `tendsto_condexp_L1` signature
2. **Lines 566-570**: Fix measure type in `approx_bounded_measurable`
3. **Line 602**: Complete or sorry the proof block

**Impact:** Blocks all downstream code, causes cascading parse errors

---

### 🟡 **Cascading** (auto-fix): Lines 609, 739, 778, 923

Will automatically resolve once line 602 is fixed (parser confusion).

---

### 🟢 **Independent** (separate proof): Lines 1138-1139, 1156

Can be fixed independently - different theorem (`condExp_project_of_condIndep`).

**Priority:** Lower - doesn't block the main scaffolding issues

---

## Recommended Approach

**Phase 1: Unblock parser (Lines 554-602)**
1. Fix helper lemma signatures (5 minutes)
2. Add `sorry` to close proof at line 602 (1 minute)
3. Verify cascading errors resolve (1 minute)

**Phase 2: Fix measurable space issues (Lines 1138-1139, 1156)**
1. Reprove `hBpre`/`hCpre` directly (2 minutes)
2. Fix `haesm_ce` to use correct ordering (1 minute)

**Total estimate:** 10-15 minutes to unblock compilation

---

## Related Files

- **Blocked by this file:** `ViaMartingale.lean` (can't import due to CondIndep errors)
- **Dependencies:** `CondExpHelpers.lean` (builds successfully with 3 sorries)
- **Status:** `CondExpHelpers.lean` linter warnings cleaned (commit 8dada01)
