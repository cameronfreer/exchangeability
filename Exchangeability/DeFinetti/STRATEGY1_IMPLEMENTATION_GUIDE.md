# Strategy 1 Bridge Implementation Guide

## Current Status (2025-11-16)

### Completed ✅
- h_meas (line 4043) proved via Strategy 2
- All Lp infrastructure in BirkhoffAvgCLM.lean complete
- `birkhoffAvgCLM_coe_ae_eq_function_avg` proved

### Remaining ⚠️
- Line 4065 (h_le): Needs bridge
- Line 4081 (h_toNorm): Needs bridge

## The Core Issue

ViaKoopman.lean uses **mathlib's `birkhoffAverage`** from `Mathlib.Dynamics.BirkhoffSum.Average`:

```lean
birkhoffAverage ℝ (koopman shift hσ) (fun f => f) n fL2
```

Our BirkhoffAvgCLM.lean provides **our own `birkhoffAvgCLM`**:

```lean
birkhoffAvgCLM (koopman shift hσ) n fL2
```

The problem: These two return Lp elements, but their coercions differ:
- `↑↑(birkhoffAverage ... (fun f => f) ...)` (coerce the result)
- `birkhoffAverage ... (fun f => ↑↑f) ...` (average coerced functions)

## Implementation Strategy

### Step 1: Understand mathlib's birkhoffAverage

**File to read**: `.lake/packages/mathlib/Mathlib/Dynamics/BirkhoffSum/Average.lean`

**Key questions**:
1. What is the definition of `birkhoffAverage`?
2. What are its type parameters?
3. How does `(fun f => f)` vs `(fun f => ↑↑f)` affect the result?

**Action**:
```bash
cd .lake/packages/mathlib
grep -A 20 "^def birkhoffAverage" Mathlib/Dynamics/BirkhoffSum/Average.lean
```

### Step 2: Prove Definitional Equality (if possible)

**Goal**: Prove `birkhoffAverage ℝ U (fun f => f) n fL2 = birkhoffAvgCLM U n fL2`

**Location**: Add to `Exchangeability/Ergodic/BirkhoffAvgCLM.lean` before line 270

**Code template**:
```lean
/-! ### Bridge to mathlib's birkhoffAverage -/

/-- mathlib's birkhoffAverage with identity function equals our birkhoffAvgCLM -/
lemma birkhoffAverage_eq_birkhoffAvgCLM
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (T : Ω → Ω) (hT_mp : MeasurePreserving T μ μ)
    (n : ℕ) (fL2 : Lp ℝ 2 μ) :
  Dynamics.birkhoffAverage ℝ (koopman T hT_mp) (fun f => f) n fL2 =
  birkhoffAvgCLM (koopman T hT_mp) n fL2 := by
  -- Unfold both definitions
  unfold Dynamics.birkhoffAverage birkhoffAvgCLM
  -- Check if they're definitionally equal
  -- If not, prove via calculation
  sorry
```

**Note**: This may require importing `Mathlib.Dynamics.BirkhoffSum.Average`

### Step 3: Prove A.E. Equality of Coercions

**Goal**: Bridge the two formulations

**Location**: Add to BirkhoffAvgCLM.lean after Step 2 lemma

**Code template**:
```lean
/-- Coercing birkhoffAverage result equals averaging coerced functions (a.e.) -/
lemma birkhoffAverage_coerce_eq_ae
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (T : Ω → Ω) (hT_meas : Measurable T) (hT_mp : MeasurePreserving T μ μ)
    (n : ℕ) (fL2 : Lp ℝ 2 μ) :
  (↑↑(Dynamics.birkhoffAverage ℝ (koopman T hT_mp) (fun f => f) n fL2) : Ω → ℝ) =ᵐ[μ]
  (fun ω => Dynamics.birkhoffAverage ℝ (koopman T hT_mp) (fun f => ↑↑f) n fL2 ω) := by
  -- Step 1: Rewrite LHS using birkhoffAverage_eq_birkhoffAvgCLM
  have h_eq : Dynamics.birkhoffAverage ℝ (koopman T hT_mp) (fun f => f) n fL2 =
              birkhoffAvgCLM (koopman T hT_mp) n fL2 :=
    birkhoffAverage_eq_birkhoffAvgCLM T hT_mp n fL2
  rw [h_eq]

  -- Step 2: Use birkhoffAvgCLM_coe_ae_eq_function_avg
  have h_coe := birkhoffAvgCLM_coe_ae_eq_function_avg T hT_meas hT_mp n fL2

  -- Step 3: Show RHS equals the function average
  -- This requires understanding how Dynamics.birkhoffAverage with (fun f => ↑↑f) works
  sorry
```

**Estimated difficulty**: Medium-High (depends on mathlib's birkhoffAverage definition)

### Step 4: Alternative - Direct Approach Without Bridge

**If Steps 2-3 are too complex**, use a.e. equality directly in ViaKoopman:

**At ViaKoopman line 4065**, instead of proving equality, use `eLpNorm_congr_ae`:

```lean
have h_le :
    ∫ ω, |(birkhoffAverage ℝ (koopman shift hσ) (fun f => f) n fL2 : Ω[α] → ℝ) ω
            - (condexpL2 (μ := μ) fL2 : Ω[α] → ℝ) ω| ∂μ
      ≤ (eLpNorm (fun ω => ...) 2 μ).toReal := by
  -- Convert integral using a.e. equality
  have h_ae : (fun ω => (birkhoffAverage ... (fun f => f) ...) ω - ...) =ᵐ[μ]
              (fun ω => (birkhoffAvgCLM ...) ω - ...) := by
    apply Filter.EventuallyEq.sub
    · -- Use birkhoffAvgCLM_coe_ae_eq_function_avg
      sorry
    · rfl
  rw [integral_congr_ae (h_ae.fun_comp _)]
  -- Now continue with eLpNorm
  sorry
```

**Estimated difficulty**: Medium (more direct, but messier)

## Decision Point

### Option A: Full Bridge (Clean, Reusable)
- **Time**: 2-3 hours
- **Benefits**: Clean abstraction, reusable lemmas, proper mathlib integration
- **Risks**: mathlib's birkhoffAverage may not align perfectly with birkhoffAvgCLM

### Option B: Direct A.E. Rewriting (Fast, Localized)
- **Time**: 1-1.5 hours
- **Benefits**: Faster, less dependency on mathlib internals
- **Risks**: Messier proofs, less reusable

## Recommended Next Steps

1. **Session 1** (30 min): Understand mathlib's birkhoffAverage
   ```bash
   # Read the definition
   cat .lake/packages/mathlib/Mathlib/Dynamics/BirkhoffSum/Average.lean

   # Search for related lemmas
   grep "birkhoffAverage" .lake/packages/mathlib/Mathlib/Dynamics/BirkhoffSum/*.lean
   ```

2. **Session 2** (1-2 hours): Choose approach (A or B) and implement
   - If definitions align: Implement Option A
   - If complex mismatch: Use Option B

3. **Session 3** (30 min): Apply to ViaKoopman lines 4065, 4081

## Files to Modify

1. `Exchangeability/Ergodic/BirkhoffAvgCLM.lean`:
   - Add import: `import Mathlib.Dynamics.BirkhoffSum.Average`
   - Add bridge lemmas (if Option A)

2. `Exchangeability/DeFinetti/ViaKoopman.lean`:
   - Fix line 4065 (h_le)
   - Fix line 4081 (h_toNorm)

## Success Criteria

✅ Line 4065 proof complete (no sorry)
✅ Line 4081 proof complete (no sorry)
✅ ViaKoopman builds without new errors
✅ All existing tests still pass

## Rollback Plan

If bridge approach fails:
1. Use Strategy 3 (axiomatize) as documented in BIRKHOFF_BRIDGE_STRATEGY.md
2. Add axiom for a.e. equality
3. Document for future resolution

## Time Estimates

| Approach | Discovery | Implementation | Testing | Total |
|----------|-----------|----------------|---------|-------|
| Option A | 30 min | 1.5-2 hours | 30 min | 2-3 hrs |
| Option B | 15 min | 1-1.5 hours | 15 min | 1.5-2 hrs |
| Axiom | 0 | 30 min | 15 min | 45 min |

---

**Created**: 2025-11-16
**Status**: Ready for implementation
**Recommended**: Start with Option B (direct approach) for faster resolution
