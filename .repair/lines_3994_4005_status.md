# Status: Lines 3994 & 4005 - Hölder Inequality Sorries

## Current Status

**Lines 3986 & 3998**: Reverted to sorries with clear documentation.

## What We Tried

### Attempt 1: Direct snorm monotonicity approach
**Goal**: Prove `∫|f| ≤ (eLpNorm f 2 μ).toReal` using `snorm_le_snorm_of_exponent_le`

**What happened**:
- Successfully found the relevant lemmas:
  - `MeasureTheory.snorm_one_eq_lintegral_nnnorm` - converts integral to snorm 1
  - `MeasureTheory.snorm_le_snorm_of_exponent_le` - snorm p ≤ snorm q when p ≤ q on finite measure
  - `Lp.norm_toLp` - converts eLpNorm to Lp norm

**Why it failed**:
1. **Coercion type mismatch**: When defining `let g := birkhoffAverage ... - condexpL2 ...`, Lean treats:
   - `g : Lp ℝ 2 μ` (the Lp element)
   - `(g : Ω[α] → ℝ)` (the coerced function)

   But `h_meas` expects `(birkhoffAverage ... : Ω[α] → ℝ) - (condexpL2 ... : Ω[α] → ℝ)`, which Lean cannot unify with `(g : Ω[α] → ℝ)`.

2. **Lambda coercion issues**: The expressions involve:
   - `(fun f => f)` in birkhoffAverage (identity on Lp)
   - `(fun f => ↑↑f)` in type inference (coercion from Lp to functions)

   These are not definitionally equal, leading to type mismatches in `h_le`.

3. **`snorm_ne_top` complexity**: The `|>.resolve_right (Lp.memℒp g).snorm_ne_top` pattern failed because:
   - `snorm_ne_top` returns `snorm f p μ ≠ ∞ ∨ f =ᵐ[μ] 0`
   - We need to resolve the right disjunct, but `(Lp.memℒp g).snorm_ne_top` doesn't have the right type

## What We Learned

### Key Lemmas Found (that should work in principle)
1. **`MeasureTheory.snorm_le_snorm_of_exponent_le`**: For finite measures, `snorm f p μ ≤ snorm f q μ` when `p ≤ q`
2. **`MeasureTheory.snorm_one_eq_lintegral_nnnorm`**: Converts L¹ norm to integral
3. **`Lp.norm_toLp`**: Converts eLpNorm of a function to the Lp norm of the element
4. **`Lp.aestronglyMeasurable`**: Any Lp element, when coerced to a function, is AEStronglyMeasurable

### Root Cause
The fundamental issue is the **coercion mismatch** between:
- **Lp-level operations**: `birkhoffAverage ℝ (koopman ...) (fun f => f) n fL2` returns an `Lp ℝ 2 μ` element
- **Function-level expectations**: Type inference expects `(fun f => ↑↑f)` which returns a function directly

This is exactly the issue documented in `.repair/line3974_analysis.md` - we need to prove that coercion commutes with birkhoffAverage operations.

## Recommended Fix Strategy

### Option A: Prove coercion commutation lemma (harder, more general)
Prove:
```lean
lemma birkhoffAvg_coe_commutes (n : ℕ) (fL2 : Lp ℝ 2 μ) :
  ((birkhoffAverage ℝ (koopman shift hσ) (fun f => f) n) fL2 : Ω[α] → ℝ)
    =ᵐ[μ]
  (birkhoffAverage ℝ (koopman shift hσ) (fun f => ↑↑f) n fL2)
```

Then use this to bridge the coercion gap.

### Option B: Work entirely at function level (recommended in PRIORITY_NEXT_STEPS.md)
Rewrite the entire proof to use `birkhoffAvgCLM` from `BirkhoffAvgCLM.lean`, computing:
```lean
((birkhoffAvgCLM (koopman shift hσ) n) fL2 : Ω[α] → ℝ)
```

This avoids the `(fun f => f)` vs `(fun f => ↑↑f)` issue entirely.

### Option C: Use mathlib's integral-norm inequality directly (simplest short-term fix)
Find and apply a direct lemma like:
```lean
integral_abs_le_snorm : ∫ x, |f x| ∂μ ≤ (snorm f p μ).toReal
```

This may exist in a more specific form for probability measures.

## Next Steps

1. **Check if Option C lemma exists**: Search mathlib for `integral.*abs.*snorm` or similar
2. **If not, implement Option B**: Use the CLM machinery we already built
3. **If all else fails, use Option A**: Prove the coercion commutation lemma

## Files Affected

- `ViaKoopman.lean:3976-3998` - The two sorry blocks
- `BirkhoffAvgCLM.lean` - CLM infrastructure (already built, line 3972 used it successfully)
- `.repair/line3974_analysis.md` - Root cause analysis of coercion mismatch
- `.repair/PRIORITY_NEXT_STEPS.md` - Strategic guidance (recommends Option B)
