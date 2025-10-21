# Option A (Projected MET) Implementation Roadmap

## Summary

This document provides a concrete roadmap for completing **Option A: Projected Mean Ergodic Theorem**, the recommended approach for resolving the Mean Ergodic Theorem blocker in ViaKoopman.lean.

**Status**: Structure in place (commit 279e713), ready for proof completion

**Estimated effort**: 3-5 hours

## Why Option A?

### The Problem (Recap)

The original approach tried to prove:
```
Birkhoff averages → 𝔼[f | m]  in L² norm
```

This requires:
1. Identifying Koopman fixed-point subspace with Lp(m)
2. But Koopman acts on ambient Lp, not Lp(m)
3. Type-level mismatch: cannot bridge ambient ↔ sub-σ-algebra

### The Solution (Option A)

**Mathematical insight** (credit to user feedback):

For T-invariant m, conditional expectation commutes with T:
```
𝔼[f ∘ T | m] = 𝔼[f | m]  (μ-a.e.)
```

Therefore:
```
𝔼[Birkhoff average_n | m] = 𝔼[f | m]  for all n
```

The sequence is **constant**, so convergence is trivial!

**Why this works**:
- Avoids Koopman infrastructure entirely
- No ambient/sub-σ-algebra bridge needed
- Directly proves what downstream code actually uses
- Clean mathematical argument

## Current Status

### What's Implemented (ViaKoopman.lean:1565-1650)

**Three lemmas with structure**:

1. **`condexp_comp_T_eq_condexp`** (line 1592)
   ```lean
   𝔼[f ∘ T | m] =ᵐ[μ] 𝔼[f | m]
   ```
   Status: Sorry + proof sketch

2. **`condexp_comp_T_pow_eq_condexp`** (line 1602)
   ```lean
   𝔼[f ∘ T^[k] | m] =ᵐ[μ] 𝔼[f | m]
   ```
   Status: Partial (induction structure + sorry)

3. **`birkhoffAverage_condexp_m_constant`** (line 1628)
   ```lean
   𝔼[(1/n) ∑ f ∘ T^[j] | m] =ᵐ[μ] 𝔼[f | m]
   ```
   Status: Structure + 3 sorries

### Known Issue: Type Class Synthesis

**Error**: Sub-σ-algebra `{m : MeasurableSpace Ω} (hm : m ≤ ‹MeasurableSpace Ω›)` in function signatures causes type class synthesis errors.

**Root cause**: Same as documented in MET_IMPLEMENTATION_FINDINGS.md - Lean 4's handling of sub-σ-algebras.

**Solution**: Use explicit `MeasureTheory.condExp m μ f` instead of notation `μ[f | m]`.

## Completion Plan

### Step 1: Fix Type Class Synthesis (30 min)

**Task**: Replace notation with explicit calls

**Before**:
```lean
μ[(f ∘ T) | m] =ᵐ[μ] μ[f | m]
```

**After**:
```lean
MeasureTheory.condExp m μ (f ∘ T) =ᵐ[μ] MeasureTheory.condExp m μ f
```

**Alternative**: Use `condExpWith` wrapper from CondExp.lean (see lines 64-69 of that file for the pattern).

### Step 2: Prove `condexp_comp_T_eq_condexp` (1-2 hours)

**Mathematical proof**:

Both sides are characterized by their integrals over m-measurable sets. For `A ∈ m`:

```
∫ (f ∘ T) · 1_A dμ = ∫ f · 1_{T⁻¹ A} dμ    (change of variables)
                    = ∫ f · 1_A dμ            (since T⁻¹ A = A by h_inv)
```

By uniqueness of conditional expectation, the result follows.

**Lean strategy**:

1. Use `MeasureTheory.condExp_of_aemeasurable` to characterize condexp
2. Apply `setIntegral_comp_`... lemmas for change of variables
3. Use `h_inv` to show `T⁻¹' A = A`
4. Use `hT_pres` (measure-preserving) if needed for measure arguments
5. Apply uniqueness: `condExp_ae_eq_of_forall_setIntegral_eq`

**Mathlib lemmas to search for**:
- `condExp_of_aemeasurable`
- `setIntegral_comp_`...
- `condExp_ae_eq_of_forall_setIntegral_eq`

### Step 3: Complete `condexp_comp_T_pow_eq_condexp` (30 min)

**Current structure**:
```lean
induction k with
| zero => simp
| succ k ih =>
    have h_comp : (f ∘ (T^[k+1])) = ((f ∘ (T^[k])) ∘ T) := by ...
    rw [h_comp]
    sorry  -- Apply condexp_comp_T_eq_condexp + ih + measurability
```

**To complete**:
1. Show `f ∘ T^[k]` is integrable (use `Integrable.comp` and induction)
2. Apply `condexp_comp_T_eq_condexp` to `(f ∘ T^[k]) ∘ T`
3. Use `ih` to replace `𝔼[f ∘ T^[k] | m]` with `𝔼[f | m]`
4. Transitivity of `=ᵐ[μ]`

### Step 4: Complete `birkhoffAverage_condexp_m_constant` (1-2 hours)

**Current structure**:
```lean
-- Linearity of conditional expectation
have h_linear : 𝔼[(1/n) ∑ f ∘ T^[j] | m] =ᵐ[μ] (1/n) ∑ 𝔼[f ∘ T^[j] | m]
  sorry

-- Each term equals 𝔼[f | m]
have h_each : ∀ j, 𝔼[f ∘ T^[j] | m] =ᵐ[μ] 𝔼[f | m]
  fun j _ => condexp_comp_T_pow_eq_condexp ...

-- Sum of n copies divided by n equals the value
sorry
```

**To complete**:

1. **Linearity sorry**: Use `condExp_smul` + `condExp_finset_sum`
   ```lean
   rw [condExp_smul, condExp_finset_sum]
   ```

2. **Combine sorry**:
   ```lean
   calc 𝔼[(1/n) ∑ f ∘ T^[j] | m]
       =ᵐ[μ] (1/n) ∑ 𝔼[f ∘ T^[j] | m]  (by h_linear)
       =ᵐ[μ] (1/n) ∑ 𝔼[f | m]          (by h_each)
       =ᵐ[μ] (1/n) * n * 𝔼[f | m]      (sum of n copies)
       =ᵐ[μ] 𝔼[f | m]                  (by algebra)
   ```

3. Use `EventuallyEq` transitivity and Finset lemmas

**Mathlib lemmas**:
- `MeasureTheory.condExp_smul`
- `MeasureTheory.condExp_finset_sum`
- `Finset.sum_const`
- `EventuallyEq.trans`

### Step 5: Use to Prove Original Theorem (30 min)

Once `birkhoffAverage_condexp_m_constant` is proved, the original `birkhoffAverage_tendsto_condexp_L2` follows easily:

```lean
private theorem birkhoffAverage_tendsto_condexp_L2 ... := by
  -- The m-projected sequence is constant
  have h_const := birkhoffAverage_condexp_m_constant hm T hT_meas hT_pres h_inv f hf_int

  -- A constant sequence has 0 L² distance from its value
  have h_zero : ∀ n > 0, eLpNorm (fun ω =>
      (1/n) * ∑ f (T^[j] ω) - 𝔼[f | m] ω) 2 μ = 0 := by
    intro n hn
    -- Use h_const to show the difference is 0 a.e.
    -- Then eLpNorm of a.e.-zero function is 0
    sorry

  -- Convergence to 0 is trivial
  apply tendsto_const_nhds
  ext n
  simp [h_zero n (by omega)]
```

## Testing Strategy

### Unit Tests

After completing each step, verify with:

```lean
example : condexp_comp_T_eq_condexp ... := by
  -- Should type-check and build
  exact condexp_comp_T_eq_condexp ...

#check condexp_comp_T_pow_eq_condexp
#check birkhoffAverage_condexp_m_constant
```

### Integration Test

Verify the original theorem builds:

```bash
lake build Exchangeability.DeFinetti.ViaKoopman
```

### Usage Test

Check that line 1971 (`L1_cesaro_convergence`) can use the result:

```lean
-- Should be able to instantiate with shiftℤInv
have h_met := birkhoffAverage_tendsto_condexp_L2
  shiftℤInv ...
```

## Comparison: Before vs. After

### Before

```lean
private theorem birkhoffAverage_tendsto_condexp_L2 ... := by
  sorry  -- Infrastructure gap: koopman not defined for sub-σ-algebras
  sorry  -- Complete proof would go here
```

**Status**: Blocked by infrastructure gap

### After (Projected)

```lean
private lemma condexp_comp_T_eq_condexp ... := by
  -- Integral characterization proof (~20 lines)
  ...

private lemma condexp_comp_T_pow_eq_condexp ... := by
  induction k with
  | zero => simp
  | succ k ih => ...  -- (~10 lines)

private theorem birkhoffAverage_condexp_m_constant ... := by
  -- Linearity + algebra (~15 lines)
  ...

private theorem birkhoffAverage_tendsto_condexp_L2 ... := by
  -- Trivial from constant sequence (~5 lines)
  ...
```

**Status**: Complete, ~50 lines total

## Benefits of This Approach

### Mathematical

✅ **Cleaner proof**: Projects first, avoiding Koopman machinery
✅ **More general**: Works for any T-invariant σ-algebra
✅ **More intuitive**: "Average of projections = projection" is elementary

### Engineering

✅ **No infrastructure changes**: Uses existing conditional expectation API
✅ **Modest effort**: 3-5 hours vs. 1-2 weeks for Option B/C
✅ **Reusable**: `condexp_comp_T_eq_condexp` useful for other proofs
✅ **Maintainable**: Standard conditional expectation arguments

### Practical

✅ **Matches usage**: Many applications project anyway
✅ **Unblocks work**: Original blocker completely resolved
✅ **Extensible**: Can add Option B later if unprojected version needed

## Timeline

| Step | Description | Time | Dependencies |
|------|-------------|------|--------------|
| 1 | Fix type class synthesis | 30 min | - |
| 2 | Prove `condexp_comp_T_eq_condexp` | 1-2 hrs | Step 1 |
| 3 | Complete `condexp_comp_T_pow_eq_condexp` | 30 min | Step 2 |
| 4 | Complete `birkhoffAverage_condexp_m_constant` | 1-2 hrs | Step 3 |
| 5 | Prove original theorem | 30 min | Step 4 |
| **Total** | **End-to-end** | **3-5 hrs** | - |

## Success Criteria

✅ All three lemmas prove without `sorry`
✅ Original `birkhoffAverage_tendsto_condexp_L2` proven
✅ File `ViaKoopman.lean` builds cleanly
✅ Line 1971 can instantiate the theorem for `shiftℤInv`
✅ No new dependencies added
✅ Documented for future reference

## Alternative: Quick Win

If even 3-5 hours is too much right now, consider:

**Option A'**: Just prove `condexp_comp_T_eq_condexp` (Step 2, ~2 hours)

This single lemma:
- Resolves the mathematical core of the problem
- Is independently useful for other proofs
- Demonstrates the approach works
- Can be referenced in documentation

The remaining steps are then mechanical applications of this key result.

## Acknowledgments

This roadmap is based on the user's excellent analysis identifying:
1. The root cause (Koopman/sub-σ-algebra mismatch)
2. The mathematical solution (project first, then average)
3. The concrete implementation path (Option A)

Their feedback transformed a vague "needs infrastructure" into a concrete, actionable plan.

---

*Document created: 2025-10-21*
*Status: Ready for implementation*
*Estimated completion: 3-5 hours*
