# Cauchy-Schwarz in IntegrationHelpers - Research Notes

## Goal

Complete the `abs_integral_mul_le_L2` lemma in `Probability/IntegrationHelpers.lean`:

```lean
lemma abs_integral_mul_le_L2
    {μ : Measure Ω} {f g : Ω → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |∫ ω, f ω * g ω ∂μ|
      ≤ (∫ ω, (f ω) ^ 2 ∂μ) ^ (1/2 : ℝ) * (∫ ω, (g ω) ^ 2 ∂μ) ^ (1/2 : ℝ)
```

## Mathematical Content

This is the Cauchy-Schwarz inequality for L² functions, which is a special case of Hölder's inequality with p = q = 2.

**Standard proof approach:**
1. Use Hölder's inequality with conjugate exponents p = q = 2
2. Express L² norms as `(∫ f² dμ)^(1/2)`
3. Derive the Cauchy-Schwarz bound

## Mathlib API Search

### Attempted Approaches

1. **Direct Hölder search**: Looked for `integral_mul_le_Lp_mul_Lq` or similar
   - Not found in expected locations

2. **L² inner product**: Searched for `L2.inner_def`, `inner_mul_le_norm_mul_norm`
   - Inner product approach might work but requires different setup

3. **MemLp.mul**: Found `MemLp.mul` with `HolderTriple` type class
   - Located in `Mathlib/MeasureTheory/Function/LpSeminorm/CompareExp.lean`
   - Requires `[HolderTriple p q r]` instance

### Key Finding: HolderTriple

```lean
theorem MemLp.mul (hf : MemLp f q μ) (hφ : MemLp φ p μ) [hpqr : HolderTriple p q r] :
    MemLp (f * φ) r μ
```

For Cauchy-Schwarz, we need `p = q = 2` and `r = 1` (since 1/2 + 1/2 = 1).

### Potential Solution Path

The proof likely requires:
1. Showing there's a `HolderTriple 2 2 1` instance
2. Using `MemLp.mul` to show `f * g ∈ L¹(μ)`
3. Bounding `∫ |f·g| dμ` using snorm inequalities
4. Converting snorm bounds to integral bounds

## Blocker

**Type system complexity**: The mathlib Hölder inequality API uses:
- `ENNReal` exponents and norms (`snorm`)
- `HolderTriple` / `HolderConjugate` type classes  
- Complex conversions between `snorm`, `MemLp`, and actual integrals

**Time estimate**: 2-4 hours of careful API research and proof development.

## Current Status

**Decision**: Keep `sorry` as documented blocker, defer completion.

**Rationale**:
- Other 3 integration helpers work and provide value (~54 call sites)
- Cauchy-Schwarz can be proven directly where needed
- Better to unblock other work than spend hours on API archaeology
- File builds successfully with `sorry` (allows rest of project to proceed)

## Recommended Next Steps

### Option A: Mathlib Community Help
Post on Zulip asking for the canonical way to prove Cauchy-Schwarz from `MemLp 2`.

### Option B: Direct Proof
Prove directly using:
```lean
∫ |f·g| ≤ snorm (f*g) 1 μ
snorm (f*g) 1 μ ≤ snorm f 2 μ * snorm g 2 μ  -- Hölder
snorm f 2 μ = (∫ f² dμ)^(1/2)               -- Definition
```

### Option C: Inner Product Approach
If `f, g ∈ L²(μ)`, use inner product Cauchy-Schwarz:
```lean
|⟨f, g⟩| ≤ ‖f‖ * ‖g‖
```
Then show `⟨f, g⟩ = ∫ f·g dμ` and `‖f‖² = ∫ f² dμ`.

## Files to Investigate

1. `Mathlib/MeasureTheory/Function/LpSeminorm/CompareExp.lean` - Hölder triple
2. `Mathlib/MeasureTheory/Function/L2Space.lean` - L² inner products
3. `Mathlib/Analysis/InnerProductSpace/Basic.lean` - Cauchy-Schwarz for inner products

## Impact Assessment

**Low priority blocker**:
- IntegrationHelpers provides value without this lemma
- No other proofs currently blocked by this sorry
- Can be completed incrementally without blocking project progress

**Updated**: 2025-10-19
