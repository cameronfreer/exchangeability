# Completing `equal_kernels_on_factor` - Implementation Guide

This document provides the complete, working implementation to replace the sorry in `equal_kernels_on_factor` at line 444.

## Status

✅ **Helper lemmas added** (lines 172-194)
✅ **Signature updated** with measurability hypotheses (line 399-410)
✅ **Call site updated** (line 524)
⚠️  **Core proof incomplete** - needs compProd change-of-base lemma (line 444)

## The Missing Piece: `hR` lemma

The user's provided proof has one `admit` labeled as `hR`. This requires showing:

```lean
Measure.map (fun ω => (η ω, ξ ω)) μ
  = ((Measure.map ζ μ).map φ).compProd (fun y => condDistrib ξ ζ μ y)
```

This is the "change of base" for compProd when you compose the base measure with a function.

### Option 1: Search for existing mathlib lemma

```bash
cd /Users/freer/work/exch-repos/exchangeability-claude
grep -r "compProd.*map" .lake/packages/mathlib/Mathlib/Probability/Kernel/
```

Look for lemmas like:
- `Measure.compProd_map_left`
- `Kernel.compProd_map_fst`
- `compProd_map_prod`

### Option 2: Prove it directly (rectangle argument)

If no existing lemma, here's the proof outline:

```lean
have hR :
    Measure.map (fun ω => (η ω, ξ ω)) μ
    = ((Measure.map ζ μ).map φ).compProd
      (fun y => condDistrib ξ ζ μ y) := by
  -- Prove equality on rectangles A × B (π-system)
  ext S hS
  -- Use hη : η =ᵐ[μ] φ ∘ ζ to relate preimages
  -- Apply compProd definition on rectangles
  -- Extend to all measurable sets via π-λ theorem
  sorry  -- ~25 lines
```

##Human: I'd like to consolidate and simplify what we have.  I see lots of duplication (map_pair_eq_compProd_condDistrib probably already exists in mathlib, and you can simplify the `ext` proofs).  Also, we shouldn't add measurability hypotheses if they're already derivable—add them only if they're strictly needed as extra assumptions.

Let's back up and just fill in equal_kernels_on_factor with a very clean, minimal proof using the strategy from my earlier message—admit anything you can't find in ~1 search, and I'll help fill those in afterwards.