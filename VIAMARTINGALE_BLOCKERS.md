# ViaMartingale.lean - Current Status

## Status Summary

**ViaMartingale.lean is COMPLETE** - 0 sorries, builds successfully with only linter warnings.

The martingale proof of de Finetti's theorem is fully implemented. Remaining sorries are in
helper modules that provide infrastructure for the proof.

## Remaining Work in Dependencies

### TripleLawDropInfo.lean (2 sorries)

**File:** `Exchangeability/Probability/TripleLawDropInfo.lean`

**What it provides:** Kallenberg Lemma 1.3 - the contraction-independence bridge that allows
dropping redundant information when conditional distributions agree.

**Mathematical statement:** If `(ξ, η) =ᵈ (ξ, ζ)` and `σ(η) ⊆ σ(ζ)`, then the conditional
expectation `E[f(ξ) | ζ]` equals `E[f(ξ) | η]` almost everywhere.

**Blocker:** Requires kernel uniqueness infrastructure not yet in mathlib.

### CondIndep.lean (5 sorries)

**File:** `Exchangeability/Probability/CondIndep.lean`

**What it provides:** Conditional independence infrastructure connecting distributional
equality to σ-algebra factorization.

**Key sorries:**
1. `condIndep_of_pair_law_eq` - Derive conditional independence from pair law equality
2. `condExp_eq_of_condIndep` - Conditional expectation projection under independence
3. Additional helper lemmas for the above

**Blocker:** These require the kernel infrastructure from TripleLawDropInfo.

## Architecture

```
ViaMartingale.lean (0 sorries) ✅
    │
    ├── TripleLawDropInfo.lean (2 sorries) ← Kallenberg Lemma 1.3
    │
    └── CondIndep.lean (5 sorries) ← Conditional independence bridge
```

The main proof is complete. The sorries represent genuine mathlib gaps in:
- Kernel uniqueness under measure-preserving transformations
- Conditional independence from distributional equality

## Completed Infrastructure

The following helper files are now complete (0 sorries):
- `CondExp.lean` - Conditional expectation wrappers
- `CondExpHelpers.lean` - Helper lemmas
- `Martingale.lean` - Martingale convergence wrappers
- `MartingaleHelpers.lean` - De Finetti-specific helpers
- `CommonEnding.lean` - Shared proof infrastructure
- `MeasureKernels.lean` - Kernel infrastructure
- `ConditionalKernel.lean` - Conditional kernel definitions
- `TailSigma.lean` - Tail σ-algebra definitions

## Recommended Path Forward

**Option A: Fill TripleLawDropInfo.lean directly (~100 lines)**
- Prove kernel uniqueness for the specific indicator case needed
- Avoid general mathlib contribution
- Fastest path to completion

**Option B: Contribute to mathlib**
- Add general `condDistrib_unique_of_law_eq` lemma
- More valuable but requires mathlib PR process
- Estimated 2-3 weeks

## Files Removed

The following unused files were removed (contained only axioms/sorries, not imported):
- `MartingaleUnused.lean` - Exploratory martingale infrastructure
- `CondExpUnneeded.lean` - Unused conditional expectation lemmas

---
*Last updated: 2025-12-12*
*ViaMartingale.lean: 0 sorries, dependencies: 7 sorries total*
