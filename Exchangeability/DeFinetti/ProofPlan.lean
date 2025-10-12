/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic), Cameron Freer

This file documents the concrete plan to eliminate ALL axioms from the de Finetti formalization
by using the Mean Ergodic Theorem + CE commutation approach.
-/

/-!
# Complete Proof Plan: Eliminating Axioms via Mean Ergodic Theorem

## Executive Summary

**Key Insight**: We can bypass ALL kernel independence axioms by proving factorization directly
from the Mean Ergodic Theorem + commutation of conditional expectation with Koopman operator.

**Result**: Converts 7 axioms → 0 axioms (modulo one Hilbert space lemma with known proof).

##  Dependency Picture (After Refactor)

### Only Two Analytic Ingredients Needed:

1. **Mean Ergodic Theorem** ✅ (already in mathlib and used)
2. **Commutation**: `condexpL2 ∘ koopman = condexpL2` on L² (straightforward Hilbert space proof)

### Everything Else Follows:

```
Mean Ergodic Theorem + Commutation
  ↓
Pair Factorization (block × singleton)
  ↓
Finite Product Factorization (by induction)
  ↓
Arbitrary Index Sets (by sorting)
  ↓
Indicator Bridge (immediate corollary)
  ↓
CommonEnding Integration
  ↓
FULL DE FINETTI THEOREM (no axioms!)
```

## Step-by-Step Implementation Plan

### Step 0: Quick Cleanups

- [x] Delete or document `axiom quantize_tendsto` (proved, never used)
- [ ] Note that `Kernel.IndepFun.comp` is already proved (lines 173-201)

### Step 1: Prove CE Commutes with Koopman

**Location**: Replace `axiom condexpL2_koopman_comm` (line 1046)

**Proof Strategy** (standard Hilbert space argument):
- P := condexpL2 is orthogonal projection onto S := fixedSubspace hσ
- U := koopman is linear isometry that fixes S pointwise
- For f = Pf + (f - Pf):
  * Pf ∈ S, so U(Pf) = Pf (definition of fixedSubspace)
  * (f - Pf) ⊥ S and U preserves orthogonality
  * Therefore P(Uf) = P(Pf) = Pf

**Implementation Notes**:
- Use `range_condexp_eq_fixedSubspace` to show P projects onto S
- Use `mem_fixedSubspace_iff` to show U fixes S pointwise
- Use `koopman_isometry` to access isometry properties
- Use `inner_condExpL2_left_eq_right` for orthogonality

**Dependencies**: Only lemmas already in the file

**Difficulty**: ~50 lines, straightforward once API is clear

### Step 2: Pair Factorization via MET (**KEY LEMMA**)

**Goal**: Prove for bounded measurable f, g : α → ℝ and any k ≥ 1:
```lean
μ[(f∘π₀)·(g∘πₖ) | ℐ] = μ[f∘π₀|ℐ]·μ[g∘π₀|ℐ]  a.s.
```
where ℐ = shiftInvariantSigma

**This replaces BOTH**:
- `condindep_pair_given_tail` (no kernel independence needed!)
- `kernel_integral_product_factorization`

**Proof Strategy** (purely ergodic theory + linearity/continuity):

1. **Constancy in k**: Let Hₖ := μ[(f∘π₀)·(g∘πₖ)|ℐ]
   - Using `condexp_precomp_iterate_eq`: CE commutes with shift
   - ℐ-measurable functions are shift-invariant
   - Therefore Hₖ₊₁ = Hₖ a.e. for all k

2. **Cesàro average identity**:
   Since Hₖ are all equal:
   ```
   H₁ = (1/n)∑ₖ Hₖ = μ[(f∘π₀)·Aₙ|ℐ]
   ```
   where Aₙ := (1/n)∑ₖ₌₁ⁿ g(ωₖ)

3. **Apply Mean Ergodic Theorem**:
   - Aₙ = (1/n)∑ₖ Uᵏ(g∘π₀) where U = koopman
   - By MET: Aₙ → P(g∘π₀) in L²
   - Therefore Aₙ → P(g∘π₀) in L¹

4. **Continuity of CE in L¹**:
   - CE is 1-Lipschitz: ‖μ[Z|ℐ] - μ[W|ℐ]‖₁ ≤ ‖Z - W‖₁
   - Therefore: μ[(f∘π₀)·Aₙ|ℐ] → μ[(f∘π₀)·P(g∘π₀)|ℐ]

5. **Pull-out property**:
   - P(g∘π₀) is ℐ-measurable and bounded
   - μ[(f∘π₀)·P(g∘π₀)|ℐ] = P(g∘π₀)·μ[f∘π₀|ℐ]

**Implementation**:
```lean
private lemma condexp_pair_factorization_MET
    (hσ : MeasurePreserving shift μ μ)
    (f g : α → ℝ)
    (hf_meas : Measurable f) (hf_bd : ∃ C, ∀ x, |f x| ≤ C)
    (hg_meas : Measurable g) (hg_bd : ∃ C, ∀ x, |g x| ≤ C) :
  μ[(fun ω => f (ω 0) * g (ω 1)) | shiftInvariantSigma (α := α)]
    =ᵐ[μ]
  (fun ω => μ[fun ω => f (ω 0) | shiftInvariantSigma (α := α)] ω
          * μ[fun ω => g (ω 0) | shiftInvariantSigma (α := α)] ω) := by
  -- Step 1: Constancy in k (use condexp_precomp_iterate_eq)
  have const_in_k : ∀ k, H_{k+1} = H_k a.e. := ...

  -- Step 2: Cesàro identity
  have cesaro_id (n) : H₁ = μ[(f∘π₀)·Aₙ|ℐ] := ...

  -- Step 3: MET convergence
  have met_conv : Aₙ → P(g∘π₀) in L¹ := ...

  -- Step 4: CE continuity
  have ce_cont : μ[(f∘π₀)·Aₙ|ℐ] → μ[(f∘π₀)·P(g∘π₀)|ℐ] := ...

  -- Step 5: Pull-out
  have pullout : μ[(f∘π₀)·P(g∘π₀)|ℐ] = P(g∘π₀)·μ[f∘π₀|ℐ] := ...

  -- Combine
  exact ...
```

**Helper Lemmas Needed**:
- `condExp_L1_lipschitz`: ‖μ[Z|ℐ] - μ[W|ℐ]‖₁ ≤ ‖Z - W‖₁
- `condExp_mul_pullout`: μ[Z·Y|ℐ] = Z·μ[Y|ℐ] when Z is ℐ-measurable

**Dependencies**:
- `condexp_precomp_iterate_eq` ✅ (already proved, line 1429)
- `birkhoffAverage_tendsto_condexp` ✅ (line 992, uses MET)
- L¹-Lipschitz property (needs proof or mathlib lemma)
- Pull-out property (standard, ~10 lines or mathlib lemma)

**Difficulty**: ~100 lines (mechanical once helpers are in place)

**Impact**: **Eliminates 2 axioms** (the deepest ones!)

### Step 3: Finite Product Factorization by Induction

**Goal**: Replace `condexp_product_factorization_ax` (line 433)

**Proof**: Straightforward induction using Step 2

```lean
theorem condexp_product_factorization
    (hσ : MeasurePreserving shift μ μ)
    (m : ℕ) (fs : Fin m → α → ℝ)
    (hmeas : ∀ k, Measurable (fs k))
    (hbd : ∀ k, ∃ C, ∀ x, |fs k x| ≤ C) :
  μ[fun ω => ∏ k, fs k (ω k) | shiftInvariantSigma (α := α)]
    =ᵐ[μ]
  (fun ω => ∏ k, ∫ x, fs k x ∂(ν (μ := μ) ω)) := by
  induction m with
  | zero =>
      -- base: CE[1|ℐ] = 1
      simp
  | succ m IH =>
      -- inductive step: apply Step 2 with X = ∏_{k<m} ... and g = fs (Fin.last m)
      have block_singleton := condexp_pair_factorization_MET ...
      -- rewrite using IH and identicalConditionalMarginals_integral
      ...
```

**Dependencies**: Step 2 + existing helpers

**Difficulty**: ~30 lines (mostly `Finset` algebra)

**Impact**: **Eliminates 1 axiom**

### Step 4: Arbitrary Index Maps

**Goal**: Replace `condexp_product_factorization_general` (line 474)

**Proof**: Sort indices and reduce to Step 3

```lean
theorem condexp_product_factorization_general
    (hσ : MeasurePreserving shift μ μ)
    (m : ℕ) (fs : Fin m → α → ℝ) (k : Fin m → ℕ)
    (hmeas : ∀ i, Measurable (fs i))
    (hbd : ∀ i, ∃ C, ∀ x, |fs i x| ≤ C) :
  μ[fun ω => ∏ i, fs i (ω (k i)) | shiftInvariantSigma (α := α)]
    =ᵐ[μ]
  (fun ω => ∏ i, ∫ x, fs i x ∂(ν (μ := μ) ω)) := by
  -- Let σ be permutation such that k ∘ σ is strictly increasing
  -- Rewrite: ∏ᵢ fs i (ω_{k i}) = ∏ᵢ fs_{σ⁻¹ i} (ω_{(k∘σ) i})
  -- Apply Step 3 to right-hand side
  -- Product of integrals invariant under permutation
  ...
```

**Dependencies**: Step 3 + `Fin.sort` utilities

**Difficulty**: ~20 lines (mostly permutation algebra)

**Impact**: **Eliminates 1 axiom**

### Step 5: Indicator Bridge

**Goal**: Convert `indicator_product_bridge_ax` to theorem (line 1155)

**Proof**: Immediate application of Step 4 with fᵢ = 1_{Bᵢ}

Already implemented correctly, just remove "axiom" keyword!

**Impact**: **Eliminates 1 axiom**

### Step 6: Final Assembly

**Goal**: Convert `exchangeable_implies_ciid_modulo_bridge_ax` to theorem (line 1179)

**Proof**: With Step 5 proved, invoke `CommonEnding.conditional_iid_from_directing_measure`

Already implemented correctly, just remove "axiom" keyword!

**Impact**: **Eliminates 1 axiom**

## Summary of Changes

### Axioms Eliminated:

1. ~~`condindep_pair_given_tail`~~ → No longer needed (bypassed by Step 2)
2. ~~`kernel_integral_product_factorization`~~ → No longer needed (bypassed by Step 2)
3. ~~`condexp_product_factorization_ax`~~ → **Theorem** (Step 3)
4. ~~`condexp_product_factorization_general`~~ → **Theorem** (Step 4)
5. ~~`indicator_product_bridge_ax`~~ → **Theorem** (Step 5)
6. ~~`exchangeable_implies_ciid_modulo_bridge_ax`~~ → **Theorem** (Step 6)
7. `condexpL2_koopman_comm` → **Theorem** (Step 1, ~50 lines of standard Hilbert space)

### Axioms Remaining After Refactor:

**ZERO** (modulo Step 1 which is straightforward Hilbert space)

### Total LOC Estimate:

- Step 1: ~50 lines (Hilbert space)
- Step 2: ~100 lines (key lemma, mechanical)
- Step 3: ~30 lines (induction)
- Step 4: ~20 lines (permutations)
- Steps 5-6: ~5 lines (remove "axiom")

**Total**: ~200 lines to eliminate all axioms!

## Implementation Order:

1. **Step 2 first** (pair factorization) - this is the breakthrough
2. Then Steps 3-6 (straightforward consequences)
3. Finally Step 1 (Hilbert space cleanup, or keep as axiom temporarily)

## Helper Lemmas Needed (from mathlib or prove):

1. **L¹-Lipschitz for CE**: `‖μ[Z|ℐ] - μ[W|ℐ]‖₁ ≤ ‖Z - W‖₁`
   - Proof: Jensen + tower property (~10 lines)

2. **Pull-out for ℐ-measurable factors**: `μ[Z·Y|ℐ] = Z·μ[Y|ℐ]`
   - Mathlib has variants, or prove by testing against ℐ-indicators

3. **MET in L¹**: Birkhoff averages converge in L¹
   - L² convergence + bounded ⇒ L¹ convergence

All of these are either in mathlib or ~10-20 line proofs.

## Why This Works:

**No kernel independence needed!** The key insight is:
- Kernel independence requires deep ergodic decomposition theory (Choquet, extremal measures)
- But factorization can be proved DIRECTLY from:
  * Mean Ergodic Theorem (already have it)
  * Commutation of CE with shift (easy Hilbert space)
  * Basic measure theory (pull-out, L¹-Lipschitz)

This is a **much shorter path** to the full theorem!

## Next Steps:

1. Implement helper lemmas (L¹-Lipschitz, pull-out)
2. Implement Step 2 (pair factorization via MET)
3. Implement Steps 3-6 (mechanical consequences)
4. Optional: Complete Step 1 (or keep as axiom with proof sketch)

Once Steps 2-6 are done, we have **FULL DE FINETTI with essentially no axioms!**

-/
