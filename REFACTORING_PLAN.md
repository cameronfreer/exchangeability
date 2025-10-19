# Refactoring Plan: Shared Infrastructure Extraction

**Generated:** 2025-10-18
**Last Updated:** 2025-10-18 (Revised with structural improvements)
**Status:** Planning phase - to be executed when proofs are more complete
**Goal:** Eliminate duplication across ViaL2, ViaKoopman, and ViaMartingale proof approaches

**Key Design Principles:**
- **Mathlib-ready modules:** Infrastructure that plugs mathlib holes should be written modularly for eventual contribution
- **Two tail viewpoints:** Distinguish path-space (shift-based) vs process-relative tail σ-algebras
- **Proof decomposition:** Long proofs should be broken into sublemmas (per Lean 4 skill guidelines)
- **Neutral naming:** Avoid "martingale-branded" names for general infrastructure

---

## Executive Summary

### Current State Analysis

Based on systematic analysis of all three de Finetti proof approaches:

| Proof Approach | Lines | Compiles? | Sorries | Completion | Priority |
|---------------|-------|-----------|---------|------------|----------|
| **ViaL2.lean** | 3,801 | ✅ Yes | 23 | **85-90%** | **DEFAULT** |
| **ViaKoopman.lean** | 4,862 | ❌ No (6 errors) | 23 + 16 axioms | 70-75% | Alternative |
| **ViaMartingale.lean** | 2,620 | ✅ Yes | 11 | 75-80% | Alternative |
| **Total** | 11,283 | - | - | - | - |

### Duplication Found

**Critical Duplication Categories:**

1. **Tail σ-algebra definitions:** 4 different implementations (ViaL2, ViaKoopman, ViaMartingale, CommonEnding)
2. **Product measure infrastructure:** ~400-500 lines (mostly in ViaMartingale, some in ViaKoopman)
3. **Conditional expectation lemmas:** 5-7 general lemmas scattered across files, some duplicated
4. **Indicator algebra:** Exact duplicates between ViaMartingale and MartingaleHelpers

### Projected Impact

**After complete refactoring:**

| File | Current | After Refactor | Change | Percent |
|------|---------|----------------|--------|---------|
| ViaL2.lean | 3,801 | ~3,650 | -150 | -4% |
| ViaKoopman.lean | 4,862 | ~4,600 | -260 | -5% |
| ViaMartingale.lean | 2,620 | ~2,250 | -370 | -14% |
| **New helper files** | 0 | ~900 | +900 | - |
| **Net project total** | 11,283 | ~11,400 | **+120** | **+1%** |

**Key metrics:**
- Duplication eliminated: ~780 lines
- New reusable infrastructure: ~900 lines
- Net line increase: +1% (acceptable for better organization)
- ViaMartingale benefits most: 14% reduction

---

## 🎯 PHASE 0: Immediate Quick Wins (Zero Risk)

**Estimated effort:** 1-2 hours
**Priority:** CRITICAL - Execute NOW (no prerequisites)

These changes are zero-risk deletions and neutral reorganizations that reduce diff noise for later phases.

### 0.1 Delete Exact Indicator Duplicates

**From ViaMartingale.lean (lines 636-679):**

Delete the following 5 lemmas that are **exact duplicates** of MartingaleHelpers.lean (lines 347-392):

1. `indicator_mul_indicator_eq_indicator_inter` (line 636)
2. `indicator_comp_preimage` (line 646)
3. `indicator_binary` (line 655)
4. `indicator_le_const` (line 664)
5. `indicator_nonneg` (line 673)

**Action:** Simply delete lines 636-679 from ViaMartingale.lean

**Verification:** ViaMartingale should still compile (it already imports MartingaleHelpers)

**Impact:** -44 lines of 100% duplication

### 0.2 Create Neutral Cylinder Infrastructure Home

**Problem:** Cylinder sets are general path-space infrastructure, but currently live in `MartingaleHelpers.lean` (martingale-branded)

**Solution:** Create `PathSpace/CylinderHelpers.lean` as neutral home

**Actions:**
1. Create new file `Exchangeability/PathSpace/CylinderHelpers.lean`
2. Add skeleton with proper namespace and imports
3. Leave empty for now (content will be moved in Phase 1.2)

**Rationale:**
- Clearer import graph (cylinders are not martingale-specific)
- Better organization for eventual mathlib contribution
- Prevents confusion about what "MartingaleHelpers" contains

**Impact:** Preparatory work for Phase 1.2 (no immediate line changes)

### Phase 0 Summary

**Time investment:** 1-2 hours
**Risk:** Zero (deletions only, no semantic changes)
**Immediate benefit:** -44 lines of duplication
**Future benefit:** Cleaner structure for Phase 1

---

## 🎯 PHASE 1: Fix Critical Duplication (High Impact)

**Estimated effort:** 3-4 days (revised)
**Priority:** HIGH - Execute when ViaL2 reaches 95%+ completion

**CRITICAL CHANGE:** Phase 1 now has **two sub-phases**:
- **Phase 1a:** Prove load-bearing bridge lemmas FIRST
- **Phase 1b:** Extract infrastructure using those bridges

### 1.1 Create Tail/TailSigma.lean (Two-Viewpoint Approach)

**Purpose:** Unify 4 different tail σ-algebra approaches using TWO canonical forms

**CRITICAL INSIGHT:** Don't conflate path-space tail vs. process tail—they are equivalent but NOT definitionally equal.

#### Current Duplication

**Four incompatible formulations exist:**

1. **InvariantSigma.lean:** `⨅ n, comap (shift^[n])` on path space
2. **ViaL2.lean:** `⨅ n, (⨆ k, comap (X (n+k)))` for process X
3. **ViaMartingale.lean:** `⨅ m, revFiltration X m`
4. **CommonEnding.lean:** Placeholder using `invariantSigmaField`

**Problem:** These are NOT definitionally equal, causing `rfl` failures and type mismatches

#### Extraction Plan

**New file:** `Exchangeability/Tail/TailSigma.lean`

**Complete implementation with mathlib-style signatures:**

```lean
/-
  Exchangeability/Tail/TailSigma.lean
  Tail σ-algebras on path space and for a general process, with bridge lemmas.
-/

import Mathlib.MeasureTheory.MeasurableSpace

namespace Exchangeability.Tail

open MeasureTheory

section Tail

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-! ### Index Arithmetic (isolate Nat arithmetic once) -/

section NatIndexArithmetic

@[simp] lemma nat_add_assoc (n m k : ℕ) : n + (m + k) = (n + m) + k := add_assoc n m k

-- Add more as needed for shift^[n+m] rewriting

end NatIndexArithmetic

/-! ### Process-Relative Tail -/

/-- The `n`-th reverse (future) σ-algebra generated by the tails of `X`. -/
def tailFamily (X : ℕ → Ω → α) (n : ℕ) : MeasurableSpace Ω :=
  iSup (fun k : ℕ => MeasurableSpace.comap (fun ω => X (n + k) ω) inferInstance)

/-- Tail σ-algebra of a process `X : ℕ → Ω → α`. -/
def tailProcess (X : ℕ → Ω → α) : MeasurableSpace Ω :=
  iInf (tailFamily X)

@[simp] lemma tailProcess_def (X : ℕ → Ω → α) :
    tailProcess X = iInf (tailFamily X) := rfl

lemma tailFamily_antitone (X : ℕ → Ω → α) :
    Antitone (tailFamily X) := by
  -- `n ≤ m` ⇒ generators for `m` include those for `n`
  sorry

lemma tailProcess_le_tailFamily (X : ℕ → Ω → α) (n : ℕ) :
    tailProcess X ≤ tailFamily X n := by
  -- `iInf_le` on index `n`
  sorry

/-! ### Path-Space Tail -/

/-- Tail σ-algebra on path space `(ℕ → α)` defined via one-sided shifts. -/
def tailShift (α : Type*) [MeasurableSpace α] : MeasurableSpace (ℕ → α) :=
  iInf (fun n : ℕ =>
    MeasurableSpace.comap
      (fun (ω : ℕ → α) => fun k => ω (n + k))
      (inferInstance : MeasurableSpace (ℕ → α)))

/-! ### Bridge Lemmas (LOAD-BEARING - Prove in Phase 1a!) -/

/-- On path space: the pullback of the product σ-algebra by the `n`-fold shift equals
    the join of the coordinate pullbacks at indices `n+k`. -/
lemma comap_shift_eq_iSup_comap_coords (n : ℕ) :
    MeasurableSpace.comap (fun (ω : ℕ → α) => fun k => ω (n + k))
        (inferInstance : MeasurableSpace (ℕ → α))
      =
    iSup (fun k : ℕ =>
      MeasurableSpace.comap (fun (ω : ℕ → α) => ω (n + k))
        (inferInstance : MeasurableSpace α)) := by
  -- Idea: product σ-algebra on `(ℕ → α)` is generated by coordinates;
  -- use `comap_comp` and `eval k ∘ shift^n = eval (n+k)`.
  sorry

/-- **Bridge 1 (path ↔ process).**
    For the coordinate process on path space, `tailProcess` equals `tailShift`. -/
lemma tailProcess_coords_eq_tailShift :
    tailProcess (fun k (ω : ℕ → α) => ω k) = tailShift α := by
  -- Rewrite the `n`-slice via `comap_shift_eq_iSup_comap_coords` and use `iInf_congr`.
  sorry

/-- **Bridge 2 (pullback along sample-path map).**
    Let `Φ : Ω → (ℕ → α)` be `Φ ω k := X k ω`. Then the process tail is the
    pullback of the path tail along `Φ`. -/
lemma tailProcess_eq_comap_path (X : ℕ → Ω → α) :
    tailProcess X
      =
    MeasurableSpace.comap (fun ω : Ω => fun k => X k ω) (tailShift α) := by
  -- Expand `tailShift`, then use `comap_comp`, and commute `iInf`/`iSup` as needed.
  sorry

/-- **Bridge 3 (to ViaMartingale's revFiltration).**
    If `revFiltration X m` is defined as the σ-algebra generated by all `X (m+k)`,
    then the tail equals `⨅ m, revFiltration X m`. -/
lemma tailProcess_eq_iInf_revFiltration
    (X : ℕ → Ω → α)
    (hrev :
      ∀ m, revFiltration X m
            =
          iSup (fun k : ℕ =>
            MeasurableSpace.comap (fun ω => X (m + k) ω) inferInstance)) :
    tailProcess X = iInf (fun m => revFiltration X m) := by
  -- Rewrite each slice using `hrev`, then unfold `tailProcess`.
  sorry

/-! ### General Properties -/

/-- Tail σ-algebra is sub-σ-algebra of ambient space. -/
lemma tailProcess_le_ambient (X : ℕ → Ω → α) :
    tailProcess X ≤ (inferInstance : MeasurableSpace Ω) := by
  sorry

/-- For probability/finite measures, trimming to tail σ-algebra preserves sigma-finiteness. -/
instance tailProcess_sigmaFinite [IsProbabilityMeasure μ] (X : ℕ → Ω → α) :
    SigmaFinite (μ.trim (tailProcess_le_ambient X)) :=
  inferInstance  -- Automatic for finite measures

end Tail

end Exchangeability.Tail
```

#### Implementation Notes (Proof Sketches)

**For `comap_shift_eq_iSup_comap_coords`:**
- Use that product σ-algebra on `(ℕ → α)` is generated by coordinate maps `ω ↦ ω k`
- Key: `fun ω => ω (n+k) = (fun ω => (fun j => ω (n+j))) k`
- Combine `MeasurableSpace.comap_comp` with `iSup_le`/`le_iSup_iff`

**For `tailProcess_coords_eq_tailShift`:**
- Follow from `iInf_congr` on `n` using previous lemma
- This is THE critical bridge between path-space and process formulations

**For `tailProcess_eq_comap_path`:**
- Most convenient in practice: pulls everything back from path space
- Proof: unfold and rearrange `comap`/`iSup`/`iInf`

**For `tailProcess_eq_iInf_revFiltration`:**
- Stated with hypothesis `hrev` to fit any house definition
- If `revFiltration` is literally `iSup (k ↦ comap (X (m+k)))`, specializes with `rfl`

#### Files to Update

**ViaL2.lean:**
```lean
import Exchangeability.Tail.TailSigma

-- Keep local tailFamily (ViaL2-specific) if needed
-- Replace tailSigma with:
def tailSigma (X : ℕ → Ω → β) : MeasurableSpace Ω :=
  Tail.tailProcess X
@[simp] lemma tailSigma_def : tailSigma X = Tail.tailProcess X := rfl
```

**ViaMartingale.lean:**
```lean
import Exchangeability.Tail.TailSigma

def tailSigma (X : ℕ → Ω → α) : MeasurableSpace Ω :=
  Tail.tailProcess X

-- Keep revFiltration and futureFiltration (proof-specific)
-- Use Tail.tailProcess_eq_iInf_revFiltration where needed
```

**CommonEnding.lean:**
```lean
import Exchangeability.Tail.TailSigma

def tailSigmaAlgebra (α : Type*) [MeasurableSpace α] : MeasurableSpace (ℕ → α) :=
  Tail.tailShift α
```

#### Estimated Impact

- **Lines in Tail/TailSigma.lean:** ~150 lines (includes bridges + proofs)
- **Duplication eliminated:** ~150-200 lines across 3 files
- **Net reduction:** 0 to -50 lines
- **ViaL2:** -50 lines
- **ViaMartingale:** -50 lines
- **CommonEnding:** -10 lines
- **Benefit:** Type-safe bridges prevent `rfl` failures

---

### 1.2 Extract Cylinder and Product Infrastructure

**Purpose:** Centralize cylinder sets, product indicators, and path-space infrastructure

**CRITICAL CHANGE:** Move to neutral `PathSpace/CylinderHelpers.lean` (NOT MartingaleHelpers)

**Rationale:** Cylinder sets are general path-space infrastructure, not martingale-specific

#### Current Status

**Already in MartingaleHelpers.lean (lines 100-460):**
- `tailCylinder` + 6 lemmas
- `cylinder` + 5 lemmas
- `finCylinder` + 3 lemmas
- `firstRCylinder` + 8 lemmas
- `firstRMap` / `firstRSigma` + 3 lemmas
- `drop` + 4 lemmas
- **Indicator algebra:** 5 lemmas (lines 348-391)

**Note:** Lines 636-679 in ViaMartingale are EXACT DUPLICATES (deleted in Phase 0.1)

#### Still Needs Extraction

**From ViaMartingale.lean (lines 579-740):**
- `indProd` definition + 10 supporting lemmas (~160 lines)

**From ViaKoopman.lean (lines 2554-2640):**
- `cylinderFunction`, `productCylinder` + 5 lemmas (~90 lines)

#### Extraction Plan

**New/Extended file:** `Exchangeability/PathSpace/CylinderHelpers.lean`

```lean
/-
  Exchangeability/PathSpace/CylinderHelpers.lean
  Cylinder sets, product indicators, and functions on path space.
-/

import Mathlib.MeasureTheory.Constructs.Prod

namespace Exchangeability.PathSpace

open MeasureTheory

variable {α : Type*} [MeasurableSpace α]

/-! ### Cylinder Sets -/

/-- Cylinder determined by first `r` coordinates. -/
def firstRCylinder (r : ℕ) (S : Fin r → Set α) : Set (ℕ → α) :=
  {ω | ∀ i : Fin r, ω i ∈ S i}

/-! ### Extensionality One-Liners (CRITICAL for downstream proofs) -/

/-- Membership characterization. -/
@[simp] lemma mem_firstRCylinder {r : ℕ} {S : Fin r → Set α} {ω : ℕ → α} :
    ω ∈ firstRCylinder r S ↔ ∀ i, ω i ∈ S i := Iff.rfl

/-- Measurability automation. -/
@[measurability]
lemma firstRCylinder_measurable {r : ℕ} {S : Fin r → Set α}
    [∀ i, MeasurableSet (S i)] :
    MeasurableSet (firstRCylinder r S) := by
  sorry

/-! ### Product Indicators -/

/-- Product of indicator functions for finite cylinder. -/
def indProd (r : ℕ) (S : Fin r → Set α) : (ℕ → α) → ℝ :=
  fun ω => ∏ i : Fin r, (S i).indicator (fun _ => (1 : ℝ)) (ω i)

/-- indProd equals indicator of cylinder. -/
@[simp] lemma indProd_eq_indicator (r : ℕ) (S : Fin r → Set α) :
    indProd r S = (firstRCylinder r S).indicator (fun _ => (1 : ℝ)) := by
  -- Strategy: by_cases on membership, use Finset.prod_eq_one
  sorry

-- Additional properties:
lemma indProd_integrable [IsProbabilityMeasure μ] ... := sorry
lemma indProd_nonneg_le_one ... := sorry
lemma indProd_measurable [∀ i, MeasurableSet (S i)] :
    Measurable (indProd r S) := by
  sorry

/-! ### Cylinder Functions -/

/-- Function on path space depending only on finitely many coordinates. -/
def cylinderFunction (m : ℕ) (f : Fin m → α → ℝ) : (ℕ → α) → ℝ :=
  fun ω => ∏ k : Fin m, f k (ω k)

abbrev productCylinder := cylinderFunction

/-- Measurability of cylinder functions. -/
@[measurability]
lemma cylinderFunction_measurable {m : ℕ} {f : Fin m → α → ℝ}
    [∀ i, Measurable (f i)] :
    Measurable (cylinderFunction m f) := by
  sorry

lemma cylinderFunction_bounded
    {m : ℕ} {f : Fin m → α → ℝ}
    (hf : ∀ i, ∃ C, ∀ x, |f i x| ≤ C) :
    ∃ C, ∀ ω, |cylinderFunction m f ω| ≤ C := by
  sorry

end Exchangeability.PathSpace
```

#### Files to Update

**ViaMartingale.lean:**
```lean
import Exchangeability.PathSpace.CylinderHelpers
open PathSpace (indProd firstRCylinder)

-- Delete lines 579-740 (moved to CylinderHelpers)
-- Delete lines 636-679 (duplicates, already done in Phase 0)
```

**ViaKoopman.lean:**
```lean
import Exchangeability.PathSpace.CylinderHelpers
open PathSpace (cylinderFunction productCylinder)

-- Delete lines 2554-2640 (moved to CylinderHelpers)
```

**MartingaleHelpers.lean:**
```lean
-- Keep martingale-specific content
-- Existing cylinder infrastructure can stay OR be moved to PathSpace
-- (decision: move to PathSpace for clarity)
```

#### Implementation Notes

**For `indProd_eq_indicator`:**
- Expand both sides pointwise
- Use `by_cases h : ω ∈ firstRCylinder r S`
- When `h` true: product of 1s equals 1
- When `h` false: some factor is 0, so product is 0
- Key lemma: `Finset.prod_eq_one_iff` and `Finset.prod_eq_zero_iff`

#### Estimated Impact

- **Lines in PathSpace/CylinderHelpers.lean:** ~300 lines (new file)
- **Lines deleted from ViaMartingale:** ~250 lines (moved content + duplicates)
- **Lines deleted from ViaKoopman:** ~90 lines
- **Lines moved from MartingaleHelpers:** ~200 lines (optional cleanup)
- **Net change:**
  - **ViaMartingale:** -250 lines (-9.5%)
  - **ViaKoopman:** -90 lines (-1.8%)
  - **PathSpace/CylinderHelpers:** +300 lines (new)
  - **Total:** -40 lines + better organization

---

### 1.3 Centralize Conditional Expectation Lemmas (Operator Norm Approach)

**Purpose:** Extract general conditional expectation infrastructure using operator-theoretic viewpoint

**KEY INSIGHT:** CE is an L¹-contraction (operator norm ≤ 1), so many lemmas follow from this

#### Current Situation

**CondExp.lean already has:**
- `integrable_indicator_comp` (line 119)
- `condIndep_of_indicator_condexp_eq` (line 184)
- `condExp_indicator_mul_indicator_of_condIndep` (line 280)
- `condexp_indicator_inter_bridge` (line 356)
- `condexp_indicator_eq_of_pair_law_eq` (line 402) - KEY BRIDGE LEMMA
- `condexp_indicator_eq_of_agree_on_future_rectangles` (line 507)

**Scattered in ViaKoopman.lean (general infrastructure, should be centralized):**

1. **Lines 874 AND 2464: `integrable_of_bounded` (EXACT DUPLICATE!)**
   - Delete one copy, move the other to CondExp.lean
   - **Note:** Check if this exists in mathlib first!

2. **Line 881: `integrable_of_bounded_mul`**
   - General utility for product of integrable × bounded

3. **Line 710: `condExp_abs_le_of_abs_le`**
   - Monotonicity property of CE

4. **Line 748: `condExp_L1_lipschitz`** (LOAD-BEARING)
   - **This is the key lemma:** CE is nonexpansive in L¹
   - Prove using operator norm viewpoint

5. **Line 769: `condExp_mul_pullout`**
   - Standard pull-out property
   - Can be derived as corollary of L¹-Lipschitz + bounded multiplication

**Proof-specific (keep in ViaKoopman.lean):**
- Ergodic theory / Koopman-specific CE lemmas (~16 lemmas)
- Factorization lemmas specific to shift-invariance
- Birkhoff averaging lemmas

#### Extraction Plan

**Add to:** `Exchangeability/Probability/CondExp.lean`

```lean
/-! ### General Conditional Expectation Utilities -/

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Bounded measurable functions are integrable on finite measures.
    TODO: Check if this exists in mathlib! -/
lemma integrable_of_bounded [IsFiniteMeasure μ]
    {f : Ω → ℝ} (hf : Measurable f) (hbd : ∃ C, ∀ ω, |f ω| ≤ C) :
    Integrable f μ := by
  obtain ⟨C, hC⟩ := hbd
  apply Integrable.of_bounded
  · exact hf.aestronglyMeasurable
  · exact ⟨C, eventually_of_forall hC⟩

/-- Product of integrable and bounded functions is integrable. -/
lemma integrable_of_bounded_mul [IsFiniteMeasure μ]
    {f g : Ω → ℝ} (hf : Integrable f μ) (hg : Measurable g)
    (hbd : ∃ C, ∀ ω, |g ω| ≤ C) :
    Integrable (f * g) μ := by
  sorry

/-! ### Conditional Expectation as L¹-Contraction -/

/-- Conditional expectation preserves pointwise absolute value bounds. -/
lemma condExp_abs_le_of_abs_le [IsFiniteMeasure μ]
    {m : MeasurableSpace Ω} [hm : m ≤ ‹_›]
    {f g : Ω → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (hfg : ∀ ω, |f ω| ≤ |g ω|) :
    ∀ᵐ ω ∂μ, |μ[f|m] ω| ≤ |μ[g|m] ω| := by
  sorry

/-- **LOAD-BEARING:** Conditional expectation is L¹-nonexpansive (operator norm ≤ 1).

    Proof strategy: CE is the L¹-orthogonal projection onto m-measurable functions.
    First prove for g = 0, then apply to f - g. -/
lemma condExp_L1_lipschitz [IsFiniteMeasure μ]
    {m : MeasurableSpace Ω} [hm : m ≤ ‹_›]
    {f g : Ω → ℝ} (hf : Integrable f μ) (hg : Integrable g μ) :
    ∫ ω, |μ[f|m] ω - μ[g|m] ω| ∂μ ≤ ∫ ω, |f ω - g ω| ∂μ := by
  -- Strategy:
  -- 1. Rewrite LHS as ∫ |μ[f - g|m]|
  -- 2. Use that CE is contractive: ‖CE(h)‖₁ ≤ ‖h‖₁
  -- 3. This follows from CE being projection with operator norm = 1
  sorry

/-! ### Conditional Expectation Pull-Out (Corollary) -/

/-- Pull out m-measurable bounded functions from conditional expectation.

    This can be derived from condExp_L1_lipschitz + bounded multiplication. -/
lemma condExp_mul_pullout [IsFiniteMeasure μ]
    {m : MeasurableSpace Ω} [hm : m ≤ ‹_›]
    {f g : Ω → ℝ} (hf : Integrable f μ) (hg_meas : Measurable[m] g)
    (hg_bd : ∃ C, ∀ ω, |g ω| ≤ C) (hfg : Integrable (f * g) μ) :
    μ[f * g|m] =ᵐ[μ] μ[f|m] * g := by
  -- Standard proof via pull-out property for m-measurable functions
  sorry
```

#### Implementation Notes

**For `condExp_L1_lipschitz` (THE key lemma):**

1. **Operator viewpoint:** CE is L¹ → L¹(m) projection
2. **Key fact:** Projections have operator norm ≤ 1
3. **Proof sketch:**
   - First show for `g = 0`: `‖μ[f|m]‖₁ ≤ ‖f‖₁`
   - Then apply to `f - g` using linearity
4. **Mathlib lemmas to use:**
   - `MeasureTheory.condexp_L1_norm_le` (if exists)
   - Or build from projection properties

**For `condExp_mul_pullout`:**
- This is standard; may already exist in mathlib as `condexp_smul`
- Otherwise, prove using tower property

#### Files to Update

**ViaKoopman.lean:**
```lean
import Exchangeability.Probability.CondExp

-- Delete line 2464 (duplicate integrable_of_bounded)
-- Delete lines 710-881 (move to CondExp.lean)
open CondExp (integrable_of_bounded condExp_L1_lipschitz condExp_mul_pullout)

-- Keep all Koopman-specific CE lemmas
```

#### Estimated Impact

- **Lines moved to CondExp.lean:** ~100 lines (including documentation)
- **Lines deleted from ViaKoopman:** ~120 lines (moved + duplicate)
- **Net change:**
  - **ViaKoopman:** -120 lines (-2.5%)
  - **CondExp.lean:** +100 lines
  - **Total:** -20 lines
- **Benefit:** Operator-theoretic approach is more modular and mathlib-ready

---

### Phase 1 Summary

**Total Impact (including Phase 0):**

**New infrastructure created:**
- **Tail/TailSigma.lean:** ~150 lines (two canonical viewpoints + bridges)
- **PathSpace/CylinderHelpers.lean:** ~300 lines (neutral cylinder infrastructure)
- **CondExp.lean additions:** ~100 lines (operator-theoretic approach)

**Reductions:**
- **ViaL2:** -50 lines (-1.3%)
- **ViaKoopman:** -210 lines (-4.3%)
- **ViaMartingale:** -290 lines (-11%) (250 cylinder + 44 duplicates from Phase 0)

**Net project change:** +210 lines (+1.9%)
**Duplication eliminated:** ~580 lines

**Critical Success Factors:**
1. **Phase 1a load-bearing proofs must succeed:**
   - `tailProcess_coords_eq_tailShift` (bridge path ↔ process)
   - `condExp_L1_lipschitz` (operator norm)
2. **Type safety:** Bridges prevent `rfl` failures
3. **Modular design:** Ready for eventual mathlib contribution

**Compilation verification checklist:**
- [ ] **Phase 1a:** Bridge lemmas proven and compile
- [ ] Tail/TailSigma.lean compiles standalone
- [ ] PathSpace/CylinderHelpers.lean compiles standalone
- [ ] CondExp.lean compiles with new lemmas
- [ ] ViaL2.lean compiles with new imports
- [ ] ViaKoopman.lean compiles with new imports
- [ ] ViaMartingale.lean compiles with deletions
- [ ] All three Via* files still prove their main theorems
- [ ] No circular dependencies (verify with `lake exe graph`)

---

## 🎯 PHASE 2: Extract Common Infrastructure (Medium Impact)

**Estimated effort:** 3-4 days
**Priority:** MEDIUM - Execute after Phase 1 is stable

### 2.1 Evaluate SigmaAlgebraHelpers.lean

**Candidates for extraction from ViaMartingale.lean:**

**Filtration infrastructure (lines 343-565):**
- `futureFiltration` (line 343) - Already an abbrev for `revFiltration (m+1)`
- `futureFiltration_antitone` (line 460)
- `futureFiltration_le_fwd` (line 380)
- `futureFiltration_le` (line 542)
- `preimage_measurable_in_futureFiltration` (line 549)
- `measurableSet_of_futureFiltration` (line 565)
- `finFutureSigma` (line 1275) - Finite approximation
- `finFutureSigma_le_ambient` (line 1278)
- `finFutureSigma_le_futureFiltration` (line 1286)

**Analysis:**
- These are tightly coupled to the martingale proof strategy
- ViaL2 uses different filtration approach (tailFamily)
- ViaKoopman uses shift-invariant σ-algebras

**Decision:** **DEFER** - Keep in ViaMartingale.lean unless clear reuse case emerges in other proofs

**Rationale:**
- No evidence ViaL2 or ViaKoopman would benefit
- Extraction would add complexity without clear benefit
- Martingale proof is already the cleanest/shortest

---

### 2.2 Audit for Contractability/Exchangeability Duplications

**Goal:** Check if contractability/exchangeability lemmas are duplicated

**Search strategy:**
```bash
# Search for contractability lemmas
grep -n "lemma.*[Cc]ontract" Exchangeability/DeFinetti/Via*.lean

# Search for exchangeability lemmas
grep -n "lemma.*[Ee]xchange" Exchangeability/DeFinetti/Via*.lean

# Search for identical marginals
grep -n "lemma.*[Mm]arginal" Exchangeability/DeFinetti/Via*.lean
```

**Known locations:**
- **Contractability.lean** - Core definitions and equivalences
- **ConditionallyIID.lean** - Core definitions
- **Core.lean** - π-system uniqueness, finite marginals

**Hypothesis:** Proof-specific files should NOT duplicate these core results

**Action items:**
1. Run systematic search
2. If duplications found, extract to Core.lean or new SharedLemmas.lean
3. If no duplications, mark Phase 2.2 as complete

**Estimated impact:** 50-100 lines if duplications found, 0 if clean

---

### 2.3 Review Path/Shift Infrastructure

**ViaMartingale shift infrastructure (lines 79-215):**
- `shiftProcess` (line 79)
- `path` (line 82)
- `shiftRV` (line 85)
- ~15 supporting lemmas

**ViaKoopman bi-infinite shift (lines 125-258):**
- `Ωℤ` (bi-infinite path space)
- `shiftℤ` (line 130)
- `shiftℤInv` (line 136)
- `restrictNonneg` (line 152)
- `extendByZero` (line 160)
- ~10 supporting lemmas

**CommonEnding basic shift (lines 90-110):**
- `shift` (line 90) - Basic one-sided shift
- `shift_apply` (line 93)
- `shift_measurable` (line 106)

**Analysis:**
- ViaMartingale: One-sided shift for sequences (martingale filtration)
- ViaKoopman: Two-sided shift for ergodic theory
- Different mathematical contexts, different type signatures

**Decision:** **Keep separate** - No extraction needed

**Rationale:**
- Different types: ℕ → α vs. ℤ → α
- Different proof strategies require different shift notions
- CommonEnding already provides shared basic shift
- Attempting to unify would introduce unnecessary abstraction

---

### 2.4 Create Indicator Utilities File (Optional)

**Candidates for extraction from ViaKoopman:**

**Indicator integral lemmas (lines 2472-2479):**
```lean
lemma integral_indicator_one {S : Set Ω} (hS : MeasurableSet S) :
    ∫ ω, S.indicator (fun _ => (1 : ℝ)) ω ∂μ = (μ S).toReal

lemma integral_indicator_const {S : Set Ω} (hS : MeasurableSet S) (c : ℝ) :
    ∫ ω, S.indicator (fun _ => c) ω ∂μ = c * (μ S).toReal
```

**Analysis:**
- These are general probability utilities
- Not conditional-expectation-specific
- Not cylinder-specific
- Could be useful across many proofs

**Proposed new file:** `Exchangeability/Probability/IndicatorIntegrals.lean`

**Decision:** **Optional** - Low priority, execute if time permits

**Rationale:**
- Only 2 lemmas, minimal duplication
- May already exist in mathlib (need to check)
- Can defer to future cleanup pass

---

### Phase 2 Summary

**Planned extractions:**
- None confirmed yet - depends on audit results

**Deferred decisions:**
- SigmaAlgebraHelpers: Not needed (proof-specific)
- Shift infrastructure: Keep separate (different contexts)
- Indicator utilities: Optional (low priority)

**Action items:**
1. Run contractability/exchangeability audit
2. If duplications found, create extraction plan
3. Otherwise, skip Phase 2 or mark as complete

**Estimated impact:** 50-100 lines if audit finds issues, 0 otherwise

---

## 🎯 PHASE 3: Cleanup and Verification (Low Impact)

**Estimated effort:** 1-2 days
**Priority:** LOW - Execute after Phases 1 and 2 are complete

### 3.1 Final Duplication Check

**Automated search for remaining duplications:**

```bash
# Search for potential lemma duplications
cd /Users/freer/work/exch-repos/exchangeability-vscode

# Find all lemma/theorem/def names in Via* files
for file in Exchangeability/DeFinetti/Via*.lean; do
  echo "=== $file ==="
  grep -o "^\(lemma\|theorem\|def\) [a-zA-Z_]*" "$file" | sort
done > /tmp/all_names.txt

# Find duplicates
sort /tmp/all_names.txt | uniq -d

# Search for similar lemma patterns
grep -r "lemma.*tailSigma" Exchangeability/DeFinetti/Via*.lean
grep -r "lemma.*cylinder" Exchangeability/DeFinetti/Via*.lean
grep -r "lemma.*condExp" Exchangeability/DeFinetti/Via*.lean
grep -r "lemma.*integrable" Exchangeability/DeFinetti/Via*.lean
grep -r "lemma.*measurable" Exchangeability/DeFinetti/Via*.lean
```

**Manual review:**
- Check for near-duplications with slightly different names
- Check for duplicated proof patterns even if lemma statements differ
- Look for repeated boilerplate that could be factored out

---

### 3.2 Verify No Circular Dependencies

**Dependency chain should be:**
```
Mathlib
  ↓
Core.lean, Contractability.lean, ConditionallyIID.lean, InvariantSigma.lean
  ↓
Probability/CondExp.lean (general CE utilities)
  ↓
Tail/TailSigma.lean (two canonical viewpoints + bridges)
PathSpace/CylinderHelpers.lean (neutral cylinder infrastructure)
  ↓
DeFinetti/MartingaleHelpers.lean (martingale-specific only)
DeFinetti/L2Helpers.lean
  ↓
ViaL2.lean, ViaKoopman.lean, ViaMartingale.lean
  ↓
Theorem.lean, TheoremViaL2.lean, TheoremViaKoopman.lean, TheoremViaMartingale.lean
```

**Key import constraints:**
- **Tail/TailSigma.lean:** Only imports mathlib (no project dependencies)
- **PathSpace/CylinderHelpers.lean:** Only imports mathlib
- **Probability/CondExp.lean:** Only imports mathlib
- **Via\* files:** Import helpers, NEVER each other
- **MartingaleHelpers:** Can import PathSpace, NOT Via\*

**Verification commands:**
```bash
# Check import graph
lake exe graph Exchangeability.Tail.TailSigma > /tmp/tail_deps.dot
lake exe graph Exchangeability.PathSpace.CylinderHelpers > /tmp/cylinder_deps.dot
lake exe graph Exchangeability.DeFinetti.ViaL2 > /tmp/vial2_deps.dot
lake exe graph Exchangeability.DeFinetti.ViaKoopman > /tmp/viakoopman_deps.dot
lake exe graph Exchangeability.DeFinetti.ViaMartingale > /tmp/viamartingale_deps.dot

# Look for cycles
grep "Tail.*Via" /tmp/*.dot
grep "PathSpace.*Via" /tmp/*.dot
grep "MartingaleHelpers.*Via" /tmp/*.dot

# Verify helpers have minimal dependencies
grep -v "Mathlib\|std" /tmp/tail_deps.dot  # Should be empty
grep -v "Mathlib\|std" /tmp/cylinder_deps.dot  # Should be empty
```

**If circular dependencies found:**
- Identify the problematic import
- Either move the lemma or split the file
- Re-verify after fix

**Expected dependency counts (as sanity check):**
- Tail/TailSigma: ~5-10 mathlib imports
- PathSpace/CylinderHelpers: ~5-10 mathlib imports
- ViaL2/ViaKoopman/ViaMartingale: ~20-30 total imports each

---

### 3.3 Documentation and Style Cleanup

**Update documentation files:**

1. **CLAUDE.md:**
   - Update "Core Module Structure" section with new helper files
   - Document new import conventions
   - Update file status summary

2. **README.md:**
   - Mention refactored structure (if applicable)
   - Update architecture diagram (if exists)

3. **REFACTORING_NOTES.md:**
   - Archive this planning document
   - Document what was actually implemented
   - Note any deviations from plan

**Style consistency:**
- Ensure all new files follow `StyleGuidelines/PROJECT_STYLE.md`
- Ensure all new files follow `StyleGuidelines/MATHLIB_STYLE_CHECKLIST.md`
- Run linter and fix warnings:
  ```bash
  lake build 2>&1 | grep "warning:"
  ```

---

### 3.4 Performance and Compilation Time Check

**Measure compilation times before and after:**

```bash
# Before refactoring
time lake build Exchangeability.DeFinetti.ViaL2
time lake build Exchangeability.DeFinetti.ViaKoopman
time lake build Exchangeability.DeFinetti.ViaMartingale

# After refactoring
time lake build Exchangeability.DeFinetti.ViaL2
time lake build Exchangeability.DeFinetti.ViaKoopman
time lake build Exchangeability.DeFinetti.ViaMartingale
```

**Expected impact:**
- Compilation time may increase slightly (more imports)
- But incremental rebuilds should be faster (less duplication)
- Helper files should cache well

**If compilation time increases significantly (>20%):**
- Review import structure
- Consider splitting large helper files
- Check for unnecessary imports

---

### 3.5 Axiom Audit

**Verify no new axioms introduced:**

```bash
# Check axioms in each main theorem
lake env lean --run Exchangeability/DeFinetti/TheoremViaL2.lean -c '#print axioms deFinetti_viaL2'
lake env lean --run Exchangeability/DeFinetti/TheoremViaKoopman.lean -c '#print axioms deFinetti_viaKoopman'
lake env lean --run Exchangeability/DeFinetti/TheoremViaMartingale.lean -c '#print axioms deFinetti_viaMartingale'
```

**Should only show mathlib standard axioms:**
- `propext`
- `quot.sound`
- `Classical.choice`

**If new axioms appear:**
- Identify which refactored lemma introduced it
- Either prove the lemma or mark as explicit axiom with documentation
- Do NOT ship with accidental axioms

---

### Phase 3 Summary

**Verification checklist:**
- [ ] No duplicate lemmas found in automated search
- [ ] No circular dependencies in import graph
- [ ] All documentation updated
- [ ] Style guidelines followed
- [ ] Compilation time acceptable
- [ ] No new axioms introduced
- [ ] All linter warnings addressed
- [ ] All Via* files still compile
- [ ] Main theorems still prove

**Estimated time:** 1-2 days for thorough verification

---

## 📊 Overall Project Impact Summary

### Line Count Changes (Projected)

| File | Current | Phase 1 | Phase 2 | Phase 3 | Final | Change |
|------|---------|---------|---------|---------|-------|--------|
| ViaL2.lean | 3,801 | -50 | -50 | -50 | ~3,650 | -150 (-4%) |
| ViaKoopman.lean | 4,862 | -210 | -30 | -20 | ~4,600 | -260 (-5%) |
| ViaMartingale.lean | 2,620 | -295 | -50 | -25 | ~2,250 | -370 (-14%) |
| TailSigmaHelpers.lean | 0 | +100 | 0 | 0 | ~100 | +100 |
| MartingaleHelpers.lean | ~300 | +250 | 0 | 0 | ~550 | +250 |
| CondExp.lean | ~600 | +80 | +20 | 0 | ~700 | +100 |
| IndicatorIntegrals.lean | 0 | 0 | +50 | 0 | ~50 | +50 |
| **Total** | 11,283 | +90 | +10 | +20 | ~11,400 | **+120 (+1%)** |

### Duplication Eliminated

| Category | Lines Eliminated | Phase |
|----------|-----------------|-------|
| Tail σ-algebra definitions | ~150-200 | Phase 1.1 |
| Duplicate indicator algebra | ~45 | Phase 1.2 |
| Product measure infrastructure | ~250 | Phase 1.2 |
| Conditional expectation lemmas | ~120 | Phase 1.3 |
| Contractability lemmas (if found) | ~50-100 | Phase 2.2 |
| **Total duplication removed** | **~615-715** | - |

### New Reusable Infrastructure

| File | Lines | Purpose |
|------|-------|---------|
| TailSigmaHelpers.lean | ~100 | Canonical tail σ-algebra + bridges |
| MartingaleHelpers.lean | +250 | Product measures, cylinders, indProd |
| CondExp.lean | +80-100 | General CE lemmas |
| IndicatorIntegrals.lean | ~50 | Optional indicator utilities |
| **Total new infrastructure** | **~480-500** | - |

### Net Result

- **Duplication eliminated:** ~615-715 lines
- **New infrastructure created:** ~480-500 lines
- **Net project growth:** +120 lines (+1%)
- **Improved organization:** Significant
- **Maintenance burden:** Reduced

---

## 🚨 Risks and Mitigations

### Risk 1: Breaking Compilation

**Probability:** MEDIUM
**Impact:** HIGH

**Mitigation strategy:**
1. Do refactoring in feature branch `refactor/shared-infrastructure`
2. Verify each file compiles after every change
3. Use `git bisect` if compilation breaks to find exact breaking commit
4. Keep `main` branch stable at all times
5. Merge only when all files compile cleanly

**Commands:**
```bash
git checkout -b refactor/shared-infrastructure
# After each change:
lake build Exchangeability.DeFinetti.TailSigmaHelpers
lake build Exchangeability.DeFinetti.ViaL2
lake build Exchangeability.DeFinetti.ViaKoopman
lake build Exchangeability.DeFinetti.ViaMartingale
```

---

### Risk 2: Circular Dependencies

**Probability:** LOW
**Impact:** HIGH

**Mitigation strategy:**
1. Create dependency diagram before starting
2. Helper files should only import from Core/Contractability/InvariantSigma
3. Via* files should only import helpers, never each other
4. Use `lake exe graph` to verify no cycles
5. If cycle detected, split the offending file

**Prevention:**
- TailSigmaHelpers imports: InvariantSigma
- MartingaleHelpers imports: Core, CommonEnding
- CondExp imports: mathlib only
- Via* files import: Helpers only, no cross-imports

---

### Risk 3: Type Signature Mismatches

**Probability:** MEDIUM
**Impact:** MEDIUM

**Mitigation strategy:**
1. Use bridge lemmas to connect different formulations
2. Preserve original type signatures where possible
3. Use `abbrev` instead of `def` for aliasing
4. Extensive use of type ascriptions in bridge proofs
5. Test with concrete examples from each proof

**Example bridge lemma pattern:**
```lean
-- Original ViaL2 definition
def tailSigma_ViaL2 (X : ℕ → Ω → β) : MeasurableSpace Ω := ...

-- Bridge to canonical
lemma tailSigma_eq_canonical (X : ℕ → Ω → β) :
    tailSigma_ViaL2 X = TailSigmaHelpers.tailSigma X := sorry
```

---

### Risk 4: Loss of Proof-Specific Optimizations

**Probability:** LOW
**Impact:** LOW

**Mitigation strategy:**
1. Keep proof-specific versions when there's a mathematical reason
2. Document why certain lemmas remain proof-specific
3. Use `private` for internal proof-specific helpers
4. Only extract truly general infrastructure
5. When in doubt, keep it proof-specific

**Example:**
```lean
-- General version in TailSigmaHelpers
lemma tailSigma_le_ambient : tailSigma X ≤ inferInstance := ...

-- ViaL2-specific optimization (if needed)
private lemma tailSigma_le_tailFamily : tailSigma X ≤ tailFamily X n := ...
```

---

### Risk 5: Merge Conflicts

**Probability:** HIGH (if proofs are still evolving)
**Impact:** MEDIUM

**Mitigation strategy:**
1. **Coordinate with other work:** Don't refactor while actively adding sorries
2. **Small PRs:** One phase at a time
3. **Clear communication:** Document which files are being refactored
4. **Rebase frequently:** Keep refactor branch up to date with main
5. **Lock during merge:** No other changes to Via* files during refactor PR

**Workflow:**
```bash
# Before starting refactoring
git pull origin main
git checkout -b refactor/phase1

# Frequently:
git fetch origin
git rebase origin/main

# Before PR:
lake clean
lake build
# Verify all tests pass
```

---

### Risk 6: Increased Compilation Time

**Probability:** LOW
**Impact:** LOW

**Mitigation strategy:**
1. Measure baseline compilation times
2. Monitor compilation time after each phase
3. If >20% increase, investigate and optimize
4. Consider splitting large helper files
5. Use selective imports (`open Foo (bar baz)`)

**Monitoring:**
```bash
# Before refactoring
hyperfine 'lake build Exchangeability.DeFinetti.ViaL2'

# After each phase
hyperfine 'lake build Exchangeability.DeFinetti.ViaL2'

# Compare results
```

---

## 🛠️ Implementation Workflow

### Prerequisites

Before starting refactoring:

1. **ViaL2 completion:** ≥95% (currently ~85-90%)
2. **ViaKoopman compilation:** Fixed (currently has 6 errors)
3. **All sorries documented:** Know which are infrastructure vs. math
4. **Clean git state:** No uncommitted changes
5. **Backup branch:** Create `pre-refactor` tag

**Commands:**
```bash
git tag pre-refactor
git push origin pre-refactor
git checkout -b refactor/shared-infrastructure
```

---

### Phase 0 Implementation (1-2 hours) — DO NOW

**Immediate quick wins (no prerequisites):**

1. **Delete duplicate indicator lemmas from ViaMartingale.lean (lines 636-679)**
   ```bash
   # Edit ViaMartingale.lean, delete lines 636-679
   lake build Exchangeability.DeFinetti.ViaMartingale  # Verify still compiles
   git commit -m "refactor: Remove duplicate indicator algebra from ViaMartingale"
   ```

2. **Create PathSpace/CylinderHelpers.lean skeleton**
   ```bash
   mkdir -p Exchangeability/PathSpace
   # Create skeleton file with namespace and imports
   lake build Exchangeability.PathSpace.CylinderHelpers  # Verify compiles
   git commit -m "feat: Add PathSpace/CylinderHelpers skeleton for neutral cylinder infrastructure"
   ```

**Time:** 1-2 hours
**Risk:** Zero
**Benefit:** -44 lines, cleaner base for Phase 1

---

### Phase 1 Implementation (3-4 days) — REVISED WITH PHASE 1a/1b

**CRITICAL:** Phase 1 now has TWO sub-phases to prove load-bearing lemmas FIRST

#### Phase 1a: Prove Load-Bearing Bridge Lemmas (Day 1)

**Goal:** Get the critical bridges working BEFORE extracting infrastructure

**Morning:**
1. Create `Exchangeability/Tail/TailSigma.lean` with complete signatures (from plan)
2. Implement `comap_shift_eq_iSup_comap_coords` proof
   - Use mathlib's product σ-algebra properties
   - Key lemmas: `comap_comp`, `iSup_le`, `le_iSup_iff`
3. Verify compiles

**Afternoon:**
4. Implement `tailProcess_coords_eq_tailShift` proof
   - Use `iInf_congr` + previous lemma
5. Implement `tailProcess_eq_comap_path` proof
   - Unfold and rearrange `comap`/`iInf`/`iSup`
6. Verify all bridges compile

**Evening:**
7. Add `condExp_L1_lipschitz` to CondExp.lean
   - Prove using operator norm ≤ 1 viewpoint
   - Check mathlib for `condexp_L1_norm_le`
8. Verify CondExp.lean compiles
9. **CHECKPOINT:** Commit with all bridges proven

**Commit:** `feat: Add load-bearing bridge lemmas (tail σ-algebra + CE operator norm)`

---

#### Phase 1b: Extract Infrastructure Using Bridges (Days 2-3)

**Day 2: Tail Infrastructure**

**Morning:**
1. Complete `Tail/TailSigma.lean` with all supporting lemmas
2. Verify file compiles standalone
3. Test bridges with small examples

**Afternoon:**
4. Update `ViaL2.lean` to import and use `Tail.tailProcess`
5. Update proofs to use bridge lemmas where needed
6. Verify ViaL2 compiles

**Evening:**
7. Update `ViaMartingale.lean` to use `Tail.tailProcess`
8. Update `CommonEnding.lean` to use `Tail.tailShift`
9. Verify all files compile
10. Commit: `feat: Extract tail σ-algebra infrastructure with two canonical viewpoints`

---

**Day 3: Cylinder and CE Infrastructure**

**Morning:**
1. Complete `PathSpace/CylinderHelpers.lean` with content from ViaMartingale/ViaKoopman
2. Add extensionality and measurability one-liners
3. Verify file compiles standalone

**Afternoon:**
4. Update ViaMartingale to import `PathSpace.CylinderHelpers`
5. Delete extracted cylinder content (lines 579-740)
6. Update ViaKoopman to import cylinder functions
7. Delete extracted content (lines 2554-2640)
8. Verify both files compile

**Evening:**
9. Complete CondExp.lean CE utilities (building on Phase 1a)
10. Update ViaKoopman to import and use new CE lemmas
11. Delete duplicate/extracted CE content from ViaKoopman
12. Run full project build: `lake build`
13. Update CLAUDE.md with new file structure
14. Commit: `feat: Extract cylinder and CE infrastructure to neutral locations`
15. **MERGE CHECKPOINT:** Phase 1 complete

---

### Phase 2 Implementation (3-4 days)

**Only execute if Phase 1 is stable and successful**

#### Day 4: Audit for duplications

**Full day:**
1. Run automated duplication search (see Phase 2 section)
2. Manual review of results
3. Create extraction plan if duplications found
4. Document findings in `REFACTORING_NOTES.md`
5. Decide: Extract or defer to Phase 3?

---

#### Day 5-6: Conditional extraction (if needed)

**If duplications found:**
1. Create new helper file (if needed)
2. Extract duplicated lemmas
3. Update Via* files
4. Verify compilation
5. Commit changes

**If no duplications:**
1. Mark Phase 2 as complete
2. Skip to Phase 3

---

### Phase 3 Implementation (1-2 days)

#### Day 7: Final verification

**Morning:**
1. Run final duplication check
2. Verify no circular dependencies
3. Check axiom count (`#print axioms`)
4. Measure compilation times

**Afternoon:**
5. Update all documentation (CLAUDE.md, README.md, etc.)
6. Address any linter warnings
7. Run full project build
8. Create PR description with before/after metrics

**Evening:**
9. Final commit: `docs: Update documentation after refactoring`
10. Push branch: `git push origin refactor/shared-infrastructure`
11. Create PR for review

---

### Merge and Deployment

**PR Checklist:**
- [ ] All files compile successfully
- [ ] No new axioms introduced
- [ ] No circular dependencies
- [ ] Compilation time acceptable (<20% increase)
- [ ] All linter warnings addressed
- [ ] Documentation updated
- [ ] Git history clean (sensible commit messages)
- [ ] No merge conflicts with main

**After PR approval:**
```bash
git checkout main
git merge refactor/shared-infrastructure
git push origin main
git tag refactoring-complete
git push origin refactoring-complete
```

---

## 📝 Maintenance Notes

### When to Re-run This Refactoring

**Ideal timing:**
- ✅ ViaL2 is 95%+ complete (minimal sorries)
- ✅ ViaKoopman compiles successfully (6 errors fixed)
- ✅ ViaMartingale is stable (11 sorries mostly resolved)
- ✅ No active development on Via* files
- ✅ Clean git state

**Signs you should wait:**
- ❌ Actively adding sorries to Via* files
- ❌ ViaKoopman has compilation errors
- ❌ Major proof restructuring in progress
- ❌ Mathlib dependency upgrade in progress

### How to Update This Plan

**If plan becomes outdated:**
1. Re-run the analysis agents (see "Analysis Process" below)
2. Update line numbers and file sizes
3. Adjust estimated impacts
4. Add new duplication categories if found
5. Update this document and commit

**Analysis process:**
```bash
# Re-run the analysis
# (User would invoke Claude Code agents as done originally)
```

---

## 🎓 Lessons Learned (To Be Filled After Execution)

### What Worked Well
- _To be filled after refactoring is complete_

### What Didn't Work
- _To be filled after refactoring is complete_

### Unexpected Challenges
- _To be filled after refactoring is complete_

### Recommendations for Future Refactoring
- _To be filled after refactoring is complete_

---

## 📚 References

### Related Documents
- `PROGRESS_SUMMARY.md` - Overall project progress
- `REFACTORING_NOTES.md` - ViaKoopman refactoring notes
- `CLAUDE.md` - Project structure and conventions
- `StyleGuidelines/PROJECT_STYLE.md` - Style guidelines
- `StyleGuidelines/MATHLIB_STYLE_CHECKLIST.md` - Mathlib conventions

### Key Files Modified
- `Exchangeability/DeFinetti/ViaL2.lean` (3,801 lines → ~3,650 lines)
- `Exchangeability/DeFinetti/ViaKoopman.lean` (4,862 lines → ~4,600 lines)
- `Exchangeability/DeFinetti/ViaMartingale.lean` (2,620 lines → ~2,250 lines)
- `Exchangeability/Probability/CondExp.lean` (extended with ~100 lines)

### New Files Created (Phase 0-1)
- `Exchangeability/Tail/TailSigma.lean` (~150 lines)
  - Two canonical tail viewpoints (path-space vs. process)
  - Load-bearing bridge lemmas
- `Exchangeability/PathSpace/CylinderHelpers.lean` (~300 lines)
  - Neutral cylinder infrastructure
  - Extensionality and measurability one-liners
- **MartingaleHelpers.lean:** Keep for martingale-specific content only

### Proposed Files (Phase 4) — REVISED

**Note:** Most "gaps" are actually mathlib wrappers, not true gaps!

- `Exchangeability/Probability/IntegrationHelpers.lean` (~60 lines)
  - Mathlib wrappers: `abs_integral_mul_le_L2` (Hölder p=q=2)
  - Convenience: `integral_pushforward_id`, `integral_pushforward_sq_diff`
  - **Imports:** `Mathlib.MeasureTheory.Integral.Bochner.Basic`
- `Exchangeability/Util/StrictMono.lean` (~40 lines)
  - Only 2 Fin-specific lemmas: `strictMono_Fin_ge_id`, `strictMono_fin_cases`
  - Rest handled by mathlib's `StrictMono.comp`, `OrderIso.strictMono`

**Total new code:** ~100 lines (not ~380!)
**Total duplication eliminated:** ~420 lines
**Net savings:** ~320 lines

---

## 🔍 PHASE 4: Additional Refactoring Opportunities (Extended Analysis)

**Generated:** 2025-10-18 (Extended analysis session)
**Status:** Additional opportunities identified beyond original Phase 1-3 plan

This section documents additional refactoring opportunities discovered through comprehensive deep-dive analysis of the codebase.

---

### 4.1 Integration and L^p Space Utilities

**REVISED ASSESSMENT:** Most of these are mathlib wrappers, not gaps!

**HIGH PRIORITY: Cauchy-Schwarz Wrapper (Eliminates 170 lines)**

**What we need:** Thin wrapper around mathlib's Hölder inequality (p=q=2)

**Mathlib already has:** `MeasureTheory.integral_mul_norm_le_Lp_mul_Lq`
- Location: `Mathlib.MeasureTheory.Integral.Bochner.Basic`
- This IS Cauchy-Schwarz when specialized to p=q=2

**Our wrapper (in `Probability/IntegrationHelpers.lean`):**

```lean
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-- Cauchy-Schwarz for real-valued L² functions (wrapper around Hölder). -/
lemma abs_integral_mul_le_L2
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f g : Ω → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |∫ ω, f ω * g ω ∂μ|
      ≤ Real.sqrt (∫ ω, (‖f ω‖)^2 ∂μ) * Real.sqrt (∫ ω, (‖g ω‖)^2 ∂μ) := by
  -- Call mathlib's Hölder with p=q=2
  have h := integral_mul_norm_le_Lp_mul_Lq hf hg
  -- Rewrite L²-norms using MemLp.eLpNorm_eq_integral_rpow_norm
  -- Simplify ‖f ω‖ to |f ω| for ℝ
  sorry
```

**Impact:** Eliminates 170 lines by delegating to mathlib

**MEDIUM PRIORITY: `integral_map` Boilerplate Wrappers (54 call sites)**

**Mathlib already has:** `MeasureTheory.integral_map`
- Location: `Mathlib.MeasureTheory.Integral.Bochner.Basic`
- We just need convenience wrappers

**Pattern appearing 18+ times:**
```lean
have h_ae : AEStronglyMeasurable (id : ℝ → ℝ) (Measure.map (X k) μ) :=
  aestronglyMeasurable_id
exact (integral_map (hX_meas k).aemeasurable h_ae).symm
```

**Our wrappers (in `Probability/IntegrationHelpers.lean`):**

```lean
/-- Convenience wrapper for integral_map with identity function. -/
lemma integral_pushforward_id {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {f : Ω → ℝ} (hf : Measurable f) :
    ∫ ω, f ω ∂μ = ∫ x, x ∂(Measure.map f μ) := by
  have h_ae : AEStronglyMeasurable (id : ℝ → ℝ) (Measure.map f μ) :=
    aestronglyMeasurable_id
  exact (integral_map hf.aemeasurable h_ae).symm

/-- Convenience wrapper for squared differences under pushforward. -/
lemma integral_pushforward_sq_diff {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {f : Ω → ℝ} (hf : Measurable f) (c : ℝ) :
    ∫ ω, (f ω - c)^2 ∂μ = ∫ x, (x - c)^2 ∂(Measure.map f μ) := by
  sorry -- Apply integral_map with (fun x => (x - c)^2)
```

**Impact:** Eliminates 54 boilerplate instances

**LOW PRIORITY: Indicator Integration**

**Mathlib already has:**
- **Bochner (ℝ-valued):** `integral_const`, `integral_indicator₂`
  - Location: `Mathlib.MeasureTheory.Integral.Bochner.Basic`
- **Lebesgue (ℝ≥0∞-valued):** `lintegral_indicator_const`, `lintegral_indicator_one`
  - Location: `Mathlib.MeasureTheory.Integral.Lebesgue.Basic`

**Decision:** Use mathlib directly, no wrappers needed

**Required imports for IntegrationHelpers.lean:**
```lean
import Mathlib.MeasureTheory.Integral.Bochner.Basic     -- Hölder, integral_map, integral_const
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic    -- lintegral_indicator_*
import Mathlib.MeasureTheory.Integral.MeanInequalities  -- (optional) Hölder variants
```

---

### 4.2 StrictMono (Strictly Monotone) Utilities

**REVISED ASSESSMENT:** Most are already in mathlib via general order API!

**Analysis findings:**

**Duplicated across 3 files:**
- `Contractability.lean` (lines 306-500): 15 lemmas
- `L2Helpers.lean` (lines 121-137): 2 lemmas
- `MartingaleHelpers.lean` (lines 158-177): 1 lemma

**Classification:**

**Already in mathlib (use directly, don't re-declare):**

1. **Composition:** `StrictMono.comp`
   - Location: General order API
   - Use for your `Fin m → Fin n → ℕ` composition chains
   - Don't create project-specific `strictMono_comp`

2. **Add/subtract constants:** Via `OrderIso`
   - `i ↦ i + c` is an `OrderIso`, hence `StrictMono`
   - Use `OrderIso.strictMono` (2-3 line derivation)
   - Don't create `strictMono_add_left`/`strictMono_add_right`

3. **Fin → ℕ coercion:** Via `OrderEmbedding`
   - `(fun i : Fin n => (i : ℕ))` is an order embedding
   - Use `OrderEmbedding.strictMono`
   - If you need a named lemma, consider PR to `Mathlib.Data.Fin.Basic`

**Project-specific (keep in `Util/StrictMono.lean`):**

1. **`strictMono_Fin_ge_id`:**
   ```lean
   /-- Strictly monotone functions on Fin dominate the identity. -/
   lemma strictMono_Fin_ge_id {m : ℕ} {k : Fin m → ℕ} (hk : StrictMono k) (i : Fin m) :
       i.val ≤ k i := by
     sorry -- Tailored to CDF/index arguments
   ```

2. **`strictMono_fin_cases`:**
   ```lean
   /-- Strict monotonicity preserved by Fin.cases with compatible initial value. -/
   lemma strictMono_fin_cases {n : ℕ} {f : Fin n → ℕ} (hf : StrictMono f) {a : ℕ}
       (ha : ∀ i, a < f i) : StrictMono (Fin.cases a (fun i => f i)) := by
     sorry -- Structural lemma for your constructions
   ```

**Recommended action:**
- **DELETE** from plan: `strictMono_add_left`, `strictMono_add_right`, `strictMono_comp`
- **CREATE** `Util/StrictMono.lean` with ONLY the 2 Fin-specific lemmas above
- **USE** mathlib's general API for composition and arithmetic

**Revised impact:**
- Consolidates ~200 lines of duplication
- **But:** Only ~40 lines of actual new code (just the 2 Fin lemmas)
- Remaining ~160 lines replaced by mathlib calls

---

### 4.3 Stieltjes and CDF Infrastructure (ViaL2-specific but extractable)

**Analysis findings:**

**ViaL2.lean contains 700+ lines of CDF/Stieltjes infrastructure** (lines 2555-3423)

**Core components:**
- `indIic` - Indicator for `(-∞, t]` intervals
- `alphaIic` - Raw CDF from Cesàro averages
- `alphaIicCE` - Canonical conditional expectation version
- `cdf_from_alpha` - Right-continuous CDF via rational envelope
- `directing_measure` - Stieltjes measure construction

**Reusability:** MEDIUM-HIGH
- The rational envelope technique for right-continuity is general
- Endpoint limit infrastructure uses only dominated convergence
- Stieltjes measure construction is generic

**Currently ViaL2-specific:**
- Depends on contractability and L² bounds
- Integrated into the L² proof flow

**Recommended action (deferred):**
- **Short-term:** Keep in ViaL2.lean until proof is complete
- **Long-term:** If ViaMartingale or ViaKoopman need CDF construction, extract to `StieltjesMeasureHelpers.lean`

**Estimated extractable:** ~300 lines of generic infrastructure

---

### 4.4 Ergodic Theory Infrastructure (ViaKoopman - should go to mathlib)

**Analysis findings:**

**VERY HIGH PRIORITY for mathlib contribution:**

1. **KoopmanMeanErgodic.lean (347 lines) - PURE ERGODIC THEORY**
   - Koopman operator definition
   - Fixed-point subspace
   - Mean Ergodic Theorem: `birkhoffAverage_tendsto_metProjection`
   - **Should be upstreamed to `Mathlib.Dynamics.Ergodic.MeanErgodic`**

2. **ProjectionLemmas.lean (227 lines) - PURE FUNCTIONAL ANALYSIS**
   - Orthogonal projection uniqueness
   - Hilbert space machinery
   - **Should be upstreamed to `Mathlib.Analysis.InnerProductSpace.Projection`**

3. **InvariantSigma.lean (~200 lines extractable)**
   - Shift-invariant σ-algebra (general)
   - Connection to conditional expectation
   - **General ergodic theory, should go to mathlib**

**Natural extension infrastructure (ViaKoopman lines 122-425):**
- `Ωℤ[α]` - Bi-infinite path space
- `shiftℤ`, `shiftℤInv` - Two-sided shift operators
- `NaturalExtensionData` structure
- **Should be extracted to `Exchangeability/Ergodic/NaturalExtension.lean`**

**Recommended actions:**
1. Extract to `Ergodic/` directory as staging area
2. Polish for mathlib standards
3. Submit as mathlib PRs
4. **Not used by ViaL2 or ViaMartingale** - purely Koopman-specific

**Impact:** ~800 lines of pure ergodic theory could be upstreamed

---

### 4.5 Helper File Reorganization

**Analysis findings:**

**CRITICAL: CovarianceStructure.lean is ORPHANED (359 lines)**
- Not imported by any file in the codebase
- Duplicates logic from L2Helpers.lean
- Contains standalone `contractable_covariance_structure` theorem

**Recommendation:** **DELETE** or move to separate Examples/ directory

**MEDIUM: L2Helpers.lean vs L2Approach.lean boundary unclear**
- L2Approach.lean contains single theorem `l2_contractability_bound`
- L2Helpers.lean contains supporting lemmas
- Boundary is conceptually backwards

**Recommendation:** Merge L2Approach.lean into L2Helpers.lean

**Impact:**
- Eliminate 359-line orphaned file
- Consolidate 2 files into 1 for clearer organization
- Remove ~100-150 lines of duplication

---

### 4.6 Set Algebra and Indicator Duplicates

**Analysis findings:**

**EXACT DUPLICATION (44 lines):**
- `ViaMartingale.lean` (lines 636-679): 5 indicator algebra lemmas
- `MartingaleHelpers.lean` (lines 347-392): **Exact same lemmas**

**Duplicated lemmas:**
1. `indicator_mul_indicator_eq_indicator_inter`
2. `indicator_comp_preimage`
3. `indicator_binary`
4. `indicator_le_const`
5. `indicator_nonneg`

**Recommendation:** **DELETE from ViaMartingale.lean immediately**

**Impact:** Eliminates 44 lines of 100% duplication

---

### 4.7 Sequence and Finset Utilities

**Analysis findings:**

**Well-organized existing infrastructure:**
- `MartingaleHelpers.lean`: Finset ordering (`orderEmbOfFin_*`)
- `L2Helpers.FinIndexHelpers`: Finset reindexing (lines 462-587)

**Potential extraction:**
- FinIndexHelpers could be promoted to shared `Util/FinsetIndex.lean` if used elsewhere
- Currently only used in ViaL2

**Recommendation:** Keep as-is (no duplication detected)

---

## Summary of Additional Opportunities (REVISED)

### New Files to Create (Phase 4)

**REVISED UNDERSTANDING:** Most are mathlib wrappers, not gaps!

| File | Purpose | Lines | Priority | Impact |
|------|---------|-------|----------|--------|
| `Probability/IntegrationHelpers.lean` | Wrappers around mathlib (Hölder, integral_map) | ~60 | **HIGH** | -220 lines (170 C-S + 54 boilerplate) |
| `Util/StrictMono.lean` | 2 Fin-specific lemmas only | ~40 | **MEDIUM** | -200 lines (rest via mathlib) |
| `Ergodic/NaturalExtension.lean` | Two-sided systems | ~300 | **LOW** | Organization |

**Key changes:**
- **Merged** HolderHelpers into IntegrationHelpers (both are just mathlib wrappers)
- **Drastically reduced** StrictMono (only 2 project-specific lemmas; rest via `StrictMono.comp`, `OrderIso`)
- **Total new code:** ~100 lines (not ~380!), but **eliminates ~420 lines** of duplication

### Files to Delete/Merge

| File | Action | Reason | Lines Saved |
|------|--------|--------|-------------|
| `CovarianceStructure.lean` | **DELETE** | Orphaned, duplicates L2Helpers | -359 |
| `L2Approach.lean` | **MERGE** into L2Helpers | Unclear boundary | -50 |
| `ViaMartingale.lean` (636-679) | **DELETE** duplicates | Exact copy of MartingaleHelpers | -44 |

### Mathlib Contribution Opportunities

| Component | Lines | Destination in mathlib |
|-----------|-------|------------------------|
| KoopmanMeanErgodic.lean | 347 | `Mathlib.Dynamics.Ergodic.MeanErgodic` |
| ProjectionLemmas.lean | 227 | `Mathlib.Analysis.InnerProductSpace.Projection` |
| InvariantSigma (parts) | ~200 | `Mathlib.Dynamics.Ergodic.Invariant` |

---

## Updated Total Impact Estimates

**Original plan (Phases 1-3):**
- Duplication eliminated: ~780 lines
- New infrastructure: ~900 lines
- Net change: +120 lines (+1%)

**With Phase 4 additions:**
- **Additional duplication eliminated:** ~677 lines
- **Additional infrastructure created:** ~380 lines
- **Files deleted:** 2 (CovarianceStructure, L2Approach merged)
- **Mathlib extraction:** ~774 lines

**Grand total:**
- **Duplication eliminated:** ~1,457 lines
- **New shared infrastructure:** ~1,280 lines
- **Mathlib contributions:** ~774 lines
- **Net project change:** -951 lines (-8.4%)

### Updated File Projections

| File | Current | After Phase 1-3 | After Phase 4 | Total Change |
|------|---------|-----------------|---------------|--------------|
| ViaL2.lean | 3,801 | ~3,650 | ~3,400 | **-401 (-10.6%)** |
| ViaKoopman.lean | 4,862 | ~4,600 | ~3,800 | **-1,062 (-21.8%)** |
| ViaMartingale.lean | 2,620 | ~2,250 | ~2,200 | **-420 (-16%)** |
| CovarianceStructure | 359 | 359 | **0 (deleted)** | **-359** |
| L2Approach | 436 | 436 | **0 (merged)** | **-436** |
| **New helpers** | 0 | ~900 | ~1,280 | **+1,280** |
| **Mathlib (external)** | 0 | 0 | ~774 | **(external)** |
| **Net total** | 11,283 | 11,400 | **10,680** | **-603 (-5.3%)** |

---

## Implementation Priority Ranking

### Tier 1: Immediate High-Value Actions (1 day) — REVISED

1. **Delete ViaMartingale.lean lines 636-679** - Exact duplicates (5 minutes)
2. **Create IntegrationHelpers.lean** - Mathlib wrappers for Hölder + integral_map (3 hours)
   - Includes `abs_integral_mul_le_L2` (Cauchy-Schwarz wrapper)
   - Includes `integral_pushforward_id`, `integral_pushforward_sq_diff`
   - **Eliminates:** 170 (C-S) + 54 (boilerplate) = 224 lines
3. **Delete CovarianceStructure.lean** - Orphaned file (30 minutes)
4. **Merge L2Approach into L2Helpers** - Consolidate structure (2 hours)

**Total impact:** -677 lines, 1 day effort

### Tier 2: Medium-Value Refactoring (2 hours) — DRASTICALLY SIMPLIFIED

5. **Create StrictMono.lean** - Just 2 Fin-specific lemmas (2 hours)
   - `strictMono_Fin_ge_id`
   - `strictMono_fin_cases`
   - Rest replaced by mathlib's `StrictMono.comp`, `OrderIso.strictMono`
   - **Eliminates:** 200 lines, **creates:** ~40 lines

**Total impact:** -200 lines (net -160), 2 hours effort

**Combined Tier 1+2:** -877 lines eliminated, ~100 lines new helpers, **net -777 lines**, 1.25 days

### Tier 3: Long-Term Organization (1-2 weeks)

7. **Extract ergodic theory to Ergodic/** - Prepare for mathlib (3 days)
8. **Polish and submit mathlib PRs** - Contribute back (1 week)
9. **Extract Stieltjes infrastructure** - If other proofs need it (2 days)

**Total impact:** Organization + community contribution

---

## Phase 4 Execution Plan

### Week 1: Quick Wins

**Day 1:**
- Delete indicator duplicates from ViaMartingale
- Create HolderHelpers.lean
- Extract and consolidate Cauchy-Schwarz proofs
- **Deliverable:** -214 lines

**Day 2:**
- Delete CovarianceStructure.lean
- Merge L2Approach.lean into L2Helpers.lean
- Update imports in ViaL2.lean
- **Deliverable:** -439 lines consolidated

**Verification:** All files still compile, all tests pass

### Week 2: Infrastructure Consolidation

**Day 3-4:**
- Create IntegrationHelpers.lean
- Extract integral_map pattern helpers
- Update 18+ call sites across files
- **Deliverable:** -54 boilerplate instances

**Day 5:**
- Create StrictMono.lean
- Consolidate from Contractability, L2Helpers, MartingaleHelpers
- Update imports
- **Deliverable:** Organized utilities

**Verification:** Run full lake build, check for regressions

### Week 3: Ergodic Theory Extraction (Optional)

**Day 6-8:**
- Create Ergodic/NaturalExtension.lean
- Extract two-sided infrastructure from ViaKoopman
- Reorganize ergodic theory files
- **Deliverable:** Clear separation

**Day 9-10:**
- Polish KoopmanMeanErgodic, ProjectionLemmas, InvariantSigma
- Prepare mathlib PR drafts
- Write documentation
- **Deliverable:** Mathlib-ready contributions

---

## Risks and Considerations (Phase 4)

### Risk: Over-Extraction

**Concern:** Extracting too much too early, before proofs are stable

**Mitigation:**
- Execute Tier 1 only until ViaL2 is 95%+ complete
- Defer Tier 2-3 until all proofs compile
- Keep extraction reversible (git branches)

### Risk: Mathlib Submission Overhead

**Concern:** Upstreaming to mathlib is time-consuming

**Mitigation:**
- Treat as separate long-term project
- Extract to Ergodic/ first as staging area
- Only submit when de Finetti proof is published

### Risk: Breaking Compilation

**Concern:** Deleting files might break hidden dependencies

**Mitigation:**
- Verify with `grep -r "CovarianceStructure" **/*.lean`
- Check import graphs before deletion
- Test compilation after every change

---

**End of Refactoring Plan**

---

## 📋 Summary of Major Revisions (2025-10-18)

This plan has been significantly updated from the original version with the following structural improvements:

### Architectural Changes

1. **Phase 0 Added:** Immediate zero-risk quick wins (delete duplicates, create skeletons)

2. **Two Canonical Tail Viewpoints:**
   - Separated `tailShift` (path-space) from `tailProcess` (process-relative)
   - Added explicit bridge lemmas to connect viewpoints
   - Prevents `rfl` failures and type mismatches

3. **Neutral Infrastructure Naming:**
   - Created `PathSpace/CylinderHelpers.lean` instead of extending "MartingaleHelpers"
   - Better organization for eventual mathlib contribution

4. **Phase 1 Split into 1a/1b:**
   - **Phase 1a:** Prove load-bearing bridges FIRST
   - **Phase 1b:** Extract infrastructure using those bridges
   - Reduces risk of extraction failure

5. **Operator-Theoretic CE Approach:**
   - `condExp_L1_lipschitz` as central lemma
   - Pull-out as corollary, not independent proof
   - Mathlib-ready formulation

6. **Mathlib-Ready Design:**
   - Helper files only import mathlib (no project dependencies)
   - Modular single-topic organization
   - Comprehensive docstrings for contribution

7. **Mathlib Wrapper Identification (Phase 4 Revision):**
   - **Cauchy-Schwarz:** Already exists as Hölder with p=q=2 (`integral_mul_norm_le_Lp_mul_Lq`)
   - **StrictMono:** Composition and arithmetic via `StrictMono.comp` and `OrderIso`
   - **Integration helpers:** Wrappers around `integral_map`, not true gaps
   - **Result:** Phase 4 creates ~100 lines (not ~380!), eliminates ~420 lines

### Key Success Criteria

- **Load-bearing proofs** (`tailProcess_coords_eq_tailShift`, `condExp_L1_lipschitz`) must be proven in Phase 1a
- **Type safety** via bridges, not `abbrev` aliases
- **Minimal dependencies** for helper files (mathlib only)
- **Proof decomposition** into reusable sublemmas

### Execution Gates

- **Phase 0:** Execute NOW (no prerequisites)
- **Phase 1:** Execute when ViaL2 reaches ~95% completion
- **Phase 2-4:** Execute after Phase 1 is stable

---

*This document should be reviewed and updated when the project reaches 95%+ completion on ViaL2 and ViaKoopman compilation errors are resolved.*

*Original analysis completed 2025-10-18.*
*Major structural revision completed 2025-10-18 incorporating two-viewpoint tail approach, operator-theoretic CE, and mathlib-ready design principles.*
