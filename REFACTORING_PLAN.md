# Refactoring Plan: Shared Infrastructure Extraction

**Generated:** 2025-10-18
**Status:** Planning phase - to be executed when proofs are more complete
**Goal:** Eliminate duplication across ViaL2, ViaKoopman, and ViaMartingale proof approaches

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

## 🎯 PHASE 1: Fix Critical Duplication (High Impact)

**Estimated effort:** 2-3 days
**Priority:** HIGH - Execute when ViaL2 reaches 95%+ completion

### 1.1 Create TailSigmaHelpers.lean

**Purpose:** Consolidate 4 different tail σ-algebra definitions into one canonical version

#### Current Duplication

**InvariantSigma.lean (line 86) - Canonical definition:**
```lean
def tailSigma : MeasurableSpace (Ω[α]) :=
  ⨅ n : ℕ, MeasurableSpace.comap (fun ω => (shift^[n]) ω) inferInstance
```

**ViaL2.lean (lines 1527-1568) - Via intermediate `tailFamily`:**
```lean
def tailFamily (X : ℕ → Ω → β) (n : ℕ) : MeasurableSpace Ω :=
  ⨆ k : ℕ, MeasurableSpace.comap (fun ω => X (n + k) ω) ‹_›

def tailSigma (X : ℕ → Ω → β) : MeasurableSpace Ω :=
  ⨅ n : ℕ, tailFamily X n
```
- Also includes: `antitone_tailFamily`, `tailSigma_le_tailFamily`, `tailSigma_le`

**ViaMartingale.lean (lines 160-537) - Via `revFiltration`:**
```lean
def tailSigma (X : ℕ → Ω → α) : MeasurableSpace Ω :=
  ⨅ m, revFiltration X m
```
- Also includes: 9 supporting lemmas (`tailSigma_le_futureFiltration`, `indicator_tailMeasurable`, etc.)

**CommonEnding.lean (line 150) - Placeholder:**
```lean
def tailSigmaAlgebra (α : Type*) [MeasurableSpace α] : MeasurableSpace (ℕ → α) :=
  -- Placeholder: uses invariantSigmaField α as proxy
  invariantSigmaField α
```

#### Extraction Plan

**New file:** `Exchangeability/DeFinetti/TailSigmaHelpers.lean`

```lean
-- Exchangeability/DeFinetti/TailSigmaHelpers.lean

import Exchangeability.DeFinetti.InvariantSigma

namespace Exchangeability.DeFinetti

/-- Canonical tail σ-algebra definition (re-exported from InvariantSigma) -/
open InvariantSigma (tailSigma)

/-- Bridge lemma: Canonical characterization as infinite intersection -/
lemma tailSigma_eq_iInf_comap_shift {α : Type*} [MeasurableSpace α] :
    tailSigma = ⨅ n : ℕ, MeasurableSpace.comap (shift^[n]) inferInstance :=
  rfl

/-- Bridge lemma: Connection to martingale formulation via reverse filtration -/
lemma tailSigma_eq_iInf_futureFiltration {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → α) :
    tailSigma X = ⨅ m, revFiltration X m :=
  sorry -- Prove equivalence

/-- Bridge lemma: Connection to L² formulation via tailFamily -/
lemma tailSigma_eq_iInf_tailFamily {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → α) :
    tailSigma X = ⨅ n : ℕ, (⨆ k : ℕ, MeasurableSpace.comap (X (n + k)) ‹_›) :=
  sorry -- Prove equivalence

/-- General lemma: Tail σ-algebra is sub-σ-algebra of ambient space -/
lemma tailSigma_le_ambient {Ω : Type*} [MeasurableSpace Ω] (X : ℕ → Ω → α) :
    tailSigma X ≤ (inferInstance : MeasurableSpace Ω) :=
  sorry

/-- General lemma: Indicators of tail sets are tail-measurable -/
lemma indicator_tailMeasurable {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → α) {S : Set Ω} (hS : MeasurableSet[tailSigma X] S) :
    Measurable[tailSigma X] (S.indicator (fun _ => (1 : ℝ))) :=
  sorry

/-- General lemma: σ-finiteness property -/
lemma sigmaFinite_trim_tailSigma {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [SigmaFinite μ] (X : ℕ → Ω → α) :
    SigmaFinite (μ.trim (tailSigma_le_ambient X)) :=
  sorry

end Exchangeability.DeFinetti
```

#### Files to Update

**ViaL2.lean:**
```lean
-- Add import at top
import Exchangeability.DeFinetti.TailSigmaHelpers

-- Keep tailFamily (ViaL2-specific)
-- Replace tailSigma definition with:
abbrev tailSigma (X : ℕ → Ω → β) : MeasurableSpace Ω :=
  TailSigmaHelpers.tailSigma X

-- Use bridge lemma in proofs that need equivalence
```

**ViaMartingale.lean:**
```lean
-- Add import
import Exchangeability.DeFinetti.TailSigmaHelpers

-- Replace tailSigma definition with import
-- Keep revFiltration and futureFiltration (proof-specific)
-- Use bridge lemma where needed
```

**CommonEnding.lean:**
```lean
-- Replace tailSigmaAlgebra with:
import Exchangeability.DeFinetti.TailSigmaHelpers
abbrev tailSigmaAlgebra := TailSigmaHelpers.tailSigma
```

#### Estimated Impact

- **Lines extracted to TailSigmaHelpers:** ~100 lines
- **Duplication eliminated:** ~150-200 lines across 3 files
- **Net reduction:** -50 to -100 lines
- **ViaL2:** -50 lines
- **ViaMartingale:** -50 lines
- **CommonEnding:** -10 lines

---

### 1.2 Extract Product Measure Infrastructure

**Purpose:** Centralize cylinder sets, projections, and indicator product infrastructure

#### Already Extracted to MartingaleHelpers.lean

**Current status:** ViaMartingale has already extracted some infrastructure to MartingaleHelpers.lean

**In MartingaleHelpers.lean (lines 100-460):**
- `tailCylinder` (line 100) + 6 lemmas
- `cylinder` (line 186) + 5 lemmas
- `finCylinder` (line 190) + 3 lemmas
- `firstRCylinder` (line 232) + 8 lemmas
- `firstRMap` / `firstRSigma` (lines 224-288) + 3 lemmas
- `drop` (line 400) + 4 lemmas
- **Indicator algebra:** 5 lemmas (lines 348-391)

**Total already extracted:** ~27 definitions/lemmas

#### Still Needs Extraction

**From ViaMartingale.lean:**

1. **Lines 636-679: DELETE (exact duplicates)**
   - `indicator_mul_indicator_eq_indicator_inter` (line 636)
   - `indicator_comp_preimage` (line 646)
   - `indicator_binary` (line 655)
   - `indicator_le_const` (line 664)
   - `indicator_nonneg` (line 673)
   - **Action:** Delete these 5 lemmas (already in MartingaleHelpers 348-391)

2. **Lines 579-740: Extract `indProd` infrastructure (~160 lines)**
   ```lean
   def indProd (r : ℕ) (S : Fin r → Set α) : (ℕ → α) → ℝ := ...
   ```
   - `indProd_as_indicator` (line 583)
   - `indProd_eq_firstRCylinder_indicator` (line 611)
   - `indProd_integrable` (line 620)
   - `indProd_stronglyMeasurable` (line 682)
   - `indProd_nonneg_le_one` (line 693)
   - `indProd_zero` (line 702)
   - `indProd_univ` (line 709)
   - `indProd_measurable` (line 716)
   - `indProd_mul` (line 723)
   - `indProd_inter_eq` (line 735)
   - **Total:** 1 definition + 10 lemmas

**From ViaKoopman.lean:**

3. **Lines 2554-2640: Extract cylinder function infrastructure (~90 lines)**
   ```lean
   def cylinderFunction (m : ℕ) (f : Fin m → α → ℝ) : (ℕ → α) → ℝ := ...
   def productCylinder (m : ℕ) (f : Fin m → α → ℝ) : (ℕ → α) → ℝ := ...
   ```
   - `productCylinder_eq_cylinder` (line 2562)
   - `measurable_cylinderFunction` (line 2567)
   - `measurable_productCylinder` (line 2578)
   - `productCylinder_bounded` (line 2590)
   - `productCylinder_memLp` (line 2616)
   - **Total:** 2 definitions + 5 lemmas

#### Extraction Plan

**Extend:** `Exchangeability/DeFinetti/MartingaleHelpers.lean`

Add after existing cylinder infrastructure (around line 460):

```lean
/-! ### Product Indicators -/

/-- Product of indicator functions for finite cylinder -/
def indProd (r : ℕ) (S : Fin r → Set α) : (ℕ → α) → ℝ :=
  fun ω => ∏ i : Fin r, (S i).indicator (fun _ => (1 : ℝ)) (ω i)

lemma indProd_as_indicator (r : ℕ) (S : Fin r → Set α) :
    indProd r S = (firstRCylinder r S).indicator (fun _ => (1 : ℝ)) := sorry

-- ... (9 more lemmas)

/-! ### Cylinder Functions -/

/-- Function on path space depending only on finitely many coordinates -/
def cylinderFunction (m : ℕ) (f : Fin m → α → ℝ) : (ℕ → α) → ℝ :=
  fun ω => ∏ k : Fin m, f k (ω k)

/-- Product cylinder (alias for cylinderFunction) -/
abbrev productCylinder := cylinderFunction

-- ... (5 lemmas)
```

#### Files to Update

**ViaMartingale.lean:**
- **Delete lines 636-679** (duplicate indicator algebra)
- **Move lines 579-740** to MartingaleHelpers.lean
- Add `open MartingaleHelpers (indProd)` to namespace

**ViaKoopman.lean:**
- **Move lines 2554-2640** to MartingaleHelpers.lean
- Add import and open statement

#### Estimated Impact

- **Lines added to MartingaleHelpers:** ~250 lines
- **Lines deleted from ViaMartingale:** ~295 lines (160 moved + 45 duplicates + 90 reorganization)
- **Lines deleted from ViaKoopman:** ~90 lines
- **Net change:**
  - **ViaMartingale:** -295 lines (-11%)
  - **ViaKoopman:** -90 lines (-2%)
  - **MartingaleHelpers:** +250 lines
  - **Total:** -135 lines

---

### 1.3 Centralize Conditional Expectation Lemmas

**Purpose:** Extract general conditional expectation infrastructure from proof-specific files

#### Current Situation

**CondExp.lean already has:**
- `integrable_indicator_comp` (line 119)
- `condIndep_of_indicator_condexp_eq` (line 184)
- `condExp_indicator_mul_indicator_of_condIndep` (line 280)
- `condexp_indicator_inter_bridge` (line 356)
- `condexp_indicator_eq_of_pair_law_eq` (line 402) - KEY BRIDGE LEMMA
- `condexp_indicator_eq_of_agree_on_future_rectangles` (line 507)

**Scattered in ViaKoopman.lean (general infrastructure, should be centralized):**

1. **Line 874 AND 2464: `integrable_of_bounded` (EXACT DUPLICATE!)**
   ```lean
   private lemma integrable_of_bounded
       {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
       {f : Ω → ℝ} (hf : Measurable f) (hbd : ∃ C, ∀ ω, |f ω| ≤ C) :
       Integrable f μ
   ```
   - **Action:** Delete one copy, move the other to CondExp.lean

2. **Line 881: `integrable_of_bounded_mul`**
   ```lean
   lemma integrable_of_bounded_mul [IsFiniteMeasure μ]
       {f g : Ω → ℝ} (hf : Integrable f μ) (hg : Measurable g)
       (hbd : ∃ C, ∀ ω, |g ω| ≤ C) :
       Integrable (f * g) μ
   ```
   - **Action:** Move to CondExp.lean (general utility)

3. **Line 710: `condExp_abs_le_of_abs_le`**
   ```lean
   lemma condExp_abs_le_of_abs_le {m : MeasurableSpace Ω} [hm : m ≤ ‹_›]
       {f g : Ω → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
       (hfg : ∀ ω, |f ω| ≤ |g ω|) :
       ∀ᵐ ω ∂μ, |μ[f|m] ω| ≤ |μ[g|m] ω|
   ```
   - **Action:** Move to CondExp.lean (general CE property)

4. **Line 748: `condExp_L1_lipschitz`**
   ```lean
   lemma condExp_L1_lipschitz {m : MeasurableSpace Ω} [hm : m ≤ ‹_›]
       {f g : Ω → ℝ} (hf : Integrable f μ) (hg : Integrable g μ) :
       ∫ ω, |μ[f|m] ω - μ[g|m] ω| ∂μ ≤ ∫ ω, |f ω - g ω| ∂μ
   ```
   - **Action:** Move to CondExp.lean (general CE property)

5. **Line 769: `condExp_mul_pullout`**
   ```lean
   lemma condExp_mul_pullout {m : MeasurableSpace Ω} [hm : m ≤ ‹_›]
       {f g : Ω → ℝ} (hf : Integrable f μ) (hg_meas : Measurable[m] g)
       (hg_bd : ∃ C, ∀ ω, |g ω| ≤ C) (hfg : Integrable (f * g) μ) :
       μ[f * g|m] =ᵐ[μ] μ[f|m] * g
   ```
   - **Action:** Move to CondExp.lean (standard pull-out property)

**Proof-specific (keep in ViaKoopman.lean):**
- All ergodic theory / Koopman-specific CE lemmas (~16 lemmas)
- Factorization lemmas specific to shift-invariance
- Birkhoff averaging lemmas

#### Extraction Plan

**Add to:** `Exchangeability/Probability/CondExp.lean`

Add section around line 600 (after existing infrastructure):

```lean
/-! ### General Conditional Expectation Utilities -/

/-- Bounded measurable functions are integrable on finite measures -/
lemma integrable_of_bounded
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {f : Ω → ℝ} (hf : Measurable f) (hbd : ∃ C, ∀ ω, |f ω| ≤ C) :
    Integrable f μ := by
  sorry

/-- Product of integrable and bounded functions is integrable -/
lemma integrable_of_bounded_mul [IsFiniteMeasure μ]
    {f g : Ω → ℝ} (hf : Integrable f μ) (hg : Measurable g)
    (hbd : ∃ C, ∀ ω, |g ω| ≤ C) :
    Integrable (f * g) μ := by
  sorry

/-! ### Conditional Expectation Bounds and Inequalities -/

/-- Conditional expectation preserves pointwise absolute value bounds -/
lemma condExp_abs_le_of_abs_le {m : MeasurableSpace Ω} [hm : m ≤ ‹_›]
    {f g : Ω → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (hfg : ∀ ω, |f ω| ≤ |g ω|) :
    ∀ᵐ ω ∂μ, |μ[f|m] ω| ≤ |μ[g|m] ω| := by
  sorry

/-- Conditional expectation is L¹-Lipschitz -/
lemma condExp_L1_lipschitz {m : MeasurableSpace Ω} [hm : m ≤ ‹_›]
    {f g : Ω → ℝ} (hf : Integrable f μ) (hg : Integrable g μ) :
    ∫ ω, |μ[f|m] ω - μ[g|m] ω| ∂μ ≤ ∫ ω, |f ω - g ω| ∂μ := by
  sorry

/-! ### Conditional Expectation Pull-Out Property -/

/-- Pull out m-measurable bounded functions from conditional expectation -/
lemma condExp_mul_pullout {m : MeasurableSpace Ω} [hm : m ≤ ‹_›]
    {f g : Ω → ℝ} (hf : Integrable f μ) (hg_meas : Measurable[m] g)
    (hg_bd : ∃ C, ∀ ω, |g ω| ≤ C) (hfg : Integrable (f * g) μ) :
    μ[f * g|m] =ᵐ[μ] μ[f|m] * g := by
  sorry
```

#### Files to Update

**ViaKoopman.lean:**
- **Delete line 2464** (duplicate `integrable_of_bounded`)
- **Delete lines 710-881** (move to CondExp.lean)
- **Add import:** `open CondExp (integrable_of_bounded condExp_abs_le_of_abs_le ...)`
- Keep all Koopman-specific CE lemmas

#### Estimated Impact

- **Lines moved to CondExp.lean:** ~80 lines
- **Lines deleted from ViaKoopman:** ~120 lines (80 moved + 40 duplicate)
- **Net change:**
  - **ViaKoopman:** -120 lines (-2.5%)
  - **CondExp.lean:** +80 lines
  - **Total:** -40 lines

---

### Phase 1 Summary

**Total Impact:**
- **New helper files:** TailSigmaHelpers.lean (~100 lines)
- **Extended files:** MartingaleHelpers.lean (+250 lines), CondExp.lean (+80 lines)
- **Reductions:**
  - ViaL2: -50 lines (-1.3%)
  - ViaKoopman: -210 lines (-4.3%)
  - ViaMartingale: -295 lines (-11.3%)
- **Net project change:** +90 lines (+0.8%)
- **Duplication eliminated:** ~560 lines

**Compilation verification checklist:**
- [ ] TailSigmaHelpers.lean compiles standalone
- [ ] MartingaleHelpers.lean compiles with new additions
- [ ] CondExp.lean compiles with new lemmas
- [ ] ViaL2.lean compiles with new imports
- [ ] ViaKoopman.lean compiles with new imports
- [ ] ViaMartingale.lean compiles with deletions
- [ ] All three Via* files still prove their main theorems

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
Core.lean, Contractability.lean, ConditionallyIID.lean
  ↓
TailSigmaHelpers.lean, MartingaleHelpers.lean, CondExp.lean
  ↓
ViaL2.lean, ViaKoopman.lean, ViaMartingale.lean
  ↓
Theorem.lean, TheoremViaL2.lean, TheoremViaKoopman.lean, TheoremViaMartingale.lean
```

**Verification commands:**
```bash
# Check import graph
lake exe graph Exchangeability.DeFinetti.ViaL2 > /tmp/vial2_deps.dot
lake exe graph Exchangeability.DeFinetti.ViaKoopman > /tmp/viakoopman_deps.dot
lake exe graph Exchangeability.DeFinetti.ViaMartingale > /tmp/viamartingale_deps.dot

# Look for cycles
grep "TailSigmaHelpers.*Via" /tmp/*.dot
grep "MartingaleHelpers.*Via" /tmp/*.dot
```

**If circular dependencies found:**
- Identify the problematic import
- Either move the lemma or split the file
- Re-verify after fix

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

### Phase 1 Implementation (2-3 days)

#### Day 1: TailSigmaHelpers.lean

**Morning:**
1. Create `Exchangeability/DeFinetti/TailSigmaHelpers.lean`
2. Write canonical `tailSigma` re-export
3. Write bridge lemmas (with sorry placeholders)
4. Verify file compiles standalone

**Afternoon:**
5. Update `ViaL2.lean` to import TailSigmaHelpers
6. Replace ViaL2's `tailSigma` with import
7. Update proofs to use bridge lemmas
8. Verify ViaL2 compiles

**Evening:**
9. Update `ViaMartingale.lean` similarly
10. Update `CommonEnding.lean`
11. Verify all files compile
12. Commit: `feat: Add TailSigmaHelpers with canonical tail σ-algebra`

---

#### Day 2: ProductMeasureHelpers.lean (extend MartingaleHelpers)

**Morning:**
1. Delete duplicate indicator algebra from ViaMartingale (lines 636-679)
2. Verify ViaMartingale still compiles (should import from MartingaleHelpers)
3. Commit: `refactor: Remove duplicate indicator algebra from ViaMartingale`

**Afternoon:**
4. Extract `indProd` from ViaMartingale to MartingaleHelpers
5. Update ViaMartingale to import `indProd`
6. Verify ViaMartingale compiles

**Evening:**
7. Extract `productCylinder` from ViaKoopman to MartingaleHelpers
8. Update ViaKoopman to import `productCylinder`
9. Verify ViaKoopman compiles (may still have pre-existing errors)
10. Commit: `feat: Centralize product measure infrastructure in MartingaleHelpers`

---

#### Day 3: ConditionalExpectationHelpers (extend CondExp.lean)

**Morning:**
1. Add `integrable_of_bounded` to CondExp.lean
2. Add other 4 general CE lemmas to CondExp.lean
3. Verify CondExp.lean compiles

**Afternoon:**
4. Delete duplicate `integrable_of_bounded` from ViaKoopman (line 2464)
5. Delete/move other CE lemmas from ViaKoopman
6. Update ViaKoopman imports
7. Verify ViaKoopman compiles

**Evening:**
8. Run full project build: `lake build`
9. Check for new warnings or errors
10. Update CLAUDE.md with new file structure
11. Commit: `feat: Centralize general CE lemmas in CondExp.lean`
12. **MERGE CHECKPOINT:** Phase 1 complete

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
- `Exchangeability/DeFinetti/ViaL2.lean` (3,801 lines)
- `Exchangeability/DeFinetti/ViaKoopman.lean` (4,862 lines)
- `Exchangeability/DeFinetti/ViaMartingale.lean` (2,620 lines)
- `Exchangeability/DeFinetti/InvariantSigma.lean` (tail σ-algebra)
- `Exchangeability/DeFinetti/MartingaleHelpers.lean` (cylinder sets)
- `Exchangeability/Probability/CondExp.lean` (conditional expectation)

### New Files Created
- `Exchangeability/DeFinetti/TailSigmaHelpers.lean` (~100 lines)
- Possibly: `Exchangeability/Probability/IndicatorIntegrals.lean` (~50 lines)

---

## 🔍 PHASE 4: Additional Refactoring Opportunities (Extended Analysis)

**Generated:** 2025-10-18 (Extended analysis session)
**Status:** Additional opportunities identified beyond original Phase 1-3 plan

This section documents additional refactoring opportunities discovered through comprehensive deep-dive analysis of the codebase.

---

### 4.1 Integration and L^p Space Utilities

**Analysis findings:**

**HIGH PRIORITY: Hölder/Cauchy-Schwarz Duplication (170 lines)**

**Exact 90-line duplication found:**
- `CovarianceStructure.lean` (lines 213-290): Cauchy-Schwarz via Hölder inequality
- `ViaL2.lean` (lines 329-386): Identical proof structure

**Recommended action:** Create `Exchangeability/Probability/HolderHelpers.lean`

```lean
/-- Cauchy-Schwarz for L² functions via Hölder inequality. -/
lemma integral_mul_le_sqrt_integral_sq_mul_sqrt_integral_sq
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f g : Ω → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |∫ ω, f ω * g ω ∂μ|
      ≤ Real.sqrt (∫ ω, (f ω)^2 ∂μ) * Real.sqrt (∫ ω, (g ω)^2 ∂μ)
```

**Impact:** Eliminates 170 lines of duplication

**MEDIUM PRIORITY: `integral_map` Boilerplate Pattern (54 lines)**

**Pattern appearing 18+ times across files:**
```lean
have h_ae : AEStronglyMeasurable (id : ℝ → ℝ) (Measure.map (X k) μ) :=
  aestronglyMeasurable_id
exact (integral_map (hX_meas k).aemeasurable h_ae).symm
```

**Locations:**
- CovarianceStructure.lean: 8 times
- ViaL2.lean: 10 times
- ViaKoopman.lean: 1 time

**Recommended action:** Create helper in `IntegrationHelpers.lean`:

```lean
lemma integral_pushforward_id {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    {μ : Measure Ω} {f : Ω → ℝ} (hf : Measurable f) :
    ∫ ω, f ω ∂μ = ∫ x, x ∂(Measure.map f μ)

lemma integral_pushforward_sq_diff {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {f : Ω → ℝ} (hf : Measurable f) (c : ℝ) :
    ∫ ω, (f ω - c)^2 ∂μ = ∫ x, (x - c)^2 ∂(Measure.map f μ)
```

**Impact:** Eliminates 54 lines of boilerplate

**LOW PRIORITY: Indicator Integration Lemmas**

Already in ViaKoopman.lean (lines 2472-2488), could be moved to shared location:
- `integral_indicator_one`
- `integral_indicator_const`

**Decision:** Move to `IntegrationHelpers.lean` for consistency

---

### 4.2 StrictMono (Strictly Monotone) Utilities

**Analysis findings:**

**Duplicated across 3 files:**
- `Contractability.lean` (lines 306-500): 15 lemmas
- `L2Helpers.lean` (lines 121-137): 2 lemmas
- `MartingaleHelpers.lean` (lines 158-177): 1 lemma

**Core lemmas to extract:**

```lean
-- Arithmetic preservation
lemma strictMono_add_left {m : ℕ} (k : Fin m → ℕ) (hk : StrictMono k) (c : ℕ) :
    StrictMono (fun i => c + k i)

lemma strictMono_add_right {m : ℕ} (k : Fin m → ℕ) (hk : StrictMono k) (c : ℕ) :
    StrictMono (fun i => k i + c)

-- Composition
lemma strictMono_comp {m n : ℕ} (f : Fin m → Fin n) (g : Fin n → ℕ)
    (hf : StrictMono f) (hg : StrictMono g) : StrictMono (fun i => g (f i))

-- Identity and bounds
lemma strictMono_Fin_ge_id {m : ℕ} {k : Fin m → ℕ} (hk : StrictMono k) (i : Fin m) :
    i.val ≤ k i

lemma fin_val_strictMono {n : ℕ} : StrictMono (fun i : Fin n => i.val)

-- Fin.cases extension
lemma strictMono_fin_cases {n : ℕ} {f : Fin n → ℕ} (hf : StrictMono f) {a : ℕ}
    (ha : ∀ i, a < f i) : StrictMono (Fin.cases a (fun i => f i))
```

**Recommended action:** Create `Exchangeability/Util/StrictMono.lean`

**Impact:** Consolidates ~200 lines of StrictMono infrastructure

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

## Summary of Additional Opportunities

### New Files to Create (Phase 4)

| File | Purpose | Lines | Priority | Impact |
|------|---------|-------|----------|--------|
| `Probability/HolderHelpers.lean` | Cauchy-Schwarz duplication | ~100 | **HIGH** | -170 lines |
| `Probability/IntegrationHelpers.lean` | integral_map boilerplate | ~80 | **MEDIUM** | -54 lines |
| `Util/StrictMono.lean` | StrictMono utilities | ~200 | **MEDIUM** | -200 lines |
| `Ergodic/NaturalExtension.lean` | Two-sided systems | ~300 | **LOW** | Organization |

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

### Tier 1: Immediate High-Value Actions (1-2 days)

1. **Delete ViaMartingale.lean lines 636-679** - Exact duplicates (5 minutes)
2. **Create HolderHelpers.lean** - Eliminates 170-line duplication (3 hours)
3. **Delete CovarianceStructure.lean** - Orphaned file (30 minutes)
4. **Merge L2Approach into L2Helpers** - Consolidate structure (2 hours)

**Total impact:** -653 lines, 1 day effort

### Tier 2: Medium-Value Refactoring (2-3 days)

5. **Create IntegrationHelpers.lean** - Eliminates 54+ boilerplate instances (1 day)
6. **Create StrictMono.lean** - Consolidates utilities (1 day)

**Total impact:** -254 lines, 2 days effort

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

*This document should be reviewed and updated when the project reaches 95%+ completion on ViaL2 and ViaKoopman compilation errors are resolved.*

*Extended analysis completed 2025-10-18. Phase 4 recommendations add significant additional refactoring opportunities beyond original plan.*
