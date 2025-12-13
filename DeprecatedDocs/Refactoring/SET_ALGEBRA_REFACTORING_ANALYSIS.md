# Set Algebra and Boolean Pattern Refactoring Analysis

## Executive Summary

Comprehensive analysis of set algebra, Boolean patterns, and indicator function lemmas across DeFinetti proof files. Found significant duplication that can be factored into helper modules.

## 1. EXACT DUPLICATES - Ready for Immediate Refactoring

### 1.1 Indicator Algebra Lemmas (100% duplicate)

**Files with exact copies:**
- `MartingaleHelpers.lean` (lines 347-392)
- `ViaMartingale.lean` (lines 636-679)

**Duplicated lemmas:**
```lean
-- All 5 lemmas are EXACTLY the same in both files:

1. indicator_mul_indicator_eq_indicator_inter
   (A B : Set Ω) (c d : ℝ) :
   (A.indicator (fun _ => c)) * (B.indicator (fun _ => d))
     = (A ∩ B).indicator (fun _ => c * d)

2. indicator_comp_preimage
   (f : Ω → α) (B : Set α) (c : ℝ) :
   (B.indicator (fun _ => c)) ∘ f = (f ⁻¹' B).indicator (fun _ => c)

3. indicator_binary
   (A : Set Ω) (ω : Ω) :
   A.indicator (fun _ => (1 : ℝ)) ω = 0 ∨ ... = 1

4. indicator_le_const
   (A : Set Ω) (c : ℝ) (hc : 0 ≤ c) (ω : Ω) :
   A.indicator (fun _ => c) ω ≤ c

5. indicator_nonneg
   (A : Set Ω) (c : ℝ) (hc : 0 ≤ c) (ω : Ω) :
   0 ≤ A.indicator (fun _ => c) ω
```

**Action:** Remove from `ViaMartingale.lean`, use from `MartingaleHelpers.lean`

---

### 1.2 Cylinder Set Lemmas

**Location:** `MartingaleHelpers.lean` (section CylinderBridge)

**Key lemmas:**
```lean
-- Coordinate-wise intersection (line 456)
cylinder_inter {r : ℕ} {C D : Fin r → Set α} :
  cylinder r C ∩ cylinder r D = cylinder r (fun i => C i ∩ D i)

-- Universal cylinder (line 446)
cylinder_univ {r : ℕ} :
  cylinder r (fun _ => Set.univ) = Set.univ

-- Measurability (line 429)
cylinder_measurable_set {r : ℕ} {C : Fin r → Set α}
  (hC : ∀ i, MeasurableSet (C i)) :
  MeasurableSet (cylinder r C)

-- Tail cylinder as preimage (line 411)
tailCylinder_eq_preimage_cylinder {r : ℕ} {C : Fin r → Set α} :
  tailCylinder r C = drop ⁻¹' (cylinder r C)

-- Membership characterization (line 421)
mem_cylinder_iff {r : ℕ} {C : Fin r → Set α} {f : ℕ → α} :
  f ∈ cylinder r C ↔ ∀ i : Fin r, f i ∈ C i
```

**Used in:** `ViaMartingale.lean`, `MartingaleHelpers.lean` itself

**Status:** Already in a good location, just needs to be imported properly

---

## 2. ENNReal Indicator Patterns (in CommonEnding.lean)

### 2.1 ENNReal Conversion Lemmas

**Location:** `CommonEnding.lean` (lines 187-199)

```lean
-- Binary property (line 188)
indicator_mem_zero_one {α : Type*} {s : Set α} {x : α} :
  ENNReal.ofReal (s.indicator (fun _ => (1 : ℝ)) x) ∈ ({0, 1} : Set ENNReal)

-- Boundedness (line 195)
indicator_le_one {α : Type*} {s : Set α} {x : α} :
  ENNReal.ofReal (s.indicator (fun _ => (1 : ℝ)) x) ≤ 1
```

### 2.2 ENNReal Product Lemmas

```lean
-- Product equals zero (line 202)
prod_eq_zero_iff {ι : Type*} [Fintype ι] {f : ι → ENNReal} :
  ∏ i, f i = 0 ↔ ∃ i, f i = 0

-- Product equals one for {0,1}-valued functions (line 216)
prod_eq_one_iff_of_zero_one {ι : Type*} [Fintype ι] {f : ι → ENNReal}
  (hf : ∀ i, f i ∈ ({0, 1} : Set ENNReal)) :
  ∏ i, f i = 1 ↔ ∀ i, f i = 1

-- Product bounded by 1 (line 238)
prod_le_one_of_le_one {ι : Type*} [Fintype ι] {f : ι → ENNReal}
  (hf : ∀ i, f i ≤ 1) :
  ∏ i, f i ≤ 1
```

### 2.3 ENNReal Measurability

```lean
-- Product measurability (line 247)
measurable_prod_ennreal {ι : Type*} [Fintype ι] {Ω : Type*} [MeasurableSpace Ω]
  (f : ι → Ω → ENNReal) (hf : ∀ i, Measurable (f i)) :
  Measurable fun ω => ∏ i, f i ω

-- Indicator composition measurability (line 255)
measurable_indicator_comp {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
  (f : Ω → α) (hf : Measurable f) (s : Set α) (hs : MeasurableSet s) :
  Measurable fun ω => ENNReal.ofReal (s.indicator (fun _ => (1 : ℝ)) (f ω))
```

**Status:** Well-organized, already in CommonEnding.lean

---

## 3. Integration Lemmas for Indicators (ViaKoopman.lean)

### 3.1 Basic Integration

**Location:** `ViaKoopman.lean` (lines 2472-2488)

```lean
-- Integral of 1-valued indicator (line 2472)
@[simp] lemma integral_indicator_one {Ω : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω} {s : Set Ω} (hs : MeasurableSet s) :
  ∫ ω, s.indicator (fun _ => (1 : ℝ)) ω ∂μ = (μ s).toReal

-- Integral of constant-valued indicator (line 2479)
lemma integral_indicator_const {Ω : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω} {s : Set Ω} (hs : MeasurableSet s) (c : ℝ) :
  ∫ ω, s.indicator (fun _ => c) ω ∂μ = c * (μ s).toReal
```

**Proof pattern for `integral_indicator_const`:**
```lean
-- Step 1: Factor out constant
have h_eq : s.indicator (fun _ => c) = fun ω => c * s.indicator (fun _ => (1 : ℝ)) ω := by
  ext ω
  by_cases h : ω ∈ s <;> simp [Set.indicator, h]

-- Step 2: Use linearity
calc ∫ ω, s.indicator (fun _ => c) ω ∂μ
    = ∫ ω, c * s.indicator (fun _ => (1 : ℝ)) ω ∂μ := by rw [h_eq]
  _ = c * ∫ ω, s.indicator (fun _ => (1 : ℝ)) ω ∂μ := integral_const_mul c _
  _ = c * (μ s).toReal := by rw [integral_indicator_one hs]
```

**Usage count:** Used 10+ times in ViaKoopman.lean

---

## 4. RECURRING PROOF PATTERNS

### 4.1 Indicator Multiplication Pattern

**Pattern:** Product of indicators = indicator of intersection

**Occurrences:**
- `MartingaleHelpers.lean:348` (as lemma)
- `ViaMartingale.lean:636` (as lemma)
- `ViaKoopman.lean:3411-3416` (inline proof in longer proof)

**Inline usage in ViaKoopman.lean:**
```lean
have h_indicator_mul : ∀ ω i j,
    (A i).indicator (fun _ => a_coef i) ω * (B j).indicator (fun _ => b_coef j) ω
    = (A i ∩ B j).indicator (fun _ => a_coef i * b_coef j) ω := by
  intro ω i j
  by_cases ha : ω ∈ A i <;> by_cases hb : ω ∈ B j <;>
    simp [Set.indicator, ha, hb, Set.mem_inter_iff]
```

**Recommendation:** Always use lemma version

---

### 4.2 "by_cases → simp indicator" Pattern

**Count:** ~15+ occurrences across files

**Standard form:**
```lean
by_cases h : ω ∈ s <;> simp [Set.indicator, h]
```

**Extended form (for intersection):**
```lean
by_cases hA : ω ∈ A <;> by_cases hB : ω ∈ B <;>
  simp [Set.indicator, hA, hB, Set.mem_inter_iff]
```

**Locations:**
- `MartingaleHelpers.lean:355, 372, 373, 381, 382, 390, 391`
- `ViaMartingale.lean:643, 660, 661, 669, 670, 678, 679`
- `ViaKoopman.lean:2266, 2484, 3306, 3416`

**Recommendation:** This pattern is fine inline (common Lean idiom)

---

### 4.3 MeasurableSet Construction Patterns

**Pattern A:** Intersection of measurable sets
```lean
apply MeasurableSet.inter
· apply MeasurableSet.inter
  · apply MeasurableSet.iInter
    ...
  · ...
· apply MeasurableSet.iInter
  ...
```

**Occurrences:**
- `ViaMartingale.lean:1466-1472` (deeply nested)
- `CommonEnding.lean` (multiple)
- All three proof files

**Pattern B:** Preimage measurability
```lean
exact MeasurableSet.preimage hS_meas (measurable_pi_lambda _ fun i => measurable_pi_apply _)
```

**Occurrences:**
- `ViaMartingale.lean:1983`
- Multiple files for product space measurability

**Recommendation:** Keep inline (standard measurability automation)

---

### 4.4 Rectangle/Cylinder Set Patterns

**Pattern:** Sets defined via `Set.univ_pi`

**Common constructions:**
```lean
-- Rectangle as product (appears 15+ times)
MeasurableSet.univ_pi hB_meas

-- Product of rectangles
(MeasurableSet.univ_pi hA).prod (hB.prod (MeasurableSet.univ_pi hC))

-- Membership characterization
simp only [Set.mem_univ_pi, Set.mem_inter_iff]
```

**Locations:**
- `CommonEnding.lean:809, 820`
- `ViaMartingale.lean:1573, 1736, 2441, 2656` (8+ occurrences)

**Note:** `CommonEnding.lean:439` has `rectangles_isPiSystem` lemma proving rectangles form π-system

**Recommendation:** Create helper lemmas for common patterns

---

## 5. MEASURABILITY AUTOMATION PATTERNS

### 5.1 Indicator Measurability

**Standard application:**
```lean
apply Measurable.indicator
· exact measurable_const
· exact hf hs
```

**Occurrences:** `ViaKoopman.lean:4296, 4302, 4338, 4361, etc.`

**For composition:**
```lean
exact Measurable.indicator measurable_const (hB_meas i) |>.comp (measurable_pi_apply (k i))
```

**Location:** `ViaKoopman.lean:2259, 2353`

---

### 5.2 Custom MeasurableSpace Instances

**Three custom σ-algebras defined:**

1. **tailSigma** (`InvariantSigma.lean:86`)
   - Tail σ-algebra for martingale approach

2. **shiftInvariantSigma** (`InvariantSigma.lean:106`)
   - Shift-invariant σ-algebra
   - Structure: `measurableSet_empty`, `measurableSet_compl`, `measurableSet_iUnion`

3. **shiftInvariantSigmaℤ** (`ViaKoopman.lean:215`)
   - ℤ-indexed version for Koopman approach
   - Same structure as shiftInvariantSigma

**Pattern for all three:**
```lean
def customSigma : MeasurableSpace Ω where
  MeasurableSet' s := ∃ t : Set Ω, MeasurableSet t ∧ <invariance property>
  measurableSet_empty := ⟨MeasurableSet.empty, ...⟩
  measurableSet_compl := fun s ⟨t, ht, ...⟩ => ...
  measurableSet_iUnion := fun f hf => ⟨MeasurableSet.iUnion ..., ...⟩
```

---

## 6. PREIMAGE AND COMPOSITION PATTERNS

### 6.1 Set.preimage Usage

**Common patterns:**
```lean
-- Preimage composition
rw [← Set.preimage_comp, ← h_factor]

-- Preimage of complement
simp [Set.preimage_compl, hs_eq]

-- Preimage of union
simp only [Set.preimage_iUnion]

-- Preimage monotonicity
apply Set.preimage_mono
```

**Locations:**
- `InvariantSigma.lean:115, 119, 368, 381, 415, 427, 451`
- `ViaMartingale.lean:561, 1312`
- `ViaKoopman.lean:224, 228, 351, 1006`
- `ViaL2.lean:2924, 3026`

---

### 6.2 Indicator Composition with Preimage

**Lemma exists:** `indicator_comp_preimage` (in MartingaleHelpers and ViaMartingale)

```lean
lemma indicator_comp_preimage
  (f : Ω → α) (B : Set α) (c : ℝ) :
  (B.indicator (fun _ => c)) ∘ f = (f ⁻¹' B).indicator (fun _ => c)
```

**Usage:** Proves indicator commutes with composition

**Inline usage pattern:**
```lean
funext y
simp only [Set.indicator, Set.mem_preimage, Pi.one_apply]
by_cases h : y k ∈ s <;> simp [h]
```

**Location:** `ViaKoopman.lean:3322-3325`

---

## 7. SET MEMBERSHIP PATTERNS

### 7.1 Intersection Characterizations

**Pattern:** `Set.mem_inter_iff` in simp sets

**Occurrences:**
- `MartingaleHelpers.lean:336, 355, 459`
- `ViaMartingale.lean:643, 732, 1462, 1525, 2562`
- `ViaKoopman.lean:3416`

**Typical usage:**
```lean
simp [Set.indicator, hA, hB, Set.mem_inter_iff]
```

---

### 7.2 Universal Product Characterizations

**Pattern:** Membership in `Set.univ_pi`

```lean
simp only [Set.mem_univ_pi, Set.mem_inter_iff]
```

**Locations:** Throughout ViaMartingale.lean (10+ times)

---

## 8. PROPOSED REFACTORING STRUCTURE

### Option A: Extend MartingaleHelpers.lean

**Current sections:**
- `IndicatorAlgebra` (lines 345-393)
- `CylinderBridge` (lines 395-460)

**Add new sections:**
```lean
section ENNRealIndicators
  -- Move from CommonEnding.lean
  lemma indicator_mem_zero_one ...
  lemma indicator_le_one ...
end ENNRealIndicators

section IntegrationLemmas
  -- Move from ViaKoopman.lean
  @[simp] lemma integral_indicator_one ...
  lemma integral_indicator_const ...
end IntegrationLemmas

section RectangleLemmas
  -- Helper lemmas for Set.univ_pi patterns
  lemma rectangle_inter ...
  lemma rectangle_measurable ...
end RectangleLemmas
```

**Pros:**
- Single import for all indicator/set algebra helpers
- MartingaleHelpers already has indicator lemmas
- Natural organization

**Cons:**
- Makes MartingaleHelpers less specific to martingale proof
- Name becomes misleading

---

### Option B: Create New SetAlgebraHelpers.lean

**Structure:**
```lean
-- Exchangeability/DeFinetti/SetAlgebraHelpers.lean

section BasicIndicatorAlgebra
  lemma indicator_mul_indicator_eq_indicator_inter
  lemma indicator_comp_preimage
  lemma indicator_binary
  lemma indicator_le_const
  lemma indicator_nonneg
end BasicIndicatorAlgebra

section ENNRealIndicators
  lemma indicator_mem_zero_one
  lemma indicator_le_one
  lemma prod_eq_zero_iff
  lemma prod_eq_one_iff_of_zero_one
  lemma prod_le_one_of_le_one
  lemma measurable_prod_ennreal
  lemma measurable_indicator_comp
end ENNRealIndicators

section IntegrationLemmas
  @[simp] lemma integral_indicator_one
  lemma integral_indicator_const
end IntegrationLemmas

section CylinderSets
  -- Import from MartingaleHelpers
  lemma cylinder_inter
  lemma cylinder_univ
  lemma cylinder_measurable_set
  lemma tailCylinder_eq_preimage_cylinder
  lemma mem_cylinder_iff
end CylinderSets

section RectangleLemmas
  lemma rectangles_isPiSystem
  -- Add common univ_pi patterns
end RectangleLemmas
```

**Pros:**
- Clear purpose and scope
- Separates general set algebra from proof-specific helpers
- Easy to find and import

**Cons:**
- Need to move code from MartingaleHelpers
- One more file to maintain

---

### Option C: Keep Current Structure, Remove Duplicates Only

**Immediate actions:**
1. Remove duplicate indicator lemmas from `ViaMartingale.lean` (lines 636-679)
2. Import from `MartingaleHelpers.lean` instead
3. Leave ENNReal lemmas in `CommonEnding.lean`
4. Leave integration lemmas in `ViaKoopman.lean`

**Pros:**
- Minimal disruption
- Removes immediate duplication
- Each proof keeps its specialized helpers

**Cons:**
- Doesn't address all refactoring opportunities
- Integration lemmas could be useful elsewhere

---

## 9. SPECIFIC DUPLICATION TO REMOVE

### 9.1 Immediate Removals

**File:** `ViaMartingale.lean`
**Lines:** 636-679 (44 lines)
**Action:** Delete these lemmas:
- `indicator_mul_indicator_eq_indicator_inter`
- `indicator_comp_preimage`
- `indicator_binary`
- `indicator_le_const`
- `indicator_nonneg`

**Replacement:** Add to imports:
```lean
open MartingaleHelpers (indicator_mul_indicator_eq_indicator_inter
                        indicator_comp_preimage indicator_binary
                        indicator_le_const indicator_nonneg)
```

**Impact:** Eliminates 44 lines of duplicate code

---

### 9.2 Potential Removals (if creating SetAlgebraHelpers)

**From CommonEnding.lean** (move to new file):
- Lines 187-264 (ENNReal indicator section)

**From ViaKoopman.lean** (move to new file):
- Lines 2472-2488 (integration lemmas)

**From MartingaleHelpers.lean** (keep or move):
- Lines 347-392 (basic indicator algebra) - KEEP as canonical location
- Lines 395-460 (cylinder bridge) - Could move

---

## 10. ANTI-PATTERNS TO AVOID

### 10.1 Don't Extract These

**"by_cases → simp" pattern:**
```lean
by_cases h : ω ∈ s <;> simp [Set.indicator, h]
```
**Reason:** Standard Lean idiom, too simple to factor out, loses clarity

**MeasurableSet applications:**
```lean
apply MeasurableSet.inter
· ...
```
**Reason:** Part of Lean's measurability automation, should stay inline

**Membership simp lemmas:**
```lean
simp only [Set.mem_inter_iff, Set.mem_univ_pi]
```
**Reason:** Standard library simplifications, not worth factoring

---

### 10.2 Keep These Inline

**Product expansions:**
```lean
rw [Finset.sum_mul]
congr 1
ext i
rw [Finset.mul_sum]
```
**Reason:** Proof-specific algebra, not a reusable pattern

**Case analysis on indicators:**
```lean
by_cases hA : ω ∈ A <;> by_cases hB : ω ∈ B <;>
  simp [Set.indicator, hA, hB, Set.mem_inter_iff]
```
**Reason:** Clear in context, factoring would obscure logic

---

## 11. USAGE STATISTICS

### Indicator Lemmas Usage

**indicator_mul_indicator_eq_indicator_inter:**
- Defined: MartingaleHelpers.lean:348, ViaMartingale.lean:636
- Used inline: ViaKoopman.lean:3411-3416
- **Total occurrences:** 3 (2 definitions + 1 inline)

**indicator_binary:**
- Defined: MartingaleHelpers.lean:367, ViaMartingale.lean:655
- Used inline: ~8 times via `by_cases → simp` pattern
- **Total occurrences:** 10+

**indicator_comp_preimage:**
- Defined: MartingaleHelpers.lean:358, ViaMartingale.lean:646
- Used explicitly: 0 times (but pattern appears inline)
- **Total occurrences:** 2 definitions

**integral_indicator_one:**
- Defined: ViaKoopman.lean:2472
- Used: ViaKoopman.lean:2340, 2488, 3327
- **Total occurrences:** 4 (1 definition + 3 uses)

**integral_indicator_const:**
- Defined: ViaKoopman.lean:2479
- Used: ViaKoopman.lean:3441, other locations
- **Total occurrences:** 5+

---

### Set Operation Patterns

**Set.preimage:**
- Total occurrences: ~20 across all files
- Mostly in transformation proofs

**Set.mem_inter_iff:**
- Total occurrences: ~12 in simp calls
- Standard pattern, no refactoring needed

**MeasurableSet.univ_pi:**
- Total occurrences: ~15
- Concentrated in ViaMartingale.lean and CommonEnding.lean

---

## 12. RECOMMENDATIONS

### Tier 1: Do Immediately

1. **Remove duplicate indicator lemmas from ViaMartingale.lean**
   - Lines 636-679
   - Import from MartingaleHelpers instead
   - **Impact:** -44 lines, cleaner code

### Tier 2: Consider for Medium-Term

2. **Create SetAlgebraHelpers.lean** (Option B)
   - Move indicator lemmas from MartingaleHelpers
   - Move ENNReal lemmas from CommonEnding
   - Move integration lemmas from ViaKoopman
   - **Impact:** Better organization, single import for helpers

3. **Add rectangle helper lemmas**
   - Factor common `Set.univ_pi` patterns
   - **Impact:** Reduce repetition in ViaMartingale.lean

### Tier 3: Low Priority

4. **Document proof patterns**
   - Add comments explaining "by_cases → simp" idiom
   - Document when to use inline vs. lemma

5. **Consolidate cylinder set lemmas**
   - All in MartingaleHelpers.CylinderBridge
   - Ensure imported where needed

### Don't Do

- ❌ Factor out "by_cases → simp" pattern
- ❌ Create lemmas for simple MeasurableSet applications
- ❌ Factor product expansion algebra
- ❌ Create helpers for `Set.mem_inter_iff` simp patterns

---

## 13. MIGRATION PLAN (if pursuing Option B)

### Step 1: Create new file
```bash
touch Exchangeability/DeFinetti/SetAlgebraHelpers.lean
```

### Step 2: Move code in order
1. Basic indicator algebra (from MartingaleHelpers)
2. ENNReal indicators (from CommonEnding)
3. Integration lemmas (from ViaKoopman)
4. Cylinder sets (from MartingaleHelpers)
5. New rectangle lemmas

### Step 3: Update imports
- MartingaleHelpers.lean: import SetAlgebraHelpers
- ViaMartingale.lean: import SetAlgebraHelpers (remove local definitions)
- ViaKoopman.lean: import SetAlgebraHelpers
- CommonEnding.lean: import SetAlgebraHelpers (remove ENNReal section)

### Step 4: Update Exchangeability.lean
Add to main module:
```lean
import Exchangeability.DeFinetti.SetAlgebraHelpers
```

### Step 5: Test
```bash
lake build Exchangeability/DeFinetti/SetAlgebraHelpers
lake build Exchangeability/DeFinetti/ViaMartingale
lake build Exchangeability/DeFinetti/ViaKoopman
lake build
```

---

## 14. FILES ANALYZED

**Main proof files:**
- `ViaL2.lean` (4143 lines)
- `ViaKoopman.lean` (5046 lines)
- `ViaMartingale.lean` (2861 lines)

**Helper files:**
- `MartingaleHelpers.lean` (460 lines)
- `CommonEnding.lean` (903 lines)
- `L2Helpers.lean`
- `InvariantSigma.lean`

**Supporting files:**
- `ProjectionLemmas.lean`
- `L2Approach.lean`
- `CovarianceStructure.lean`
- `MathlibGaps.lean`

**Total analyzed:** 17 Lean files in DeFinetti directory

---

## 15. CONCLUSION

**Key Findings:**
1. **44 lines of exact duplication** in indicator algebra (ViaMartingale vs MartingaleHelpers)
2. **Well-organized ENNReal helpers** already exist in CommonEnding.lean
3. **Useful integration lemmas** in ViaKoopman.lean could be shared
4. **Many patterns are fine inline** (by_cases, MeasurableSet applications)

**Recommended Actions:**
- **Immediate:** Remove duplicates from ViaMartingale.lean
- **Optional:** Create SetAlgebraHelpers.lean for better organization
- **Don't:** Over-factor common Lean idioms

**Impact:**
- Immediate refactoring: -44 lines, cleaner imports
- Full refactoring: Better organization, single source of truth for set algebra
- Risk: Low (mostly moving proven code)
