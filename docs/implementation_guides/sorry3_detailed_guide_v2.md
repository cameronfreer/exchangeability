# Sorry #3 Implementation Guide - DETAILED (v2 - Projection Approach)

**File:** `Exchangeability/DeFinetti/ViaL2.lean`
**Line:** 3590
**Current Goal:** `⊢ Measurable[TailSigma.tailSigma X] α_f`
**REVISED Target:** `AEStronglyMeasurable'[TailSigma.tailSigma X] α_L2 μ`

---

## Context Available in Scope

```lean
Ω : Type u_1
inst✝¹ : MeasurableSpace Ω
μ : Measure Ω
inst✝ : IsProbabilityMeasure μ
X : ℕ → Ω → ℝ                    -- The exchangeable sequence
hX_contract : Contractable μ X
hX_meas : ∀ (i : ℕ), Measurable (X i)
f : ℝ → ℝ                         -- Bounded measurable function
hf_meas : Measurable f
hf_bdd : ∀ (x : ℝ), |f x| ≤ 1

-- From Sorry #2 (L² completeness):
α_L2 : Lp ℝ 2 μ                   -- L² limit of block averages
α_f : Ω → ℝ := α_L2               -- Representative (coercion)
hα_memLp : MemLp α_f 2 μ
hα_limit : Tendsto (fun n => eLpNorm (blockAvg f X 0 n - α_f) 2 μ) atTop (𝓝 0)
```

---

## The Problem

**What we have:** `StronglyMeasurable α_f` (w.r.t. ambient σ-algebra)
**What we need:** `AEStronglyMeasurable'[TailSigma.tailSigma X] α_L2 μ`

**Key insight:** Work with `α_L2 : Lp ℝ 2 μ` directly rather than the representative `α_f`. The conditional expectation API in mathlib is designed to work with `AEStronglyMeasurable'`, which is the natural notion for sub-σ-algebras in L² theory.

**Why `AEStronglyMeasurable'` not `Measurable`:**
- The uniqueness lemmas in Sorry #4 require `AEStronglyMeasurable'`
- It's strictly easier to work with in L² contexts
- Represents "measurable up to null sets" which is the right notion for integration

---

## Why This Is (Now) Tractable

**OLD APPROACH (HARD):** Prove closedness of `{f ∈ L² | Measurable[m] f}` as a subspace.

**NEW APPROACH (EASY):** Use the continuous projection property of `condExpL2`.

**Key fact:** For any sub-σ-algebra `m ≤ m₀`, the conditional expectation
```lean
P_m := condExpL2 m : L² → L²
```
is a **continuous idempotent linear map** (projection) that:
1. Fixes every `m`-measurable L² function: `P_m f = f` iff `f` is `m`-measurable
2. Is continuous in L² topology

**Therefore:** If `g_k` are eventually `m`-measurable and `g_k → α` in L², then:
- Eventually `P_m g_k = g_k`
- By continuity: `P_m α = lim P_m g_k = lim g_k = α`
- So `α` is a fixed point of `P_m`, hence `m`-measurable

**No closedness lemma needed!**

---

## Relevant Definitions

### TailSigma.tailSigma (from `Exchangeability/Tail/TailSigma.lean`)

```lean
-- Future σ-algebra from index n onward
def tailFamily (X : ℕ → Ω → α) (n : ℕ) : MeasurableSpace Ω :=
  MeasurableSpace.comap (fun ω => fun k => X (n + k) ω) inferInstance

-- Tail σ-algebra = intersection of all future σ-algebras
def tailProcess (X : ℕ → Ω → α) : MeasurableSpace Ω :=
  ⨅ n, tailFamily X n
```

### blockAvg (from line 1640)

```lean
def blockAvg (f : α → ℝ) (X : ℕ → Ω → α) (m n : ℕ) (ω : Ω) : ℝ :=
  (n : ℝ)⁻¹ * (Finset.range n).sum (fun k => f (X (m + k) ω))
```

**Key property:** `blockAvg f X m n` only depends on `X m, X (m+1), ..., X (m+n-1)`

---

## Step-by-Step Implementation Plan (REVISED)

### STEP 1: Prove blockAvg measurability w.r.t. tailFamily

**Location:** Add as helper lemma before `cesaro_to_condexp_L2`

```lean
/-- Each shifted coordinate is measurable for the tail family. -/
lemma measurable_X_shift
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i))
    (m k : ℕ) :
    Measurable[TailSigma.tailFamily X m] (fun ω => X (m + k) ω) := by
  -- tailFamily X m := comap (ω ↦ (j ↦ X (m+j) ω))
  -- X (m+k) = (coord k) ∘ shift
  -- where shift ω = (j ↦ X (m+j) ω) and coord k is k-th projection
  -- coord k is measurable on product σ-algebra by measurable_pi_apply
  -- compose with shift (measurable by comap definition)
  sorry

/-- Block averages are measurable w.r.t. the m-tail family. -/
lemma blockAvg_measurable_tailFamily
    {Ω : Type*} [MeasurableSpace Ω]
    {f : ℝ → ℝ} (hf : Measurable f)
    {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i))
    (m n : ℕ) :
    Measurable[TailSigma.tailFamily X m] (blockAvg f X m n) := by
  unfold blockAvg
  -- (n⁻¹) * ∑_{k<n} f(X_{m+k})
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro k _
  -- Each term: f ∘ X_{m+k}
  have hXmk : Measurable[TailSigma.tailFamily X m] (fun ω => X (m+k) ω) :=
    measurable_X_shift hX m k
  exact hf.comp hXmk
```

**Mathlib hooks:**
- `Finset.measurable_sum` - measurability of finite sums
- `Measurable.const_mul` - scalar multiplication
- `Measurable.comp` - composition
- `measurable_pi_apply` - coordinate projections on product space

---

### STEP 2: Construct approximating sequence (OPTIONAL BUT CLEAN)

**Note:** This step is optional - any sequence with `g_k → α_L2` in L² and `g_k` eventually `σ(X_{≥N})`-measurable works. The diagonal construction gives clean "eventually k ≥ N" properties.

```lean
-- For each k, find n_k with ‖blockAvg f X k n_k - α_f‖₂ ≤ 2^{-k}
-- (This uses contractability to ensure all starting points converge to same limit)

have h_exists_nk : ∀ k : ℕ, ∃ n_k : ℕ, n_k > 0 ∧
    eLpNorm (blockAvg f X k n_k - α_f) 2 μ < ENNReal.ofReal (2^(-(k:ℤ) : ℝ)) := by
  intro k
  -- Use contractability: blockAvg f X k n has same limit as blockAvg f X 0 n
  -- Apply hα_limit with ε = 2^{-k}
  sorry

choose n_k hn_k_pos hn_k_bound using h_exists_nk

let g := fun k => blockAvg f X k (n_k k)
```

---

### STEP 3: Projection/Fixed-Point Argument (REPLACES OLD STEP 3)

**Key lemma to add:**

```lean
/-- If a sequence is eventually `m`-measurable in L² and converges to `α`, 
    then `α` is also `m`-measurable, by the projection fixed-point property. -/
lemma aeStronglyMeasurable_of_projection_fixed
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (m : MeasurableSpace Ω) (hm : m ≤ inferInstance)
    {g : ℕ → Ω → ℝ} {α : Lp ℝ 2 μ}
    (hconv : Tendsto (fun k => (g k : Lp ℝ 2 μ)) atTop (𝓝 α))
    (hg_meas : ∀ᶠ k in atTop, AEStronglyMeasurable'[m] (g k) μ) :
    AEStronglyMeasurable'[m] α μ := by
  -- Let P := condExpL2 m
  -- P is continuous linear: ‖P f - P f'‖₂ ≤ ‖f - f'‖₂
  -- From hg_meas: eventually P (g k) = g k (fixed points)
  -- Map limit through P: P α = P (lim g k) = lim P (g k) = lim g k = α
  -- So α is a fixed point of P, hence m-measurable
  sorry
```

**Why this works:**
- `P := condExpL2 m` is a continuous projection onto the `m`-measurable subspace
- Continuous maps preserve limits: `P (lim g_k) = lim P g_k`
- Eventually `P g_k = g_k` (since `g_k` is `m`-measurable)
- Therefore `P α = α`, so `α` is `m`-measurable

**Mathlib hooks to search for:**
- `condExpL2` or `condExpL2_CLM` - the continuous linear map version
- Lemmas about `condExpL2` being idempotent
- `ContinuousLinearMap.map_tendsto` or similar for continuity

---

### STEP 4: Apply to each tailFamily X N

```lean
have hg_meas_k : ∀ k, AEStronglyMeasurable'[TailSigma.tailFamily X k] (g k) μ := by
  intro k
  exact (blockAvg_measurable_tailFamily hf_meas hX_meas k (n_k k)).aestronglyMeasurable'

-- For each N, eventually k ≥ N, hence by antitonicity:
-- tailFamily X k ≤ tailFamily X N, so g k is also tailFamily X N-measurable

have hg_meas_N : ∀ N, ∀ᶠ k in atTop,
    AEStronglyMeasurable'[TailSigma.tailFamily X N] (g k) μ := by
  intro N
  refine (eventually_ge_atTop N).mono (fun k hk => ?_)
  have h_mono : TailSigma.tailFamily X k ≤ TailSigma.tailFamily X N :=
    TailSigma.tailFamily_antitone X hk
  exact (hg_meas_k k).mono h_mono

-- Now apply projection fixed-point lemma for each N:
have h_tail_N : ∀ N, AEStronglyMeasurable'[TailSigma.tailFamily X N] α_L2 μ := by
  intro N
  exact aeStronglyMeasurable_of_projection_fixed _ _ h_tendsto (hg_meas_N N)
```

**Mathlib hook:**
- `TailSigma.tailFamily_antitone` - already exists in `Exchangeability/Tail/TailSigma.lean:69`

---

### STEP 5: Intersection property (iInf characterization)

```lean
-- tailSigma X = ⨅ N, tailFamily X N (by definition)
-- So AEStronglyMeasurable'[tailSigma X] ↔ AEStronglyMeasurable'[tailFamily X N] for all N

have : TailSigma.tailSigma X = ⨅ N, TailSigma.tailFamily X N := rfl

-- Use iInf characterization:
-- For each N, have AEStronglyMeasurable'[tailFamily X N] α_L2
-- Since tailSigma X ≤ tailFamily X N for all N (by iInf_le)
-- Get AEStronglyMeasurable'[tailSigma X] α_L2 by monotonicity

refine AEStronglyMeasurable'.mono ?_ (fun N => iInf_le _ N)
intro N
exact h_tail_N N
```

**Mathlib hooks:**
- `iInf_le` - infimum is ≤ each element
- `AEStronglyMeasurable'.mono` - transfer to larger σ-algebra

**Pattern:**
```lean
-- If f is Measurable[m_i] for all i, and ⨅ i, m_i ≤ each m_i,
-- then f is Measurable[⨅ i, m_i]
```

---

## Complete Proof Sketch

```lean
-- Step 1: Basic measurability
have hg_meas_k : ∀ k, AEStronglyMeasurable'[TailSigma.tailFamily X k] (g k) μ :=
  fun k => (blockAvg_measurable_tailFamily hf_meas hX_meas k (n_k k)).aestronglyMeasurable'

-- Step 2: Monotonicity for each N
have hg_meas_N : ∀ N, ∀ᶠ k in atTop, AEStronglyMeasurable'[TailSigma.tailFamily X N] (g k) μ :=
  fun N => (eventually_ge_atTop N).mono (fun k hk =>
    (hg_meas_k k).mono (TailSigma.tailFamily_antitone X hk))

-- Step 3: Fixed-point argument for each N
have h_tail_N : ∀ N, AEStronglyMeasurable'[TailSigma.tailFamily X N] α_L2 μ :=
  fun N => aeStronglyMeasurable_of_projection_fixed _ _ h_tendsto (hg_meas_N N)

-- Step 4: Descend to infimum
exact AEStronglyMeasurable'.mono (fun N => h_tail_N N) (fun N => iInf_le _ N)
```

**Total: ~10 lines of actual proof, 4 helper lemmas**

---

## Key Mathlib Searches

### 1. Continuous linear map for conditional expectation

```bash
grep -r "condExpL2.*CLM\|CLM.*condExpL2" \
  .lake/packages/mathlib/Mathlib/MeasureTheory/Function/ConditionalExpectation/
```

**Look for:**
- `condExpL2_CLM` or similar - the continuous linear map version
- Lemmas about continuity: `‖condExpL2 m f‖ ≤ ‖f‖`

### 2. Fixed-point/idempotent property

```bash
grep -r "condExpL2.*aeStronglyMeasurable\|condExpL2.*fixed\|idempotent" \
  .lake/packages/mathlib/Mathlib/MeasureTheory/Function/ConditionalExpectation/
```

**Look for:**
- `condExpL2_of_aestronglyMeasurable'` - if `f` is `m`-measurable, then `condExpL2 m f = f`
- Projection properties

### 3. Lean checks to run

```lean
#check condExpL2          -- L²-valued conditional expectation
#check condExpL2_CLM      -- continuous linear map version (name may vary)
#check AEStronglyMeasurable'.mono
#check iInf_le
#check TailSigma.tailFamily_antitone  -- should exist in your codebase
```

---

## What Changed from v1

### OLD (v1): Closedness argument
- **Step 3:** Prove `{f ∈ L² | Measurable[m] f}` is closed
- **Requires:** Deep Hilbert space theory or finding the right mathlib lemma
- **Blocker:** Lemma may not exist in current mathlib

### NEW (v2): Projection/fixed-point
- **Step 3:** Use `P_m g_k = g_k` eventually + continuity ⇒ `P_m α = α`
- **Requires:** Basic properties of `condExpL2` (should exist)
- **Benefits:** 
  - No custom closedness lemma needed
  - Matches mathlib's design philosophy
  - Cleaner conceptually

---

## Potential Shortcuts

### If condExpL2 API is incomplete:

Temporarily use:
```lean
axiom aeStronglyMeasurable_of_projection_fixed : ...
```

Then file an issue/PR to mathlib noting this is a basic property of conditional expectation.

### If you want to avoid the diagonal construction:

You can use ANY sequence `g_k → α_L2` with `g_k` eventually `σ(X_{≥N})`-measurable.
Even just `g_k := blockAvg f X N (k+1)` for each fixed `N` works - you'd just need to handle multiple sequences (one per `N`) instead of one diagonal sequence.

---

## Recommended Next Steps

1. **Add the 3 helper lemmas** (measurable_X_shift, blockAvg_measurable_tailFamily, aeStronglyMeasurable_of_projection_fixed)

2. **Search for condExpL2 API:**
   ```lean
   #check condExpL2
   #check @AEStronglyMeasurable'
   ```

3. **Try the proof sketch** - should be ~10 lines once helpers are in place

4. **If stuck on Step 3:** Use axiom temporarily and move to Sorry #4

---

## Files to Reference

- `Exchangeability/Tail/TailSigma.lean` - Definitions and `tailFamily_antitone`
- `.lake/packages/mathlib/Mathlib/MeasureTheory/Function/ConditionalExpectation/CondexpL2.lean`
- `.lake/packages/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/Basic.lean`
- `.lake/packages/mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean` - For `measurable_pi_apply`

