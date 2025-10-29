# Mathlib Search Guide for Sorry #3

## Commands to Run

### 1. Search for comap measurability lemmas

```bash
# In the repository root:
grep -r "comap" .lake/packages/mathlib/Mathlib/MeasureTheory/MeasurableSpace/ | grep -i "measurable"
```

**What to look for:** Lemmas about measurability with respect to `MeasurableSpace.comap`

**Likely names:**
- `Measurable.of_comap`
- `measurable_comap`
- `MeasurableSpace.comap_measurable`

### 2. Search for iInf characterization

```bash
grep -r "iInf.*Measurable\|Measurable.*iInf" .lake/packages/mathlib/Mathlib/MeasureTheory/
```

**What to look for:** Lemmas relating `Measurable[⨅ i, m i]` to `∀ i, Measurable[m i]`

**Likely location:** `Mathlib.MeasureTheory.MeasurableSpace.Defs`

### 3. Search for closedness of conditional expectation

```bash
grep -r "condExpL2" .lake/packages/mathlib/Mathlib/MeasureTheory/Function/ConditionalExpectation/ | grep -i "closed\|range\|proj"
```

**What to look for:**
- Lemmas about range of `condExpL2` being closed
- `condExpL2` being a projection
- `LinearMap.range_eq_of_proj`

### 4. Search for L² convergence preserving measurability

```bash
grep -r "Lp.*lim\|limit.*Lp" .lake/packages/mathlib/Mathlib/MeasureTheory/Function/LpSpace/ | grep -i "measurable"
```

**Alternative search:**
```bash
grep -r "AEStronglyMeasurable.*lim" .lake/packages/mathlib/Mathlib/MeasureTheory/
```

**What to look for:** Lemmas about limits in Lp preserving (ae)strong measurability

---

## Using Lean Search Tools

### Within Lean file:

```lean
-- Add at top of file for interactive search:
#check MeasurableSpace.comap
#check MeasurableSpace.iInf
#check condExpL2
#check AEStronglyMeasurable

-- Search by type:
example : Measurable[MeasurableSpace.comap f m] g := by
  apply?  -- Will suggest applicable lemmas
```

### Using lean_local_search (MCP tool):

From Claude Code, you can run:
```lean
mcp__lean-lsp__lean_local_search("comap.*Measurable", limit=20)
mcp__lean-lsp__lean_local_search("iInf", limit=20)
mcp__lean-lsp__lean_local_search("condExpL2", limit=20)
```

### Using lean_loogle (online search):

```lean
mcp__lean-lsp__lean_loogle("_ → Measurable[MeasurableSpace.comap _ _] _")
mcp__lean-lsp__lean_loogle("Measurable[⨅ _, _] _")
```

---

## Specific Lemmas to Check

### From Mathlib.MeasureTheory.MeasurableSpace.Defs:

```lean
#check @Measurable.mono  -- Transfer measurability to smaller σ-algebra
#check MeasurableSpace.le_def
#check iInf_le
```

### From Mathlib.MeasureTheory.Function.StronglyMeasurable:

```lean
#check StronglyMeasurable.of_subsingleton_dom
#check AEStronglyMeasurable.measurable
#check StronglyMeasurable.measurable
```

### From Mathlib.Analysis.NormedSpace.Banach:

```lean
#check LinearMap.isClosed_range_of_proj  -- For closedness argument
#check IsClosed.mem_of_tendsto  -- Limit of closed set members
```

### From Mathlib.MeasureTheory.Function.ConditionalExpectation.CondexpL2:

```lean
#check condExpL2
#check condExpL2_congr_ae
#check Lp.induction  -- Might help with limit arguments
```

---

## Alternative Approaches to Explore

### Approach 1: Use AEStronglyMeasurable' instead

The documentation mentions the goal might actually be `AEStronglyMeasurable'` not `Measurable`.

```lean
#check @AEStronglyMeasurable'
-- Signature: AEStronglyMeasurable' {m : MeasurableSpace α} (f : α → β) (μ : Measure α)
```

This might have more lemmas available for limits.

### Approach 2: Work in Lp space throughout

Instead of extracting `α_f : Ω → ℝ`, keep working with `α_L2 : Lp ℝ 2 μ`:

```lean
-- Check if Lp has sub-σ-algebra structure
#check @Lp.stronglyMeasurable'  -- Does this exist?
```

### Approach 3: Use product σ-algebra structure

`tailFamily X m` is defined as comap from product space `ℕ → ℝ`.

```lean
#check MeasurableSpace.pi  -- Product σ-algebra
#check measurable_pi_iff  -- Characterization
```

---

## Example: How to Use These Searches

### Step-by-step process:

1. **Start with local search:**
   ```lean
   mcp__lean-lsp__lean_local_search("comap", limit=50)
   ```

2. **Filter results for relevant files:**
   Look for results in:
   - `Mathlib.MeasureTheory.MeasurableSpace.*`
   - `Mathlib.MeasureTheory.Constructions.Pi`
   - `Mathlib.MeasureTheory.Function.StronglyMeasurable.*`

3. **Read the file containing promising lemmas:**
   ```lean
   Read("/path/to/.lake/packages/mathlib/Mathlib/MeasureTheory/MeasurableSpace/Defs.lean")
   ```

4. **Try applying in your proof:**
   ```lean
   apply Measurable.of_comap  -- or whatever you found
   ```

5. **If it doesn't work directly, check the exact type:**
   ```lean
   #check @Measurable.of_comap
   -- Compare types carefully
   ```

---

## What Each Missing Lemma Does

### LEMMA 1: measurable_of_comap_shift

**Purpose:** Show that `X (m+k)` is measurable w.r.t. `tailFamily X m`

**Why it should exist:** `tailFamily X m` is literally defined as the comap through the function that produces `X (m+·)`, so `X (m+k)` should be measurable by definition.

**Fallback:** If not found, prove it directly using:
```lean
show Measurable[MeasurableSpace.comap shift inferInstance] (fun ω => X (m+k) ω)
-- where shift ω = fun j => X (m+j) ω
-- This is (coord k) ∘ shift, where coord k : (ℕ → ℝ) → ℝ is the k-th projection
apply Measurable.comp
· exact measurable_pi_apply k  -- coord k is measurable
· exact measurable_id  -- shift is measurable by construction of comap
```

### LEMMA 2: L2_limit_preserves_measurability

**Purpose:** If `f_n` are measurable w.r.t. sub-σ-algebra `m` and converge in L² to `f`, then `f` is also measurable w.r.t. `m`.

**Why it's hard:** This requires showing the set `{f ∈ L² | Measurable[m] f}` is closed. This is equivalent to showing the range of `condExpL2` is closed.

**Where to look:**
- Properties of `condExpL2` as a projection
- Hilbert space projection theorems
- `LinearMap.isClosed_range_of_proj`

**Fallback:** Temporarily use axiom and file an issue/PR to mathlib if this lemma doesn't exist.

### LEMMA 3: measurable_iInf_iff

**Purpose:** Measurability w.r.t. `⨅ i, m i` iff measurability w.r.t. each `m i`.

**Why it should exist:** This is a basic property of infimum of σ-algebras.

**Where to look:** `Mathlib.MeasureTheory.MeasurableSpace.Defs` or `Basic.lean`

**Fallback:** Prove directly:
```lean
constructor
· intro h i
  exact Measurable.mono h (iInf_le _ i)
· intro h
  apply measurable_of_le_comap
  -- Need to show: ∀ s measurable in target, preimage is in ⨅ i, m i
  -- Which means: preimage is in each m i
  -- Which follows from h i
  sorry
```

### LEMMA 4: contract_implies_same_limit

**Purpose:** If block averages starting at 0 converge, then by contractability, block averages starting at any index also converge to the same limit.

**Why it's needed:** To construct the diagonal sequence.

**Where it might exist:** Might already be proven in `ViaL2.lean` or `L2Helpers.lean` as part of the contraction bound machinery.

**Fallback:** Prove using the L² contraction bound:
```lean
-- ‖blockAvg f X m n - blockAvg f X 0 n‖₂ ≤ C/√n → 0
-- Combined with ‖blockAvg f X 0 n - α_f‖₂ → 0
-- Gives ‖blockAvg f X m n - α_f‖₂ → 0 by triangle inequality
```

---

## Priority Order for Implementation

1. **EASIEST:** LEMMA 1 (comap measurability) - should exist or be trivial
2. **MEDIUM:** LEMMA 3 (iInf characterization) - should exist
3. **MEDIUM:** LEMMA 4 (contractability) - can prove from existing bounds
4. **HARDEST:** LEMMA 2 (closedness) - may need to add to mathlib

**Recommendation:** Start with 1, 3, 4. If you get stuck on 2, use axiom temporarily.

