# Understanding `fun_prop (disch := <tactic>)` in Lean 4

## What Does `disch` Mean?

**`disch`** is short for **"discharge"** - as in "discharge subgoals."

In proof theory, to "discharge" a goal means to **prove it and remove it from the goal stack**.

## The Full Syntax

```lean
fun_prop (disch := <tactic_name>)
```

**Translation:** "Prove this function property, and when you generate subgoals, use `<tactic_name>` to discharge (solve) them."

---

## How `fun_prop` Works (Under the Hood)

`fun_prop` is a **compositional tactic** for proving function properties. It:

1. **Decomposes** the function into simpler parts
2. **Generates subgoals** for proving properties of those parts
3. **Combines** the proven parts back into the whole

**The problem:** Step 2 generates subgoals that need to be solved.

**The solution:** `disch := <tactic>` tells `fun_prop` which tactic to use for step 2.

---

## Examples from the Exchangeability Codebase

All 8 instances in your codebase use `disch := measurability`. Let me show the pattern:

### Example 1: Simple Lambda with Function Application

**File:** `Exchangeability/DeFinetti/L2Helpers.lean:96`

```lean
have h_meas_k : Measurable fun ω => fun j : Fin 1 => X (k j) ω := by
  fun_prop (disch := measurability)
```

**What happens:**

1. **Goal:** `Measurable (fun ω => fun j : Fin 1 => X (k j) ω)`

2. **`fun_prop` decomposes:**
   ```
   Outer: fun ω => ...
   Inner: fun j => ...
   Body:  X (k j) ω
   ```

3. **Subgoals generated:**
   ```
   ⊢ Measurable (X (k j))  -- for each j : Fin 1
   ```

4. **`disch := measurability` solves:**
   - Calls `measurability` on subgoal
   - Uses context: `hX_meas : ∀ n, Measurable (X n)`
   - Proves `Measurable (X (k j))` using `hX_meas (k j)`

5. **Result:** Original goal discharged ✓

---

### Example 2: Indexed Function (More Complex)

**File:** `Exchangeability/DeFinetti/ViaMartingale.lean:1475`

```lean
have h_meas_idx : Measurable (fun ω (i : Fin (r + 1 + k)) => X (idx i) ω) := by
  fun_prop (disch := measurability)
```

**What happens:**

1. **Goal:** `Measurable (fun ω (i : Fin (r + 1 + k)) => X (idx i) ω)`

2. **`fun_prop` decomposes:**
   ```
   Lambda over ω: fun ω => ...
   Lambda over i: fun i => ...
   Application:   X (idx i) ω
   ```

3. **Subgoals generated:**
   ```
   ⊢ Measurable (X (idx i))  -- for each i
   ⊢ Measurable idx          -- the indexing function
   ```

4. **`disch := measurability` solves all subgoals:**
   - `Measurable (X (idx i))` via `hX : ∀ n, Measurable (X n)`
   - `Measurable idx` via Pi measurability rules

5. **Result:** Complex goal solved automatically ✓

---

### Example 3: Pattern Across All 8 Instances

Looking at all uses in your codebase:

```lean
-- Pattern 1: Reindexed sequence (4 instances)
Measurable fun ω => fun j : Fin n => X (k j) ω
Measurable fun ω => fun j : Fin n => X j.val ω

-- Pattern 2: Complex indexing (4 instances)
Measurable (fun ω (i : Fin (r + 1 + k)) => X (idx i) ω)
Measurable (fun ω (i : Fin (r + 1 + k)) => X (↑i) ω)
```

**Common theme:** Proving measurability of **compositional functions** where:
- You have a sequence `X : ℕ → Ω → α`
- You reindex it: `k j`, `j.val`, `idx i`, etc.
- You need to prove the reindexed version is measurable

**Without `disch := measurability`** you'd write ~6 lines of manual proof per instance.

**With `disch := measurability`** you write 1 line and let automation handle it.

---

## Other Possible `disch` Tactics (Not in Your Code)

While your codebase only uses `measurability`, here are other common `disch` tactics:

### 1. `disch := continuity`

For continuous functions:

```lean
example (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x => f x + g x) := by
  fun_prop (disch := continuity)
```

**Subgoals discharged:** `Continuous f`, `Continuous g` (via `continuity` tactic)

---

### 2. `disch := simp`

For algebraic properties:

```lean
example (f : ℝ → ℝ) :
    (fun x => f (x + 0)) = f := by
  funext x
  fun_prop (disch := simp)
```

**Subgoals discharged:** Arithmetic simplifications via `simp`

---

### 3. `disch := assumption`

When subgoals are in context:

```lean
example (f g : ℝ → ℝ) (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun x => (f x, g x)) := by
  fun_prop (disch := assumption)
```

**Subgoals discharged:** `Measurable f`, `Measurable g` directly from hypotheses

---

## When to Use `fun_prop (disch := ...)`

**Use it when:**

1. ✅ Proving a **function property** (Measurable, Continuous, Differentiable, etc.)
2. ✅ The function is **compositional** (built from simpler functions)
3. ✅ You know which tactic can solve the component proofs

**Don't use it when:**

1. ❌ The function is simple enough for direct tactics (`measurability`, `continuity` alone)
2. ❌ The property isn't about functions (use regular tactics)
3. ❌ You don't know what `disch` tactic to use (try without `disch` first to see subgoals)

---

## Comparison: With vs Without `disch`

### Without `disch` (Manual Subgoal Solving)

```lean
have h_meas : Measurable (fun ω => fun j : Fin 1 => X (k j) ω) := by
  fun_prop
  -- Now stuck with subgoal:
  -- ⊢ Measurable (X (k j))
  exact hX_meas (k j)  -- Solve manually
```

### With `disch := measurability` (Automatic)

```lean
have h_meas : Measurable (fun ω => fun j : Fin 1 => X (k j) ω) := by
  fun_prop (disch := measurability)
  -- Done! Subgoal automatically discharged
```

**Savings:** 2-3 lines per instance, no manual subgoal handling.

---

## How to Choose the Right `disch` Tactic

**Decision tree:**

```
What property are you proving?
├─ Measurable?
│  └─ Use: disch := measurability
├─ Continuous?
│  └─ Use: disch := continuity
├─ Differentiable?
│  └─ Use: disch := differentiability
├─ Linear?
│  └─ Use: disch := simp (or linear_combination)
└─ Not sure?
   └─ Try fun_prop alone, see what subgoals appear, then add disch
```

---

## Advanced: Multiple `disch` Options

You can also pass a **tactic sequence** to `disch`:

```lean
fun_prop (disch := (measurability <;> simp))
```

**Meaning:** "Try `measurability` on subgoals; if that doesn't fully solve them, follow up with `simp`."

**Example use case:**
- `fun_prop` generates `Measurable (f (x + 0))`
- `measurability` solves `Measurable f` part
- `simp` simplifies `x + 0` to `x`
- Combined: goal discharged

---

## Etymology and Terminology

**Discharge** in logic means:

> To remove a hypothesis or goal from consideration by proving it.

**Examples:**
- "Discharge the assumption that x > 0" = Prove x > 0 so we can stop assuming it
- "Discharge the subgoal ⊢ Measurable f" = Prove it so it's no longer blocking us

**In Lean tactics:**
- `disch` = the tactic that **discharges (proves and removes)** subgoals
- `fun_prop (disch := <tactic>)` = "use `<tactic>` to discharge any subgoals I generate"

---

## Summary

| Concept | Meaning |
|---------|---------|
| `fun_prop` | Tactic for proving function properties compositionally |
| `disch` | Short for "discharge" (prove and remove subgoals) |
| `fun_prop (disch := measurability)` | "Prove function property; use `measurability` to solve subgoals" |

**Your codebase pattern:**
- All 8 instances use `disch := measurability`
- All prove `Measurable` for compositional functions
- Pattern: `Measurable (fun ω => fun i => X (reindex i) ω)`
- Saves ~40 lines of manual subgoal handling

**Key insight:** `disch` turns `fun_prop` from a decomposition tool into a **full automation tool** by telling it how to solve the pieces it creates.

---

## Real-World Impact in Your Codebase

**Before Phase 1 refactoring:**
```lean
-- Manual proof (6 lines)
have h_meas_k : Measurable fun ω => fun j : Fin 1 => X (k j) ω := by
  refine measurable_pi_lambda _ (fun i => ?_)
  intro ω
  simp
  exact hX_meas (k i)
```

**After Phase 1 refactoring:**
```lean
-- Automated (1 line)
have h_meas_k : Measurable fun ω => fun j : Fin 1 => X (k j) ω := by
  fun_prop (disch := measurability)
```

**Result:** 8 instances × 5 lines saved = **40 lines eliminated** from your codebase, with clearer intent and no loss of correctness.
