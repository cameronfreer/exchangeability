# LSP MCP Tool Examples - Practical Demonstrations

This file shows real examples of using the Lean LSP MCP tools from the exchangeability codebase.

## Example 1: Checking Goal State

**File:** `Exchangeability/Util/StrictMono.lean:81`

**Command:**
```python
lean_goal(file_path, line=81)
```

**Result:**
```
Before:
⊢ j < j_succ

After (after `simp only [Fin.lt_iff_val_lt_val, j, j_succ]`):
⊢ n < n.succ
```

**Key insight:** You can see BOTH the goal before and after the tactic at that line, showing exactly what the tactic accomplishes.

---

## Example 2: Testing Multiple Tactics with lean_multi_attempt

**File:** `Exchangeability/Util/StrictMono.lean:98`

**Context:** Proving `fin_val_strictMono : StrictMono (fun i : Fin n => i.val)`

**Command:**
```python
lean_multi_attempt(
  file_path,
  line=98,
  snippets=[
    "  exact hij",
    "  assumption",
    "  apply hij"
  ]
)
```

**Result:**
```json
[
  "  exact hij\n:\n no goals\n\n",
  "  assumption:\n no goals\n\n",
  "  apply hij:\n no goals\n\n"
]
```

**Key insight:** All three tactics work! You can A/B test different approaches instantly without editing the file.

---

## Example 3: When lean_multi_attempt Reveals Errors

**File:** `Exchangeability/Util/StrictMono.lean:82`

**Goal:** Prove `n < n.succ` after simplification

**Command:**
```python
lean_multi_attempt(
  file_path,
  line=82,
  snippets=[
    "  exact Nat.lt_succ_self n",
    "  apply Nat.lt_succ_self",
    "  simp"
  ]
)
```

**Result:**
```
Snippet 1: "exact Nat.lt_succ_self n"
  ERROR: Unknown identifier `n`
  (Context lost - n was in nested proof scope)

Snippet 2: "apply Nat.lt_succ_self"
  ERROR: Could not unify conclusion
  (Wrong tactic for this context)

Snippet 3: "simp"
  SUCCESS: no goals
  (Simplification works!)
```

**Key insight:** `lean_multi_attempt` shows you EXACTLY why each approach fails, helping you understand the proof state.

---

## Example 4: Complete Workflow - Checking Then Testing

**Scenario:** You're at a `sorry` and want to find the right tactic.

**Step 1: Check what you need to prove**
```python
lean_goal("StrictMono.lean", line=97)
```
```
⊢ StrictMono (fun i : Fin n => i.val)
```

**Step 2: Expand the definition**
```python
lean_hover_info("StrictMono.lean", line=96, column=12)
```
```
StrictMono f means: ∀ a b, a < b → f a < f b
```

**Step 3: Test different proof strategies**
```python
lean_multi_attempt(
  "StrictMono.lean",
  line=97,
  snippets=[
    "  intro i j hij; exact hij",  # Direct proof
    "  intro i j; exact id",        # Using identity
    "  unfold StrictMono; simp"     # Unfolding definition
  ]
)
```

**Step 4: Choose the clearest approach**
```
Result: First two work, third doesn't.
Choose: "intro i j hij; exact hij" (most explicit)
```

---

## Example 5: Diagnostic Messages - Instant Error Feedback

**File:** Any file after editing

**Command:**
```python
lean_diagnostic_messages(file_path)
```

**Example output (when there's an error):**
```
l82c26-l82c27, severity: 1
Unknown identifier `n`
```

**Example output (when successful):**
```
(empty list)
```

**Key insight:** Instant feedback without waiting for `lake build`. Check this after EVERY edit.

---

## Example 6: Search Tools Comparison

**Goal:** Find lemmas about strict monotonicity and addition

**Tool 1: lean_local_search (FAST, unlimited)**
```python
lean_local_search("StrictMono", limit=5)
```
```
Returns: Local declarations matching "StrictMono"
- strictMono_add_left
- strictMono_add_right
- strictMono_Fin_ge_id
- etc.
```

**Tool 2: lean_loogle (Type-based, rate-limited)**
```python
lean_loogle("StrictMono ?f → StrictMono (fun i => ?f i + ?c)")
```
```
Returns: Mathlib lemmas matching the type pattern
```

**Tool 3: lean_leansearch (Natural language, rate-limited)**
```python
lean_leansearch("strict monotone preserved by addition", num_results=5)
```
```
Returns: Semantically related theorems
```

**Best practice:** Always use `lean_local_search` FIRST (it's unlimited and fast!), then move to the rate-limited tools if needed.

---

## Common Patterns

### Pattern 1: The "Check-Test-Apply" Loop

```python
# 1. Check goal
goal = lean_goal(file, line)

# 2. Test approaches
results = lean_multi_attempt(file, line, [
  "  tactic1",
  "  tactic2",
  "  tactic3"
])

# 3. Choose winner and edit file
# (Edit file with winning tactic)

# 4. Verify
diagnostics = lean_diagnostic_messages(file)
# Should be empty!
```

### Pattern 2: The "Search-Hover-Apply" Loop

```python
# 1. Search for lemma
results = lean_local_search("keyword")

# 2. Check signature
info = lean_hover_info(file, line, column)

# 3. Apply
# (Edit file)

# 4. Verify
lean_diagnostic_messages(file)
```

### Pattern 3: The "Goal-Driven Development"

```python
# Start with goal
goal = lean_goal(file, line)

# Apply tactic
# (Edit: add tactic)

# Check new goal
new_goal = lean_goal(file, line+1)

# Repeat until "no goals"
```

---

## Why This Matters: Before vs After

### Without LSP Tools (Blind Coding)
```
1. Edit file with guess
2. Run `lake build` (wait 30s)
3. See error
4. Try different guess
5. Run `lake build` (wait 30s)
6. Repeat...
```

### With LSP Tools (Goal-Driven)
```
1. Check goal (instant)
2. Test 3 tactics (instant)
3. Choose winner
4. Check diagnostics (instant)
5. Done! ✓
```

**Time saved:** Minutes → seconds per proof step.

---

## Key Takeaways

1. **`lean_goal`** is your InfoView - use it constantly
2. **`lean_multi_attempt`** lets you A/B test tactics without editing
3. **`lean_diagnostic_messages`** gives instant error feedback
4. **`lean_local_search`** is unlimited - always try it first
5. **Check-Test-Verify** replaces slow build cycles

These tools transform Lean development from a guess-and-check process into an interactive, goal-driven workflow.
