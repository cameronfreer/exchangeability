# Battle-Tested LSP-Driven Lean 4 Proof Workflow for Coding Agents

## Core Principle
**Always check goal state before making changes.** The LSP tools are your InfoView - use them like a human would use the interactive editor.

## The Workflow Pattern

### Step 1: Check Goal State FIRST
```
Before touching any proof, check what you need to prove:
→ mcp__lean-lsp__lean_goal(file_path, line, column)
```

**Example:**
```lean
lemma foo : a + b = b + a := by
  sorry  -- <- Check goal at line before sorry
```

**Action:** `lean_goal(file, line=2)`
**See:** `⊢ a + b = b + a`

### Step 2: Check Diagnostics BEFORE Building
```
After ANY edit, check errors immediately:
→ mcp__lean-lsp__lean_diagnostic_messages(file_path)
```

**Advantage over building:** Instant feedback, no waiting for full project build.

### Step 3: Iterate with Goal Tracking
```
After each tactic, check remaining goals:
→ lean_goal(file, line=N)  -- after each line
```

**Example workflow:**
```lean
lemma foo : a + b = b + a := by
  ring  -- Line 2
```

- Check `lean_goal(file, 2)` → See "no goals" or next subgoal
- If subgoals remain, check what's left
- If error, check `lean_diagnostic_messages(file)`

### Step 4: Search for Lemmas DURING Proof
```
When stuck on a goal, search immediately:
→ lean_leansearch(query, num_results=5)  # Natural language
→ lean_loogle(query, num_results=8)      # Type pattern
→ lean_local_search(query)               # FAST - use this FIRST!
```

**Example:**
```
Goal: ⊢ StrictMono (fun i => k i + c)

Search: lean_local_search("StrictMono")  # Check what exists locally
Then:   lean_leansearch("strict monotone addition preserves")
Or:     lean_loogle("StrictMono _ → StrictMono _")
```

**Priority order:**
1. `lean_local_search` - instant, checks workspace declarations
2. `lean_loogle` - fast, type-based pattern matching
3. `lean_leansearch` - slower, natural language

### Step 5: Hover for Documentation
```
Don't guess syntax - check it:
→ lean_hover_info(file, line, column)
```

**Use when:**
- Unsure about function signature
- Need to see implicit arguments
- Want to check available tactics

---

## Complete Example Workflow

**Task:** Fill in a sorry in StrictMono.lean

```lean
lemma strictMono_add_right (k : Fin m → ℕ) (hk : StrictMono k) (c : ℕ) :
    StrictMono (fun i => k i + c) := by
  sorry
```

**Agent workflow:**

1. **Check goal:**
   ```
   lean_goal(StrictMono.lean, line=3)
   → ⊢ StrictMono (fun i => k i + c)
   ```

2. **Search for relevant lemma:**
   ```
   lean_local_search("add_lt_add")
   → Found: Nat.add_lt_add_right

   lean_hover_info(StrictMono.lean, line=2, column=40)
   → See StrictMono definition: StrictMono f means ∀ a b, a < b → f a < f b
   ```

3. **Apply the proof pattern:**
   ```lean
   lemma strictMono_add_right ... := by
     fun ⦃_ _⦄ hab ↦ Nat.add_lt_add_right (hk hab) c
   ```

4. **Check result immediately:**
   ```
   lean_diagnostic_messages(StrictMono.lean)
   → (empty = success!)

   lean_goal(StrictMono.lean, line=2)
   → "no goals" (proof complete!)
   ```

---

## Key LSP Tools Reference

| Tool | When to Use | Rate Limit | Output |
|------|-------------|-----------|--------|
| `lean_goal` | After every tactic | None | Remaining subgoals |
| `lean_diagnostic_messages` | After every edit | None | Errors/warnings |
| `lean_hover_info` | When unsure about syntax | None | Documentation |
| `lean_local_search` | **Use FIRST!** Find declarations | None | Fast, structured |
| `lean_term_goal` | In term mode | None | Expected type |
| `lean_loogle` | Type-based search | 3 req/30s | Pattern matching |
| `lean_leansearch` | Natural language search | 3 req/30s | Mathlib theorems |
| `lean_state_search` | Goal-based search | 3 req/30s | Premise search |

**Note on rate limits:** lean_loogle, lean_leansearch, and lean_state_search are rate-limited. Always use `lean_local_search` first - it's unlimited and often finds what you need.

---

## Critical Rules

1. **NEVER edit without checking goal state first**
2. **ALWAYS check diagnostics after edits** (don't wait for build)
3. **Search before guessing** - use `lean_local_search` FIRST (fast & unlimited!)
4. **Check goals between tactics** - see intermediate progress
5. **Use hover for syntax** - don't guess function signatures
6. **Respect rate limits** - `lean_local_search` is unlimited, others are 3 req/30s

---

## Advanced: Multi-Attempt Testing

When you have multiple candidate tactics, test them efficiently:

```
lean_multi_attempt(file, line, snippets=[
  "  ring",
  "  omega",
  "  simp [add_comm]"
])
→ Returns goal state and diagnostics for EACH snippet
```

**Use when:**
- Exploring different approaches
- Comparing tactic effectiveness
- A/B testing proof strategies

**Note:** Only for single-line, fully-indented snippets. For real proofs, edit the file.

---

## Common Mistakes to Avoid

❌ **DON'T:**
- Edit proof → build → see error (too slow!)
- Guess lemma names without searching
- Apply tactics blind without checking goal
- Build entire project to check one proof
- Use rate-limited search when `lean_local_search` would work
- Skip intermediate goal checks in multi-step proofs

✅ **DO:**
- Check goal → search (local first!) → apply → check diagnostics
- Use LSP for instant feedback loop
- Verify lemma exists with `lean_local_search` first
- Check intermediate goals after each tactic
- Respect rate limits - use unlimited tools when possible

---

## Comparison: Build-Only vs LSP-Driven

| Build-Only Workflow | LSP-Driven Workflow |
|---------------------|---------------------|
| Edit → wait 30s → see error | Edit → instant diagnostic |
| Guess remaining goals | See exact goal state |
| Search externally | Integrated search |
| No intermediate feedback | Step-by-step verification |
| Full project build required | File-level instant feedback |
| Blind tactic application | Goal-aware tactic choice |

---

## Real-World Example: Fixing a Sorry

**Before:**
```lean
lemma example_lemma (n : ℕ) : n + 0 = n := by
  sorry
```

**LSP-Driven workflow:**

```bash
# Step 1: Check what we need to prove
lean_goal(file, line=2, column=1)
→ ⊢ n + 0 = n

# Step 2: Search for relevant lemmas
lean_local_search("add_zero")
→ Found: Nat.add_zero : ∀ n, n + 0 = n

# Step 3: Apply the lemma
# Edit file: by exact Nat.add_zero n

# Step 4: Verify immediately
lean_diagnostic_messages(file)
→ (empty - success!)

lean_goal(file, line=2)
→ "no goals"
```

**Result:** Proof completed in seconds with certainty, no guessing, no waiting for builds.

---

## Why This Matters

**Without LSP:** You're coding blind, relying on slow build cycles for feedback.

**With LSP:** You have the same interactive feedback loop as a human using the Lean InfoView.

**Key insight:** The LSP tools give you **goal state visibility** - the single most important thing when writing proofs. Use them aggressively, check constantly, and you'll write correct proofs faster.

---

## Quick Reference Command Sequence

**Standard proof workflow:**
```
1. lean_goal(file, line)              # What do I need to prove?
2. lean_local_search("keyword")       # Does the lemma exist? (FAST)
3. lean_hover_info(file, line, col)   # How do I use it?
4. [Edit file with tactic]
5. lean_diagnostic_messages(file)     # Did it work?
6. lean_goal(file, line)              # What's left?
7. Repeat steps 2-6 until "no goals"
```

**When stuck:**
```
1. lean_goal(file, line)              # See exact goal
2. lean_loogle("pattern")             # Find by type pattern
3. lean_leansearch("description")     # Find by description
4. lean_state_search(file, line, col) # Find by proof state
```

---

This workflow transforms Lean 4 proof development from a slow, iterative guess-and-check process into a fast, feedback-driven, interactive experience - exactly as intended by the language designers.
