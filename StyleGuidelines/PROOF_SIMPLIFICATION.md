# Proof Simplification Guide

This guide describes systematic passes to simplify and clean up proofs after the entire
file compiles successfully.

## When to Simplify

**After the file compiles**, perform simplification passes to improve:
- Code readability and maintainability
- Proof conciseness without sacrificing clarity
- Alignment with mathlib style conventions

**Do not** prematurely optimize proofs while still getting the code to work. First make
it compile, then make it clean.

## Simplification Patterns

### 1. Inline Unnecessary Intermediate Lemmas

**Before:**
```lean
have hterm : ∀ j ∈ Neg, |c j| = -c j := fun j hj => abs_of_neg (Finset.mem_filter.mp hj).2
calc ∑ j ∈ Neg, |c j|
    = ∑ j ∈ Neg, (-c j) := Finset.sum_congr rfl hterm
  _ = -∑ j ∈ Neg, c j := by simp [Finset.sum_neg_distrib]
```

**After:**
```lean
calc ∑ j ∈ Neg, |c j|
    = ∑ j ∈ Neg, (-c j) := Finset.sum_congr rfl (fun j hj => abs_of_neg (Finset.mem_filter.mp hj).2)
  _ = -∑ j ∈ Neg, c j := by simp [Finset.sum_neg_distrib]
```

**When to inline:**
- The intermediate lemma is used exactly once
- Inlining doesn't make the proof significantly harder to read
- The term fits naturally as a lambda or inline expression

**When to keep separate:**
- The lemma is used multiple times
- The proof is complex and benefits from a descriptive name
- Inlining would create an unreadably long line

### 2. Consolidate Chains of Simple Rewrites

**Before:**
```lean
have hσSq_nonneg : 0 ≤ σSq := by
  simpa [σSq] using sq_nonneg σ

have hvar : ∀ k, ∫ ω, (ξ k ω - m)^2 ∂μ = σSq := by
  intro k; simpa [σSq] using _hvar k
```

**After:**
```lean
have hσSq_nonneg : 0 ≤ σSq := sq_nonneg σ
have hvar : ∀ k, ∫ ω, (ξ k ω - m)^2 ∂μ = σSq := fun k => _hvar k
```

**When to consolidate:**
- `simpa` or `simpa using` that just unfolds definitions
- Simple `intro` followed by direct application
- `by exact` wrappers (just remove the `by exact`)

### 3. Merge Simp Steps

**Before:**
```lean
have hc_sum : ∑ j, c j = 0 := by
  simp only [c]
  have hp := _hp_prob.1
  have hq := _hq_prob.1
  rw [Finset.sum_sub_distrib, hp, hq]
  ring
```

**After:**
```lean
have hc_sum : ∑ j, c j = 0 := by
  simp only [c, Finset.sum_sub_distrib, _hp_prob.1, _hq_prob.1]; ring
```

**When to merge:**
- Multiple `simp only` or `rw` steps that could be combined
- Sequential rewrites that don't need intermediate inspection
- Proof ends with `ring`, `linarith`, or other finishing tactic

### 4. Replace `trans` + `calc` with Single `calc`

**Before:**
```lean
have h_diag : ... := by
  trans (∑ i, (c i)^2 * σSq)
  · congr 1; ext i
    calc ...
  · rw [← Finset.sum_mul]; ring
```

**After:**
```lean
have h_diag : ... := by
  calc ∑ i, c i * c i * ∫ ω, (ξ i ω - m) * (ξ i ω - m) ∂μ
      = ∑ i, (c i)^2 * σSq := by congr 1; ext i; calc ...
    _ = σSq * ∑ i, (c i)^2 := by rw [← Finset.sum_mul]; ring
```

**When to use single calc:**
- The intermediate step is clear from the calc chain
- `trans` is only being used to set up a calc
- The proof becomes more readable as a unified calculation

### 5. Eliminate Nested Helper Lemmas in Calc Chains

**Before:**
```lean
have h_offdiag : ... := by
  have h_cov_term : ∀ i j, ... := by ...
  have h_rewrite : ... := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j hj
    exact h_cov_term i j ...
  have h_factor : ... := by simp [Finset.mul_sum, mul_assoc]
  calc ... = ... := h_rewrite
       _ = ... := h_factor
```

**After:**
```lean
have h_offdiag : ... := by
  calc ∑ i, ∑ j with j ≠ i, c i * c j * ∫ ω, (ξ i ω - m) * (ξ j ω - m) ∂μ
      = ∑ i, ∑ j with j ≠ i, σSq * ρ * (c i * c j) := by
          apply Finset.sum_congr rfl; intro i _
          apply Finset.sum_congr rfl; intro j hj
          have hcov_ij := hcov i j (Ne.symm (Finset.mem_filter.mp hj).2)
          simp [hcov_ij, mul_comm, mul_assoc]
    _ = σSq * ρ * ∑ i, ∑ j with j ≠ i, c i * c j := by simp [Finset.mul_sum, mul_assoc]
```

**When to inline helpers:**
- Helper lemmas are used exactly once in the final calc
- The proof logic is clearer when steps are inline
- The helper names don't add significant documentation value

### 6. Use Direct Proof Terms Instead of Tactic Mode

**Before:**
```lean
have hσ_1ρ_nonneg : 0 ≤ σSq * (1 - ρ) := by
  apply mul_nonneg hσSq_nonneg
  linarith [_hρ_bd.2]
```

**After:**
```lean
have hσ_1ρ_nonneg : 0 ≤ σSq * (1 - ρ) :=
  mul_nonneg hσSq_nonneg (by linarith [_hρ_bd.2])
```

**When to use term mode:**
- The proof is a simple function application
- The result is more concise and readable
- You can still use `by` for complex sub-proofs

### 7. Reuse Intermediate Definitions

**Before:**
```lean
have step5 : ... := by
  have hbdd : BddAbove ... := ...
  ...

have hsup_nonneg : 0 ≤ ⨆ j, |c j| := by
  have hbdd : BddAbove ... := ...  -- duplicate!
  ...
```

**After:**
```lean
have hbdd : BddAbove (Set.range fun j : Fin n => |c j|) := ...

have step5 : ... := by
  ...  -- uses hbdd

have hsup_nonneg : 0 ≤ ⨆ j, |c j| := by
  ...  -- also uses hbdd
```

**When to factor out definitions:**
- The same definition appears multiple times
- The definition is used in multiple proofs
- Factoring improves clarity of proof dependencies

### 8. Simplify `simpa` Wrappers

**Before:**
```lean
have h_sq : (∑ i, c i)^2 = ∑ i, ∑ j, c i * c j := by
  simpa [pow_two] using
    (Finset.sum_mul_sum (s := Finset.univ) (t := Finset.univ)
      (f := fun i => c i) (g := fun j => c j))
```

**After:**
```lean
have h_sq : (∑ i, c i)^2 = ∑ i, ∑ j, c i * c j := by
  rw [pow_two, Finset.sum_mul_sum (s := Finset.univ) (t := Finset.univ)
    (f := fun i => c i) (g := fun j => c j)]
```

**When to replace `simpa`:**
- It's just unfolding a definition (`pow_two`)
- `rw` or `simp only` is clearer
- The `using` clause is doing the real work

### 9. Remove Commented-Out Code

**After the file compiles successfully**, remove:
- Failed proof attempts
- Debugging traces
- Commented-out alternative approaches
- Old versions of refactored code

**Exception:** Keep brief comments explaining:
- Why a particular approach was chosen
- Known issues or future TODOs
- Strategies for completing sorrys

**Good comment (keep):**
```lean
-- Strategy: Use Dynkin's π-λ theorem to extend from rectangles to product σ-algebra
-- TODO: Complete the π-system verification
```

**Bad comment (remove):**
```lean
-- have h1 := ...
-- rw [...]
-- -- this doesn't work
-- have h2 := ...
-- rw [...]
-- -- also doesn't work
```

### 9a. Extract and Remove Canonical Tactic Usage

The [Canonical](https://github.com/chasenorman/Canonical) tactic can help find proofs
during development, but should be removed before committing. See
[PROJECT_STYLE.md](PROJECT_STYLE.md#using-the-canonical-tactic) for full guidelines.

**Workflow:**
1. During development, use `by canonical` to find difficult proofs
2. Extract the proof term (hover over the tactic to see what it synthesized)
3. Refactor the extracted proof for clarity
4. Remove `import Canonical` from the file
5. After all files are cleaned up, remove Canonical from `lakefile.lean`

**Example:**

During development:
```lean
lemma helper : x + 0 = x := by canonical
```

After extraction and refactoring:
```lean
lemma helper : x + 0 = x := Nat.add_zero x
```

**When to use Canonical:**
- You're stuck on a technical lemma
- The proof is likely straightforward but tedious
- You want to quickly unblock development

**When NOT to use Canonical:**
- For proofs with mathematical insight (write them explicitly)
- As a permanent solution (always extract and refactor)
- When a simple tactic like `simp`, `ring`, or `linarith` would work

### 10. Factor Out Large Proof Blocks into Lemmas

When a proof becomes very long (>50 lines) with clear logical sections, consider
factoring major steps into separate lemmas.

**Before (in main theorem):**
```lean
theorem main_result : ... := by
  -- 150 lines of proof with steps 1-6
  calc ...
```

**After:**
```lean
lemma step1 : ... := by
  -- 20 lines

lemma step2 : ... := by
  -- 25 lines

-- ... more steps

theorem main_result : ... := by
  calc ... = ... := step1
       _ = ... := step2
       ...
```

**Benefits:**
- Main theorem structure is immediately clear
- Individual steps are independently testable
- Lemmas can be reused elsewhere
- Easier to review and maintain

## Systematic Simplification Workflow

When you've finished getting a file to compile, follow this workflow:

### Pass 1: Structural Cleanup

1. Remove commented-out code
2. Factor out major proof blocks into lemmas (if needed)
3. Move definitions closer to their use sites
4. Reorder lemmas into logical groups

### Pass 2: Local Simplifications

5. Inline single-use intermediate lemmas
6. Consolidate simple rewrites
7. Replace `simpa` with direct `rw` or `simp only` where clearer
8. Remove unnecessary `by exact` wrappers
9. Convert simple tactic proofs to term mode

### Pass 3: Proof Chain Improvements

10. Merge sequential simp/rw steps
11. Replace `trans` + `calc` with single `calc`
12. Eliminate nested helpers in calc chains
13. Identify and reuse common sub-expressions

### Pass 4: Verification

14. Run `lake build` to ensure everything still compiles
15. Run `#lint` to check for new issues
16. Read through simplified proofs to verify readability

## Measuring Success

Good simplifications should:
- **Reduce line count** without sacrificing clarity
- **Improve readability** by removing redundant steps
- **Maintain proof structure** - the mathematical logic should still be clear
- **Follow mathlib conventions** - align with standard proof patterns

**Example metrics from past simplifications:**

- `59ca440`: L2Approach.lean reduced by 19 lines (481→462)
- `b888499`: L2Approach.lean reduced by 18 lines with better organization
- `d3edd30`: KoopmanMeanErgodic.lean reduced by 12 lines (50→38 in affected proofs)

## Anti-Patterns to Avoid

### Don't Over-Inline

**Bad:**
```lean
calc x = y := by
  apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j hj;
  have h1 := ...; have h2 := ...; have h3 := ...; simp [h1, h2, h3, mul_comm, mul_assoc];
  rw [h4, h5]; ring; linarith [h6, h7]
```

If inlining creates a proof that's hard to follow, keep intermediate steps.

### Don't Remove Helpful Names

**Bad:**
```lean
have : ... := by
  ... -- 10 lines of proof
have : ... := by
  ... -- uses first anonymous have
```

**Good:**
```lean
have hkey_property : ... := by
  ... -- 10 lines of proof
have hconclusion : ... := by
  ... -- uses hkey_property
```

If an intermediate result has mathematical significance, give it a descriptive name.

### Don't Sacrifice Clarity for Brevity

**Bad:**
```lean
theorem main : ... :=
  ⟨λ h => h.1.2.1, λ h => ⟨⟨h.1, h.2⟩, ⟨h.3, h.4⟩, ⟨h.5, h.6⟩⟩⟩
```

**Good:**
```lean
theorem main : ... := by
  constructor
  · intro h; exact h.prop1
  · intro h; exact ⟨h.left, h.right, h.key⟩
```

If term-mode proof becomes cryptic, stick with tactic mode.

## Examples from This Project

See these commits for examples of successful simplification passes:

- `59ca440`: L2Approach.lean simplifications (19 line reduction)
  - Consolidated simp steps, inlined single-use lemmas, merged calc chains
- `b888499`: L2Approach.lean refactoring (18 line reduction)
  - Factored step 6 into lemma, reorganized declarations, improved structure
- `d3edd30`: KoopmanMeanErgodic.lean simplifications (12 line reduction)
  - Removed simpa wrappers, consolidated hypotheses, direct term proofs
- `f728bbf`: ViaKoopman.lean cleanup (98 line reduction)
  - Removed commented-out proof attempts, clear TODO comments

## Related Documents

- [PROJECT_STYLE.md](PROJECT_STYLE.md): General project style guidelines
- [MATHLIB_STYLE_CHECKLIST.md](MATHLIB_STYLE_CHECKLIST.md): Mathlib style conventions
