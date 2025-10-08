# Mathlib Style: Implicit Parameters Conversion Guide

**Date**: October 2025
**Status**: Complete conversion of exchangeability project
**Purpose**: Reference guide for future implicit parameter conversions

---

## What We Learned

### Overview

We successfully converted 70+ lemmas/theorems/definitions across 15 files to use mathlib-style implicit `{}` parameters. This document captures the patterns, strategies, and lessons learned for applying this to other Lean 4 projects.

---

## Core Principle: When to Use `{}` vs `()`

### Use Implicit `{param : Type}` when:

1. **Type inferrable from other parameters**
   ```lean
   -- ✅ GOOD: n inferrable from S
   def prefixCylinder {n : ℕ} (S : Set (Fin n → α)) : Set (ℕ → α)

   -- ✅ GOOD: n inferrable from c, p, q
   lemma l2_bound_from_steps {n : ℕ} {c p q : Fin n → ℝ} (σSq ρ : ℝ)
   ```

2. **Parameter appears in types but not needed at call site**
   ```lean
   -- ✅ GOOD: m inferrable from fs
   def productCylinder {m : ℕ} (fs : Fin m → α → ℝ) : Ω[α] → ℝ

   -- ✅ GOOD: n inferrable from ξ
   theorem l2_contractability_bound {n : ℕ} (ξ : Fin n → Ω → ℝ)
   ```

3. **Multiple parameters depend on same type variable**
   ```lean
   -- ✅ GOOD: Both c and covariance matrices depend on n
   lemma double_sum_covariance_formula {n : ℕ} {c : Fin n → ℝ} (σSq ρ : ℝ)
   ```

### Keep Explicit `(param : Type)` when:

1. **Primary data arguments**
   ```lean
   -- ✅ CORRECT: μ and X are the main subjects
   theorem deFinetti {μ : Measure Ω} (X : ℕ → Ω → α)

   -- ✅ CORRECT: s is what we're testing
   def isShiftInvariant (s : Set (Ω[α])) : Prop
   ```

2. **Parameter used in function body, not in types**
   ```lean
   -- ✅ CORRECT: n used in shift^[n], not inferrable
   def shiftedCylinder (n : ℕ) (F : Ω[α] → ℝ) : Ω[α] → ℝ :=
     fun ω => F ((shift^[n]) ω)
   ```

3. **Application lemmas**
   ```lean
   -- ✅ CORRECT: n is the explicit argument being applied
   lemma shift_apply {α : Type*} (ξ : ℕ → α) (n : ℕ) :
     shift ξ n = ξ (n + 1)
   ```

4. **Named hypotheses/proofs**
   ```lean
   -- ✅ CORRECT: These are explicit assumptions
   (hX : Measurable X) (hcov : ∀ i j, ...)
   ```

5. **Parameters in return types**
   ```lean
   -- ✅ CORRECT: n appears in Fin n in return type
   lemma Exchangeable.refl {μ : Measure Ω} {X : ℕ → Ω → α} (n : ℕ) :
     ... → (Fin n → α) = ...
   ```

---

## Systematic Conversion Strategy

### Phase 1: Search and Identify

**Commands to find candidates:**
```bash
# Find lemmas with explicit nat parameters
grep -rn "^lemma .* (n : ℕ)" . --include="*.lean" | grep -v "{n : ℕ}"

# Find definitions with Fin parameters
grep -rn "^def .* (.*: Fin .* →" . --include="*.lean" | grep -v "{.*: Fin"

# Find theorems with type parameters
grep -rn "^theorem .* (n : ℕ)\|^theorem .* (m : ℕ)" . --include="*.lean"
```

### Phase 2: Analyze Each Candidate

For each candidate, ask:

1. **Can it be inferred?** Does the parameter appear in the type of another parameter?
2. **Is it the main subject?** Is this what the lemma is "about"?
3. **Is it in the return type?** Does it appear in the result type?
4. **Is it used in the body?** Does it appear in the definition but not in parameter types?

### Phase 3: Convert and Update Call Sites

**Pattern for conversion:**

1. Change definition:
   ```lean
   -- Before
   lemma foo (n : ℕ) (c : Fin n → ℝ) := ...

   -- After
   lemma foo {n : ℕ} {c : Fin n → ℝ} := ...
   ```

2. Update call sites:
   ```lean
   -- Before
   foo n c

   -- After
   foo  -- fully inferred, or
   foo (c := c)  -- if needed for disambiguation
   ```

3. Build and fix errors:
   ```bash
   lake build <file>
   # Fix any "function expected" errors by adding named parameters
   ```

---

## Common Patterns We Converted

### Pattern 1: Fin-Indexed Functions

**Before:**
```lean
lemma sum_sq_le_sum_abs_mul_sup (n : ℕ) (c : Fin n → ℝ) :
  ∑ i, (c i)^2 ≤ ∑ i, |c i| * (⨆ j, |c j|)
```

**After:**
```lean
lemma sum_sq_le_sum_abs_mul_sup {n : ℕ} {c : Fin n → ℝ} :
  ∑ i, (c i)^2 ≤ ∑ i, |c i| * (⨆ j, |c j|)
```

**Call sites:** Remove `(n:=n) c` → becomes fully inferred

### Pattern 2: Cylinder Sets

**Before:**
```lean
def prefixCylinder (n : ℕ) (S : Set (Fin n → α)) : Set (ℕ → α)
```

**After:**
```lean
def prefixCylinder {n : ℕ} (S : Set (Fin n → α)) : Set (ℕ → α)
```

**Call sites:** `prefixCylinder n S` → `prefixCylinder S`

### Pattern 3: Permutations

**Before:**
```lean
def extendFinPerm (n : ℕ) (σ : Equiv.Perm (Fin n)) : Equiv.Perm ℕ
```

**After:**
```lean
def extendFinPerm {n : ℕ} (σ : Equiv.Perm (Fin n)) : Equiv.Perm ℕ
```

**Call sites:** `extendFinPerm n σ` → `extendFinPerm σ`

### Pattern 4: Main Theorems

**Before:**
```lean
theorem l2_contractability_bound
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (n : ℕ) (ξ : Fin n → Ω → ℝ)
    (p q : Fin n → ℝ) ...
```

**After:**
```lean
theorem l2_contractability_bound
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} (ξ : Fin n → Ω → ℝ)
    (p q : Fin n → ℝ) ...
```

**Rationale:** `n` inferred from `ξ`, `p`, and `q`, but `ξ`, `p`, `q` remain explicit as primary data

---

## Common Errors and Fixes

### Error 1: "Function expected"

**Symptom:**
```
error: Function expected at
  foo n c
but this term has type ...
```

**Cause:** After making `n` implicit, call site still passes it explicitly

**Fix:** Use named parameters or remove the argument
```lean
-- Option 1: Remove argument (if fully inferrable)
foo c

-- Option 2: Named parameter (if needed)
foo (n:=n) c

-- Option 3: Make explicit with @ (rarely needed)
@foo n c
```

### Error 2: "Cannot infer implicit parameter"

**Symptom:**
```
error: Cannot infer implicit argument 'n'
```

**Cause:** Made parameter implicit when it's NOT inferrable

**Fix:** Keep it explicit - it was correct before!

### Error 3: Merge conflicts on call sites

**Symptom:** Remote branch has `@foo α _ ν`, local has `foo (ν:=ν)`

**Resolution:** Keep the mathlib-style named parameter version

---

## Files We Converted

### High-Value Files (Good starting points for other projects)

1. **Core.lean** - Basic infrastructure
   - `prefixCylinder`, `prefixProj`, `reindex`
   - Pattern: Type parameters inferrable from Set/function types

2. **L2Approach.lean** - Complete proof file
   - All 7 helper lemmas + main theorem
   - Pattern: `n` inferrable from `c : Fin n → ℝ`
   - **Best example for conversion workflow**

3. **ViaKoopman.lean** - Ergodic theory approach
   - `cylinderFunction`, `productCylinder`
   - Pattern: `m` inferrable from function types

4. **Contractability.lean** - Core definitions
   - `extendFinPerm`
   - Pattern: `n` inferrable from `Equiv.Perm (Fin n)`

### Summary Statistics

| File | Conversions | Main Pattern |
|------|-------------|--------------|
| L2Approach.lean | 7 | `{n : ℕ} {c : Fin n → ℝ}` |
| Core.lean | 15+ | Cylinder sets, projections |
| ViaKoopman.lean | 12 | Cylinder functions |
| Contractability.lean | 5 | Permutations, exchangeability |
| ConditionallyIID.lean | 3 | Measure operations |
| InfiniteProduct.lean | 6 | Projective families |

---

## Best Practices for Future Conversions

### 1. Work File-by-File

Don't try to convert the whole codebase at once. Pick logical units:
- Start with infrastructure files (Core, basic definitions)
- Move to proof files that depend on them
- Finish with high-level theorems

### 2. Build After Each Change

```bash
lake build <file>
```

Fix errors immediately before moving on. This prevents cascading failures.

### 3. Use Grep Patterns Systematically

```bash
# Pattern to find ALL candidates in one file
grep -n "^lemma\|^theorem\|^def" File.lean | \
  grep " (n : ℕ)\| (m : ℕ)\| (i : Fin" | \
  grep -v "{n : ℕ}\|{m : ℕ}\|{i : Fin"
```

### 4. Document Rationale in Commits

Good commit message format:
```
Make n parameter implicit in <function>

Converted the explicit `n : ℕ` parameter to implicit in <function>
since it can be inferred from the type `x : Fin n → T`.

## Changes

- Change `def foo (n : ℕ)` to `def foo {n : ℕ}`
- Updated X call sites to remove explicit n argument

Following mathlib conventions for inferrable parameters.
```

### 5. When in Doubt, Keep Explicit

It's better to have one explicit parameter that could be implicit than to have an implicit parameter causing inference issues. Main theorems especially benefit from clarity.

---

## Verification Checklist

Before considering conversion complete:

- [ ] All helper lemmas converted
- [ ] All definitions with inferrable params converted
- [ ] Main theorems reviewed (convert or document why not)
- [ ] All call sites updated
- [ ] Build succeeds: `lake build`
- [ ] No new "cannot infer" errors introduced
- [ ] Git grep confirms no missed opportunities:
  ```bash
  grep -rn "^lemma .* (n : ℕ)" . --include="*.lean" | grep -v "{n : ℕ}"
  ```

---

## What to Try Next

### For This Project (exchangeability-cursor)

1. **After fixing pre-existing errors** in CommonEnding.lean and InvariantSigma.lean, verify those files have no additional conversion opportunities

2. **Future file additions**: Apply these patterns immediately when adding new lemmas

3. **Review main theorems** periodically as they evolve - e.g., if `deFinetti` theorem gets additional parameters

### For Other Lean 4 Projects

1. **Start with search**: Run the grep patterns to find candidates
   ```bash
   grep -rn "^lemma .* (n : ℕ)" . --include="*.lean" | grep -v "{n : ℕ}" | wc -l
   ```

2. **Pick a pilot file**: Choose a small, self-contained file (~100-200 lines) with clear type dependencies

3. **Follow the L2Approach.lean model**:
   - Convert helper lemmas first (bottom-up)
   - Then convert main theorems
   - Build and test after each batch

4. **Focus on these parameter patterns**:
   - `(n : ℕ)` when functions have type `Fin n → T`
   - `(α : Type*)` when it appears in other parameter types
   - Type parameters in generic definitions

5. **Document exceptions**: When you decide NOT to convert, add a comment explaining why

---

## References

### Mathlib Style Guide

Key section: **3.2.2 Implicit and Explicit Arguments**

Rules from mathlib:
- `()` - Explicit data and named hypotheses the caller must provide
- `{}` - Types and values uniquely determined by unification from other arguments
- `[]` - Typeclass instances filled by instance synthesis

### Related Commits in This Project

- `b6a687d` - Main theorem in L2Approach (best example)
- `f71b8a4` - Helper lemmas in L2Approach (systematic conversion)
- `7e2ebe7` - Core and ViaKoopman (definitions)
- `6379dc7` - Single definition (minimal example)

### Useful Grep Patterns

```bash
# Find all lemmas with explicit parameters
grep -rn "^lemma .* ([a-z] : " . --include="*.lean"

# Find theorems needing review
grep -rn "^theorem" . --include="*.lean" | grep " (n : ℕ)\| (m : ℕ)"

# Count conversions remaining
grep -rn "^lemma .* (n : ℕ)" . --include="*.lean" | grep -v "{n : ℕ}" | wc -l

# Verify no missed Fin parameters
grep -rn "^lemma .* (.*: Fin.*→" . --include="*.lean" | grep -v "{.*: Fin"
```

---

## Success Metrics

For the exchangeability project:
- ✅ 70+ items converted
- ✅ 15 files reviewed
- ✅ 100% of L2Approach.lean converted
- ✅ All builds successful (2516+ jobs)
- ✅ Zero "cannot infer" errors introduced
- ✅ Code more concise and mathlib-compliant

**Key insight**: Systematic conversion following these patterns resulted in cleaner, more idiomatic Lean 4 code that better matches mathlib conventions, making the project more maintainable and easier to contribute to mathlib in the future.
