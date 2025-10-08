# Mathlib Style Compliance Checklist

This document summarizes what we learned about Mathlib style conventions and what to check in future reviews.

**Last Updated:** 2025-10-07
**Status:** All major style issues resolved ✅

---

## Quick Reference: What to Check

### 1. Copyright Headers (CRITICAL)
**Status:** ✅ Fixed - All 15 files now have proper headers

```lean
/-
Copyright (c) YYYY Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
```

**Key Points:**
- Goes at the very top of every `.lean` file
- No blank line between copyright and imports
- Authors line has no period at the end
- Use `Authors:` even for single author

**Future checks:**
- When adding new files, copy the header from existing files
- Update year if needed

---

### 2. Naming Conventions (VERIFIED COMPLIANT)
**Status:** ✅ No violations found

**Quick rules:**
- `snake_case`: Theorems, lemmas, proofs (anything returning `Prop`)
- `UpperCamelCase`: Types, structures, classes, inductive types
- `lowerCamelCase`: Functions returning non-Prop types, definitions
- When `UpperCamelCase` appears in `snake_case`, use `lowerCamelCase`
  - Example: `IID` becomes `iid` in `iidProjectiveFamily`

**Examples from our codebase:**
- ✅ `deFinetti_RyllNardzewski_equivalence` (theorem)
- ✅ `DirectingMeasure` (structure)
- ✅ `iidProjectiveFamily` (function)
- ✅ `conditionallyIID_of_contractable` (theorem with acronym)

**Future checks:**
- Run grep for potential violations: `grep -n "^theorem [A-Z]" *.lean`
- Check new definitions follow the pattern

---

### 3. Line Length (MOSTLY FIXED)
**Status:** ✅ Fixed 40+ violations; ~20 minor ones remain (101-111 chars in docstrings)

**Rule:** Lines should not exceed 100 characters

**Common fixes applied:**
```lean
-- Before (103 chars)
theorem foo {μ : Measure (Ω[α])} [IsProbabilityMeasure μ] [StandardBorelSpace α] [StandardBorelSpace (Ω[α])] :

-- After
theorem foo {μ : Measure (Ω[α])} [IsProbabilityMeasure μ] [StandardBorelSpace α]
    [StandardBorelSpace (Ω[α])] :
```

**Breaking strategies used:**
1. Break after function parameters (before `:`)
2. Break after `:=` in long assignments
3. Break in calc chains after relation symbols
4. Indent continuation lines by 4 spaces (or 2 for certain contexts)

**Future checks:**
```bash
# Find all lines > 100 chars
awk 'length > 100 {print FILENAME ":" NR ": " length($0) " chars"}' **/*.lean
```

---

### 4. File Names
**Status:** ✅ All compliant

**Rule:** Use `UpperCamelCase.lean` for all files

**Our files (all correct):**
- ✅ `Core.lean`, `DeFinetti.lean`, `ConditionallyIID.lean`
- ✅ `ViaKoopman.lean`, `ViaL2.lean`, `ViaMartingale.lean`

**Exception (very rare):** Files named after lowercase objects like `lp.lean` for ℓ^p space (not applicable to us)

---

### 5. Module Docstrings
**Status:** ✅ All files have excellent docstrings

**Required structure:**
```lean
/-!
# Title of Module

Brief description of what this file does.

## Main results

- `theorem_name`: Description of what it proves
- `another_theorem`: More description

## Notation

- `|_|`: The barrification operator

## References

- [Author2000] Full citation
-/
```

**Our best examples:**
- `Core.lean`: Great overview of π-system approach
- `DeFinetti.lean`: Excellent 3-proof comparison
- `ConditionallyIID.lean`: Clear structure with main results

**Future checks:**
- Every new file needs a module docstring
- Update "Main results" when adding new theorems
- Keep docstrings accurate as code evolves

---

### 6. Import Formatting
**Status:** ✅ All correct

**Rules:**
- Imports go immediately after copyright (no blank line)
- Each import on separate line
- Blank line between imports and module docstring
- No sorting requirement, but grouping related imports is nice

**Pattern used throughout:**
```lean
/-
Copyright...
-/
import Mathlib.Foo
import Mathlib.Bar
import Exchangeability.Baz

/-!
# Module docstring
```

---

### 7. Tactic Mode Formatting
**Status:** ✅ Generally good

**Key rules:**
- `by` goes at end of previous line, NOT on its own line
- Indent tactics by 2 spaces
- Use focusing dot `·` for subgoals (also indented 2 spaces)
- Avoid semicolons when possible; prefer newlines

**Good example from our code:**
```lean
theorem foo : ... := by
  intro x
  cases x
  · exact h1  -- First case
  · exact h2  -- Second case
```

**Minor issues found (acceptable):**
- 3 instances of `by exact` (could use `:=` directly)
- 5 semicolons at line end (discouraged but not wrong)

**Future improvements (optional):**
```lean
-- Instead of:
theorem foo : P := by exact proof_term
-- Use:
theorem foo : P := proof_term
```

---

### 8. Calculation Proofs (`calc`)
**Status:** ✅ Good style throughout

**Our pattern (from L2Approach.lean):**
```lean
calc σSq * (1 - ρ) * ∑ i, (c i)^2
    ≤ σSq * (1 - ρ) * (∑ i, |c i| * (⨆ j, |c j|)) :=
        mul_le_mul_of_nonneg_left step5 hσ_1ρ_nonneg
  _ = σSq * (1 - ρ) * ((∑ i, |c i|) * (⨆ j, |c j|)) := by rw [Finset.sum_mul]
```

**Key points:**
- Align `=` or `≤` symbols
- Justify each step
- Can use `by` for simple rewrites

---

## 9. Documentation Content

### Avoid Development History References
**Rule:** Don't reference "earlier drafts", "previous versions", or development history in
comments or docstrings.

**Why:** Comments should be timeless documentation of the current state. Historical
references become outdated and confusing.

❌ **Bad:**
```lean
/-- In earlier drafts, this used axioms, but now it doesn't. -/
/-- Originally defined differently, but we changed the approach. -/
/-- This replaces the old broken implementation. -/
```

✅ **Good:**
```lean
/-- Uses mathlib's standard measure theory infrastructure. -/
/-- Constructs a shift-invariant function via the Koopman representation. -/
```

**Check for violations:**
```bash
grep -n "earlier draft\|previous version\|originally\|used to\|old implementation" \
  Exchangeability/**/*.lean
```

---

## 10. Things We Don't Need to Worry About

**✅ Already compliant:**
- No `$` operator (we use `<|` correctly)
- No `λ` syntax (we use `fun`)
- Proper `←` spacing (always `← ` with space after)
- No unwanted emojis
- Type parameters are implicit `{}` (recent fix)

---

## 11. Known Non-Issues

**Sorry statements (40 total):**
- NOT a style violation
- These are placeholder proofs we're working on
- Located in: DeFinetti.lean (2), ViaKoopman.lean (7), ViaL2.lean (16),
  ViaMartingale.lean (9), CondExp.lean (6)

**Empty lines in declarations:**
- Mathlib discourages but doesn't forbid
- We have some but they're generally for readability in long proofs
- Not critical to fix

---

## Quick Commands for Future Checks

```bash
# 1. Check copyright headers
head -5 Exchangeability/**/*.lean | grep -A 5 "Copyright"

# 2. Check line lengths
awk 'length > 100 {print FILENAME ":" NR}' Exchangeability/**/*.lean

# 3. Check for naming violations
grep -n "^theorem [A-Z]" Exchangeability/**/*.lean  # Should be empty
grep -n "^def [a-z_].*: Prop" Exchangeability/**/*.lean  # Should be empty

# 4. Count sorries (expected to decrease over time)
grep -c "sorry" Exchangeability/**/*.lean

# 5. Check for disallowed syntax
grep -n "\\$" Exchangeability/**/*.lean  # Should use <|
grep -n "\\lambda" Exchangeability/**/*.lean  # Should use fun
```

---

## What to Do for New Files

1. **Start with copyright header** (copy from existing file)
2. **Add imports** (no blank line after copyright)
3. **Add module docstring** with `/-!` delimiter
4. **Follow naming conventions**:
   - Theorems: `snake_case`
   - Types: `UpperCamelCase`
   - Functions: `lowerCamelCase`
5. **Keep lines ≤ 100 chars**
6. **Use `by` at end of line, not alone**
7. **Add docstrings to main declarations**

---

## Resources

- [Mathlib Style Guide](https://leanprover-community.github.io/contribute/style.html)
- [Naming Conventions](https://leanprover-community.github.io/contribute/naming.html)
- Our codebase examples:
  - Best docstrings: `Core.lean`, `DeFinetti.lean`
  - Good calc proofs: `L2Approach.lean`
  - Clean structure: `ConditionallyIID.lean`

---

## Changelog

- **2025-10-07**: Initial review
  - Fixed all copyright headers (15 files)
  - Fixed 40+ line length violations
  - Verified naming conventions (all compliant)
  - Documented current state and future checks
