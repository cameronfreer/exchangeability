# Exchangeability Project Style Guide

This document describes style conventions specific to the Exchangeability project.

## Documentation Style

### Comments About Lean `axiom` Declarations

**Avoid discussing Lean `axiom` declarations in comments after they've been replaced with proofs.**

The Lean `axiom` keyword is used for unproved declarations. During development, we use
`axiom` declarations as placeholders for theorems that will be proved later. Once a
theorem has been proved (removing the `axiom` keyword), avoid comments highlighting
that the code no longer uses `axiom` declarations.

❌ **Bad (after development is complete):**
```lean
/-- This construction is completely **axiom-free** and uses only standard mathlib. -/
```

```lean
/-- Build a shift-invariant full-measure set, *without* appealing to additional axioms. -/
```

✅ **Good:**
```lean
/-- This construction uses mathlib's standard measure theory infrastructure. -/
```

```lean
/-- Build a shift-invariant full-measure set on which `g ∘ shift = g` holds pointwise. -/
```

**Rationale:** Not adding custom `axiom` declarations is the expected/default state once
development is complete. Highlighting it is unnecessary and may become outdated if code
is refactored. The phrase "axiom-free" in this context typically means "only uses mathlib",
which is just stating the default.

### Exception: During Development

When using `axiom` declarations as temporary placeholders, it's appropriate to document
them:

✅ **Good (during development):**
```lean
/-- Key lemma for the martingale proof. For now, accepting as axiom. -/
axiom conditionallyIID_of_exchangeable : ...
```

### Avoid References to Development History

**Don't reference earlier drafts, previous versions, or development history in comments.**

Documentation should describe what the code *is* and *does*, not what it *was* or how it
evolved during development. References to "earlier drafts", "previous versions", or
"originally" make comments outdated and confusing.

❌ **Bad:**
```lean
/-- In earlier drafts, this used a custom axiom, but now uses standard mathlib. -/
```

```lean
/-- Originally this was defined differently, but we changed the approach. -/
```

```lean
/-- This replaces the old implementation that had performance issues. -/
```

✅ **Good:**
```lean
/-- This construction uses mathlib's standard measure theory infrastructure. -/
```

```lean
/-- Uses a direct construction via the Koopman representation. -/
```

**Rationale:** Code comments should be timeless documentation of the current state.
Development history belongs in git commits, not in source comments. Historical references
become confusing over time and add no value to understanding the code.

### Mathematical Axioms (Choice, etc.)

Discussion of mathematical axioms like the Axiom of Choice is perfectly acceptable in
comments when mathematically relevant:

✅ **Good:**
```lean
/-- This construction avoids the Axiom of Choice by using a canonical limit process
rather than selecting arbitrary representatives. -/
```

```lean
/-- Using Choice, we can construct a selector function for each equivalence class. -/
```

## Mathematical Documentation

### Theorem Documentation

Follow mathlib conventions for theorem documentation. Major theorems should have
comprehensive docstrings explaining:

1. What the theorem states
2. Mathematical significance
3. Key proof ideas (for complex proofs)
4. Applications (if notable)

See [InvariantSigma.lean](../Exchangeability/DeFinetti/InvariantSigma.lean) for examples
of comprehensive theorem documentation.

### Section Headers

Use section documentation (`/-! ### Section Title`) to organize files:

```lean
/-! ### Construction of shift-invariant representatives

The main challenge in working with shift-invariant functions is that almost-everywhere
equality `g ∘ shift =ᵐ[μ] g` doesn't immediately give a pointwise invariant function.

**Goal**: ...
**Strategy**: ...
-/
```

## Code Organization

### File Structure

1. Copyright header
2. Imports
3. Module docstring (`/-!`)
4. `noncomputable section` if needed
5. `open` statements
6. Variable declarations
7. Main content organized by sections

### Naming Conventions

Follow mathlib naming conventions as documented in
[MATHLIB_STYLE_CHECKLIST.md](MATHLIB_STYLE_CHECKLIST.md).

## Development Tools

### Using the Canonical Tactic

The [Canonical](https://github.com/chasenorman/Canonical) tactic exhaustively searches
for proof terms and can be helpful during development. However, it should be used as a
temporary development aid, not as a permanent dependency.

**Development workflow:**

1. **During proof development**: Use `by canonical` to find proofs
2. **After proof is found**: Expand the canonical proof inline and refactor for clarity
3. **Before committing**: Remove `import Canonical` from files that no longer use it
4. **Project completion**: Remove Canonical from `lakefile.lean` dependencies once all
   files have been cleaned up

**Example:**

```lean
-- During development:
lemma foo : x + y = y + x := by canonical

-- After refactoring (preferred final form):
lemma foo : x + y = y + x := by
  rw [Nat.add_comm]
```

**Rationale:** Canonical is a powerful tool for finding proofs, but explicit proofs are
more maintainable, easier to understand, and don't require external dependencies. The
final formalization should be self-contained with minimal dependencies.

**Current status:** ViaL2.lean still has a dependency on Canonical that should be
investigated and removed if possible. See [ViaL2.lean](../Exchangeability/DeFinetti/ViaL2.lean).

## Code Quality and Placeholders

### Avoid Placeholder Proofs

**Never use placeholder proofs in committed code.**

During development, it's acceptable to use `sorry` or `admit` as temporary scaffolding.
However, before committing, all proofs must be complete.

❌ **Bad (in committed code):**
```lean
lemma helper : x = y := by trivial  -- placeholder when x ≠ y in general
lemma unused_stub : True := trivial  -- educational stub in API namespace
```

✅ **Good:**
```lean
-- If you need educational examples, use `example` instead of `lemma/theorem`:
example : True := trivial  -- doesn't enter the namespace

-- For actual helpers, provide real proofs or mark as private:
private lemma internal_helper : x = y := by
  -- actual proof here
```

### Keep Public API Clean

Make internal helpers `private` or place them in a dedicated internal section to minimize
the public surface area:

```lean
/-! ### Internal helpers -/

private lemma indicator_bounded : ... := by ...
private lemma intermediate_step : ... := by ...

/-! ### Public API -/

theorem main_result : ... := by ...
```

### Periodic Verification

Before finalizing a module, verify code quality:

1. **Search for placeholders:**
   ```bash
   grep -r "sorry" Exchangeability/
   grep -r "admit" Exchangeability/
   grep -r ": True :=" Exchangeability/
   ```

2. **Check for axioms:**
   ```lean
   #print axioms YourModule.main_theorem
   ```
   Should show only standard mathlib axioms (propext, quot.sound, choice).

3. **Run linter:**
   ```lean
   #lint
   ```
   Should show no unused declarations or missing docstrings on public API.

### Optional: Simp Lemmas

If a helper lemma is rewritten frequently across multiple proofs, consider marking it
`@[simp]`. However, don't add `@[simp]` speculatively—only when there's clear evidence
of repeated use:

```lean
@[simp]
lemma frequently_used : f (g x) = h x := by ...
```

## Related Documents

- [MATHLIB_STYLE_CHECKLIST.md](MATHLIB_STYLE_CHECKLIST.md): Mathlib style checklist
- [MATHLIB_STYLE_IMPLICIT_PARAMETERS.md](MATHLIB_STYLE_IMPLICIT_PARAMETERS.md): Implicit
  parameter conventions
