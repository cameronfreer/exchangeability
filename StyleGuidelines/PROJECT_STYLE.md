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

## Related Documents

- [MATHLIB_STYLE_CHECKLIST.md](MATHLIB_STYLE_CHECKLIST.md): Mathlib style checklist
- [MATHLIB_STYLE_IMPLICIT_PARAMETERS.md](MATHLIB_STYLE_IMPLICIT_PARAMETERS.md): Implicit
  parameter conventions
