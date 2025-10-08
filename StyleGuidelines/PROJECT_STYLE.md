# Exchangeability Project Style Guide

This document describes style conventions specific to the Exchangeability project.

## Documentation Style

### Comments About Implementation Choices

**Avoid discussing axioms or choice principles in comments.** Do not include commentary
about whether constructions are "axiom-free", "avoid Choice", or similar remarks.

❌ **Bad:**
```lean
/-- Build a shift-invariant full-measure set, *without* appealing to additional axioms. -/
```

```lean
/-- This construction is completely **axiom-free** and uses only mathlib's standard
measure theory infrastructure. -/
```

```lean
/-- This avoids the Axiom of Choice by using a canonical limit process. -/
```

✅ **Good:**
```lean
/-- Build a shift-invariant full-measure set on which `g ∘ shift = g` holds pointwise. -/
```

```lean
/-- This construction uses only mathlib's standard measure theory infrastructure. -/
```

```lean
/-- This construction uses a canonical limit process rather than selecting arbitrary
representatives from equivalence classes. -/
```

**Rationale:** Whether a construction uses particular axioms is an implementation detail
that may change over time. Focus on what the code does, not on what axioms it does or
doesn't use.

### Exception: `axiom` Declarations

When using `axiom` declarations as temporary placeholders for unfinished proofs, it's
appropriate to document them as axioms:

✅ **Good:**
```lean
/-- Key lemma for the martingale proof. For now, accepting as axiom. -/
axiom conditionallyIID_of_exchangeable : ...
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

## Related Documents

- [MATHLIB_STYLE_CHECKLIST.md](MATHLIB_STYLE_CHECKLIST.md): Mathlib style checklist
- [MATHLIB_STYLE_IMPLICIT_PARAMETERS.md](MATHLIB_STYLE_IMPLICIT_PARAMETERS.md): Implicit
  parameter conventions
