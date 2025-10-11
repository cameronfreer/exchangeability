# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

This is a **Lean 4 formalization** of **de Finetti's theorem** and the **de Finetti-Ryll-Nardzewski equivalence** for infinite sequences on Borel spaces. The project implements **all three proofs** from Kallenberg (2005) of the key implication: **contractable → conditionally i.i.d.**

**Core equivalence being proved:**
```
Contractable ⟺ Exchangeable ⟺ Conditionally i.i.d.
```

## Building and Testing

### Build Commands
```bash
# Full build
lake build

# Build specific file
lake build Exchangeability.DeFinetti.ViaL2

# Clean build artifacts
lake clean

# Update dependencies
lake update

# Execute main program
lake exe exchangeability
```

### Checking Proofs
```bash
# Check a specific file for errors
lake env lean Exchangeability/DeFinetti/ViaL2.lean

# Check for axioms used in a theorem (from within Lean file):
#print axioms deFinetti_viaL2
# Should only show standard mathlib axioms: propext, quot.sound, choice
```

### No Test Suite
This project does not have a test suite. Correctness is verified by Lean's type checker during `lake build`.

## Architecture Overview

### Three Independent Proof Approaches

The project implements three mathematically distinct proofs of the main theorem. Each proof is self-contained:

1. **L² Approach** (`DeFinetti/ViaL2.lean`) - **Default proof**
   - Uses elementary L² contractability bounds
   - Lightest dependencies (no ergodic theory)
   - Kallenberg's "second proof"

2. **Koopman/Ergodic Approach** (`DeFinetti/ViaKoopman.lean`)
   - Uses Mean Ergodic Theorem via Koopman operator
   - Deep connection to dynamical systems
   - Heavy dependencies: requires `Ergodic/KoopmanMeanErgodic.lean`
   - Kallenberg's "first proof"

3. **Martingale Approach** (`DeFinetti/ViaMartingale.lean`)
   - Uses reverse martingale convergence
   - Elegant probabilistic argument
   - Kallenberg's "third proof" (after Aldous)

**Key insight:** The default public API (`DeFinetti/Theorem.lean`) re-exports the L² proof to minimize dependencies.

### Core Module Structure

```
Exchangeability/
├── Core.lean                    # π-system machinery, finite marginals theorem
├── Contractability.lean         # Exchangeable ↔ Contractable (easy direction)
├── ConditionallyIID.lean        # ConditionallyIID → Exchangeable (easy direction)
├── Probability/                 # Infrastructure
│   ├── InfiniteProduct.lean    # Ionescu-Tulcea construction
│   └── CondExp.lean            # Conditional expectation extensions
└── DeFinetti/
    ├── Theorem.lean            # Public API (re-exports ViaL2)
    ├── TheoremViaL2.lean       # L² proof theorem statement
    ├── TheoremViaKoopman.lean  # Ergodic proof theorem statement
    ├── TheoremViaMartingale.lean # Martingale proof theorem statement
    ├── ViaL2.lean              # L² proof implementation
    ├── ViaKoopman.lean         # Ergodic proof implementation
    ├── ViaMartingale.lean      # Martingale proof implementation
    ├── L2Approach.lean         # L² lemmas
    ├── CommonEnding.lean       # Shared final step (monotone class)
    └── InvariantSigma.lean     # Shift-invariant σ-algebras
```

### Key Technical Machinery

#### π-system Uniqueness (`Core.lean`)
- Defines `prefixCylinders`: sets determined by finite prefixes
- Proves they form a π-system generating the product σ-algebra
- **Main theorem:** `measure_eq_of_fin_marginals_eq` - measures are determined by finite marginals
- This enables the proof that **exchangeable ⟺ fully exchangeable**

#### Permutation Extension (`Contractability.lean`)
- **Key lemma:** `exists_perm_extending_strictMono`
- Any strictly increasing function `k : Fin m → ℕ` extends to a permutation
- Uses `Equiv.extendSubtype` to build the extension
- This proves **exchangeable → contractable** (easy direction)

## Development Workflow

### Working with Proofs

1. **Development placeholders:** During development, `axiom` or `sorry` are acceptable as temporary scaffolding
2. **Before committing:** All proofs must be complete - no `sorry` allowed
3. **Check axiom usage:** Use `#print axioms theorem_name` to verify only standard mathlib axioms are used

### Proof Style Guidelines

From `StyleGuidelines/PROJECT_STYLE.md`:

- **Avoid historical references** in comments - describe what code *is*, not what it *was*
- **Avoid "axiom-free" claims** - this is the default state for complete code
- **Keep public API clean** - mark internal helpers as `private`
- **Use section headers** (`/-! ### Section Title`) to organize files
- **Document major theorems** with comprehensive docstrings

### Naming Conventions

Follow mathlib conventions (see `StyleGuidelines/MATHLIB_STYLE_CHECKLIST.md`):
- Theorems: descriptive names like `measure_eq_of_fin_marginals_eq`
- Implications: `foo_of_bar` means bar → foo
- Equivalences: `foo_iff_bar`
- Definitional lemmas: use `@[simp]` when appropriate

### Dependencies

**External:**
- `mathlib` (from GitHub) - Lean 4 mathematics library
- `Canonical` (from GitHub) - Development aid for proof search
  - Currently used in `ViaL2.lean`
  - Should be removed once proofs are finalized

**Lean version:** Specified in `lean-toolchain` (currently v4.24.0-rc1)

## Common Patterns

### Working with Measures

```lean
-- Pushforward measures via measurable functions
Measure.map f μ

-- Finite marginals
Measure.map (prefixProj n) μ  -- Project to first n coordinates

-- Probability measure assumptions
[IsProbabilityMeasure μ]
```

### Working with Sequences

```lean
-- Exchangeability: finite permutations preserve distribution
def Exchangeable (μ : Measure Ω) (X : ℕ → Ω → α) : Prop

-- Contractability: strictly increasing subsequences have same distribution
def Contractable (μ : Measure Ω) (X : ℕ → Ω → α) : Prop

-- Conditional i.i.d.: conditionally independent given tail σ-algebra
def ConditionallyIID (μ : Measure Ω) (X : ℕ → Ω → α) : Prop
```

### Cylinder Sets

```lean
-- Prefix cylinder: sequences with first n coordinates in S
prefixCylinder S : Set (ℕ → α)

-- Measurability
prefixCylinder_measurable_in_prefixCylinders

-- Intersection structure
prefixCylinder_inter : prefixCylinder S ∩ prefixCylinder T = prefixCylinder (...)
```

## Understanding Current State

### Active Development Areas

From `PROGRESS_SUMMARY.md` and `REFACTORING_NOTES.md`:

1. **ViaMartingale.lean:** Recently had surgical patch to remove axiom dependencies
   - Infrastructure added for indicator algebra and cylinder sets
   - ~1 sorry remaining for conditional independence

2. **ViaKoopman.lean:** Step B dyadic approximation ~95% complete
   - 4 technical sorries for linarith limitations and convergence
   - Potential refactoring to use `SimpleFunc.approxOn` from mathlib

3. **CondExp.lean:** Pre-existing compilation errors being addressed
   - Not from recent work
   - Blocks full project compilation

### File Status (22 total Lean files)

- **Complete and building:** Core.lean, Contractability.lean, ConditionallyIID.lean
- **Nearly complete:** ViaL2.lean (has Canonical dependency), ViaKoopman.lean (4 sorries)
- **In progress:** ViaMartingale.lean (1 sorry), CondExp.lean (has errors)

## Important Implementation Details

### Measurability Automation

Files use `measurability` attribute to enable tactic automation:
```lean
attribute [measurability] measurable_prefixProj takePrefix_measurable measurable_reindex
```

### Type Class Instances

Extensive use of type class inference for:
- `MeasurableSpace` instances on product types
- `IsProbabilityMeasure` and `IsFiniteMeasure`
- `Measurable` predicates on functions

### Classical Logic

Most files use `classical` mode:
```lean
noncomputable section
-- ... proofs using classical logic
```

This is standard for measure theory in Lean.

### Linter Configuration

Some sections disable false-positive linter warnings:
```lean
set_option linter.unusedSectionVars false
```
This is necessary when the linter doesn't track transitive dependencies through `Pi.measurableSpace`.

## Mathematical Background

### Main Theorem (Kallenberg Theorem 1.1)

For infinite sequences on Borel spaces, the following are equivalent:
1. **Contractable:** All strictly increasing subsequences of equal length have the same distribution
2. **Exchangeable:** Distribution invariant under finite permutations
3. **Conditionally i.i.d.:** Coordinates are independent given the tail σ-algebra

### Proof Strategy

- **(1) ⇒ (2):** Direct from permutation extension (`Contractability.lean`)
- **(2) ⇒ (3):** This is the deep direction - three independent proofs in `DeFinetti/`
- **(3) ⇒ (1):** Direct from definition (`ConditionallyIID.lean`)

### Key Technical Result

`exchangeable_iff_fullyExchangeable` (`Core.lean`):
- Proves finite exchangeability ⟺ infinite exchangeability
- Uses π-system uniqueness theorem
- Critical for connecting finite and infinite perspectives

## References

Primary mathematical source:
- Kallenberg (2005), *Probabilistic Symmetries and Invariance Principles*, Chapter 1, Theorem 1.1

See `README.md` for complete bibliography and related work.
