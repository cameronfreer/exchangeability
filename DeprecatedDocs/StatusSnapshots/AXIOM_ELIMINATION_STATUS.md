# Axiom Elimination Status

## Overview
Tracking progress on converting axioms to proofs and eliminating sorries across the de Finetti proof implementations.

## ViaMartingale.lean Status

### Recent Progress
- ✅ **filtration_antitone** (line 1525): Converted from axiom to lemma (commit 40bc9ab)
  - One-line proof using existing `futureFiltration_antitone`
  - 10 axioms → 9 axioms

### Remaining Axioms (9 total)

| Line | Name | Status | Blocker |
|------|------|--------|---------|
| 487 | `condexp_convergence` | Axiom | Requires conditional expectation convergence theory |
| 1530 | `M` | Axiom | Typeclass metavariable issues in conditional expectation |
| 1557 | `coordinate_future_condIndep` | Stub (`: True`) | Typeclass resolution blockers |
| 1593 | `condExp_product_of_condIndep` | Stub (`: True`) | Typeclass resolution blockers |
| 1609 | `condexp_indicator_inter_of_condIndep` | Stub (`: True`) | Typeclass resolution blockers |
| 1633 | `finite_level_factorization` | Stub (`: True`) | Typeclass resolution blockers |
| 1807 | `tail_factorization_from_future` | Axiom | Depends on above |
| 1890 | `directingMeasure_of_contractable` | Axiom | Measure construction from conditional expectations |
| 1934 | `finite_product_formula` | Axiom | Product formula for finite cylinders |

### Remaining Sorries (5 total)

| Line | Lemma | Status | Notes |
|------|-------|--------|-------|
| 506 | `extreme_members_equal_on_tail` | Sorry | Blocked by `condexp_convergence` axiom |
| 587 | `sigmaFinite_trim_tailSigma` | Sorry | Mathlib doesn't provide automatic `SigmaFinite (μ.trim h)` instance |
| 829 | `firstRSigma_le_futureFiltration` | Sorry | Statement needs design correction per comments |
| 1715 | (conditional independence) | Sorry | Needs full CondIndep theory development |
| 1874 | `deFinetti_viaMartingale` | Sorry | Main theorem - blocked by all above |

## CondExp.lean Status

### Completed Proofs
- ✅ **condExp_indicator_mul_indicator_of_condIndep** (line 279): Fully proven
  - One-line proof using mathlib's `ProbabilityTheory.condIndep_iff`
  - Production-ready

- ✅ **condIndep_of_indicator_condexp_eq** (line 180): Fully proven
  - ~80 lines proving Doob's characterization
  - Uses tower property and pullout lemmas
  - Production-ready

### Remaining Sorry (1 total)

| Line | Lemma | Status | Blocker |
|------|-------|--------|---------|
| 134 | `condexp_indicator_eq_of_agree_on_future_rectangles` | Sorry | Lean 4 typeclass inference issues with sub-σ-algebras |

**Note:** Mathematical proof is complete (was in comments), but encounters metavariable issues with multiple `MeasurableSpace` instances on same type.

## Other Files

### ViaL2.lean
- **35 sorries** (needs detailed analysis)
- Default proof used by public API
- Has `Canonical` dependency (should be removed eventually)

### ViaKoopman.lean
- **12 sorries** (needs detailed analysis)
- Uses Mean Ergodic Theorem
- Heavy dependencies on ergodic theory

### TheoremViaL2.lean, TheoremViaMartingale.lean, TheoremViaKoopman.lean
- Main theorem statement files
- May contain axioms/sorries (needs check)

## Key Technical Challenges

### Typeclass Resolution Issues
Many axioms are stubs (`: True`) because full type signatures encounter Lean 4 typeclass resolution problems:
- Multiple `MeasurableSpace` instances
- `MeasurableSpace.comap` and sub-σ-algebras
- Conditional expectation notation `μ[f | m]` with explicit `m : MeasurableSpace Ω`

### Missing Mathlib Instances
- No automatic `SigmaFinite (μ.trim h)` for general sigma-finite measures
- May need manual construction or mathlib contribution

### Conditional Independence Infrastructure
Several axioms require full development of:
- Conditional independence properties
- Product factorization for conditional expectations
- Approximation theory for simple functions
- L¹ convergence for conditional expectations

## Recommendations

### Immediate Next Steps
1. ✅ **Document current status** (this file)
2. Analyze ViaL2.lean sorries for easy wins
3. Analyze ViaKoopman.lean sorries for easy wins
4. Look for other structural improvements (file organization, documentation)

### Medium-Term Goals
1. Develop conditional independence infrastructure
2. Resolve typeclass issues in CondExp.lean
3. Work on ViaL2 as default proof (lightest dependencies)

### Long-Term Strategy
1. Complete one full proof (likely ViaL2) to main theorem
2. Use insights to complete other proofs
3. Remove all temporary scaffolding (`Canonical` dependency, etc.)
4. Contribute missing instances to mathlib if needed

## Build Status
✅ All files compile successfully (as of commit 40bc9ab)

## Commit History
- `40bc9ab`: Convert `filtration_antitone` from axiom to lemma
- `667c03b`: Complete Track B.1 - Full π-λ theorem proof for measure extension
- Earlier: Track B.2 completion, conditional independence proofs

---
*Last updated: 2025-10-12*
