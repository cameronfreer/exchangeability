# ForMathlib: Upstream Contributions to Mathlib

This directory contains general-purpose lemmas extracted from the exchangeability project,
organized for potential contribution to [mathlib4](https://github.com/leanprover-community/mathlib4).

## PR Tracking

| Candidate | Target | Status | Axioms | PR # |
|-----------|--------|--------|--------|------|
| `exists_perm_extending_strictMono` | `Combinatorics/PermutationExtension.lean` | ✅ Extracted | Standard | - |
| `iInf_comap_eq_comap_iInf_of_surjective` | `MeasureTheory/MeasurableSpace/ComapInfima.lean` | ✅ Extracted | Standard | - |
| π-system/cylinder infrastructure | `MeasureTheory/Constructions/Pi/Cylinders.lean` | ✅ Extracted | Standard | - |
| `sigmaFinite_trim` | `MeasureTheory/Measure/TrimInstances.lean` | ✅ Existing | Standard | - |
| `condExp_L1_lipschitz` | `MeasureTheory/Function/ConditionalExpectation/Lipschitz.lean` | ✅ Extracted | Standard | - |

All extracted files:
- Import only mathlib (no `Exchangeability.*` dependencies)
- Use only standard axioms: `propext`, `Classical.choice`, `Quot.sound`
- Follow mathlib style (<100 char lines)
- Include module docstrings with mathematical context

## PR Sequencing Strategy

```
Level 0 (independent - can be submitted in parallel):
  PR1: PermutationExtension - pure combinatorics, no measure theory
  PR2: ComapInfima - σ-algebra infrastructure
  PR3: TrimInstances - already essentially in mathlib

Level 1 (after Level 0):
  PR4: Cylinders - uses ComapInfima patterns, π-system infrastructure
  PR5: CondExp helpers - missing API additions

Level 2 (after Level 1):
  PR6: TailSigmaAlgebra - uses ComapInfima, Cylinders
  PR7: FinMarginals - uses Cylinders
```

## Directory Structure

```
ForMathlib/
├── Combinatorics/
│   └── PermutationExtension.lean       # exists_perm_extending_strictMono
├── MeasureTheory/
│   ├── MeasurableSpace/
│   │   └── ComapInfima.lean            # iInf_comap_eq_comap_iInf_of_surjective
│   ├── Constructions/
│   │   └── Pi/
│   │       └── Cylinders.lean          # π-system, measure_eq_of_fin_marginals_eq
│   ├── Measure/
│   │   └── TrimInstances.lean          # sigmaFinite_trim (existing)
│   └── Function/
│       └── ConditionalExpectation/
│           └── Lipschitz.lean          # condExp_L1_lipschitz
└── README.md                           # This file
```

## Contribution Guidelines

Each ForMathlib file should:
1. Import **only** from mathlib (no `Exchangeability.*` imports)
2. Include a module docstring with:
   - Mathematical context and references
   - Suggested mathlib location
   - Known downstream applications
3. Follow mathlib style conventions
4. Pass `#print axioms` with only standard axioms (propext, quot.sound, choice)

## References

- Kallenberg (2005), *Probabilistic Symmetries and Invariance Principles*, Theorem 1.1
- Mathlib documentation: https://leanprover-community.github.io/mathlib4_docs/
