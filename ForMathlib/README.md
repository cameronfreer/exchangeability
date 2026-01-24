# ForMathlib: Upstream Contributions to Mathlib

This directory contains general-purpose lemmas extracted from the exchangeability project,
organized for potential contribution to [mathlib4](https://github.com/leanprover-community/mathlib4).

## PR Tracking

| Candidate | Source | Target | Status | PR # |
|-----------|--------|--------|--------|------|
| `exists_perm_extending_strictMono` | `Contractability.lean:313-370` | `Combinatorics/PermutationExtension.lean` | Ready | - |
| `iInf_comap_eq_comap_iInf_of_surjective` | `Tail/TailSigma.lean:98-220` | `MeasureTheory/MeasurableSpace/ComapInfima.lean` | Ready | - |
| π-system/cylinder infrastructure | `Core.lean:150-346` | `MeasureTheory/Constructions/Pi/Cylinders.lean` | Ready | - |
| `sigmaFinite_trim` | `ForMathlib/.../TrimInstances.lean` | `MeasureTheory/Measure/TrimInstances.lean` | Ready | - |
| Conditional expectation helpers | `Probability/CondExp.lean` | `MeasureTheory/Function/ConditionalExpectation/Lipschitz.lean` | Ready | - |
| Tail σ-algebra infrastructure | `Tail/TailSigma.lean`, `RevFiltration.lean` | `Probability/Process/TailSigmaAlgebra.lean` | Planned | - |
| Finite marginals uniqueness | `Core.lean:336` | `MeasureTheory/Measure/FinMarginals.lean` | Planned | - |

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
│   │       └── Cylinders.lean          # π-system infrastructure
│   ├── Measure/
│   │   ├── TrimInstances.lean          # sigmaFinite_trim (existing)
│   │   └── FinMarginals.lean           # measure_eq_of_fin_marginals_eq
│   └── Function/
│       └── ConditionalExpectation/
│           └── Lipschitz.lean          # condExp_L1_lipschitz
├── Probability/
│   ├── Independence/
│   │   └── Conditional/
│   │       └── Indicator.lean          # condIndep_of_indicator_condexp_eq
│   └── Process/
│       └── TailSigmaAlgebra.lean       # tail filtration infrastructure
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
