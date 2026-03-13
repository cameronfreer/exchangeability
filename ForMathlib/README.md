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
| Lp/integration helpers | `MeasureTheory/Function/LpHelpers.lean` | ✅ Extracted | Standard | - |
| σ-algebra helpers | `MeasureTheory/MeasurableSpace/SigmaAlgebraHelpers.lean` | ✅ Extracted | Standard | - |
| Product kernel measurability | `Probability/Kernel/ProductMeasurable.lean` | ✅ Extracted | Standard | - |
| `condIndep_of_indicator_condexp_eq` | `Probability/Independence/Conditional.lean` | ✅ Extracted | Standard | - |
| `finset_sum_ae_eq` | `MeasureTheory/Function/AEHelpers.lean` | ✅ Extracted | Standard | - |
| `condexp_indicator_eq_of_pair_law_eq` | `Probability/ConditionalExpectation/Distributional.lean` | ✅ Extracted | Standard | - |

All extracted files:
- Import only mathlib (no `Exchangeability.*` dependencies)
- Use only standard axioms: `propext`, `Classical.choice`, `Quot.sound`
- Follow mathlib style (<100 char lines)
- Include module docstrings with mathematical context

## Directory Structure

```
ForMathlib/
├── Combinatorics/
│   └── PermutationExtension.lean       # exists_perm_extending_strictMono
├── MeasureTheory/
│   ├── MeasurableSpace/
│   │   ├── ComapInfima.lean            # iInf_comap_eq_comap_iInf_of_surjective
│   │   └── SigmaAlgebraHelpers.lean    # aestronglyMeasurable_iInf_antitone
│   ├── Constructions/
│   │   └── Pi/
│   │       └── Cylinders.lean          # π-system, measure_eq_of_fin_marginals_eq
│   ├── Measure/
│   │   └── TrimInstances.lean          # sigmaFinite_trim (existing)
│   └── Function/
│       ├── ConditionalExpectation/
│       │   └── Lipschitz.lean          # condExp_L1_lipschitz
│       ├── AEHelpers.lean              # finset_sum_ae_eq
│       └── LpHelpers.lean              # eLpNorm_two_sq_eq_integral_sq, abs_integral_mul_le_L2
├── Probability/
│   ├── Independence/
│   │   └── Conditional.lean            # condIndep_of_indicator_condexp_eq (Doob)
│   ├── ConditionalExpectation/
│   │   └── Distributional.lean         # condexp_indicator_eq_of_pair_law_eq
│   └── Kernel/
│       └── ProductMeasurable.lean      # measurable_measure_pi, rectangles_isPiSystem
└── README.md                           # This file
```

## PR Sequencing Strategy

```
Level 0 (independent - can be submitted in parallel):
  PR1: PermutationExtension - pure combinatorics, no measure theory
  PR2: ComapInfima - σ-algebra infrastructure
  PR3: TrimInstances - already essentially in mathlib

Level 1 (after Level 0):
  PR4: Cylinders - uses ComapInfima patterns, π-system infrastructure
  PR5: Lipschitz - conditional expectation helpers
  PR6: LpHelpers - Lp norm/integral bridges
  PR7: SigmaAlgebraHelpers - AEStronglyMeasurable for infima
  PR8: AEHelpers - finset_sum_ae_eq utility

Level 2 (after Level 1):
  PR9: ProductMeasurable - uses π-system infrastructure from Cylinders
  PR10: Independence/Conditional - Doob's characterization
  PR11: ConditionalExpectation/Distributional - CE equality from dist equality
```

## Module Summaries

### MeasureTheory/Function/LpHelpers.lean
Bridges ENNReal-valued Lp norms and Real-valued integrals:
- `eLpNorm_two_sq_eq_integral_sq`: L² norm² = integral of square
- `eLpNorm_lt_of_integral_sq_lt`: integral bound → norm bound
- `abs_integral_mul_le_L2`: Cauchy-Schwarz for L² functions
- `L2_tendsto_implies_L1_tendsto_of_bounded`: L² → L¹ convergence
- `setIntegral_le_eLpNorm_mul_measure`: |∫_A g| ≤ ‖g‖₂·√(μ A)

### MeasureTheory/Function/AEHelpers.lean
Utility for combining a.e. equalities:
- `finset_sum_ae_eq`: combine finitely many a.e. equalities into sum equality

### MeasureTheory/MeasurableSpace/SigmaAlgebraHelpers.lean
Support for AEStronglyMeasurable with respect to infima:
- `aestronglyMeasurable_iInf_antitone`: preservation under antitone infima
- `aestronglyMeasurable_sub_of_tendsto_ae`: preservation under a.e. limits

### Probability/Kernel/ProductMeasurable.lean
Measurability of product measure kernels:
- `rectangles_isPiSystem`: measurable rectangles form a π-system
- `rectangles_generate_pi_sigma`: product σ-algebra = generateFrom of rectangles
- `measurable_measure_pi`: ω ↦ ∏ᵢ ν(ω) is measurable

### Probability/Independence/Conditional.lean
Doob's characterization of conditional independence:
- `condIndep_of_indicator_condexp_eq`: projection property ⟹ conditional independence

### Probability/ConditionalExpectation/Distributional.lean
Bridge from distributional equality to conditional expectation equality:
- `condexp_indicator_eq_of_pair_law_eq`: if (Y,Z) and (Y',Z) have same law,
  then E[1_{Y∈B}|σ(Z)] = E[1_{Y'∈B}|σ(Z)] a.e.

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
- Williams (1991), *Probability with Martingales*
- Mathlib documentation: https://leanprover-community.github.io/mathlib4_docs/
