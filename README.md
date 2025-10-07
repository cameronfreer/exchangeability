# Exchangeability

[![Lean 4](https://img.shields.io/badge/Lean-4-blue)](https://leanprover.github.io/lean4/doc/)

Formalization of **exchangeability** and **de Finetti's theorem** in Lean 4.

## Overview

This project formalizes the **de Finetti-Ryll-Nardzewski theorem** (Kallenberg's Theorem 1.1), which establishes a three-way equivalence for infinite sequences on Borel spaces:

**(i) Contractable** ⟺ **(ii) Exchangeable** ⟺ **(iii) Conditionally i.i.d.**

We implement **all three proofs** from Kallenberg (2005) of the key implication **contractable → conditionally i.i.d.**:

1. **L² Approach** (Kallenberg's "second proof") - Elementary L² contractability bounds
   - ✅ **Lightest dependencies** (no ergodic theory required)
   - ✅ Default proof in the public API
   - File: [`Exchangeability/DeFinetti/ViaL2.lean`](Exchangeability/DeFinetti/ViaL2.lean)

2. **Koopman Approach** (Kallenberg's "first proof") - Mean Ergodic Theorem
   - Deep connection to dynamical systems and ergodic theory
   - File: [`Exchangeability/DeFinetti/ViaKoopman.lean`](Exchangeability/DeFinetti/ViaKoopman.lean)

3. **Martingale Approach** (Kallenberg's "third proof", after Aldous) - Reverse martingales
   - Elegant probabilistic argument
   - File: [`Exchangeability/DeFinetti/ViaMartingale.lean`](Exchangeability/DeFinetti/ViaMartingale.lean)

## Quick Start

### Prerequisites

- [Lean 4](https://leanprover.github.io/lean4/doc/setup.html)
- [elan](https://github.com/leanprover/elan) (Lean version manager)

### Installation

```bash
# Install elan
curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh

# Clone and build
git clone https://github.com/cameronfreer/exchangeability.git
cd exchangeability
lake build
```

### Using the Library

```lean
import Exchangeability

-- de Finetti's theorem (uses L² proof by default)
example {Ω α : Type*} [MeasurableSpace Ω] [TopologicalSpace α]
    [MeasurableSpace α] [BorelSpace α]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → α) (hX_meas : ∀ i, Measurable (X i))
    (hX_exch : Exchangeable μ X) :
    ConditionallyIID μ X :=
  deFinetti μ X hX_meas hX_exch
```

## Project Structure

```
Exchangeability/
├── Core.lean                    # Exchangeability definitions, π-systems
├── Contractability.lean         # Contractability ↔ exchangeability
├── ConditionallyIID.lean        # Conditionally i.i.d. sequences
├── Probability/                 # Probability infrastructure
│   ├── InfiniteProduct.lean
│   └── CondExp.lean
├── DeFinetti/                   # Three proofs of de Finetti
│   ├── Theorem.lean            # Public API (canonical theorem)
│   ├── ViaL2.lean              # L² proof (default)
│   ├── ViaKoopman.lean         # Ergodic proof
│   ├── ViaMartingale.lean      # Martingale proof
│   ├── L2Approach.lean         # L² contractability lemmas
│   ├── CommonEnding.lean       # Shared final step
│   ├── InvariantSigma.lean     # Shift-invariant σ-algebras
│   └── ProjectionLemmas.lean   # Orthogonal projection tools
└── Ergodic/
    └── KoopmanMeanErgodic.lean # Mean Ergodic Theorem
```

## Documentation

- **Blueprint**: [`blueprint/`](blueprint/) - Mathematical blueprint for the formalization
- **Work Plans**: [`WorkPlans/`](WorkPlans/) - Development notes and progress reports

## Main Results

### Core Theory
- `exchangeable_iff_fullyExchangeable` - Finite and infinite exchangeability are equivalent
- `measure_eq_of_fin_marginals_eq` - Measures determined by finite marginals

### de Finetti's Theorem (Three-way Equivalence)
- `deFinetti` - Exchangeable sequences are conditionally i.i.d.
- `conditionallyIID_of_contractable` - **Contractable implies conditionally i.i.d.** (three independent proofs via L², Koopman, and martingale approaches)
- `contractable_of_exchangeable` - Exchangeability implies contractability
- `exchangeable_of_conditionallyIID` - Conditionally i.i.d. implies exchangeability

## References

### Primary Sources

- **Kallenberg, Olav** (2005). *Probabilistic Symmetries and Invariance Principles*. Probability and Its Applications. Springer-Verlag, New York. [https://doi.org/10.1007/0-387-28861-9](https://doi.org/10.1007/0-387-28861-9) [Chapter 1, Theorem 1.1]

- **De Finetti, Bruno** (1937). "La prévision : ses lois logiques, ses sources subjectives." *Annales de l'Institut Henri Poincaré* 7 (1): 1–68. [[English translation: "Foresight: Its Logical Laws, Its Subjective Sources" (1964) in *Studies in Subjective Probability*, H. E. Kyburg and H. E. Smokler, eds.]](https://www.numdam.org/item/AIHP_1937__7_1_1_0/)

- **Aldous, David J.** (1985). "Exchangeability and related topics." In *École d'Été de Probabilités de Saint-Flour XIII—1983*, Lecture Notes in Mathematics 1117, pp. 1–198. Springer-Verlag, Berlin. [https://doi.org/10.1007/BFb0099421](https://doi.org/10.1007/BFb0099421)

### Related Work

- **Hewitt, Edwin and Savage, Leonard J.** (1955). "Symmetric measures on Cartesian products." *Transactions of the American Mathematical Society* 80 (2): 470–501.

- **Diaconis, Persi and Freedman, David** (1980). "Finite exchangeable sequences." *The Annals of Probability* 8 (4): 745–764.

## Contributing

This is an active research project. See [`WorkPlans/`](WorkPlans/) for current tasks and progress.

## License

[Apache 2.0](LICENSE)

## Acknowledgments

This formalization was developed with assistance from:
- **Claude Sonnet 4.5** (Anthropic) - Code generation, refactoring, and proof development
- **GPT-5-Codex** (OpenAI) - Mathematical reasoning and proof strategy

Built with [Lean 4](https://leanprover.github.io/) and [Mathlib](https://github.com/leanprover-community/mathlib4).
