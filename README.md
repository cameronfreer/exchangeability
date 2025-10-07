# Exchangeability

[![Lean 4](https://img.shields.io/badge/Lean-4-blue)](https://leanprover.github.io/lean4/doc/)

Formalization of **exchangeability** and **de Finetti's theorem** in Lean 4.

## Overview

This project formalizes de Finetti's theorem, which states that an infinite exchangeable sequence is conditionally i.i.d. (independent and identically distributed given the tail σ-algebra).

We implement **all three proofs** from Kallenberg (2005):

1. **L² Approach** (Elementary) - Uses L² contractability bounds
   - ✅ Lightest dependencies
   - Default proof in the public API
   - File: [`Exchangeability/DeFinetti/ViaL2.lean`](Exchangeability/DeFinetti/ViaL2.lean)

2. **Koopman Approach** (Ergodic Theory) - Via Mean Ergodic Theorem
   - Deep connection to dynamical systems
   - File: [`Exchangeability/DeFinetti/ViaKoopman.lean`](Exchangeability/DeFinetti/ViaKoopman.lean)

3. **Martingale Approach** (Aldous) - Via reverse martingale convergence
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

### de Finetti's Theorem
- `deFinetti` - Exchangeable sequences are conditionally i.i.d. (three independent proofs)
- `contractable_of_exchangeable` - Exchangeability implies contractability
- `exchangeable_of_conditionallyIID` - Conditionally i.i.d. implies exchangeability

## References

- Olav Kallenberg (2005), *Probabilistic Symmetries and Invariance Principles*, Springer
- Bruno De Finetti (1937), *La prévision : ses lois logiques, ses sources subjectives*
- David Aldous (1983), *Exchangeability and related topics*

## Contributing

This is an active research project. See [`WorkPlans/`](WorkPlans/) for current tasks and progress.

## License

[Apache 2.0](LICENSE)

## Acknowledgments

Built with [Lean 4](https://leanprover.github.io/) and [Mathlib](https://github.com/leanprover-community/mathlib4).
