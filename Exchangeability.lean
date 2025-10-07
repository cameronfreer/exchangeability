-- Core definitions: exchangeability, π-systems, finite marginals
import Exchangeability.Core

-- Probability infrastructure
import Exchangeability.Contractability
import Exchangeability.ConditionallyIID
import Exchangeability.Probability.InfiniteProduct
import Exchangeability.Probability.CondExp

-- de Finetti theorem (default proof via L²)
import Exchangeability.DeFinetti.Theorem

/-!
# Exchangeability

Public API for the exchangeability library and de Finetti's theorem.

This is the **umbrella module** - import it to get access to all main results.

## Main results

* **Core exchangeability theory** (`Exchangeability.Core`):
  - `exchangeable_iff_fullyExchangeable`: Finite and infinite exchangeability are equivalent
  - `measure_eq_of_fin_marginals_eq`: Measures determined by finite marginals
  - π-system machinery for infinite products

* **de Finetti's theorem** (`Exchangeability.DeFinetti.Theorem`):
  - `deFinetti`: Exchangeable sequences are conditionally i.i.d.
  - Three proof approaches available (L², Koopman, Martingale)

* **Probability infrastructure**:
  - `Contractable`: Convergence of empirical distributions
  - `ConditionallyIID`: Conditionally independent and identically distributed
  - Infinite product measures and kernels

## Usage

```lean
import Exchangeability

-- All main theorems are now available
example {Ω α : Type*} [MeasurableSpace Ω] [TopologicalSpace α]
    [MeasurableSpace α] [BorelSpace α]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → α) (hX_meas : ∀ i, Measurable (X i))
    (hX_exch : Exchangeable μ X) :
    ConditionallyIID μ X :=
  deFinetti μ X hX_meas hX_exch
```

## Alternative proofs

To use a specific proof approach, import the corresponding module directly:
- `import Exchangeability.DeFinetti.ViaL2` - Elementary L² contractability
- `import Exchangeability.DeFinetti.ViaKoopman` - Mean Ergodic Theorem
- `import Exchangeability.DeFinetti.ViaMartingale` - Reverse martingale convergence

## References

* Olav Kallenberg (2005), *Probabilistic Symmetries and Invariance Principles*
* Bruno De Finetti (1937), *La prévision : ses lois logiques, ses sources subjectives*
* David Aldous (1983), *Exchangeability and related topics*
-/

-- Note: Heavy-dependency modules are NOT imported by default:
-- - Exchangeability.Ergodic.KoopmanMeanErgodic (ergodic theory)
-- - Exchangeability.DeFinetti.ViaKoopman (requires ergodic theory)
-- Import these explicitly if needed.
