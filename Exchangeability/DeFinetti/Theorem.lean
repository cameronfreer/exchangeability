/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Exchangeability.DeFinetti.TheoremViaMartingale

/-!
# de Finetti's Theorem - Default Export

This file re-exports the **martingale proof** of de Finetti's theorem as the default.

The martingale approach (Kallenberg's "third proof") is chosen as the default because
it is the **first complete proof** in this formalization. While it has medium dependencies
(conditional expectation, reverse martingale convergence), it provides an elegant and
direct probabilistic argument.

## Available proofs

Three proofs of Kallenberg Theorem 1.1 are available:

1. **Martingale proof** ✅ **COMPLETE** (default, re-exported here):
   - `import Exchangeability.DeFinetti.TheoremViaMartingale`
   - Uses reverse martingale convergence + tail σ-algebra factorization
   - Medium dependencies: conditional expectation, reverse martingale convergence
   - Reference: Kallenberg (2005), page 27-28, "Third proof" + Aldous (1983)

2. **L² proof** ✅ **COMPLETE**:
   - `import Exchangeability.DeFinetti.TheoremViaL2`
   - Uses elementary L² contractability bounds (Lemma 1.2)
   - **Lightest dependencies**: Only Lp spaces and basic measure theory
   - Reference: Kallenberg (2005), page 27, "Second proof"

3. **Koopman/Ergodic proof** ✅ **COMPLETE**:
   - `import Exchangeability.DeFinetti.TheoremViaKoopman`
   - Uses Mean Ergodic Theorem via Koopman operator
   - Heavy dependencies: ergodic theory
   - Reference: Kallenberg (2005), page 26, "First proof"

## Usage

For most users:
```lean
import Exchangeability.DeFinetti.Theorem  -- Gets the martingale proof by default
```

For a specific proof approach:
```lean
import Exchangeability.DeFinetti.TheoremViaMartingale -- Martingale proof (complete)
import Exchangeability.DeFinetti.TheoremViaL2         -- L² proof (complete)
import Exchangeability.DeFinetti.TheoremViaKoopman    -- Ergodic theory proof (complete)
```

## Main theorems (re-exported)

All theorems from `TheoremViaMartingale` are available in this namespace:
- `deFinetti_RyllNardzewski_equivalence`: The full three-way equivalence
- `deFinetti`: Standard statement (Exchangeable ⇒ ConditionallyIID)
- `deFinetti_equivalence`: Two-way equivalence (Exchangeable ⇔ ConditionallyIID)
- `conditionallyIID_of_contractable`: Direct from contractability

## References

* Kallenberg (2005), *Probabilistic Symmetries and Invariance Principles*,
  Theorem 1.1 (pages 26-28)
* Aldous (1983), *Exchangeability and related topics*, École d'Été de
  Probabilités de Saint-Flour XIII
-/

-- Re-export all theorems from the martingale proof
-- These are available directly from Exchangeability.DeFinetti namespace
-- imported via TheoremViaMartingale
