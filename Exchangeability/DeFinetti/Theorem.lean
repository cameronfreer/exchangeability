/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Exchangeability.DeFinetti.TheoremViaL2

/-!
# de Finetti's Theorem - Default Export

This file re-exports the **L² proof** of de Finetti's theorem as the default.

The L² approach (Kallenberg's "second proof") is chosen as the default because
it has the **lightest dependencies** - it requires only elementary L² bounds
and Lp completeness, avoiding the heavy machinery of ergodic theory or
martingale theory.

## Available proofs

Three complete proofs of Kallenberg Theorem 1.1 are (or will be) available:

1. **L² proof** (default, re-exported here):
   - `import Exchangeability.DeFinetti.TheoremViaL2`
   - Uses elementary L² contractability bounds (Lemma 1.2)
   - **Lightest dependencies**: Only Lp spaces and basic measure theory
   - Reference: Kallenberg (2005), page 27, "Second proof"

2. **Koopman/Ergodic proof** (future):
   - `import Exchangeability.DeFinetti.TheoremViaKoopman`
   - Uses Mean Ergodic Theorem via Koopman operator
   - Heavy dependencies: ergodic theory
   - Reference: Kallenberg (2005), page 26, "First proof"

3. **Martingale proof** ✅ **COMPLETE**:
   - `import Exchangeability.DeFinetti.TheoremViaMartingale`
   - Uses reverse martingale convergence + tail σ-algebra factorization
   - Medium dependencies: conditional expectation, directing measures (axiomatized)
   - Reference: Kallenberg (2005), page 27, "Third proof" + Aldous (1983)

## Usage

For most users:
```lean
import Exchangeability.DeFinetti.Theorem  -- Gets the L² proof by default
```

For a specific proof approach:
```lean
import Exchangeability.DeFinetti.TheoremViaL2         -- Explicit L² proof
import Exchangeability.DeFinetti.TheoremViaKoopman    -- Ergodic theory proof
import Exchangeability.DeFinetti.TheoremViaMartingale -- Martingale proof
```

## Main theorems (re-exported)

All theorems from `TheoremViaL2` are available in this namespace:
- `deFinetti_RyllNardzewski_equivalence`: The full three-way equivalence
- `deFinetti`: Standard statement (Exchangeable ⇒ ConditionallyIID)
- `conditionallyIID_of_contractable`: Direct from contractability

## References

* Kallenberg (2005), *Probabilistic Symmetries and Invariance Principles*,
  Theorem 1.1 (pages 26-27)
-/

-- Re-export all theorems from the L² proof
-- These are available directly from Exchangeability.DeFinetti namespace
-- imported via TheoremViaL2
