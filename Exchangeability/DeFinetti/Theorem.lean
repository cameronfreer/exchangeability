/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Exchangeability.DeFinetti.ViaL2
import Exchangeability.DeFinetti.CommonEnding

/-!
# de Finetti's Theorem - Public API

This file provides the **standard entry point** for de Finetti's theorem,
with a single stable theorem name that is independent of the proof method.

## Main theorem

* `deFinetti`: An exchangeable sequence on a Borel space is conditionally i.i.d.

This defaults to the **L² proof** (lightest dependencies). The theorem name remains
stable regardless of which proof is used as the default.

## Alternative proofs

Three complete proofs are available in separate files:

1. **`ViaL2.lean`** - Elementary proof using L² contractability bounds
   (Kallenberg's "second proof", Lemma 1.2)
   - ✅ **Lightest dependencies** - only basic L² space theory
   - ✅ Elementary and direct
   - ✅ **Default proof**

2. **`ViaKoopman.lean`** - Proof via Koopman operator and Mean Ergodic Theorem
   (Kallenberg's "first proof")
   - ❌ Heavy dependencies - requires ergodic theory
   - ✅ Deep connection to dynamical systems

3. **`ViaMartingale.lean`** - Proof via reverse martingale convergence
   (Aldous' approach, Kallenberg's "third proof")
   - ⚖️ Medium dependencies - requires martingale theory
   - ✅ Elegant probabilistic argument

To use a specific proof, import the corresponding file directly:
```lean
import Exchangeability.DeFinetti.ViaL2        -- or
import Exchangeability.DeFinetti.ViaKoopman   -- or
import Exchangeability.DeFinetti.ViaMartingale
```

## References

* Olav Kallenberg (2005), *Probabilistic Symmetries and Invariance Principles*,
  Chapter 1, Theorem 1.1 (pages 26-27)
* Bruno De Finetti (1937), *La prévision : ses lois logiques, ses sources subjectives*
* David Aldous (1983), *Exchangeability and related topics*
-/

namespace Exchangeability.Probability

-- Re-export the L² proof under the standard name
-- Users who import this module get the stable `deFinetti` name
-- without needing to know which proof is used

end Exchangeability.Probability
