/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Exchangeability.DeFinetti.ViaL2.BlockAverages
import Exchangeability.DeFinetti.ViaL2.CesaroConvergence
import Exchangeability.DeFinetti.ViaL2.MainConvergence
import Exchangeability.DeFinetti.ViaL2.DirectingMeasure
import Exchangeability.DeFinetti.ViaL2.MoreL2Helpers

/-!
# de Finetti's Theorem via L² Contractability

This is the main file for the L² approach to de Finetti's theorem. The proof
has been split across multiple files for maintainability:

* `ViaL2/BlockAverages.lean` - Block average definitions and early infrastructure  
  (~1600 lines)
* `ViaL2/CesaroConvergence.lean` - Cesàro convergence via L² bounds  
  (~2800 lines)
* `ViaL2/MainConvergence.lean` - Main convergence theorems and directing measure  
  (~2800 lines)
* `ViaL2/MoreL2Helpers.lean` - Technical lemmas and temporary axioms  
  (~500 lines)

This file re-exports all the main results for use by `TheoremViaL2.lean`.

## Main result

The infrastructure theorem `directing_measure_satisfies_requirements` (from
`MainConvergence.lean`) packages the L² approach, showing that for a contractable
sequence we can construct a directing measure ν that satisfies all requirements.

## References

* Kallenberg (2005), *Probabilistic Symmetries and Invariance Principles*,
  Chapter 1, "Second proof of Theorem 1.1"
-/
