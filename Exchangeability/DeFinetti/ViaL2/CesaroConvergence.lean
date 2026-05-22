/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Exchangeability.DeFinetti.ViaL2.CesaroConvergence.KallenbergBound
import Exchangeability.DeFinetti.ViaL2.CesaroConvergence.Cauchy
import Exchangeability.DeFinetti.ViaL2.CesaroConvergence.L2
import Exchangeability.DeFinetti.ViaL2.CesaroConvergence.L1

/-!
# Cesàro Convergence via L² Bounds — Re-export Shim

This file is the umbrella for Kallenberg's L² approach to Cesàro convergence of
block averages of contractable sequences. Following the split for maintainability,
the contents now live in four sub-files:

* `CesaroConvergence/KallenbergBound.lean` — `kallenberg_L2_bound` (Kallenberg
  Lemma 1.2; retained for documentation but unused by the active proof)
* `CesaroConvergence/Cauchy.lean` — `blockAvg_cauchy_in_L2`, `blockAvgFrozen`
  (block averages are Cauchy in L²)
* `CesaroConvergence/L2.lean` — `cesaro_to_condexp_L2`,
  `blockAvg_measurable_tailFamily` (L² convergence to the tail conditional
  expectation)
* `CesaroConvergence/L1.lean` — `cesaro_to_condexp_L1` (L¹ form, consumed by
  `AlphaConvergence.lean`)

Existing call sites continue to work via this umbrella import.

## References

* Kallenberg (2005), *Probabilistic Symmetries and Invariance Principles*,
  Chapter 1, Lemma 1.2 and "Second proof"
-/
