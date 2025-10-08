/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Exchangeability.DeFinetti.ViaL2
import Exchangeability.DeFinetti.CommonEnding

/-!
# de Finetti's Theorem - Completed Proof

This file **completes** the de Finetti proof by combining:
- `ViaL2`: Proves convergence A_n_m → α for each bounded f
- `CommonEnding`: Builds the kernel K from the map f ↦ α

## Proof flow

1. `ViaL2.weighted_sums_converge_L1` gives: ∃α, ∀n. A_n_m → α in L¹
2. Show α is tail-measurable (contractability argument)
3. `CommonEnding` machinery:
   - Build kernel K : Ω → Measure α from f ↦ α_f
   - Monotone class theorem extends to all measurables
   - Prove conditional i.i.d. property

## Alternative proofs

Each Via* file should eventually complete its own proof this way:
- `ViaKoopman.lean` + `CommonEnding` → full proof via ergodic theory
- `ViaMartingale.lean` + `CommonEnding` → full proof via martingales

## Current status

TODO: Once CommonEnding compiles, implement the completion here.
For now this file documents the intended architecture.

## References

* Kallenberg (2005), Theorem 1.1 (pages 26-27)
-/

namespace Exchangeability.DeFinetti

open MeasureTheory ProbabilityTheory

-- TODO: Complete the proof
-- theorem deFinetti_viaL2 := ViaL2.weighted_sums_converge_L1 + CommonEnding machinery

end Exchangeability.DeFinetti
