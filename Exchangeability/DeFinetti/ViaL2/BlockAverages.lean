/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Exchangeability.DeFinetti.ViaL2.BlockAverages.Covariance
import Exchangeability.DeFinetti.ViaL2.BlockAverages.TwoWindows
import Exchangeability.DeFinetti.ViaL2.BlockAverages.LongVsTail
import Exchangeability.Tail.TailSigma

/-!
# BlockAverages — re-export shim + TailSigma compatibility aliases

Following the split for maintainability, the contents now live in three
sub-files:

* `BlockAverages/Covariance.lean` — `contractable_covariance_structure`, the
  uniform mean/variance/correlation package for a contractable L² sequence.
* `BlockAverages/TwoWindows.lean` — `l2_bound_two_windows_uniform`, the L²
  Cauchy bound for two windows of the same length.
* `BlockAverages/LongVsTail.lean` — `get_covariance_constant` and
  `l2_bound_long_vs_tail`, the second L² Cauchy bound (long average vs.
  tail-shifted average).

This umbrella file additionally exposes a small `TailSigma` namespace with
`@[reducible]` aliases for the canonical `Exchangeability.Tail` declarations,
kept for backward compatibility with downstream code in the ViaL2 family.
-/

namespace Exchangeability.DeFinetti.ViaL2

/-!
## Tail σ-algebra for sequences

Now using the canonical definitions from `Exchangeability.Tail.TailSigma`.

For backward compatibility in this file, we create a namespace with re-exports:
- `TailSigma.tailFamily X n` := `Tail.tailFamily X n` (future σ-algebra from index n onward)
- `TailSigma.tailSigma X` := `Tail.tailProcess X` (tail σ-algebra)
-/

namespace TailSigma

-- Re-export the definitions for backward compatibility
/-- Re-export of `Tail.tailFamily` for backward compatibility. -/
@[reducible] def tailFamily := @Exchangeability.Tail.tailFamily
/-- Re-export of `Tail.tailProcess` for backward compatibility. -/
@[reducible] def tailSigma := @Exchangeability.Tail.tailProcess

-- Re-export the lemmas for backward compatibility
@[nolint unusedArguments]
lemma antitone_tailFamily {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    (X : ℕ → Ω → β) : Antitone (tailFamily X) :=
  Exchangeability.Tail.tailFamily_antitone X


lemma tailSigma_le {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    (X : ℕ → Ω → β) (hX_meas : ∀ i, Measurable (X i)) :
    tailSigma X ≤ (inferInstance : MeasurableSpace Ω) :=
  Exchangeability.Tail.tailProcess_le_ambient X hX_meas

end TailSigma

end Exchangeability.DeFinetti.ViaL2
