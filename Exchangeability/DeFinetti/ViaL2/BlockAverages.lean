/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Exchangeability.DeFinetti.ViaL2.BlockAverages.Covariance
import Exchangeability.DeFinetti.ViaL2.BlockAverages.TwoWindows
import Exchangeability.DeFinetti.ViaL2.BlockAverages.LongVsTail

/-!
# BlockAverages — re-export shim

Following the split for maintainability, the contents now live in three
sub-files:

* `BlockAverages/Covariance.lean` — `contractable_covariance_structure`, the
  uniform mean/variance/correlation package for a contractable L² sequence.
* `BlockAverages/TwoWindows.lean` — `l2_bound_two_windows_uniform`, the L²
  Cauchy bound for two windows of the same length.
* `BlockAverages/LongVsTail.lean` — `get_covariance_constant` and
  `l2_bound_long_vs_tail`, the second L² Cauchy bound (long average vs.
  tail-shifted average).

Callers should refer to the canonical tail σ-algebra declarations directly:
`Exchangeability.Tail.tailFamily`, `Exchangeability.Tail.tailProcess`,
`Exchangeability.Tail.tailFamily_antitone`, and
`Exchangeability.Tail.tailProcess_le_ambient`.
-/
