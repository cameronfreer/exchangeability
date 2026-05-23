/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Exchangeability.Probability.Martingale.Crossings.Pathwise
import Exchangeability.Probability.Martingale.Crossings.Bounds
import Exchangeability.Probability.Martingale.Crossings.AntitoneLimit

/-!
# Downcrossings and Pathwise Reversal Lemmas — Re-export Shim

This file is the umbrella for the crossing-based reverse-martingale infrastructure.
Following the split for maintainability, the contents now live in three sub-files:

* `Crossings/Pathwise.lean` — `downcrossingsBefore`, `downcrossings`, congruence
  lemmas, `upBefore_le_downBefore_rev_succ`
* `Crossings/Bounds.lean` — `upcrossings_bdd_uniform` (uniform-in-`N` bound on
  upcrossings of the reverse martingale)
* `Crossings/AntitoneLimit.lean` — `condExp_exists_ae_limit_antitone`,
  `ae_limit_is_condexp_iInf`

Existing call sites continue to work via this umbrella import.
-/
