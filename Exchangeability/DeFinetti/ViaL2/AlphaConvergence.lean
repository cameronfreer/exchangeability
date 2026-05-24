/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Exchangeability.DeFinetti.ViaL2.AlphaConvergence.AlphaIicEq
import Exchangeability.DeFinetti.ViaL2.AlphaConvergence.EndpointAtBot
import Exchangeability.DeFinetti.ViaL2.AlphaConvergence.EndpointAtTop

/-!
# Alpha Convergence: Endpoint Limits for `alphaIicCE`

Umbrella module re-exporting the endpoint-limit results for `alphaIicCE`.
Contents are split across topic-named subfiles:

* `AlphaConvergence/AlphaIicEq.lean` — identification
  (`alphaIic_ae_eq_alphaIicCE`).
* `AlphaConvergence/EndpointAtBot.lean` — limit at `-∞`
  (`alphaIicCE_ae_tendsto_zero_atBot`, plus a private L¹ stepping stone).
* `AlphaConvergence/EndpointAtTop.lean` — limit at `+∞`
  (`alphaIicCE_ae_tendsto_one_atTop`, plus a private L¹ stepping stone).
* `AlphaConvergence/EndpointCommon.lean` — the shared measure-theoretic helper
  `ae_tendsto_const_of_ae_convergent_of_L1_const` consumed by both endpoint files
  (identifies a pointwise a.e. limit with the L¹-limit constant).

Downstream consumers (`DirectingMeasureIic`, `DirectingMeasureCore`) can
import this umbrella module unchanged.

## References

* Kallenberg (2005), *Probabilistic Symmetries and Invariance Principles*,
  Chapter 1, "Second proof of Theorem 1.1"
-/
