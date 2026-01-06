/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
-- Re-export all infrastructure components
import Exchangeability.DeFinetti.ViaKoopman.InfraCore
import Exchangeability.DeFinetti.ViaKoopman.InfraLagConstancy
import Exchangeability.DeFinetti.ViaKoopman.InfraGeneralized

/-! # Infrastructure for ViaKoopman Proof

This file re-exports infrastructure from split modules:
- `InfraCore`: Two-sided extension, instance-locking shims, CE pullback
- `InfraLagConstancy`: Lag-constancy from exchangeability
- `InfraGeneralized`: Generalized lag-constancy, CE helpers

Import this file to get all infrastructure in one import.

**Split into**: InfraCore.lean, InfraLagConstancy.lean, InfraGeneralized.lean
-/
