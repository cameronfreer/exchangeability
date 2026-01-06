/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
-- Re-export all Cesàro convergence components
import Exchangeability.DeFinetti.ViaKoopman.CesaroL2ToL1
import Exchangeability.DeFinetti.ViaKoopman.CesaroL1Bounded
import Exchangeability.DeFinetti.ViaKoopman.CesaroPairFactorization

/-! # L¹ Cesàro Convergence via Cylinder Functions

This file re-exports the Cesàro convergence infrastructure from split modules:
- `CesaroL2ToL1`: L² to L¹ bridge lemmas, bounded L¹ convergence helpers
- `CesaroL1Bounded`: L¹ Cesàro convergence (bounded and general integrable cases)
- `CesaroPairFactorization`: Pair factorization via MET + exchangeability

Import this file to get all Cesàro convergence lemmas in one import.

**Split into**: CesaroL2ToL1.lean, CesaroL1Bounded.lean, CesaroPairFactorization.lean
-/
