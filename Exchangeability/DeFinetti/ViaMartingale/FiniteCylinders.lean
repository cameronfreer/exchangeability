/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Exchangeability.Contractability
import Exchangeability.DeFinetti.MartingaleHelpers
import Exchangeability.DeFinetti.ViaMartingale.ShiftOperations
import Exchangeability.DeFinetti.ViaMartingale.FutureFiltration
import Exchangeability.Probability.MeasureKernels

/-!
# Finite Cylinder Machinery for Kallenberg Lemma 1.3

This file provides the finite approximation infrastructure for proving
conditional independence from contractability.

## Main definitions

* `finFutureSigma X m k` - Finite approximation of the future σ-algebra
* `contractable_finite_cylinder_measure` - Cylinder measure formula from contractability
* `contractable_triple_pushforward` - Triple pushforward equality
* `join_eq_comap_pair_finFuture` - σ-algebra join characterization

## Strategy

We prove conditional independence by working with finite future approximations.
The key insight is that contractability implies distributional equality for
cylinder sets, which extends to the full σ-algebra via π-λ theorem.
-/

noncomputable section
open scoped MeasureTheory
open MeasureTheory

namespace Exchangeability.DeFinetti.ViaMartingale

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

open MartingaleHelpers

/-! ### Finite Future σ-Algebra -/

/-- **Finite future σ-algebra.**

Approximates the infinite future σ(X_{m+1}, X_{m+2}, ...) by finite truncation. -/
def finFutureSigma (X : ℕ → Ω → α) (m k : ℕ) : MeasurableSpace Ω :=
  MeasurableSpace.comap (fun ω => fun i : Fin k => X (m + 1 + i.val) ω) inferInstance

end Exchangeability.DeFinetti.ViaMartingale
