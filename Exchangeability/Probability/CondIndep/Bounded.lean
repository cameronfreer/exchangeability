/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Exchangeability.Probability.CondIndep.Bounded.Approximation
import Exchangeability.Probability.CondIndep.Bounded.Extension
import Exchangeability.Probability.CondIndep.Bounded.Projection

/-!
# Conditional Independence - Bounded Measurable Extension

This file re-exports the bounded measurable extension infrastructure for
conditional independence.

## Module structure

* `Bounded/Approximation.lean` - L¹ approximation infrastructure
* `Bounded/Extension.lean` - Extension from simple to bounded measurable functions
* `Bounded/Projection.lean` - Projection theorems for conditional expectations

## Main results (re-exported)

* `tendsto_condexp_L1`: L¹ convergence of conditional expectations
* `eapprox_real_approx`: Simple function approximation for real-valued functions
* `condIndep_simpleFunc_left`: Simple function → bounded measurable extension
* `condIndep_bddMeas_extend_left`: Full bounded measurable extension
* `condIndep_boundedMeasurable`: Conditional independence for bounded measurable functions
* `condIndep_of_rect_factorization`: Rectangle factorization implies conditional independence
* `condExp_project_of_condIndep`: Conditional expectation projection theorem
* `condIndep_project`: Main projection theorem

## References

* Kallenberg (2005), *Probabilistic Symmetries and Invariance Principles*, Section 6.1
-/
