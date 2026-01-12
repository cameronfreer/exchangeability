/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Exchangeability.Probability.CondExpHelpers.AEComb
import Exchangeability.Probability.CondExpHelpers.Convergence
import Exchangeability.Probability.CondExpHelpers.Integrability

/-!
# Helper lemmas for conditional expectation

This module re-exports all submodules for backwards compatibility.

This file contains helper lemmas for working with conditional expectations,
particularly for uniqueness arguments via set integrals and σ-algebra factorizations.

These lemmas support the proof of de Finetti's theorem via martingales, specifically
the three key lemmas about conditional independence and factorization.

## Main results

* `finset_sum_ae_eq`: Combine finitely many a.e.-equalities into a sum
* `tendsto_condExpL1_domconv`: DCT for conditional expectation in L¹
* `integrable_mul_of_bound_one`: Product with bounded factor is integrable
* `sigma_factor_le`: Pullback σ-algebra inequality for factorizations

## Module Structure

- `CondExpHelpers.AEComb`: Combining finitely many a.e. equalities
- `CondExpHelpers.Convergence`: DCT and subsequence extraction
- `CondExpHelpers.Integrability`: Integrability, uniqueness, σ-algebra factorization
-/
