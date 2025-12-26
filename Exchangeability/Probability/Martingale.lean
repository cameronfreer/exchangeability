/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Exchangeability.Probability.Martingale.OrderDual
import Exchangeability.Probability.Martingale.Reverse
import Exchangeability.Probability.Martingale.Crossings
import Exchangeability.Probability.Martingale.Convergence

/-!
# Martingale Convergence for De Finetti

This module re-exports all martingale submodules for backwards compatibility.

This file provides Lévy's upward and downward theorems needed for the martingale proof
of de Finetti's theorem.

## Main Results

- `condExp_tendsto_iSup`: Lévy upward theorem (complete - wraps mathlib)
- `condExp_tendsto_iInf`: Lévy downward theorem (to be proved)

## Module Structure

- `Martingale.OrderDual`: OrderDual infrastructure, why reindexing fails
- `Martingale.Reverse`: Time-reversal infrastructure (revFiltration, revCEFinite)
- `Martingale.Crossings`: Downcrossing machinery and upcrossing bounds
- `Martingale.Convergence`: Main convergence theorems

## References

* Kallenberg, *Probabilistic Symmetries and Invariance Principles* (2005), Section 1
* Durrett, *Probability: Theory and Examples* (2019), Section 5.5
* Williams, *Probability with Martingales* (1991), Theorem 12.12
-/
