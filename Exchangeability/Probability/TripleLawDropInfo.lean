/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer, Claude (Anthropic)
-/
import Exchangeability.Probability.TripleLawDropInfo.PairLawHelpers
import Exchangeability.Probability.TripleLawDropInfo.DropInfo

/-!
# Kallenberg Lemma 1.3: Drop-Info Property via Contraction

This module re-exports all submodules for backwards compatibility.

This file implements **Kallenberg (2005), Lemma 1.3**, the "contraction-independence" lemma.

## Main Results

* `condExp_indicator_eq_of_law_eq_of_comap_le`: If `(X,W) =^d (X,W')` and `σ(W) ⊆ σ(W')`,
  then `E[1_{X∈A}|σ(W')] = E[1_{X∈A}|σ(W)]` a.e.

## Module Structure

- `TripleLawDropInfo.PairLawHelpers`: Helper lemmas for RN-derivative approach
- `TripleLawDropInfo.DropInfo`: Main theorem and wrappers

## Mathematical Background

**Kallenberg's Lemma 1.3 (Contraction-Independence):**

Given random elements ξ, η, ζ where:
1. `(ξ, η) =^d (ξ, ζ)` (pair laws match)
2. `σ(η) ⊆ σ(ζ)` (η is a *contraction* of ζ — i.e., η = f ∘ ζ for some measurable f)

**Conclusion:** `P[ξ ∈ B | ζ] = P[ξ ∈ B | η]` a.s.

## References

* Kallenberg (2005), *Probabilistic Symmetries and Invariance Principles*, Lemma 1.3
-/
