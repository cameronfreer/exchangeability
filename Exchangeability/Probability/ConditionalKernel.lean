/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Exchangeability.Probability.ConditionalKernel.CondExpKernel
import Exchangeability.Probability.ConditionalKernel.JointLawEq

/-!
# Conditional Expectation via Conditional Distribution Kernels

This module re-exports all submodules for backwards compatibility.

This file establishes the connection between conditional expectations and
regular conditional probability distributions (kernels).

## Main results

* `condExp_indicator_eq_integral_condDistrib`: Conditional expectation of an indicator
  function can be expressed as integration against the conditional distribution kernel.

* `integral_condDistrib_eq_of_compProd_eq`: If two kernels produce the same compProd,
  then integrating bounded functions against them yields the same result a.e.

* `condExp_eq_of_joint_law_eq`: Conditional expectations w.r.t. different σ-algebras
  coincide when the joint laws match and one σ-algebra is contained in the other.

## Module Structure

- `ConditionalKernel.CondExpKernel`: Representation lemma linking condExp to condDistrib
- `ConditionalKernel.JointLawEq`: Main theorem on conditional expectation equality
-/
