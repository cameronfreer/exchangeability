/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Exchangeability.Probability.ConditionalKernel.JointLawEq

/-!
# Conditional Expectation via Conditional Distribution Kernels

This module re-exports all submodules for backwards compatibility.

## Main results

* `integral_condDistrib_eq_of_compProd_eq`: If two kernels produce the same compProd,
  then integrating bounded functions against them yields the same result a.e.

* `condExp_eq_of_joint_law_eq`: Conditional expectations w.r.t. different σ-algebras
  coincide when the joint laws match and one σ-algebra is contained in the other.

## Module Structure

- `ConditionalKernel.JointLawEq`: Main theorem on conditional expectation equality
-/
