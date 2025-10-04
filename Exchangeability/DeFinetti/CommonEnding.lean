/-
Copyright (c) 2025 exchangeability contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: exchangeability contributors
-/
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Probability.Kernel.Basic
import Exchangeability.Exchangeability
import Exchangeability.Contractability

/-!
# Common Ending for de Finetti Proofs

This file contains the common final step shared by Kallenberg's First and Second proofs
of de Finetti's theorem. Both proofs construct a directing measure ν and then use
the same argument to establish the conditional i.i.d. property.

## The common structure

Given:
- A contractable/exchangeable sequence ξ
- A directing measure ν (constructed differently in each proof)
- The property that E[f(ξ_i) | ℱ] = ν^f for bounded measurable f

Show:
- ξ is conditionally i.i.d. given the tail σ-algebra

## References

* Kallenberg (2005), page 26-27: "The proof can now be completed as before"

-/

noncomputable section

namespace Exchangeability.DeFinetti.CommonEnding

open MeasureTheory ProbabilityTheory
open Exchangeability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-!
## The common completion argument

Kallenberg's text says: "The proof can now be completed as before."

This refers to the final step of the first proof, which goes:
1. Have directing measure ν with E[f(ξ_i) | ℱ] = ν^f
2. Use monotone class argument to extend to product sets
3. Show P[∩ Bᵢ | ℱ] = ν^k B for B ∈ 𝒮^k
4. This establishes conditional independence

TODO: Formalize this common argument.
-/

/-- Given a sequence and a directing measure satisfying the key property
E[f(ξ_i) | ℱ] = ν^f for bounded measurable functions, we can establish
conditional independence.

This is the "completed as before" step referenced in the Second proof.

TODO: Complete proof using monotone class argument.
-/
theorem conditional_iid_from_directing_measure
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → α)
    (hX_meas : ∀ i, Measurable (X i))
    (ν : Ω → Measure α)
    (hν_prob : ∀ ω, IsProbabilityMeasure (ν ω))
    -- ν is tail-measurable
    (hν_tail : sorry)
    -- For all bounded measurable f and all i:
    -- E[f(X_i) | tail σ-algebra] = ∫ f dν a.e.
    (hν_cond : ∀ (f : α → ℝ) (hf_meas : Measurable f) (hf_bdd : ∃ M, ∀ x, |f x| ≤ M),
      ∀ i, sorry) :  -- E[f(X_i) | tail] = ∫ f dν
    -- Then X is conditionally i.i.d. given tail with law ν
    sorry := by  -- ConditionallyIID μ X (kernel from ν)
  sorry

/-- The monotone class extension argument: if a property holds for bounded
measurable functions, it extends to product σ-algebras.

This is referenced as "FMP 1.1" in Kallenberg.

TODO: Either find this in mathlib or prove it.
-/
theorem monotone_class_product_extension
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → α) (hX_meas : ∀ i, Measurable (X i))
    (ν : Ω → Measure α) (hν_prob : ∀ ω, IsProbabilityMeasure (ν ω))
    (k : ℕ)
    -- If the property holds for products of bounded functions
    (h_prod : ∀ (f : Fin k → α → ℝ),
      (∀ i, Measurable (f i)) →
      (∀ i, ∃ M, ∀ x, |f i x| ≤ M) →
      sorry) :  -- E[∏ f_i(X_i) | tail] = ∏ ∫ f_i dν
    -- Then it holds for all product measurable sets
    ∀ (B : Fin k → Set α), (∀ i, MeasurableSet (B i)) →
      sorry := by  -- P[∩ X_i ∈ B_i | tail] = ∏ ν(B_i)
  sorry

/-- Package the common ending as a reusable theorem.

Given a contractable sequence and a directing measure ν constructed via
either approach (Mean Ergodic Theorem or L² bound), this completes the
proof to conditional i.i.d.

This encapsulates the "completed as before" step.
-/
theorem complete_from_directing_measure
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → α) (hX_meas : ∀ i, Measurable (X i))
    (hX_contract : Contractable μ X)
    (ν : Ω → Measure α) (hν_prob : ∀ ω, IsProbabilityMeasure (ν ω))
    (hν_tail : sorry)  -- tail-measurable
    (hν_dir : sorry) :  -- E[f(X_i) | tail] = ∫ f dν for bounded f
    ∃ (K : Kernel Ω α),
      IsMarkovKernel K ∧
      sorry ∧  -- K tail-measurable
      sorry := by  -- X conditionally i.i.d. with law K
  -- Apply the conditional_iid_from_directing_measure
  sorry

end Exchangeability.DeFinetti.CommonEnding
