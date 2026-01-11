/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Probability.Kernel.CompProdEqIff
import Exchangeability.Probability.ConditionalKernel.CondExpKernel
import Exchangeability.Probability.TripleLawDropInfo.DropInfo

/-!
# Conditional Expectation Equality from Joint Laws

This file proves the main theorem relating conditional expectations to joint laws.

## Main results

* `integral_condDistrib_eq_of_compProd_eq`: If two kernels produce the same compProd,
  then integrating bounded functions against them yields the same result a.e.

* `condExp_eq_of_joint_law_eq`: Conditional expectations w.r.t. different σ-algebras
  coincide when the joint laws match and one σ-algebra is contained in the other.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {Ω Γ E : Type*}

/-!
### Main theorem: Conditional expectation equality from joint law
-/

/-- **Conditional expectation equality from matching joint laws**

If random variables ζ and η satisfy:
- Their joint laws with ξ coincide: Law(ξ, ζ) = Law(ξ, η)
- σ(η) ⊆ σ(ζ)
- η = φ ∘ ζ for some measurable φ (implied by σ(η) ⊆ σ(ζ))

Then conditional expectations w.r.t. σ(ζ) and σ(η) are equal.

This is the key result needed for the ViaMartingale proof. It follows directly
from Kallenberg's Lemma 1.3 (drop-info lemma).

**Proof:** Direct application of `condExp_indicator_eq_of_law_eq_of_comap_le`
from `TripleLawDropInfo.DropInfo`, with variable mapping:
- X = ξ (the target random variable)
- W = η (coarser σ-algebra)
- W' = ζ (finer σ-algebra)
- h_law.symm provides (ξ, η) =^d (ξ, ζ) matching the drop-info lemma's (X, W) =^d (X, W')
-/
@[nolint unusedArguments]
theorem condExp_eq_of_joint_law_eq
    [MeasurableSpace Ω] [MeasurableSpace Γ] [MeasurableSpace E]
    [StandardBorelSpace Ω] [StandardBorelSpace Γ] [StandardBorelSpace E]
    [Nonempty Ω] [Nonempty Γ] [Nonempty E]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (ζ η : Ω → Γ) (hζ : Measurable ζ) (hη : Measurable η)
    (ξ : Ω → E) (hξ : Measurable ξ)
    (B : Set E) (hB : MeasurableSet B)
    (h_law : μ.map (fun ω => (ξ ω, ζ ω)) = μ.map (fun ω => (ξ ω, η ω)))
    (h_le : MeasurableSpace.comap η inferInstance ≤ MeasurableSpace.comap ζ inferInstance)
    (_hηfac : ∃ φ : Γ → Γ, Measurable φ ∧ η = φ ∘ ζ) :
    μ[(ξ ⁻¹' B).indicator (fun _ => (1 : ℝ))|MeasurableSpace.comap ζ inferInstance]
      =ᵐ[μ] μ[(ξ ⁻¹' B).indicator (fun _ => (1 : ℝ))|MeasurableSpace.comap η inferInstance] :=
  -- Direct application of Kallenberg Lemma 1.3 (drop-info)
  -- Mapping: X=ξ, W=η (coarser), W'=ζ (finer)
  -- Need h_law.symm to convert (ξ,ζ)=(ξ,η) to (ξ,η)=(ξ,ζ) for the lemma signature
  condExp_indicator_eq_of_law_eq_of_comap_le ξ η ζ hξ hη hζ h_law.symm h_le hB
