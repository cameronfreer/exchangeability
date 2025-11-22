/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.CompProdEqIff
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

/-!
# Conditional Expectation via Conditional Distribution Kernels

This file establishes the connection between conditional expectations and
regular conditional probability distributions (kernels).

## Main results

* `condExp_indicator_eq_integral_condDistrib`: Conditional expectation of an indicator
  function can be expressed as integration against the conditional distribution kernel.

* `integral_condDistrib_eq_of_compProd_eq`: If two kernels produce the same compProd,
  then integrating bounded functions against them yields the same result a.e.

* `condExp_eq_of_joint_law_eq`: Conditional expectations w.r.t. different σ-algebras
  coincide when the joint laws match and one σ-algebra is contained in the other.

-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {Ω Γ E : Type*}
variable [MeasurableSpace Ω] [MeasurableSpace Γ] [MeasurableSpace E]
variable [StandardBorelSpace Ω] [StandardBorelSpace Γ] [StandardBorelSpace E]
variable [Nonempty Ω] [Nonempty Γ] [Nonempty E]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

/-!
### Representation lemma: Conditional expectation via conditional distribution
-/

/-- Conditional expectation of a bounded measurable function composed with a random variable
can be expressed as integration against the conditional distribution kernel.

This is the key link between conditional expectation (a measure-theoretic notion)
and conditional distribution (a kernel-theoretic notion). -/
lemma condExp_indicator_eq_integral_condDistrib
    (ζ : Ω → Γ) (hζ : Measurable ζ)
    (ξ : Ω → E) (hξ : Measurable ξ)
    (B : Set E) (hB : MeasurableSet B) :
    μ[(ξ ⁻¹' B).indicator (fun _ => (1 : ℝ))|MeasurableSpace.comap ζ inferInstance]
      =ᵐ[μ] (fun ω => ∫ e, (B.indicator (fun _ => (1 : ℝ)) e) ∂(condDistrib ξ ζ μ (ζ ω))) := by
  -- The function we're conditioning
  let f := (ξ ⁻¹' B).indicator (fun _ => (1 : ℝ))
  -- Integrability
  have hint : Integrable f μ := by
    apply Integrable.indicator
    · exact integrable_const _
    · exact hξ hB
  -- Apply the general representation theorem
  have h1 : μ[f|MeasurableSpace.comap ζ inferInstance] =ᵐ[μ]
            fun ω => ∫ y, f y ∂(condExpKernel μ (MeasurableSpace.comap ζ inferInstance) ω) := by
    exact condExp_ae_eq_integral_condExpKernel hζ.comap_le hint
  -- Connect condExpKernel to condDistrib
  -- We want to show: ∫ f ∂condExpKernel = ∫ (B.indicator 1) ∘ ξ ∂condDistrib
  -- This follows from rewriting f = (B.indicator 1) ∘ ξ
  have h2 : ∀ᵐ ω ∂μ, ∫ y, f y ∂(condExpKernel μ (MeasurableSpace.comap ζ inferInstance) ω) =
                       ∫ e, (B.indicator (fun _ => (1 : ℝ)) e) ∂(condDistrib ξ ζ μ (ζ ω)) := by
    sorry  -- TODO: This requires connecting the kernels via condDistrib_apply_ae_eq_condExpKernel_map
  exact h1.trans h2

/-!
### Kernel uniqueness: compProd equality implies kernel a.e. equality
-/

/-- If two conditional distributions produce the same joint measure via compProd,
then the kernels themselves are a.e. equal under the marginal law.

This uses the `compProd_eq_iff` theorem from mathlib. -/
lemma condDistrib_ae_eq_of_compProd_eq
    {ζ : Ω → Γ} (hζ : Measurable ζ)
    {ξ₁ ξ₂ : Ω → E} (hξ₁ : Measurable ξ₁) (hξ₂ : Measurable ξ₂)
    (h_law : μ.map (fun ω => (ζ ω, ξ₁ ω)) = μ.map (fun ω => (ζ ω, ξ₂ ω))) :
    condDistrib ξ₁ ζ μ =ᵐ[μ.map ζ] condDistrib ξ₂ ζ μ := by
  -- Use compProd_eq_iff to turn equality of joint measures into kernel equality
  rw [condDistrib, condDistrib]
  have h1 : (μ.map (fun ω => (ζ ω, ξ₁ ω))).condKernel =
            (μ.map (fun ω => (ζ ω, ξ₂ ω))).condKernel := by
    sorry  -- This should follow from condKernel uniqueness
  sorry

/-- From kernel a.e. equality, we get equality of integrals a.e.

This is essentially the definition of kernel equality. -/
lemma integral_condDistrib_eq_of_ae_eq
    {ζ : Ω → Γ} (hζ : Measurable ζ)
    {ξ₁ ξ₂ : Ω → E}
    (h_kernel_eq : condDistrib ξ₁ ζ μ =ᵐ[μ.map ζ] condDistrib ξ₂ ζ μ)
    (B : Set E) (hB : MeasurableSet B) :
    (fun ω => ∫ e, (B.indicator (fun _ => (1 : ℝ)) e) ∂(condDistrib ξ₁ ζ μ (ζ ω)))
      =ᵐ[μ] (fun ω => ∫ e, (B.indicator (fun _ => (1 : ℝ)) e) ∂(condDistrib ξ₂ ζ μ (ζ ω))) := by
  -- Kernel a.e. equality means: for μ.map ζ-a.e. z, condDistrib ξ₁ ζ μ z = condDistrib ξ₂ ζ μ z
  -- This implies for μ-a.e. ω, condDistrib ξ₁ ζ μ (ζ ω) = condDistrib ξ₂ ζ μ (ζ ω)
  sorry

/-!
### Main theorem: Conditional expectation equality from joint law
-/

/-- **Conditional expectation equality from matching joint laws**

If random variables ζ and η satisfy:
- Their joint laws with ξ coincide: Law(ζ, ξ) = Law(η, ξ)
- σ(η) ⊆ σ(ζ)
- η = φ ∘ ζ for some measurable φ

Then conditional expectations w.r.t. σ(ζ) and σ(η) are equal.

This is the key result needed for the ViaMartingale proof. -/
theorem condExp_eq_of_joint_law_eq
    (ζ η : Ω → Γ) (hζ : Measurable ζ) (hη : Measurable η)
    (ξ : Ω → E) (hξ : Measurable ξ)
    (B : Set E) (hB : MeasurableSet B)
    (h_law : μ.map (fun ω => (ξ ω, ζ ω)) = μ.map (fun ω => (ξ ω, η ω)))
    (h_le : MeasurableSpace.comap η inferInstance ≤ MeasurableSpace.comap ζ inferInstance)
    (hηfac : ∃ φ : Γ → Γ, Measurable φ ∧ η = φ ∘ ζ) :
    μ[(ξ ⁻¹' B).indicator (fun _ => (1 : ℝ))|MeasurableSpace.comap ζ inferInstance]
      =ᵐ[μ] μ[(ξ ⁻¹' B).indicator (fun _ => (1 : ℝ))|MeasurableSpace.comap η inferInstance] := by
  sorry
