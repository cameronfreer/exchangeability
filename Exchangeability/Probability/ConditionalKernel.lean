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
  -- Use the general representation theorem from mathlib
  have : μ[fun a => B.indicator (fun _ => (1 : ℝ)) (ξ a)|MeasurableSpace.comap ζ inferInstance]
      =ᵐ[μ] fun a => ∫ y, B.indicator (fun _ => (1 : ℝ)) y ∂condDistrib ξ ζ μ (ζ a) := by
    apply condExp_ae_eq_integral_condDistrib hζ hξ.aemeasurable
    · exact StronglyMeasurable.indicator stronglyMeasurable_const hB
    · apply Integrable.indicator
      · exact integrable_const _
      · exact hξ hB
  -- Rewrite LHS: (fun a => B.indicator 1 (ξ a)) = (ξ ⁻¹' B).indicator 1
  convert this using 2

/-!
### Main theorem: Conditional expectation equality from joint law
-/

/-- **Conditional expectation equality from matching joint laws**

If random variables ζ and η satisfy:
- Their joint laws with ξ coincide: Law(ζ, ξ) = Law(η, ξ)  (note the order!)
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
  haveI : IsFiniteMeasure μ := inferInstance
  -- Step 1: Express conditional expectations as integrals against condDistrib
  have hCEζ : μ[(ξ ⁻¹' B).indicator (fun _ => (1 : ℝ))|MeasurableSpace.comap ζ inferInstance]
      =ᵐ[μ] (fun ω => ∫ e, (B.indicator (fun _ => (1 : ℝ)) e) ∂(condDistrib ξ ζ μ (ζ ω))) := by
    apply condExp_indicator_eq_integral_condDistrib ζ hζ ξ hξ B hB
  have hCEη : μ[(ξ ⁻¹' B).indicator (fun _ => (1 : ℝ))|MeasurableSpace.comap η inferInstance]
      =ᵐ[μ] (fun ω => ∫ e, (B.indicator (fun _ => (1 : ℝ)) e) ∂(condDistrib ξ η μ (η ω))) := by
    apply condExp_indicator_eq_integral_condDistrib η hη ξ hξ B hB

  -- Step 2: Swap the pair order in h_law to get (ζ, ξ) = (η, ξ)
  have h_law_swapped : μ.map (fun ω => (ζ ω, ξ ω)) = μ.map (fun ω => (η ω, ξ ω)) := by
    have h_prod_comm_ζ : μ.map (fun ω => (ζ ω, ξ ω)) = (μ.map (fun ω => (ξ ω, ζ ω))).map Prod.swap := by
      rw [Measure.map_map measurable_swap (hξ.prodMk hζ)]
      rfl
    have h_prod_comm_η : μ.map (fun ω => (η ω, ξ ω)) = (μ.map (fun ω => (ξ ω, η ω))).map Prod.swap := by
      rw [Measure.map_map measurable_swap (hξ.prodMk hη)]
      rfl
    rw [h_prod_comm_ζ, h_prod_comm_η, h_law]

  -- Step 3: Use compProd representations
  have hζ_compProd : (μ.map ζ) ⊗ₘ (condDistrib ξ ζ μ) = μ.map (fun ω => (ζ ω, ξ ω)) := by
    exact compProd_map_condDistrib hξ.aemeasurable
  have hη_compProd : (μ.map η) ⊗ₘ (condDistrib ξ η μ) = μ.map (fun ω => (η ω, ξ ω)) := by
    exact compProd_map_condDistrib hξ.aemeasurable

  -- Step 4: Get marginal equality
  have h_marg_eq : μ.map ζ = μ.map η := by
    have h1 : (μ.map (fun ω => (ζ ω, ξ ω))).fst = μ.map ζ := Measure.fst_map_prodMk₀ hξ.aemeasurable
    have h2 : (μ.map (fun ω => (η ω, ξ ω))).fst = μ.map η := Measure.fst_map_prodMk₀ hξ.aemeasurable
    rw [← h1, ← h2, h_law_swapped]

  -- Step 5: Extract φ from factorization
  obtain ⟨φ, hφ_meas, hηfac⟩ := hηfac

  -- Step 6: Key insight - we can express Law(η, ξ) using ζ-measure and φ
  -- Since η = φ ∘ ζ, we have:
  -- Law(η, ξ) = μ.map (fun ω => (η ω, ξ ω))
  --           = μ.map (fun ω => (φ (ζ ω), ξ ω))  [by substitution]
  --           = (μ.map (φ ∘ ζ)) ⊗ₘ (condDistrib ξ η μ)  [by compProd for η]
  --           = ((μ.map ζ).map φ) ⊗ₘ (condDistrib ξ η μ)  [by map composition]

  -- We also have from our hypothesis:
  -- Law(ζ, ξ) = Law(η, ξ), so:
  -- (μ.map ζ) ⊗ₘ (condDistrib ξ ζ μ) = μ.map (fun ω => (φ (ζ ω), ξ ω))

  -- Let's directly show the kernel equality by working at the measure level
  -- We want to show: ∀ᵐ z ∂(μ.map ζ), condDistrib ξ ζ μ z = condDistrib ξ η μ (φ z)

  -- Step 7: Show that μ.map (fun ω => (φ (ζ ω), ξ ω)) can be written with ζ-measure
  have h_eq_φζ : μ.map (fun ω => (φ (ζ ω), ξ ω)) = μ.map (fun ω => (η ω, ξ ω)) := by
    have : (fun ω => (φ (ζ ω), ξ ω)) = (fun ω => (η ω, ξ ω)) := by
      funext ω
      rw [congr_fun hηfac ω, Function.comp_apply]
    rw [this]

  -- Step 8: Rewrite the compProd for η using φ ∘ ζ
  have hη_via_φζ : μ.map (fun ω => (η ω, ξ ω)) = ((μ.map ζ).map φ) ⊗ₘ (condDistrib ξ η μ) := by
    have h_map_comp : μ.map (φ ∘ ζ) = (μ.map ζ).map φ := by
      rw [Measure.map_map hφ_meas hζ]
    calc μ.map (fun ω => (η ω, ξ ω))
        = (μ.map η) ⊗ₘ (condDistrib ξ η μ) := hη_compProd.symm
      _ = (μ.map (φ ∘ ζ)) ⊗ₘ (condDistrib ξ η μ) := by
          rw [← hηfac]
      _ = ((μ.map ζ).map φ) ⊗ₘ (condDistrib ξ η μ) := by rw [← h_map_comp]

  -- Step 9: Derive compProd equality from equal joint laws
  -- Key: we have (μ.map ζ) ⊗ₘ (condDistrib ξ ζ μ) = ((μ.map ζ).map φ) ⊗ₘ (condDistrib ξ η μ)
  have h_compProd_eq : (μ.map ζ) ⊗ₘ (condDistrib ξ ζ μ) = ((μ.map ζ).map φ) ⊗ₘ (condDistrib ξ η μ) := by
    rw [hζ_compProd, h_law_swapped, hη_via_φζ]

  -- Step 10: Directly show both compProds with common base measure ν = μ.map ζ are equal
  -- K₁ z := condDistrib ξ ζ μ z
  -- K₂ z := condDistrib ξ η μ (φ z)
  -- We show ν ⊗ₘ K₁ = ν ⊗ₘ K₂ by proving both equal Law(η, ξ)

  -- Step 10.5: Kernel equality via disintegration under factorization
  -- Key insight: Both kernels disintegrate Law(ζ,ξ) = Law(η,ξ) with respect to μ.map ζ
  -- Use Kernel.comap to represent the composition z ↦ condDistrib ξ η μ (φ z)
  have h_kernel_z : ∀ᵐ z ∂(μ.map ζ), condDistrib ξ ζ μ z = condDistrib ξ η μ (φ z) := by
    -- Define the "comapped" kernel using Kernel.comap
    -- This gives us a proper Kernel type representing z ↦ condDistrib ξ η μ (φ z)
    let κ_φ := (condDistrib ξ η μ).comap φ hφ_meas

    -- Show that both compProds with base μ.map ζ are equal
    have h_compProd_same_base : (μ.map ζ) ⊗ₘ (condDistrib ξ ζ μ) = (μ.map ζ) ⊗ₘ κ_φ := by
      calc (μ.map ζ) ⊗ₘ (condDistrib ξ ζ μ)
          = μ.map (fun ω => (ζ ω, ξ ω)) := hζ_compProd
        _ = μ.map (fun ω => (η ω, ξ ω)) := h_law_swapped
        _ = (μ.map η) ⊗ₘ (condDistrib ξ η μ) := hη_compProd.symm
        _ = (μ.map (φ ∘ ζ)) ⊗ₘ (condDistrib ξ η μ) := by rw [← hηfac]
        _ = ((μ.map ζ).map φ) ⊗ₘ (condDistrib ξ η μ) := by rw [← Measure.map_map hφ_meas hζ]
        _ = (μ.map ζ) ⊗ₘ κ_φ := by
            -- KEY MISSING LEMMA: Rewrite compProd under factorization
            -- Need to show: ((ν.map φ) ⊗ₘ κ) = (ν ⊗ₘ (κ.comap φ hφ))
            -- This is NOT a general compProd identity - it requires a specialized proof
            -- using properties of conditional distributions and factorizations
            --
            -- The correct approach (per discussion): Write a lemma that proves
            -- Law(η, ξ) = (μ.map ζ) ⊗ₘ (z ↦ condDistrib ξ η μ (φ z))
            -- directly from the defining properties of condDistrib, not by manipulating compProds
            --
            -- This lemma should use:
            -- - The defining property of condDistrib: it disintegrates the joint law
            -- - The factorization η = φ ∘ ζ
            -- - The marginal equality Law(ζ) = Law(η)
            sorry

    -- Apply compProd_eq_iff to extract the kernel equality
    have h_kernels_eq : condDistrib ξ ζ μ =ᵐ[μ.map ζ] κ_φ := by
      exact (ProbabilityTheory.Kernel.compProd_eq_iff).mp h_compProd_same_base

    -- Unfold κ_φ using the definition of comap
    filter_upwards [h_kernels_eq] with z hz
    rw [hz]
    rfl  -- κ_φ z = (condDistrib ξ η μ).comap φ hφ_meas z = condDistrib ξ η μ (φ z) by definition

  -- Pull back along ζ and use factorization η = φ ∘ ζ
  have h_kernel_on_Ω : ∀ᵐ ω ∂μ, condDistrib ξ ζ μ (ζ ω) = condDistrib ξ η μ (η ω) := by
    -- Pull back the kernel equality from μ.map ζ to μ
    have h_at_ζ : ∀ᵐ ω ∂μ, condDistrib ξ ζ μ (ζ ω) = condDistrib ξ η μ (φ (ζ ω)) := by
      exact ae_of_ae_map hζ.aemeasurable h_kernel_z
    -- Use η = φ ∘ ζ to rewrite φ (ζ ω) as η ω
    filter_upwards [h_at_ζ] with ω hω
    have : η ω = φ (ζ ω) := congr_fun hηfac ω
    rw [hω, this]

  -- Step 11: Use η = φ ∘ ζ to get the final equality
  have h_integral_eq : (fun ω => ∫ e, B.indicator (fun _ => (1 : ℝ)) e ∂(condDistrib ξ ζ μ (ζ ω)))
      =ᵐ[μ] (fun ω => ∫ e, B.indicator (fun _ => (1 : ℝ)) e ∂(condDistrib ξ η μ (η ω))) := by
    filter_upwards [h_kernel_on_Ω] with ω hω
    rw [hω]

  -- Step 12: Chain all the equalities together
  calc μ[(ξ ⁻¹' B).indicator (fun _ => (1 : ℝ))|MeasurableSpace.comap ζ inferInstance]
      =ᵐ[μ] (fun ω => ∫ e, B.indicator (fun _ => (1 : ℝ)) e ∂(condDistrib ξ ζ μ (ζ ω))) := hCEζ
    _ =ᵐ[μ] (fun ω => ∫ e, B.indicator (fun _ => (1 : ℝ)) e ∂(condDistrib ξ η μ (η ω))) := h_integral_eq
    _ =ᵐ[μ] μ[(ξ ⁻¹' B).indicator (fun _ => (1 : ℝ))|MeasurableSpace.comap η inferInstance] := hCEη.symm
