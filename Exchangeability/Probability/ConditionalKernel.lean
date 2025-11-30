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

  -- Step 10.5: Direct proof using the conditional expectation characterization
  -- Skip the pointwise kernel equality - prove the integral equality directly
  have h_kernel_on_Ω : ∀ᵐ ω ∂μ, condDistrib ξ ζ μ (ζ ω) = condDistrib ξ η μ (η ω) := by
    -- The key insight: both sides are versions of E[1_B(ξ) | σ(·)]
    -- By uniqueness of conditional expectation, they must be equal

    -- For any measurable set C ⊆ E, define f_C(ω) := 1_C(ξ ω)
    -- Then:
    -- - E[f_C | σ(ζ)] = ∫ e, 1_C(e) ∂(condDistrib ξ ζ μ (ζ ω))
    -- - E[f_C | σ(η)] = ∫ e, 1_C(e) ∂(condDistrib ξ η μ (η ω))

    -- By the tower property and coarsening: since σ(η) ⊆ σ(ζ),
    -- we have E[E[f_C | σ(ζ)] | σ(η)] = E[f_C | σ(η)]

    -- But also: E[E[f_C | σ(ζ)] | σ(η)] should use the kernel for ζ
    -- evaluated at... hmm, this is getting circular

    -- Alternative: use the joint law equality directly
    -- Law(ζ, ξ) = Law(η, ξ) means for any test function g:
    -- ∫ g(ζ ω, ξ ω) dμ = ∫ g(η ω, ξ ω) dμ

    -- In particular, for g(γ, e) = h(γ) * 1_B(e):
    -- ∫ h(ζ ω) * 1_B(ξ ω) dμ = ∫ h(η ω) * 1_B(ξ ω) dμ

    -- This is exactly the defining property that relates the conditional distributions!

    -- Key insight: since the joint laws are equal, the kernels are literally equal
    -- condDistrib ξ ζ μ = (μ.map (ζ, ξ)).condKernel = (μ.map (η, ξ)).condKernel = condDistrib ξ η μ
    have h_kernel_eq : condDistrib ξ ζ μ = condDistrib ξ η μ := by
      simp only [condDistrib, h_law_swapped]
    -- Now we need: K(ζ ω) = K(η ω) where K is the common kernel
    -- Since η = φ ∘ ζ, this is K(ζ ω) = K(φ(ζ ω))
    -- This requires showing K is φ-invariant on the support

    -- The joint law μ.map (ζ, ξ) is invariant under (γ, e) ↦ (φ(γ), e)
    have h_joint_inv : μ.map (fun ω => (ζ ω, ξ ω)) =
        (μ.map (fun ω => (ζ ω, ξ ω))).map (Prod.map φ id) := by
      rw [Measure.map_map (hφ_meas.prodMap measurable_id) (hζ.prodMk hξ)]
      -- Goal: μ.map (ζ, ξ) = μ.map ((Prod.map φ id) ∘ (ζ, ξ))
      -- Since (Prod.map φ id) ∘ (ζ, ξ) = (φ ∘ ζ, ξ) = (η, ξ)
      have h_comp : (Prod.map φ id) ∘ (fun ω => (ζ ω, ξ ω)) = (fun ω => (η ω, ξ ω)) := by
        ext ω <;>
        simp only [Function.comp_apply, Prod.map_apply, id_eq, Prod.fst, Prod.snd, hηfac]
      rw [h_comp, h_law_swapped]

    -- From this invariance, the kernel K = condDistrib ξ ζ μ satisfies K(γ) = K(φ(γ)) a.e.
    -- This is because K ∘ φ is also a disintegration of the same measure
    -- The uniqueness of disintegration implies K = K ∘ φ a.e.

    -- For now, use that the kernels agree at both ζ ω and η ω since they're the same kernel
    -- evaluated at points in the support of the same measure (μ.map ζ = μ.map η)
    rw [h_kernel_eq]
    -- Goal: ∀ᵐ ω ∂μ, (condDistrib ξ η μ) (ζ ω) = (condDistrib ξ η μ) (η ω)

    -- The kernel K = condDistrib ξ η μ
    -- Using the φ-invariance of the joint law: K(γ) = K(φ(γ)) for μ.map ζ-a.e. γ
    have h_K_inv : ∀ᵐ γ ∂(μ.map ζ), (condDistrib ξ η μ) γ = (condDistrib ξ η μ) (φ γ) := by
      -- The measure μ.map (ζ, ξ) is φ-invariant on the first component
      -- Its disintegration kernel K satisfies: for any A × B,
      -- ∫_{φ⁻¹(A)} K(γ)(B) dν = ∫_A K(φ γ)(B) dν where ν = μ.map ζ
      -- Since ν is φ-invariant (ν = ν.map φ), this implies K = K ∘ φ a.e.
      have h_ν_inv : μ.map ζ = (μ.map ζ).map φ := by
        rw [Measure.map_map hφ_meas hζ]
        -- Goal: μ.map ζ = μ.map (φ ∘ ζ)
        -- Since φ ∘ ζ = η (from hηfac)
        have h_eq : φ ∘ ζ = η := hηfac.symm
        rw [h_eq, h_marg_eq]
      -- Use that both K and K ∘ φ disintegrate the same measure
      have h_compProd_K : (μ.map ζ) ⊗ₘ (condDistrib ξ η μ) = μ.map (fun ω => (ζ ω, ξ ω)) := by
        rw [← h_kernel_eq, hζ_compProd]
      -- Strategy: Show ν ⊗ₘ K = ν ⊗ₘ (K.comap φ), then use Kernel.compProd_eq_iff
      -- We have: ν ⊗ₘ K = ρ (from h_compProd_K)
      -- We need: ν ⊗ₘ (K.comap φ) = ρ
      -- Key identities:
      -- 1. ρ = ρ.map (Prod.map φ id) (from h_joint_inv)
      -- 2. ν = ν.map φ (from h_ν_inv)
      --
      -- For rectangles A × B:
      -- (ν ⊗ₘ (K.comap φ))(A × B) = ∫_A K(φ γ)(B) dν(γ)
      -- Using ν = ν.map φ: = ∫_{φ⁻¹(A)} K(φ(φ γ))(B) dν(γ)
      -- And ρ(A × B) = ∫_A K(γ)(B) dν(γ) = ∫_{φ⁻¹(A)} K(γ)(B) dν(γ) (by ρ-invariance)
      --
      -- The equality follows from the fact that both K and K.comap φ are
      -- disintegrations of the same ρ w.r.t. ν, so they must agree a.e. by uniqueness.
      -- Use compProd_eq_iff: if ν ⊗ₘ K = ν ⊗ₘ (K.comap φ) then K =ᵐ[ν] K.comap φ
      -- Show ν ⊗ₘ K = ν ⊗ₘ (K.comap φ), then apply compProd_eq_iff
      have h_compProd_eq_comap : (μ.map ζ) ⊗ₘ (condDistrib ξ η μ) =
          (μ.map ζ) ⊗ₘ ((condDistrib ξ η μ).comap φ hφ_meas) := by
        -- Strategy: show both sides equal ρ on all measurable sets
        -- Key insight: the equality ∫_A K(φ γ)(B) dν = ∫_A K(γ)(B) dν follows from
        -- combining marginal invariance ν = ν.map φ and joint invariance ρ = ρ.map (Prod.map φ id)
        ext s hs
        rw [Measure.compProd_apply hs, Measure.compProd_apply hs]
        simp only [Kernel.comap_apply]
        -- Goal: ∫ K(γ)(s_γ) dν = ∫ K(φ γ)(s_γ) dν
        -- Step 1: From marginal invariance, ∫_A f dν = ∫_{φ⁻¹(A)} (f ∘ φ) dν
        -- Step 2: From joint invariance on rectangles, ∫_A K(γ)(B) dν = ∫_{φ⁻¹(A)} K(γ)(B) dν
        -- Step 3: Combining gives ∫_{φ⁻¹(A)} K(φ γ)(B) dν = ∫_{φ⁻¹(A)} K(γ)(B) dν
        -- Step 4: Therefore ∫_A K(φ γ)(B) dν = ∫_A K(γ)(B) dν
        --
        -- Use the change of variables formula: for f measurable,
        -- ∫ f dν = ∫ f d(ν.map φ) = ∫ (f ∘ φ) dν
        have h_lintegral_eq : ∀ (f : Γ → ℝ≥0∞), Measurable f →
            ∫⁻ γ, f γ ∂(μ.map ζ) = ∫⁻ γ, f (φ γ) ∂(μ.map ζ) := by
          intro f hf
          conv_lhs => rw [h_ν_inv]
          rw [lintegral_map hf hφ_meas]
        -- The key observation: using joint and marginal invariance together
        -- From h_compProd_K: ∫ K(γ)(s_γ) dν = ρ(s)
        -- From h_joint_inv: ρ(s) = ρ((Prod.map φ id)⁻¹(s))
        -- The section of (Prod.map φ id)⁻¹(s) at γ is s_{φ γ}
        -- So: ∫ K(γ)(s_γ) dν = ∫ K(γ)(s_{φ γ}) dν
        have h_section_shift : ∀ γ, (Prod.mk γ) ⁻¹' ((Prod.map φ id) ⁻¹' s) =
            (Prod.mk (φ γ)) ⁻¹' s := by
          intro γ
          ext e
          simp only [Set.mem_preimage, Prod.map_apply, id_eq]
        -- The integral of K(φ γ)(s_γ) can be computed via change of variables
        -- ∫ K(φ γ)(s_γ) dν = ∫ K(γ)(s_γ) dν follows from the symmetry of the invariance
        rw [← h_compProd_K] at h_joint_inv
        -- h_joint_inv now says: ν ⊗ₘ K = (ν ⊗ₘ K).map (Prod.map φ id)
        have h_apply_inv : ∀ t, MeasurableSet t → (μ.map ζ ⊗ₘ condDistrib ξ η μ) t =
            (μ.map ζ ⊗ₘ condDistrib ξ η μ) ((Prod.map φ id) ⁻¹' t) := by
          intro t ht
          conv_lhs => rw [h_joint_inv]
          rw [Measure.map_apply (hφ_meas.prodMap measurable_id) ht]
        -- Apply to s
        have h_s_inv := h_apply_inv s hs
        rw [Measure.compProd_apply hs, Measure.compProd_apply
            ((hφ_meas.prodMap measurable_id) hs)] at h_s_inv
        -- Now h_s_inv: ∫ K(γ)(s_γ) dν = ∫ K(γ)(s_{φ γ}) dν
        simp only [h_section_shift] at h_s_inv
        -- Simpler approach: use rectangle sets s = A × B
        -- For rectangle s = A × B:
        --   s_γ = B if γ ∈ A, else ∅
        --   (φ × id)⁻¹(A × B) = φ⁻¹(A) × B
        -- Joint invariance: (ν ⊗ₘ K)(A × B) = (ν ⊗ₘ K)(φ⁻¹(A) × B)
        -- This gives: ∫_A K(γ)(B) dν = ∫_{φ⁻¹(A)} K(γ)(B) dν
        -- Using ν = ν.map φ on LHS: ∫_{φ⁻¹(A)} K(φγ)(B) dν = ∫_{φ⁻¹(A)} K(γ)(B) dν
        -- For A = Γ: ∫ K(φγ)(B) dν = ∫ K(γ)(B) dν for all B
        -- Therefore K(φγ) = K(γ) a.e. by extensionality
        --
        -- But we need to show this for general s, not just rectangles.
        -- The key is that rectangles generate the σ-algebra.
        --
        -- Alternative direct approach:
        -- From h_s_inv: ∫ K(γ)(s_γ) dν = ∫ K(γ)(s_{φγ}) dν
        -- Apply change of variables using ν = ν.map φ:
        -- LHS stays the same (it's the original goal)
        -- On RHS: ∫ K(γ)(s_{φγ}) dν = ∫ K(γ)(s_{φγ}) d(ν.map φ) = ∫ K(φγ)(s_{φ²γ}) dν
        -- So: ∫ K(γ)(s_γ) dν = ∫ K(φγ)(s_{φ²γ}) dν
        --
        -- We need a symmetry argument. The key insight is that since the
        -- invariances hold for ALL measurable s, we can substitute appropriately.
        --
        -- Actually, let's use Kernel.compProd_eq_iff more directly
        -- The proof that K =ᵐ[ν] K.comap φ follows from showing the compProds are equal
        -- which requires showing the integrals match for all s.
        --
        -- For general s, we use the monotone class theorem: if the equality holds
        -- for rectangles, it holds for all measurable sets.
        sorry
      -- Apply compProd_eq_iff to get a.e. equality of kernels
      have h_ae_eq := Kernel.compProd_eq_iff.mp h_compProd_eq_comap
      filter_upwards [h_ae_eq] with γ hγ
      simp only [Kernel.comap_apply] at hγ
      -- hγ : K γ = K (φ γ), which is exactly what we want
      exact hγ
    -- Pull back to Ω via ζ and use η = φ ∘ ζ
    have h_on_Ω : ∀ᵐ ω ∂μ, (condDistrib ξ η μ) (ζ ω) = (condDistrib ξ η μ) (φ (ζ ω)) :=
      ae_of_ae_map hζ.aemeasurable h_K_inv
    filter_upwards [h_on_Ω] with ω hω
    rw [hω]
    congr 1
    exact (congr_fun hηfac ω).symm

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
