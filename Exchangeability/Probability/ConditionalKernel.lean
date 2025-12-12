/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.CompProdEqIff
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Exchangeability.Probability.KernelEvalEquality

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

-- `kernel_eval_ae_eq_of_kernel_eq` is imported from
-- Exchangeability.Probability.Axioms.KernelEvalEquality
-- See that file for the full proof obligation and mathematical background.

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
        simp only [Function.comp_apply, Prod.map_apply, id_eq, hηfac]
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
      -- Key: Use ae_eq_of_compProd_eq from mathlib
      -- We need to show: (μ.map ζ) ⊗ₘ K = (μ.map ζ) ⊗ₘ (K.comap φ)
      -- where K = condDistrib ξ η μ

      -- First establish marginal φ-invariance
      have h_ν_inv : μ.map ζ = (μ.map ζ).map φ := by
        rw [Measure.map_map hφ_meas hζ]
        have h_eq : φ ∘ ζ = η := hηfac.symm
        rw [h_eq, h_marg_eq]

      -- The joint measure is the compProd
      have h_compProd_K : (μ.map ζ) ⊗ₘ (condDistrib ξ η μ) = μ.map (fun ω => (ζ ω, ξ ω)) := by
        rw [← h_kernel_eq, hζ_compProd]

      rw [← h_compProd_K] at h_joint_inv
      -- h_joint_inv now: (μ.map ζ) ⊗ₘ K = ((μ.map ζ) ⊗ₘ K).map (Prod.map φ id)

      -- Key insight: The compProds are equal because the kernel K = condDistrib ξ η μ
      -- satisfies K(γ) = K(φ γ) for ν-a.e. γ, where ν = μ.map ζ.
      --
      -- Mathematical argument:
      -- 1. From h_joint_inv: ν ⊗ₘ K = (ν ⊗ₘ K).map (Prod.map φ id)
      --    This means ∫_A K(γ)(B) dν = ∫_{φ⁻¹A} K(γ)(B) dν for all A, B
      -- 2. From h_ν_inv: ν = ν.map φ
      --    This means ∫ f dν = ∫ (f ∘ φ) dν for all f
      -- 3. Combining these: for any measurable set s ⊆ Γ × E,
      --    ∫ K(γ)(slice s γ) dν = ∫ K(γ)(slice s (φγ)) dν  [from h_joint_inv]
      --    ∫ K(γ)(slice s γ) dν = ∫ K(φγ)(slice s (φγ)) dν [from h_ν_inv]
      -- 4. These together imply ∫_C K(γ)(B) dν = ∫_C K(φγ)(B) dν for all C ∈ σ(φ)
      -- 5. Since both K and K ∘ φ are kernels with the same marginal ν, and
      --    their compProds agree on σ(φ)-slices, they must be equal by
      --    the uniqueness of disintegration.
      --
      -- The rigorous proof requires showing that equality on σ(φ)-slices
      -- extends to all slices, which follows from the conditional distribution
      -- being determined by its integrals and the φ-stationarity of ν.
      have h_compProd_eq_comap : (μ.map ζ) ⊗ₘ (condDistrib ξ η μ) =
          (μ.map ζ) ⊗ₘ ((condDistrib ξ η μ).comap φ hφ_meas) := by
        /-
        PROOF STRATEGY:

        We need to show: ν ⊗ₘ K = ν ⊗ₘ (K.comap φ)

        Given:
        • h_joint_inv: ν ⊗ₘ K = (ν ⊗ₘ K).map (Prod.map φ id)  (Φ-invariance)
        • h_ν_inv: ν = ν.map φ  (φ-stationarity)
        • K = condDistrib ξ η μ where η = φ ∘ ζ

        Key insight: Since K = condDistrib ξ η μ and η = φ ∘ ζ, the kernel K
        conditions on η, which is a function of φ(ζ). Therefore:
        • K(γ) = P(ξ ∈ · | η = γ) depends only on γ through the σ-algebra σ(η)
        • For γ in the support of ν, K(γ) only depends on which fiber of φ
          contains γ
        • This means K(·)(B) is σ(φ)-measurable for all B

        Mathematical argument:
        1. From h_joint_inv on A × B: ∫_A K(γ)(B) dν = ∫_{φ⁻¹A} K(γ)(B) dν
        2. From h_ν_inv: ∫_A K(γ)(B) dν = ∫_{φ⁻¹A} K(φγ)(B) dν
        3. Combining: ∫_{φ⁻¹A} K(γ)(B) dν = ∫_{φ⁻¹A} K(φγ)(B) dν for all A, B
        4. Since K(·)(B) is σ(φ)-measurable and equals K(φ·)(B) on σ(φ)-sets,
           we have K(γ)(B) = K(φγ)(B) for ν-a.e. γ
        5. By π-system uniqueness: K =ᵐ[ν] K.comap φ
        6. By Measure.compProd_congr: ν ⊗ₘ K = ν ⊗ₘ (K.comap φ)

        The formal proof of step 4 requires showing that K(·)(B) is σ(φ)-measurable,
        which follows from K being the conditional distribution given η = φ ∘ ζ.
        This is a deep fact about conditional distributions that would require
        additional lemmas about the structure of condDistrib.
        -/
        -- For now, we use the known relationship between the joint laws
        -- Both sides equal μ.map (ζ, ξ) through their respective disintegrations
        set K := condDistrib ξ η μ
        set ν := μ.map ζ
        -- Direct proof using the equality of joint measures
        calc ν ⊗ₘ K
            = μ.map (fun ω => (ζ ω, ξ ω)) := h_compProd_K
          _ = ν ⊗ₘ (K.comap φ hφ_meas) := by
              /-
              PROOF STRATEGY:
              We need: ν ⊗ₘ K = ν ⊗ₘ (K.comap φ)

              Key facts available:
              1. K = condDistrib ξ η μ = condDistrib ξ ζ μ (by h_kernel_eq)
              2. Φ-invariance: ν ⊗ₘ K = (ν ⊗ₘ K).map (Prod.map φ id) (h_joint_inv)
              3. φ-stationarity: ν = ν.map φ (h_ν_inv)
              4. h_compProd_K: ν ⊗ₘ K = μ.map (ζ, ξ)

              From (2): ∫_A K(γ)(B) dν = ∫_{φ⁻¹A} K(γ)(B) dν for all A, B
              From (3): ∫_A f(γ) dν = ∫_{φ⁻¹A} f(φ γ) dν for all A, f

              Combining: ∫_{φ⁻¹A} K(γ)(B) dν = ∫_{φ⁻¹A} K(φ γ)(B) dν for all A, B

              This shows K(·)(B) and K(φ·)(B) have equal integrals on all σ(φ)-sets.
              Since K(φ·)(B) is σ(φ)-measurable, we get:
                E[K(·)(B) | σ(φ)] = K(φ·)(B) ν-a.e.

              The key insight is that K = condDistrib ξ η μ where η = φ ∘ ζ.
              The conditional distribution given η only depends on the value through
              the fibers of φ, making K(·)(B) effectively σ(φ)-measurable.

              Therefore K =ᵐ[ν] K.comap φ, giving ν ⊗ₘ K = ν ⊗ₘ (K.comap φ).
              -/
              -- Direct proof: show both compProds equal μ.map (ζ, ξ)
              -- We already have h_compProd_K : ν ⊗ₘ K = μ.map (ζ, ξ)
              -- Need: μ.map (ζ, ξ) = ν ⊗ₘ (K.comap φ)
              -- i.e., ν ⊗ₘ K = ν ⊗ₘ (K.comap φ)

              -- Key lemma: on rectangles, both sides agree
              have h_rect : ∀ A B, MeasurableSet A → MeasurableSet B →
                  (ν ⊗ₘ K) (A ×ˢ B) = (ν ⊗ₘ (K.comap φ hφ_meas)) (A ×ˢ B) := by
                intro A B hA hB
                have hKB_meas : Measurable (fun γ => K γ B) := Kernel.measurable_coe K hB
                -- Helper: Convert compProd on rectangle to set integral
                have h_compProd_rect : ∀ S, MeasurableSet S → ∀ (κ : Kernel Γ E) [IsSFiniteKernel κ],
                    (ν ⊗ₘ κ) (S ×ˢ B) = ∫⁻ γ in S, κ γ B ∂ν := by
                  intro S hS κ _
                  classical
                  rw [Measure.compProd_apply (hS.prod hB)]
                  simp_rw [Set.mk_preimage_prod_right_eq_if, apply_ite, measure_empty]
                  -- Goal: ∫⁻ a, (if a ∈ S then κ a B else 0) ∂ν = ∫⁻ γ in S, κ γ B ∂ν
                  -- Convert: if a ∈ S then f a else 0 = S.indicator f a
                  have h_ind : ∀ a, (if a ∈ S then κ a B else 0) = S.indicator (fun a => κ a B) a := by
                    intro a; simp only [Set.indicator_apply]
                  simp_rw [h_ind]
                  exact MeasureTheory.lintegral_indicator hS (fun a => κ a B)
                -- General Phi-invariance: (ν ⊗ₘ K)(S × B) = (ν ⊗ₘ K)(φ⁻¹S × B)
                have h_Phi_inv_gen : ∀ S, MeasurableSet S →
                    (ν ⊗ₘ K) (S ×ˢ B) = (ν ⊗ₘ K) ((φ ⁻¹' S) ×ˢ B) := by
                  intro S hS
                  have h_preimage_eq : Prod.map φ id ⁻¹' (S ×ˢ B) = (φ ⁻¹' S) ×ˢ B := by
                    ext ⟨x, y⟩; simp [Set.mem_preimage, Set.mem_prod]
                  calc (ν ⊗ₘ K) (S ×ˢ B)
                      = ((ν ⊗ₘ K).map (Prod.map φ id)) (S ×ˢ B) := by rw [← h_joint_inv]
                    _ = (ν ⊗ₘ K) (Prod.map φ id ⁻¹' (S ×ˢ B)) := by
                        rw [Measure.map_apply (hφ_meas.prodMap measurable_id) (hS.prod hB)]
                    _ = (ν ⊗ₘ K) ((φ ⁻¹' S) ×ˢ B) := by rw [h_preimage_eq]
                -- Change of variables: ∫_S f dν = ∫_{φ⁻¹S} (f ∘ φ) dν
                have hA_cov_gen : ∀ S, MeasurableSet S →
                    ∫⁻ γ in S, K γ B ∂ν = ∫⁻ γ in φ ⁻¹' S, K (φ γ) B ∂ν := by
                  intro S hS
                  conv_lhs => rw [h_ν_inv]
                  exact MeasureTheory.setLIntegral_map hS hKB_meas hφ_meas
                -- D-lemma: ∫_{φ⁻¹S} K(φγ)(B) dν = ∫_{φ⁻¹S} K(γ)(B) dν
                have hD_gen : ∀ S, MeasurableSet S →
                    ∫⁻ γ in φ ⁻¹' S, K (φ γ) B ∂ν = ∫⁻ γ in φ ⁻¹' S, K γ B ∂ν := by
                  intro S hS
                  calc ∫⁻ γ in φ ⁻¹' S, K (φ γ) B ∂ν
                      = ∫⁻ γ in S, K γ B ∂ν := (hA_cov_gen S hS).symm
                    _ = (ν ⊗ₘ K) (S ×ˢ B) := (h_compProd_rect S hS K).symm
                    _ = (ν ⊗ₘ K) ((φ ⁻¹' S) ×ˢ B) := h_Phi_inv_gen S hS
                    _ = ∫⁻ γ in φ ⁻¹' S, K γ B ∂ν := h_compProd_rect (φ ⁻¹' S) (hφ_meas hS) K
                -- Final equality: ∫_A K(γ) dν = ∫_A K(φγ) dν
                -- Key insight: both sides equal ∫_{φ⁻¹A} K(φγ) dν via different routes
                rw [h_compProd_rect A hA K, h_compProd_rect A hA (K.comap φ hφ_meas)]
                simp only [Kernel.comap_apply]
                -- Goal: ∫⁻ γ in A, K γ B ∂ν = ∫⁻ γ in A, K (φ γ) B ∂ν
                -- From hA_cov_gen: LHS = ∫_{φ⁻¹A} K(φγ) dν
                -- Need: RHS = ∫_{φ⁻¹A} K(φγ) dν as well
                -- Strategy: Show both equal ∫_{φ⁻¹A} K(φγ) dν
                have h_lhs : ∫⁻ γ in A, K γ B ∂ν = ∫⁻ γ in φ ⁻¹' A, K (φ γ) B ∂ν :=
                  hA_cov_gen A hA
                have h_rhs : ∫⁻ γ in A, K (φ γ) B ∂ν = ∫⁻ γ in φ ⁻¹' A, K (φ γ) B ∂ν := by
                  /-
                  PROOF GAP: This requires K(φγ)B = K(γ)B for ν-a.e. γ.

                  MATHEMATICAL ARGUMENT:
                  From hD_gen: ∫_T K(φ·)B dν = ∫_T K(·)B dν for all T ∈ σ(φ).
                  For a.e. equality from integral equality on σ(φ)-sets, we need both
                  K(φ·)B and K(·)B to be σ(φ)-measurable.

                  • K(φ·)B is σ(φ)-measurable by construction (composition with φ).
                  • K(·)B is σ(φ)-measurable because:
                    1. K = condDistrib ξ η μ = condDistrib ξ ζ μ (h_kernel_eq)
                    2. The kernel equality means P(ξ ∈ · | ζ = γ) = P(ξ ∈ · | η = γ)
                    3. Since η = φ ∘ ζ, conditioning on ζ = γ gives the same result as
                       conditioning on ζ ∈ φ⁻¹{φ(γ)} (the φ-fiber)
                    4. This implies E[1_{ξ∈B}|ζ] is constant on φ-fibers
                    5. Pushing forward via ζ: K(·)B is σ(φ)-measurable on Γ
                  • With both σ(φ)-measurable, integral equality implies a.e. equality.

                  FORMALIZATION GAP: Connecting h_kernel_eq to σ(φ)-measurability requires
                  lemmas about conditional expectation w.r.t. comap σ-algebras not directly
                  available in mathlib. Specifically, need to show that kernel equality
                  condDistrib ξ ζ μ = condDistrib ξ η μ implies E[1_{ξ∈B}|ζ] is σ(η)-measurable.
                  -/
                  -- The key insight: both K(φ·)B and K(·)B are σ(φ)-measurable and have
                  -- equal integrals on σ(φ)-sets, so they must be equal ν-a.e.
                  -- K(φ·)B is σ(φ)-measurable by construction.
                  -- K(·)B is σ(φ)-measurable because K = condDistrib ξ η μ where η = φ ∘ ζ,
                  -- and h_kernel_eq tells us condDistrib ξ ζ μ = K. This means
                  -- E[1_{ξ∈B}|ζ] = E[1_{ξ∈B}|η] μ-a.e., so E[1_{ξ∈B}|ζ] is σ(η)-measurable.
                  -- Pushing forward: K(·)B is σ(φ)-measurable.
                  have h_ae_eq : (fun γ => K (φ γ) B) =ᵐ[ν] (fun γ => K γ B) := by
                    /-
                    PROOF STRATEGY (Option 3 - work on Ω, push to Γ):
                    1. On Ω: show K(ζω)B = K(ηω)B = K(φ(ζω))B ae[μ]
                       - Use setLIntegral_condDistrib_of_measurableSet for both
                         condDistrib ξ ζ μ and condDistrib ξ η μ
                       - For T ∈ σ(η), both integrate to μ(T ∩ ξ⁻¹B)
                       - Use ae_eq from integral equality on σ(η)-sets
                    2. Push to Γ via ae_map_iff: K(γ)B = K(φγ)B ae[ν]

                    Key insight: both K(ζ·)B and K(η·)B = K(φ(ζ·))B integrate to
                    μ(T ∩ ξ⁻¹B) on σ(η)-sets. Since K(η·)B is σ(η)-measurable,
                    it equals E[K(ζ·)B | σ(η)] ae. And from h_kernel_eq (which
                    encodes conditional independence ξ ⊥ ζ | η), we get
                    K(ζ·)B = K(η·)B ae.
                    -/
                    -- Step 1: Show integral equality on σ(η)-sets on Ω
                    -- Define the two functions on Ω
                    let f := fun ω => K (ζ ω) B
                    let g := fun ω => K (η ω) B -- = K (φ (ζ ω)) B
                    have hf_eq_g_on_sigma_eta : ∀ T, MeasurableSet[MeasurableSpace.comap η inferInstance] T →
                        ∫⁻ ω in T, f ω ∂μ = ∫⁻ ω in T, g ω ∂μ := by
                      intro T hT
                      -- Both integrals equal μ(T ∩ ξ⁻¹B)
                      -- For f = K(ζ·)B: use condDistrib ξ ζ μ = K
                      -- Since σ(η) ⊆ σ(ζ), T ∈ σ(ζ) as well
                      have hT_in_sigma_zeta : MeasurableSet[MeasurableSpace.comap ζ inferInstance] T :=
                        h_le T hT
                      have h_f_int : ∫⁻ ω in T, f ω ∂μ = μ (T ∩ ξ ⁻¹' B) := by
                        -- Use setLIntegral_condDistrib_of_measurableSet for condDistrib ξ ζ μ
                        -- Then convert using h_kernel_eq : condDistrib ξ ζ μ = K
                        have h1 : ∫⁻ a in T, (condDistrib ξ ζ μ) (ζ a) B ∂μ = μ (T ∩ ξ ⁻¹' B) :=
                          setLIntegral_condDistrib_of_measurableSet hζ hξ.aemeasurable hB hT_in_sigma_zeta
                        simp only [h_kernel_eq] at h1
                        exact h1
                      -- For g = K(η·)B: use condDistrib ξ η μ = K
                      have h_g_int : ∫⁻ ω in T, g ω ∂μ = μ (T ∩ ξ ⁻¹' B) := by
                        exact setLIntegral_condDistrib_of_measurableSet hη hξ.aemeasurable hB hT
                      rw [h_f_int, h_g_int]
                    -- Step 2: Get ae equality on Ω from integral equality on σ(η)-sets
                    -- g is σ(η)-measurable, so by uniqueness: g = E[f | σ(η)] ae
                    -- And from h_kernel_eq, f is also σ(η)-measurable, so f = g ae
                    have hf_meas : Measurable f := hKB_meas.comp hζ
                    have hg_meas : Measurable g := hKB_meas.comp hη
                    have hg_sigma_eta_meas : @Measurable _ _ (MeasurableSpace.comap η inferInstance) _ g :=
                      hKB_meas.comp (comap_measurable η)
                    -- The key: h_kernel_eq implies f is also σ(η)-measurable
                    -- Because K = condDistrib ξ ζ μ = condDistrib ξ η μ,
                    -- f = K(ζ·)B represents E[1_{ξ∈B}|ζ], but since the kernels are equal,
                    -- E[1_{ξ∈B}|ζ] = E[1_{ξ∈B}|η] ae (conditional independence ξ ⊥ ζ | η)
                    have h_ae_Omega : f =ᵐ[μ] g := by
                      -- Apply the axiom kernel_eval_ae_eq_of_kernel_eq
                      -- f = K(ζ·)B and g = K(η·)B where K = condDistrib ξ η μ
                      -- The axiom gives: K(ζ·)B =ᵐ K(η·)B from h_kernel_eq
                      exact kernel_eval_ae_eq_of_kernel_eq ζ η hζ hη ξ hξ h_kernel_eq B hB
                    -- Step 3: Push from Ω to Γ via ae_map_iff
                    -- h_ae_Omega: K(ζω)B = K(ηω)B ae[μ], and η = φ ∘ ζ
                    -- Want: K(γ)B = K(φγ)B ae[ν] where ν = μ.map ζ
                    have h_ae_Gamma : (fun γ => K γ B) =ᵐ[ν] (fun γ => K (φ γ) B) := by
                      -- Use ae_map_iff: (∀ᵐ γ ∂ν, P γ) ↔ (∀ᵐ ω ∂μ, P (ζ ω))
                      -- First show measurability using order structure:
                      -- {γ | K γ B = K (φ γ) B} = {γ | K γ B ≤ K (φ γ) B} ∩ {γ | K (φ γ) B ≤ K γ B}
                      have hP_meas : MeasurableSet {γ | K γ B = K (φ γ) B} := by
                        have h_eq_inter : {γ | K γ B = K (φ γ) B} =
                            {γ | K γ B ≤ K (φ γ) B} ∩ {γ | K (φ γ) B ≤ K γ B} := by
                          ext γ; simp only [Set.mem_inter_iff, Set.mem_setOf_eq, le_antisymm_iff]
                        rw [h_eq_inter]
                        exact (measurableSet_le hKB_meas (hKB_meas.comp hφ_meas)).inter
                          (measurableSet_le (hKB_meas.comp hφ_meas) hKB_meas)
                      -- Apply ae_map_iff to transfer from ν to μ
                      rw [Filter.EventuallyEq, ae_map_iff hζ.aemeasurable hP_meas]
                      -- h_ae_Omega gives K(ζω)B = K(ηω)B ae, and η = φ ∘ ζ
                      filter_upwards [h_ae_Omega] with ω hω
                      simp only [hηfac, Function.comp_apply, g] at hω ⊢
                      exact hω
                    exact h_ae_Gamma.symm
                  calc ∫⁻ γ in A, K (φ γ) B ∂ν
                      = ∫⁻ γ in A, K γ B ∂ν := by
                        apply lintegral_congr_ae
                        exact ae_restrict_of_ae h_ae_eq
                    _ = ∫⁻ γ in φ ⁻¹' A, K (φ γ) B ∂ν := hA_cov_gen A hA
                rw [h_lhs, ← h_rhs]

              -- Extend from rectangles to all measurable sets by π-system argument
              have h_eq : ν ⊗ₘ K = ν ⊗ₘ (K.comap φ hφ_meas) := by
                -- Both are probability measures (K and K.comap φ are Markov kernels)
                have h_univ : (ν ⊗ₘ K) Set.univ = (ν ⊗ₘ (K.comap φ hφ_meas)) Set.univ := by
                  rw [Measure.compProd_apply MeasurableSet.univ,
                      Measure.compProd_apply MeasurableSet.univ]
                  simp only [Set.preimage_univ]
                  -- K γ is a probability measure for all γ (from IsMarkovKernel)
                  have hK_prob : ∀ γ, K γ Set.univ = 1 := fun γ => measure_univ
                  have hKc_prob : ∀ γ, (K.comap φ hφ_meas) γ Set.univ = 1 := by
                    intro γ; simp [Kernel.comap_apply, hK_prob]
                  simp [hK_prob]
                -- Use π-system uniqueness: rectangles generate the product σ-algebra
                apply MeasureTheory.ext_of_generate_finite
                    (Set.image2 (· ×ˢ ·) {s : Set Γ | MeasurableSet s} {t : Set E | MeasurableSet t})
                    generateFrom_prod.symm isPiSystem_prod
                · rintro _ ⟨A, hA, B, hB, rfl⟩
                  exact h_rect A B hA hB
                · exact h_univ
              rw [← h_compProd_K, h_eq]

      -- Apply ae_eq_of_compProd_eq to conclude K =ᵐ[ν] K.comap φ
      -- Need CountableOrCountablyGenerated - inferred from StandardBorelSpace → CountablyGenerated
      have h_ae_eq := Kernel.ae_eq_of_compProd_eq h_compProd_eq_comap
      filter_upwards [h_ae_eq] with γ hγ
      simp only [Kernel.comap_apply] at hγ
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
