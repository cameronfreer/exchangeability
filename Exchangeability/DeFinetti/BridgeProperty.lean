/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Exchangeability.DeFinetti.ViaMartingale.FiniteProduct
import Exchangeability.Probability.MeasureKernels
import Exchangeability.Util.StrictMono

/-!
# Bridge Property: Product Formula for Indicators

This file provides the **bridge property** used by CommonEnding to complete
the de Finetti proof. It converts the measure equality from ViaMartingale's
`finite_product_formula` to the integral equality form needed by
`CommonEnding.conditional_iid_from_directing_measure`.

## Main results

* `indicator_product_bridge_strictMono`: Bridge property for strictly monotone selections
* `indicator_product_bridge`: Bridge property for injective selections (main result)

## Architecture

This is shared infrastructure used by both:
- **ViaL2**: via `MoreL2Helpers.directing_measure_bridge`
- **ViaMartingale**: directly via `finite_product_formula`

The proof uses:
1. ViaMartingale's `finite_product_formula` for the measure equality
2. Conversion from measure equality to integral equality on rectangles
3. Extension from strictly monotone to injective via permutation

## References

* Kallenberg (2005), *Probabilistic Symmetries and Invariance Principles*,
  Theorem 1.1 (pages 26-28)
-/

noncomputable section
open scoped BigOperators MeasureTheory Topology
open MeasureTheory Set

namespace Exchangeability.DeFinetti

open ViaMartingale

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-! ### Converting measure equality to integral equality -/

/-- Convert measure equality on rectangles to integral equality for products of indicators.

This is the key bridge between ViaMartingale's measure-theoretic formulation
and CommonEnding's integral formulation.

Given `Measure.map (fun ω => fun i => X (k i) ω) μ = μ.bind (fun ω => Measure.pi ν)`,
applying both sides to the rectangle `∏ᵢ Bᵢ` and using:
- LHS: `μ (preimage) = ∫⁻ ∏ᵢ 1_{Bᵢ}(X (k i) ω) ∂μ`
- RHS: `∫⁻ (Measure.pi ν)(rectangle) ∂μ = ∫⁻ ∏ᵢ ν ω (Bᵢ) ∂μ`

gives the desired integral equality. -/
@[nolint unusedArguments]
lemma measure_eq_implies_lintegral_prod_eq
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (ν : Ω → Measure α) [∀ ω, IsProbabilityMeasure (ν ω)]
    (hν_meas : ∀ B : Set α, MeasurableSet B → Measurable (fun ω => ν ω B))
    (X : ℕ → Ω → α) (hX_meas : ∀ n, Measurable (X n))
    {m : ℕ} (k : Fin m → ℕ)
    (h_measure_eq : Measure.map (fun ω => fun i : Fin m => X (k i) ω) μ
        = μ.bind (fun ω => Measure.pi fun _ : Fin m => ν ω))
    (B : Fin m → Set α) (hB : ∀ i, MeasurableSet (B i)) :
    ∫⁻ ω, ∏ i : Fin m,
        ENNReal.ofReal ((B i).indicator (fun _ => (1 : ℝ)) (X (k i) ω)) ∂μ
      = ∫⁻ ω, ∏ i : Fin m, ν ω (B i) ∂μ := by
  -- The rectangle S = univ.pi B is measurable
  let S := univ.pi B
  have hS : MeasurableSet S := MeasurableSet.univ_pi hB

  -- Preimage characterization
  have hpre : (fun ω => fun i : Fin m => X (k i) ω) ⁻¹' S = ⋂ i : Fin m, (X (k i)) ⁻¹' (B i) := by
    ext ω; simp only [S, mem_preimage, mem_pi, mem_univ, true_implies, mem_iInter]

  -- Measurability of preimage
  have hpre_meas : MeasurableSet (⋂ i : Fin m, (X (k i)) ⁻¹' (B i)) :=
    .iInter fun i => hX_meas (k i) (hB i)

  -- Measurability of the mapping function
  have hf_meas : Measurable (fun ω => fun i : Fin m => X (k i) ω) := by
    measurability

  -- Characterization: ω in preimage ↔ ∀ i, X (k i) ω ∈ B i
  have hpre_mem : ∀ ω, ω ∈ ⋂ i : Fin m, (X (k i)) ⁻¹' (B i) ↔ ∀ i, X (k i) ω ∈ B i := by
    intro ω; simp only [mem_iInter, mem_preimage]

  -- LHS: Compute map measure on the rectangle S
  have hL : (Measure.map (fun ω => fun i : Fin m => X (k i) ω) μ) S
      = ∫⁻ ω, ∏ i : Fin m,
          ENNReal.ofReal ((B i).indicator (fun _ => (1 : ℝ)) (X (k i) ω)) ∂μ := by
    rw [Measure.map_apply hf_meas hS, hpre]
    -- Convert measure to lintegral of product indicator
    rw [← lintegral_indicator_one hpre_meas]
    congr 1; funext ω
    -- Product of indicators equals indicator of intersection
    by_cases h : ω ∈ ⋂ i : Fin m, (X (k i)) ⁻¹' (B i)
    · -- ω is in all preimages, so all factors are 1
      rw [indicator_of_mem h]
      rw [hpre_mem] at h
      have hprod : (∏ i : Fin m, ENNReal.ofReal ((B i).indicator (fun _ => (1 : ℝ)) (X (k i) ω)))
          = 1 := by
        apply Finset.prod_eq_one
        intro i _
        rw [indicator_of_mem (h i), ENNReal.ofReal_one]
      simp only [hprod, Pi.one_apply]
    · -- ω is not in some preimage, so at least one factor is 0
      rw [indicator_of_notMem h]
      rw [hpre_mem] at h; push Not at h
      obtain ⟨i, hi⟩ := h
      rw [Finset.prod_eq_zero (i := i) (hi := Finset.mem_univ i)]
      simp only [indicator_of_notMem hi, ENNReal.ofReal_zero]

  -- RHS: Compute bind measure on the rectangle S
  -- bind_apply: (μ.bind f) S = ∫⁻ ω, f ω S ∂μ
  have hR : (μ.bind (fun ω => Measure.pi fun _ : Fin m => ν ω)) S
      = ∫⁻ ω, ∏ i : Fin m, ν ω (B i) ∂μ := by
    -- Use aemeasurable_measure_pi from MeasureKernels.lean
    have h_ae_meas : AEMeasurable (fun ω => Measure.pi fun _ : Fin m => ν ω) μ :=
      aemeasurable_measure_pi ν (fun ω => inferInstance) hν_meas
    rw [Measure.bind_apply hS h_ae_meas]
    congr 1; funext ω
    -- Measure.pi on a rectangle is the product
    rw [Measure.pi_pi (fun _ => ν ω) B]

  -- Combine: LHS = (map μ) S = (bind μ) S = RHS
  calc ∫⁻ ω, ∏ i : Fin m,
          ENNReal.ofReal ((B i).indicator (fun _ => (1 : ℝ)) (X (k i) ω)) ∂μ
      = (Measure.map (fun ω => fun i : Fin m => X (k i) ω) μ) S := hL.symm
    _ = (μ.bind (fun ω => Measure.pi fun _ : Fin m => ν ω)) S := by rw [h_measure_eq]
    _ = ∫⁻ ω, ∏ i : Fin m, ν ω (B i) ∂μ := hR

/-- **Bridge property for strictly monotone selections.**

This converts ViaMartingale's `finite_product_formula` to the integral form. -/
lemma indicator_product_bridge_strictMono
    [StandardBorelSpace Ω]
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → α)
    (hX : Contractable μ X)
    (hX_meas : ∀ n, Measurable (X n))
    (ν : Ω → Measure α)
    (hν_prob : ∀ ω, IsProbabilityMeasure (ν ω))
    (hν_meas : ∀ B : Set α, MeasurableSet B → Measurable (fun ω => ν ω B))
    (hν_law : ∀ n B, MeasurableSet B →
        (fun ω => (ν ω B).toReal) =ᵐ[μ] μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ (X n) | tailSigma X])
    {m : ℕ} (k : Fin m → ℕ) (hk : StrictMono k)
    (B : Fin m → Set α) (hB : ∀ i, MeasurableSet (B i)) :
    ∫⁻ ω, ∏ i : Fin m,
        ENNReal.ofReal ((B i).indicator (fun _ => (1 : ℝ)) (X (k i) ω)) ∂μ
      = ∫⁻ ω, ∏ i : Fin m, ν ω (B i) ∂μ := by
  haveI : ∀ ω, IsProbabilityMeasure (ν ω) := hν_prob
  -- Use finite_product_formula to get measure equality
  have h_measure_eq := finite_product_formula X hX hX_meas ν hν_prob hν_meas hν_law m k hk
  -- Convert to integral form
  exact measure_eq_implies_lintegral_prod_eq ν hν_meas X hX_meas k h_measure_eq B hB

/-- **Bridge property for injective selections.**

For any injective k : Fin m → ℕ, the integral of the product of indicators equals
the integral of the product of directing measure evaluations.

This is the main result used by `CommonEnding.conditional_iid_from_directing_measure`. -/
lemma indicator_product_bridge
    [StandardBorelSpace Ω]
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → α)
    (hX : Contractable μ X)
    (hX_meas : ∀ n, Measurable (X n))
    (ν : Ω → Measure α)
    (hν_prob : ∀ ω, IsProbabilityMeasure (ν ω))
    (hν_meas : ∀ B : Set α, MeasurableSet B → Measurable (fun ω => ν ω B))
    (hν_law : ∀ n B, MeasurableSet B →
        (fun ω => (ν ω B).toReal) =ᵐ[μ] μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ (X n) | tailSigma X])
    {m : ℕ} (k : Fin m → ℕ) (hk : Function.Injective k)
    (B : Fin m → Set α) (hB : ∀ i, MeasurableSet (B i)) :
    ∫⁻ ω, ∏ i : Fin m,
        ENNReal.ofReal ((B i).indicator (fun _ => (1 : ℝ)) (X (k i) ω)) ∂μ
      = ∫⁻ ω, ∏ i : Fin m, ν ω (B i) ∂μ := by
  -- Use injective_implies_strictMono_perm to get permutation σ with k ∘ σ strictly monotone
  obtain ⟨σ, hρ_mono⟩ := Util.StrictMono.injective_implies_strictMono_perm k hk
  let ρ := k ∘ σ
  -- Reindex both sides using σ
  -- LHS: ∏ᵢ 1_{Bᵢ}(X_{k(i)}) = ∏ⱼ 1_{B_{σ⁻¹(j)}}(X_{ρ(j)}) after reindexing by σ⁻¹
  -- But products are permutation-invariant, so ∏ᵢ f(i) = ∏ᵢ f(σ(i))
  have hL : ∫⁻ ω, ∏ i : Fin m,
        ENNReal.ofReal ((B i).indicator (fun _ => (1 : ℝ)) (X (k i) ω)) ∂μ
      = ∫⁻ ω, ∏ j : Fin m,
        ENNReal.ofReal ((B (σ j)).indicator (fun _ => (1 : ℝ)) (X (ρ j) ω)) ∂μ := by
    congr 1; funext ω
    -- ∏ᵢ f(σ i) = ∏ᵢ f(i) by Equiv.Perm.prod_comp (applied symmetrically)
    symm
    have hsup : {a : Fin m | σ a ≠ a} ⊆ (Finset.univ : Finset (Fin m)) := by
      simp only [Finset.coe_univ, Set.subset_univ]
    exact Equiv.Perm.prod_comp σ Finset.univ
      (fun j => ENNReal.ofReal ((B j).indicator (fun _ => (1 : ℝ)) (X (k j) ω))) hsup

  have hR : ∫⁻ ω, ∏ i : Fin m, ν ω (B i) ∂μ
      = ∫⁻ ω, ∏ j : Fin m, ν ω (B (σ j)) ∂μ := by
    congr 1; funext ω
    symm
    have hsup : {a : Fin m | σ a ≠ a} ⊆ (Finset.univ : Finset (Fin m)) := by
      simp only [Finset.coe_univ, Set.subset_univ]
    exact Equiv.Perm.prod_comp σ Finset.univ (fun j => ν ω (B j)) hsup

  -- Now use the strictly monotone case with reindexed B
  rw [hL, hR]
  let B' := B ∘ σ
  have hB' : ∀ i, MeasurableSet (B' i) := fun i => hB (σ i)
  exact indicator_product_bridge_strictMono X hX hX_meas ν hν_prob hν_meas hν_law ρ hρ_mono B' hB'

end Exchangeability.DeFinetti
