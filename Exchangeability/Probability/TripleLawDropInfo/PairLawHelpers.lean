/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer, Claude (Anthropic)
-/
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Function.FactorsThrough
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Exchangeability.Probability.CondExpBasic

/-!
# Helper Lemmas for RN-Derivative Approach to Kallenberg 1.3

This file provides helper lemmas for the Radon-Nikodym derivative approach to
Kallenberg Lemma 1.3 (contraction-independence).

## Main results

* `marginal_law_eq_of_pair_law`: From `(X,W) =^d (X,W')`, extract `W =^d W'`
* `joint_measure_eq_of_pair_law`: Restricted measure equality from pair law
* `integral_sq_condExp_eq_of_pair_law`: Square integrals equal via Doob-Dynkin

## References

* Kallenberg (2005), *Probabilistic Symmetries and Invariance Principles*, Lemma 1.3
-/

open MeasureTheory MeasurableSpace
open scoped ENNReal Classical

variable {Ω α γ : Type*}
variable [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace γ]

/-- From pair law equality `(X,W) =^d (X,W')`, extract marginal law equality `W =^d W'`. -/
lemma marginal_law_eq_of_pair_law
    {μ : Measure Ω}
    (X : Ω → α) (W W' : Ω → γ)
    (hX : Measurable X) (hW : Measurable W) (hW' : Measurable W')
    (h_law : Measure.map (fun ω => (X ω, W ω)) μ = Measure.map (fun ω => (X ω, W' ω)) μ) :
    Measure.map W μ = Measure.map W' μ := by
  have h1 : Measure.map W μ = Measure.map Prod.snd (Measure.map (fun ω => (X ω, W ω)) μ) := by
    rw [Measure.map_map measurable_snd (hX.prodMk hW)]; rfl
  have h2 : Measure.map W' μ = Measure.map Prod.snd (Measure.map (fun ω => (X ω, W' ω)) μ) := by
    rw [Measure.map_map measurable_snd (hX.prodMk hW')]; rfl
  rw [h1, h_law, ← h2]

/-- From pair law equality, derive joint measure equality on the conditioning space.

If `(X,W) =^d (X,W')`, then `map W (μ.restrict (X ⁻¹' A)) = map W' (μ.restrict (X ⁻¹' A))`.

Intuitively: "the law of W restricted to {X ∈ A}" equals "the law of W' restricted to {X ∈ A}". -/
lemma joint_measure_eq_of_pair_law
    {μ : Measure Ω}
    (X : Ω → α) (W W' : Ω → γ)
    (hX : Measurable X) (hW : Measurable W) (hW' : Measurable W')
    (h_law : Measure.map (fun ω => (X ω, W ω)) μ = Measure.map (fun ω => (X ω, W' ω)) μ)
    {A : Set α} (hA : MeasurableSet A) :
    Measure.map W (μ.restrict (X ⁻¹' A)) = Measure.map W' (μ.restrict (X ⁻¹' A)) := by
  ext B hB
  -- ν(B) = μ((X ⁻¹' A) ∩ (W ⁻¹' B)) = law(X,W)(A ×ˢ B)
  rw [Measure.map_apply hW hB, Measure.map_apply hW' hB]
  rw [Measure.restrict_apply (hW hB), Measure.restrict_apply (hW' hB)]
  -- Note: restrict_apply gives (W ⁻¹' B) ∩ (X ⁻¹' A), so use commutativity
  rw [Set.inter_comm (W ⁻¹' B), Set.inter_comm (W' ⁻¹' B)]
  -- Show both equal (map (X,W) μ)(A ×ˢ B)
  have h1 : (X ⁻¹' A) ∩ (W ⁻¹' B) = (fun ω => (X ω, W ω)) ⁻¹' (A ×ˢ B) := by
    ext ω; simp [Set.mem_prod]
  have h2 : (X ⁻¹' A) ∩ (W' ⁻¹' B) = (fun ω => (X ω, W' ω)) ⁻¹' (A ×ˢ B) := by
    ext ω; simp [Set.mem_prod]
  rw [h1, h2]
  rw [← Measure.map_apply (hX.prodMk hW) (hA.prod hB)]
  rw [← Measure.map_apply (hX.prodMk hW') (hA.prod hB)]
  rw [h_law]

/-- Helper for Kallenberg 1.3: Square integrals are equal via Doob-Dynkin factorization.

Given:
- `(X,W) =^d (X,W')` (pair laws equal, hence ρ = law(W) = law(W'))
- `μ₁ = E[φ|σ(W)]` and `μ₂ = E[φ|σ(W')]` where φ = 1_{X∈A}

This lemma proves `∫ μ₁² dμ = ∫ μ₂² dμ` using:
1. Doob-Dynkin: μ₁ = g₁ ∘ W, μ₂ = g₂ ∘ W' for measurable g₁, g₂
2. Set-integral uniqueness: g₁ = g₂ ρ-a.e.
3. Change of variables: ∫ μ₁² dμ = ∫ g₁² dρ = ∫ g₂² dρ = ∫ μ₂² dμ
-/
lemma integral_sq_condExp_eq_of_pair_law
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : Ω → α) (W W' : Ω → γ)
    (hX : Measurable X) (hW : Measurable W) (hW' : Measurable W')
    (h_law : Measure.map (fun ω => (X ω, W ω)) μ
           = Measure.map (fun ω => (X ω, W' ω)) μ)
    {A : Set α} (hA : MeasurableSet A) :
    ∫ ω, (μ[Set.indicator (X ⁻¹' A) (fun _ => (1 : ℝ)) | MeasurableSpace.comap W inferInstance]) ω
       * (μ[Set.indicator (X ⁻¹' A) (fun _ => (1 : ℝ)) | MeasurableSpace.comap W inferInstance]) ω ∂μ
    = ∫ ω, (μ[Set.indicator (X ⁻¹' A) (fun _ => (1 : ℝ)) | MeasurableSpace.comap W' inferInstance]) ω
         * (μ[Set.indicator (X ⁻¹' A) (fun _ => (1 : ℝ)) | MeasurableSpace.comap W' inferInstance]) ω ∂μ := by
  -- Get law equality FIRST, before introducing any local MeasurableSpace aliases
  have hρ_eq : Measure.map W μ = Measure.map W' μ :=
    marginal_law_eq_of_pair_law X W W' hX hW hW' h_law

  -- Abbreviations (NOT MeasurableSpace, just functions and condExp)
  let φ : Ω → ℝ := Set.indicator (X ⁻¹' A) (fun _ => (1 : ℝ))
  let μ₁ : Ω → ℝ := μ[φ | MeasurableSpace.comap W inferInstance]
  let μ₂ : Ω → ℝ := μ[φ | MeasurableSpace.comap W' inferInstance]

  -- σ-algebra relationships (using local abbreviations for readability)
  have hmW_le : MeasurableSpace.comap W inferInstance ≤ ‹MeasurableSpace Ω› :=
    measurable_iff_comap_le.mp hW
  have hmW'_le : MeasurableSpace.comap W' inferInstance ≤ ‹MeasurableSpace Ω› :=
    measurable_iff_comap_le.mp hW'

  -- Integrability of indicator
  have hφ_int : Integrable φ μ := Integrable.indicator (integrable_const 1) (hX hA)

  -- Doob-Dynkin factorization: μ₁ = g₁ ∘ W and μ₂ = g₂ ∘ W'
  have hμ₁_sm : StronglyMeasurable[MeasurableSpace.comap W inferInstance] μ₁ :=
    stronglyMeasurable_condExp
  obtain ⟨g₁, hg₁_sm, hμ₁_eq⟩ := hμ₁_sm.exists_eq_measurable_comp
  have hμ₂_sm : StronglyMeasurable[MeasurableSpace.comap W' inferInstance] μ₂ :=
    stronglyMeasurable_condExp
  obtain ⟨g₂, hg₂_sm, hμ₂_eq⟩ := hμ₂_sm.exists_eq_measurable_comp

  -- Integrability of g₁, g₂ on ρ = map W μ
  have hg₁_int : Integrable g₁ (Measure.map W μ) := by
    have h : Integrable (g₁ ∘ W) μ := by
      have : μ₁ = g₁ ∘ W := hμ₁_eq
      rw [← this]; exact integrable_condExp
    exact (integrable_map_measure hg₁_sm.aestronglyMeasurable hW.aemeasurable).mpr h
  have hg₂_int : Integrable g₂ (Measure.map W' μ) := by
    have h : Integrable (g₂ ∘ W') μ := by
      have : μ₂ = g₂ ∘ W' := hμ₂_eq
      rw [← this]; exact integrable_condExp
    exact (integrable_map_measure hg₂_sm.aestronglyMeasurable hW'.aemeasurable).mpr h
  have hg₂_int' : Integrable g₂ (Measure.map W μ) := by rw [hρ_eq]; exact hg₂_int

  -- Key: g₁ = g₂ ρ-a.e. via set-integral characterization
  have hg_eq : g₁ =ᵐ[Measure.map W μ] g₂ := by
    apply Integrable.ae_eq_of_forall_setIntegral_eq g₁ g₂ hg₁_int hg₂_int'
    intro B hB _
    -- ∫_B g₁ dρ = ∫_{W⁻¹B} φ dμ (change of variables + condExp property)
    have h1 : ∫ y in B, g₁ y ∂(Measure.map W μ) = ∫ ω in W ⁻¹' B, φ ω ∂μ := by
      -- Use restrict_map: (map W μ).restrict B = (μ.restrict (W ⁻¹' B)).map W
      have h_remap : (Measure.map W μ).restrict B = (μ.restrict (W ⁻¹' B)).map W :=
        Measure.restrict_map hW hB
      -- Set integral ∫_B g dν = ∫ g d(ν.restrict B), so rewrite the measure
      calc ∫ y in B, g₁ y ∂(Measure.map W μ)
          = ∫ y, g₁ y ∂((Measure.map W μ).restrict B) := rfl
        _ = ∫ y, g₁ y ∂((μ.restrict (W ⁻¹' B)).map W) := by rw [h_remap]
        _ = ∫ ω, g₁ (W ω) ∂(μ.restrict (W ⁻¹' B)) := by
              apply integral_map hW.aemeasurable.restrict hg₁_sm.aestronglyMeasurable
        _ = ∫ ω in W ⁻¹' B, g₁ (W ω) ∂μ := rfl
        _ = ∫ ω in W ⁻¹' B, μ₁ ω ∂μ := by
              apply setIntegral_congr_fun (hW hB)
              intro ω _; exact (congrFun hμ₁_eq ω).symm
        _ = ∫ ω in W ⁻¹' B, φ ω ∂μ := by
              apply setIntegral_condExp hmW_le hφ_int
              exact measurableSet_comap.mpr ⟨B, hB, rfl⟩
    -- ∫_B g₂ dρ = ∫_{W'⁻¹B} φ dμ (similarly, using ρ = ρ')
    have h2 : ∫ y in B, g₂ y ∂(Measure.map W μ) = ∫ ω in W' ⁻¹' B, φ ω ∂μ := by
      rw [hρ_eq]
      have h_remap : (Measure.map W' μ).restrict B = (μ.restrict (W' ⁻¹' B)).map W' :=
        Measure.restrict_map hW' hB
      calc ∫ y in B, g₂ y ∂(Measure.map W' μ)
          = ∫ y, g₂ y ∂((Measure.map W' μ).restrict B) := rfl
        _ = ∫ y, g₂ y ∂((μ.restrict (W' ⁻¹' B)).map W') := by rw [h_remap]
        _ = ∫ ω, g₂ (W' ω) ∂(μ.restrict (W' ⁻¹' B)) := by
              apply integral_map hW'.aemeasurable.restrict hg₂_sm.aestronglyMeasurable
        _ = ∫ ω in W' ⁻¹' B, g₂ (W' ω) ∂μ := rfl
        _ = ∫ ω in W' ⁻¹' B, μ₂ ω ∂μ := by
              apply setIntegral_congr_fun (hW' hB)
              intro ω _; exact (congrFun hμ₂_eq ω).symm
        _ = ∫ ω in W' ⁻¹' B, φ ω ∂μ := by
              apply setIntegral_condExp hmW'_le hφ_int
              exact measurableSet_comap.mpr ⟨B, hB, rfl⟩
    -- By pair law: ∫_{W⁻¹B} φ dμ = ∫_{W'⁻¹B} φ dμ
    have h3 : ∫ ω in W ⁻¹' B, φ ω ∂μ = ∫ ω in W' ⁻¹' B, φ ω ∂μ := by
      rw [setIntegral_indicator (hX hA), setIntegral_indicator (hX hA)]
      rw [setIntegral_const, setIntegral_const]
      congr 1
      rw [Set.inter_comm (W ⁻¹' B), Set.inter_comm (W' ⁻¹' B)]
      have heq1 : (X ⁻¹' A) ∩ (W ⁻¹' B) = (fun ω => (X ω, W ω)) ⁻¹' (A ×ˢ B) := by
        ext ω; simp [Set.mem_prod]
      have heq2 : (X ⁻¹' A) ∩ (W' ⁻¹' B) = (fun ω => (X ω, W' ω)) ⁻¹' (A ×ˢ B) := by
        ext ω; simp [Set.mem_prod]
      rw [heq1, heq2]
      have h_meas1 : μ ((fun ω => (X ω, W ω)) ⁻¹' (A ×ˢ B))
                   = (Measure.map (fun ω => (X ω, W ω)) μ) (A ×ˢ B) :=
        (Measure.map_apply (hX.prodMk hW) (hA.prod hB)).symm
      have h_meas2 : μ ((fun ω => (X ω, W' ω)) ⁻¹' (A ×ˢ B))
                   = (Measure.map (fun ω => (X ω, W' ω)) μ) (A ×ˢ B) :=
        (Measure.map_apply (hX.prodMk hW') (hA.prod hB)).symm
      simp only [Measure.real, ENNReal.toReal_eq_toReal_iff]
      left
      rw [h_meas1, h_meas2, h_law]
    rw [h1, h3, ← h2]

  -- Push squares through integral_map
  have calc1 : ∫ ω, μ₁ ω * μ₁ ω ∂μ = ∫ ω, (g₁ (W ω))^2 ∂μ := by
    apply integral_congr_ae
    filter_upwards with ω
    simp only [μ₁, hμ₁_eq, Function.comp_apply, sq]
  have calc2 : ∫ ω, (g₁ (W ω))^2 ∂μ = ∫ y, (g₁ y)^2 ∂(Measure.map W μ) := by
    symm; apply integral_map hW.aemeasurable
    exact (hg₁_sm.pow 2).aestronglyMeasurable
  have calc3 : ∫ y, (g₁ y)^2 ∂(Measure.map W μ) = ∫ y, (g₂ y)^2 ∂(Measure.map W μ) := by
    apply integral_congr_ae
    filter_upwards [hg_eq] with y hy; rw [hy]
  have calc4 : ∫ y, (g₂ y)^2 ∂(Measure.map W μ) = ∫ ω, (g₂ (W' ω))^2 ∂μ := by
    rw [hρ_eq]; apply integral_map hW'.aemeasurable
    exact (hg₂_sm.pow 2).aestronglyMeasurable
  have calc5 : ∫ ω, (g₂ (W' ω))^2 ∂μ = ∫ ω, μ₂ ω * μ₂ ω ∂μ := by
    apply integral_congr_ae
    filter_upwards with ω
    simp only [μ₂, hμ₂_eq, Function.comp_apply, sq]
  rw [calc1, calc2, calc3, calc4, calc5]
