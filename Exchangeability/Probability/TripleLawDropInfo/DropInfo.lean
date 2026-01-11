/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Exchangeability.Probability.TripleLawDropInfo.PairLawHelpers
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-!
# Kallenberg Lemma 1.3: Drop-Info Property via Contraction

This file implements **Kallenberg (2005), Lemma 1.3**, the "contraction-independence" lemma.

## Main Results

* `condExp_indicator_eq_of_law_eq_of_comap_le`: If `(X,W) =^d (X,W')` and `σ(W) ⊆ σ(W')`,
  then `E[1_{X∈A}|σ(W')] = E[1_{X∈A}|σ(W)]` a.e.

## Mathematical Background

**Kallenberg's Lemma 1.3 (Contraction-Independence):**

Given random elements ξ, η, ζ where:
1. `(ξ, η) =^d (ξ, ζ)` (pair laws match)
2. `σ(η) ⊆ σ(ζ)` (η is a *contraction* of ζ — i.e., η = f ∘ ζ for some measurable f)

**Conclusion:** `P[ξ ∈ B | ζ] = P[ξ ∈ B | η]` a.s.

The intuition: conditioning on the finer σ-algebra σ(ζ) gives the same result as
conditioning on the coarser σ-algebra σ(η), because the "extra" information in ζ
beyond η doesn't change the relationship with ξ (due to the pair law equality).

## References

* Kallenberg (2005), *Probabilistic Symmetries and Invariance Principles*, Lemma 1.3
-/

open MeasureTheory MeasurableSpace
open scoped ENNReal Classical

variable {Ω α γ : Type*}
variable [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace γ]

/-- **Kallenberg Lemma 1.3 (Contraction-Independence).**

If `(X,W) =^d (X,W')` (pair laws equal) and `σ(W) ⊆ σ(W')` (W is a contraction of W'),
then conditioning an indicator of X on σ(W') equals conditioning on σ(W).

This is the "drop information from finer to coarser σ-algebra" property.

**Proof:** L²/martingale argument.
1. Let μ₁ := E[φ|σ(W)] and μ₂ := E[φ|σ(W')] where φ = 1_{X∈A}
2. Tower: μ₁ = E[μ₂|σ(W)] (since σ(W) ≤ σ(W'))
3. Law equality: E[μ₁²] = E[μ₂²] (from pair law)
4. Compute: E[(μ₂-μ₁)²] = E[μ₂²] - 2E[μ₂μ₁] + E[μ₁²]
           = E[μ₂²] - 2E[E[μ₂|σ(W)]·μ₁] + E[μ₁²]  (tower)
           = E[μ₂²] - 2E[μ₁²] + E[μ₁²]
           = E[μ₂²] - E[μ₁²] = 0
5. So μ₂ = μ₁ a.e.
-/
lemma condExp_indicator_eq_of_law_eq_of_comap_le
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : Ω → α) (W W' : Ω → γ)
    (hX : Measurable X) (hW : Measurable W) (hW' : Measurable W')
    (h_law : Measure.map (fun ω => (X ω, W ω)) μ
           = Measure.map (fun ω => (X ω, W' ω)) μ)
    (h_le : MeasurableSpace.comap W inferInstance ≤ MeasurableSpace.comap W' inferInstance)
    {A : Set α} (hA : MeasurableSet A) :
    μ[Set.indicator (X ⁻¹' A) (fun _ => (1 : ℝ)) | MeasurableSpace.comap W' inferInstance]
      =ᵐ[μ]
    μ[Set.indicator (X ⁻¹' A) (fun _ => (1 : ℝ)) | MeasurableSpace.comap W inferInstance] := by
  -- Step 4b (moved up): Square equality E[μ₁²] = E[μ₂²]
  have h_sq_eq_raw : ∫ ω, (μ[Set.indicator (X ⁻¹' A) (fun _ => (1 : ℝ)) | MeasurableSpace.comap W inferInstance]) ω
                        * (μ[Set.indicator (X ⁻¹' A) (fun _ => (1 : ℝ)) | MeasurableSpace.comap W inferInstance]) ω ∂μ
                   = ∫ ω, (μ[Set.indicator (X ⁻¹' A) (fun _ => (1 : ℝ)) | MeasurableSpace.comap W' inferInstance]) ω
                        * (μ[Set.indicator (X ⁻¹' A) (fun _ => (1 : ℝ)) | MeasurableSpace.comap W' inferInstance]) ω ∂μ :=
    integral_sq_condExp_eq_of_pair_law X W W' hX hW hW' h_law hA

  have hρ_eq : Measure.map W μ = Measure.map W' μ :=
    marginal_law_eq_of_pair_law X W W' hX hW hW' h_law
  let ρ : Measure γ := @Measure.map Ω γ _ _ W μ
  have hρ_def : ρ = Measure.map W μ := rfl
  have hρ'_eq : ρ = Measure.map W' μ := hρ_eq

  -- Setup notation
  let φ : Ω → ℝ := Set.indicator (X ⁻¹' A) (fun _ => (1 : ℝ))
  let mW : MeasurableSpace Ω := MeasurableSpace.comap W inferInstance
  let mW' : MeasurableSpace Ω := MeasurableSpace.comap W' inferInstance

  -- σ-algebra relationships
  have hmW_le : mW ≤ _ := measurable_iff_comap_le.mp hW
  have hmW'_le : mW' ≤ _ := measurable_iff_comap_le.mp hW'
  haveI hσW : SigmaFinite (μ.trim hmW_le) :=
    (inferInstance : IsFiniteMeasure (μ.trim hmW_le)).toSigmaFinite
  haveI hσW' : SigmaFinite (μ.trim hmW'_le) :=
    (inferInstance : IsFiniteMeasure (μ.trim hmW'_le)).toSigmaFinite

  -- Integrability of indicator
  have hφ_int : Integrable φ μ := Integrable.indicator (integrable_const 1) (hX hA)

  -- Define the conditional expectations
  set μ₁ := μ[φ | mW] with hμ₁_def
  set μ₂ := μ[φ | mW'] with hμ₂_def

  -- Step 1: Tower property: E[μ₂|mW] = E[φ|mW] = μ₁
  have h_tower : μ[μ₂ | mW] =ᵐ[μ] μ₁ := condExp_condExp_of_le h_le hmW'_le

  -- Step 2: Boundedness [0,1] for both conditional expectations
  have hφ_bdd : ∀ ω, 0 ≤ φ ω ∧ φ ω ≤ 1 := fun ω => by
    show 0 ≤ (Set.indicator (X ⁻¹' A) (fun _ => (1 : ℝ))) ω ∧
         (Set.indicator (X ⁻¹' A) (fun _ => (1 : ℝ))) ω ≤ 1
    simp only [Set.indicator_apply]
    split_ifs <;> constructor <;> linarith

  have hμ₁_bdd : ∀ᵐ ω ∂μ, 0 ≤ μ₁ ω ∧ μ₁ ω ≤ 1 := by
    have h1 : ∀ᵐ ω ∂μ, 0 ≤ μ₁ ω :=
      condExp_nonneg (ae_of_all μ (fun ω => (hφ_bdd ω).1))
    have h2 : ∀ᵐ ω ∂μ, μ₁ ω ≤ 1 := by
      have hc : μ[(fun _ => (1 : ℝ))|mW] = fun _ => 1 := condExp_const hmW_le (1 : ℝ)
      have hmono := condExp_mono (m := mW) hφ_int (integrable_const 1)
          (ae_of_all μ (fun ω => (hφ_bdd ω).2))
      filter_upwards [hmono] with ω h1
      calc μ₁ ω ≤ μ[(fun _ => (1 : ℝ))|mW] ω := h1
        _ = 1 := congrFun hc ω
    filter_upwards [h1, h2] with ω h1 h2
    exact ⟨h1, h2⟩

  have hμ₂_bdd : ∀ᵐ ω ∂μ, 0 ≤ μ₂ ω ∧ μ₂ ω ≤ 1 := by
    have h1 : ∀ᵐ ω ∂μ, 0 ≤ μ₂ ω :=
      condExp_nonneg (ae_of_all μ (fun ω => (hφ_bdd ω).1))
    have h2 : ∀ᵐ ω ∂μ, μ₂ ω ≤ 1 := by
      have hc : μ[(fun _ => (1 : ℝ))|mW'] = fun _ => 1 := condExp_const hmW'_le (1 : ℝ)
      have hmono := condExp_mono (m := mW') hφ_int (integrable_const 1)
          (ae_of_all μ (fun ω => (hφ_bdd ω).2))
      filter_upwards [hmono] with ω h1
      calc μ₂ ω ≤ μ[(fun _ => (1 : ℝ))|mW'] ω := h1
        _ = 1 := congrFun hc ω
    filter_upwards [h1, h2] with ω h1 h2
    exact ⟨h1, h2⟩

  -- Step 3: Integrability facts
  have hμ₁_int : Integrable μ₁ μ := integrable_condExp
  have hμ₂_int : Integrable μ₂ μ := integrable_condExp

  have hμ₁_bound : ∀ᵐ ω ∂μ, ‖μ₁ ω‖ ≤ 1 := by
    filter_upwards [hμ₁_bdd] with ω ⟨h0, h1⟩
    rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith
  have hμ₂_bound : ∀ᵐ ω ∂μ, ‖μ₂ ω‖ ≤ 1 := by
    filter_upwards [hμ₂_bdd] with ω ⟨h0, h1⟩
    rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith

  have hμ₁sq_int : Integrable (fun ω => μ₁ ω * μ₁ ω) μ :=
    Integrable.bdd_mul' hμ₁_int hμ₁_int.aestronglyMeasurable hμ₁_bound

  have hμ₂sq_int : Integrable (fun ω => μ₂ ω * μ₂ ω) μ :=
    Integrable.bdd_mul' hμ₂_int hμ₂_int.aestronglyMeasurable hμ₂_bound

  have hμ₂μ₁_int : Integrable (fun ω => μ₂ ω * μ₁ ω) μ :=
    Integrable.bdd_mul' hμ₁_int hμ₂_int.aestronglyMeasurable hμ₂_bound

  -- Step 4a: Cross term E[μ₂μ₁] = E[μ₁²] using pull-out + tower
  have h_cross : ∫ ω, μ₂ ω * μ₁ ω ∂μ = ∫ ω, μ₁ ω * μ₁ ω ∂μ := by
    have hμ₁_meas : StronglyMeasurable[mW] μ₁ := stronglyMeasurable_condExp
    have h_pullout := condExp_mul_of_stronglyMeasurable_right (m := mW)
        hμ₁_meas hμ₂μ₁_int hμ₂_int
    calc ∫ ω, μ₂ ω * μ₁ ω ∂μ
        = ∫ ω, μ[fun ω => μ₂ ω * μ₁ ω | mW] ω ∂μ := (integral_condExp hmW_le).symm
      _ = ∫ ω, μ[μ₂ | mW] ω * μ₁ ω ∂μ := integral_congr_ae h_pullout
      _ = ∫ ω, μ₁ ω * μ₁ ω ∂μ := by
          apply integral_congr_ae
          filter_upwards [h_tower] with ω hω
          rw [hω]

  have h_sq_eq : ∫ ω, μ₁ ω * μ₁ ω ∂μ = ∫ ω, μ₂ ω * μ₂ ω ∂μ := h_sq_eq_raw

  -- Step 5: L² = 0 computation
  have h_L2_zero : ∫ ω, (μ₂ ω - μ₁ ω)^2 ∂μ = 0 := by
    have h_expand : ∀ᵐ ω ∂μ, (μ₂ ω - μ₁ ω)^2 = μ₂ ω * μ₂ ω - 2 * (μ₂ ω * μ₁ ω) + μ₁ ω * μ₁ ω := by
      filter_upwards with ω; ring
    have h1 : ∫ ω, (μ₂ ω - μ₁ ω)^2 ∂μ =
        ∫ ω, μ₂ ω * μ₂ ω ∂μ - 2 * ∫ ω, μ₂ ω * μ₁ ω ∂μ + ∫ ω, μ₁ ω * μ₁ ω ∂μ := by
      rw [integral_congr_ae h_expand]
      have h_sub : ∫ ω, (μ₂ ω * μ₂ ω - 2 * (μ₂ ω * μ₁ ω)) ∂μ =
          ∫ ω, μ₂ ω * μ₂ ω ∂μ - ∫ ω, 2 * (μ₂ ω * μ₁ ω) ∂μ :=
        integral_sub hμ₂sq_int (hμ₂μ₁_int.const_mul 2)
      have h_add : ∫ ω, (μ₂ ω * μ₂ ω - 2 * (μ₂ ω * μ₁ ω) + μ₁ ω * μ₁ ω) ∂μ =
          ∫ ω, (μ₂ ω * μ₂ ω - 2 * (μ₂ ω * μ₁ ω)) ∂μ + ∫ ω, μ₁ ω * μ₁ ω ∂μ :=
        integral_add (hμ₂sq_int.sub (hμ₂μ₁_int.const_mul 2)) hμ₁sq_int
      rw [h_add, h_sub]
      have h_mul2 : ∫ ω, 2 * (μ₂ ω * μ₁ ω) ∂μ = 2 * ∫ ω, μ₂ ω * μ₁ ω ∂μ :=
        integral_const_mul 2 (fun ω => μ₂ ω * μ₁ ω)
      linarith
    rw [h1, h_cross, h_sq_eq]; ring

  -- Step 6: L² = 0 implies a.e. equality
  have h_diff_zero : ∀ᵐ ω ∂μ, (μ₂ ω - μ₁ ω)^2 = 0 := by
    have h_nonneg : ∀ᵐ ω ∂μ, 0 ≤ (μ₂ ω - μ₁ ω)^2 := ae_of_all μ (fun ω => sq_nonneg _)
    have h_diff_int : Integrable (μ₂ - μ₁) μ := hμ₂_int.sub hμ₁_int
    have h_diff_bound : ∀ᵐ ω ∂μ, ‖(μ₂ - μ₁) ω‖ ≤ 2 := by
      filter_upwards [hμ₁_bdd, hμ₂_bdd] with ω ⟨h0₁, h1₁⟩ ⟨h0₂, h1₂⟩
      simp only [Pi.sub_apply]
      rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith
    have h_sq_int : Integrable (fun ω => (μ₂ ω - μ₁ ω)^2) μ := by
      have h_sq_eq_mul : ∀ ω, (μ₂ ω - μ₁ ω)^2 = (μ₂ - μ₁) ω * (μ₂ - μ₁) ω := fun ω => by
        simp only [Pi.sub_apply]; ring
      simp_rw [h_sq_eq_mul]
      exact Integrable.bdd_mul' h_diff_int h_diff_int.aestronglyMeasurable h_diff_bound
    exact (integral_eq_zero_iff_of_nonneg_ae h_nonneg h_sq_int).mp h_L2_zero

  -- (μ₂ - μ₁)² = 0 implies μ₂ = μ₁
  filter_upwards [h_diff_zero] with ω hω
  have : μ₂ ω - μ₁ ω = 0 := by nlinarith [sq_nonneg (μ₂ ω - μ₁ ω)]
  linarith

/-- Helper to extract pair law from triple law. -/
lemma pair_law_of_triple_law {β : Type*} [MeasurableSpace β]
    {μ : Measure Ω}
    (X : Ω → α) (Y : Ω → β) (W W' : Ω → γ)
    (hX : Measurable X) (hY : Measurable Y) (hW : Measurable W) (hW' : Measurable W')
    (h_triple : Measure.map (fun ω => (X ω, Y ω, W ω)) μ
              = Measure.map (fun ω => (X ω, Y ω, W' ω)) μ) :
    Measure.map (fun ω => ((X ω, Y ω), W ω)) μ
      = Measure.map (fun ω => ((X ω, Y ω), W' ω)) μ := by
  -- Reassociation via the isomorphism (α × β) × γ ≃ α × (β × γ)
  have h_assoc : Measurable (fun t : α × β × γ => ((t.1, t.2.1), t.2.2)) :=
    (measurable_fst.prodMk measurable_snd.fst).prodMk measurable_snd.snd
  have h1 : (fun ω => ((X ω, Y ω), W ω)) =
            (fun t : α × β × γ => ((t.1, t.2.1), t.2.2)) ∘ (fun ω => (X ω, Y ω, W ω)) := rfl
  have h2 : (fun ω => ((X ω, Y ω), W' ω)) =
            (fun t : α × β × γ => ((t.1, t.2.1), t.2.2)) ∘ (fun ω => (X ω, Y ω, W' ω)) := rfl
  rw [h1, h2]
  rw [← Measure.map_map h_assoc (hX.prodMk (hY.prodMk hW))]
  rw [← Measure.map_map h_assoc (hX.prodMk (hY.prodMk hW'))]
  rw [h_triple]

/-- Legacy wrapper: the old `condExp_eq_of_triple_law_direct` interface.

**WARNING:** This lemma's original statement was incorrect. It claimed that
the triple law `(Z,Y,W) =^d (Z,Y,W')` alone implies `E[φ|σ(Z,W)] = E[φ|σ(W)]`.
This is FALSE in general.

This wrapper provides backward compatibility but adds the missing contraction
hypothesis. If your use case doesn't have this hypothesis, the original
claim was invalid and you need to restructure your proof.

The correct statement (Kallenberg 1.3) is `condExp_indicator_eq_of_law_eq_of_comap_le`:
you need `σ(W) ≤ σ(W')` (W is a contraction of W') to drop from σ(W') to σ(W).
-/
lemma condExp_eq_of_triple_law_direct
    {β : Type*} [MeasurableSpace β]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (Y : Ω → α) (Z : Ω → β) (W W' : Ω → γ)
    (hY : Measurable Y) (hZ : Measurable Z) (hW : Measurable W) (hW' : Measurable W')
    (h_triple : Measure.map (fun ω => (Z ω, Y ω, W ω)) μ =
                Measure.map (fun ω => (Z ω, Y ω, W' ω)) μ)
    -- NEW REQUIRED HYPOTHESIS: σ(W) ≤ σ(W') (contraction)
    (h_contraction : MeasurableSpace.comap W inferInstance
                   ≤ MeasurableSpace.comap W' inferInstance)
    {A : Set α} (hA : MeasurableSet A) :
    -- Note: conclusion is now σ(W') → σ(W), not σ(Z,W) → σ(W)
    μ[Set.indicator (Y ⁻¹' A) (fun _ => (1 : ℝ))
       | MeasurableSpace.comap W' inferInstance]
      =ᵐ[μ]
    μ[Set.indicator (Y ⁻¹' A) (fun _ => (1 : ℝ))
       | MeasurableSpace.comap W inferInstance] := by
  -- Extract pair law (Y,W) =^d (Y,W') from triple law by projecting out Z
  have h_pair : Measure.map (fun ω => (Y ω, W ω)) μ
              = Measure.map (fun ω => (Y ω, W' ω)) μ := by
    -- Project triple law (Z,Y,W) to (Y,W) by dropping Z
    have h_proj : Measurable (fun t : β × α × γ => (t.2.1, t.2.2)) :=
      measurable_snd.fst.prodMk measurable_snd.snd
    have h1 : (fun ω => (Y ω, W ω)) =
              (fun t : β × α × γ => (t.2.1, t.2.2)) ∘ (fun ω => (Z ω, Y ω, W ω)) := rfl
    have h2 : (fun ω => (Y ω, W' ω)) =
              (fun t : β × α × γ => (t.2.1, t.2.2)) ∘ (fun ω => (Z ω, Y ω, W' ω)) := rfl
    rw [h1, h2]
    rw [← Measure.map_map h_proj (hZ.prodMk (hY.prodMk hW))]
    rw [← Measure.map_map h_proj (hZ.prodMk (hY.prodMk hW'))]
    rw [h_triple]
  -- Apply the main Kallenberg 1.3 lemma
  exact condExp_indicator_eq_of_law_eq_of_comap_le Y W W' hY hW hW' h_pair h_contraction hA
