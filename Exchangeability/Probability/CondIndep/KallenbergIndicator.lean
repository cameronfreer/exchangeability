/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Exchangeability.Probability.CondIndep.Bounded

/-!
# Kallenberg 1.3 Indicator Conditional Independence

This file provides infrastructure for proving conditional independence from the "drop-info"
property, which is Kallenberg Lemma 1.3.

## Main results

* `condIndep_indicator_of_dropInfoY`: Drop-info implies indicator conditional independence

## References

* Kallenberg (2005), *Probabilistic Symmetries and Invariance Principles*, Lemma 1.3
-/

open scoped Classical

noncomputable section
open scoped MeasureTheory ENNReal
open MeasureTheory ProbabilityTheory Set Exchangeability.Probability

variable {Ω α β γ : Type*}
variable [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

section KallenbergIndicator

/-- **From drop‑info for `Y` to indicator conditional independence**.

Assume for all Borel `A` we have
`condExp μ (σ[Z,W]) (1_A ∘ Y) =ᵐ condExp μ (σ[W]) (1_A ∘ Y)`.
Then for all Borel `A,B`:

E[ 1_A(Y) 1_B(Z) | σ(W) ]
= E[ 1_A(Y) | σ(W) ] * E[ 1_B(Z) | σ(W) ] a.e.
-/
lemma condIndep_indicator_of_dropInfoY
  {Ω : Type*} [inst_mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
  {Y Z W : Ω → ℝ}
  {mW : MeasurableSpace Ω}
  (_hmW_le : mW ≤ inst_mΩ)  -- mW is a sub-σ-algebra of the ambient space
  (hmW_le_mZW : mW ≤ MeasurableSpace.comap (fun ω => (Z ω, W ω)) inferInstance)  -- mW ≤ σ(Z,W)
  (dropY :
    ∀ A : Set ℝ, MeasurableSet A →
      condExp (MeasurableSpace.comap (fun ω => (Z ω, W ω)) inferInstance) μ
        (fun ω => Set.indicator (Y ⁻¹' A) (fun _ => (1 : ℝ)) ω)
      =ᵐ[μ]
      condExp mW μ (fun ω => Set.indicator (Y ⁻¹' A) (fun _ => (1 : ℝ)) ω))
  (hY : @Measurable Ω ℝ inst_mΩ _ Y) (hZ : @Measurable Ω ℝ inst_mΩ _ Z) (hW : @Measurable Ω ℝ inst_mΩ _ W)
  {A B : Set ℝ} (hA : MeasurableSet A) (hB : MeasurableSet B) :
  condExp mW μ
    (fun ω =>
      (Set.indicator (Y ⁻¹' A) (fun _ => (1 : ℝ)) ω) *
      (Set.indicator (Z ⁻¹' B) (fun _ => (1 : ℝ)) ω))
  =ᵐ[μ]
  (condExp mW μ (fun ω => Set.indicator (Y ⁻¹' A) (fun _ => (1 : ℝ)) ω))
  *
  (condExp mW μ (fun ω => Set.indicator (Z ⁻¹' B) (fun _ => (1 : ℝ)) ω)) := by
  /-
  **Proof (from Kallenberg 2005, Lemma 1.3):**

  Let indA := 1_A ∘ Y and indB := 1_B ∘ Z.
  Define mZW := σ(Z, W) = MeasurableSpace.comap (Z, W) inferInstance.

  Step 1: Pull-out for mZW (indB is mZW-measurable)
    condExp mZW (indA * indB) =ᵐ condExp mZW (indA) * indB

  Step 2: Apply dropY hypothesis
    condExp mZW (indA) =ᵐ condExp mW (indA)
    So: condExp mZW (indA * indB) =ᵐ condExp mW (indA) * indB

  Step 3: Tower property (mW ≤ mZW)
    condExp mW (condExp mZW (indA * indB)) = condExp mW (indA * indB)
    Applying condExp mW to step 2:
    condExp mW (indA * indB) =ᵐ condExp mW (condExp mW (indA) * indB)

  Step 4: Pull-out for mW (condExp mW (indA) is mW-measurable)
    condExp mW (condExp mW (indA) * indB)
    = condExp mW (indA) * condExp mW (indB)
  -/
  -- Notation
  let mZW := MeasurableSpace.comap (fun ω => (Z ω, W ω)) inferInstance
  let indA := fun ω => Set.indicator (Y ⁻¹' A) (fun _ => (1 : ℝ)) ω
  let indB := fun ω => Set.indicator (Z ⁻¹' B) (fun _ => (1 : ℝ)) ω

  -- σ-algebra relationship for mZW
  have hmZW_le : mZW ≤ inst_mΩ := by
    intro s hs
    obtain ⟨S, hS_meas, rfl⟩ := hs
    exact hS_meas.preimage (hZ.prodMk hW)

  -- SigmaFinite instance for trim (needed for condExp lemmas)
  haveI hσZW : SigmaFinite (μ.trim hmZW_le) := sigmaFinite_trim_of_le μ hmZW_le

  -- Integrability of indicators (bounded by 1)
  have hIndA_int : Integrable indA μ := (integrable_const 1).indicator (hA.preimage hY)
  have hIndB_int : Integrable indB μ := (integrable_const 1).indicator (hB.preimage hZ)
  have hProd_int : Integrable (indA * indB) μ := by
    -- indA is bounded by 1, so we can use bdd_mul with indB integrable
    have hIndA_bdd : ∀ᵐ x ∂μ, ‖indA x‖ ≤ 1 := by
      filter_upwards with x
      simp only [indA, Real.norm_eq_abs]
      rw [Set.indicator_apply]
      by_cases h : x ∈ Y ⁻¹' A <;> simp [h]
    exact hIndB_int.bdd_mul hIndA_int.aestronglyMeasurable hIndA_bdd

  -- indB is mZW-measurable (depends only on Z)
  -- Key: indB = (indicator B 1) ∘ Prod.fst ∘ (Z, W), and (Z,W) is mZW-measurable
  have hIndB_mZW_meas : @Measurable Ω ℝ mZW inferInstance indB := by
    -- Z is mZW-measurable: Z = Prod.fst ∘ (Z,W) where (Z,W) is the identity on comap
    have hZW_meas : @Measurable Ω (ℝ × ℝ) mZW _ (fun ω => (Z ω, W ω)) :=
      measurable_iff_comap_le.mpr le_rfl
    have hZ_mZW : @Measurable Ω ℝ mZW _ Z := measurable_fst.comp hZW_meas
    -- indicator B 1 : ℝ → ℝ is measurable
    have h_ind_meas : Measurable (Set.indicator B (fun _ => (1 : ℝ))) :=
      measurable_const.indicator hB
    -- indB = (indicator B 1) ∘ Z
    have h_eq : indB = (Set.indicator B (fun _ => (1 : ℝ))) ∘ Z := by
      ext ω; simp only [Function.comp_apply, indB, Set.indicator]; rfl
    rw [h_eq]
    exact h_ind_meas.comp hZ_mZW

  -- Step 1-2: Use dropY to get condExp mZW (indA) =ᵐ condExp mW (indA)
  have h_drop : μ[indA | mZW] =ᵐ[μ] μ[indA | mW] := dropY A hA

  -- Step 3: Tower property: condExp mW (condExp mZW f) = condExp mW f
  have h_tower_prod : μ[μ[indA * indB | mZW] | mW] =ᵐ[μ] μ[indA * indB | mW] :=
    condExp_condExp_of_le hmW_le_mZW hmZW_le

  -- Step 1: Pull-out for mZW: condExp mZW (indA * indB) =ᵐ condExp mZW (indA) * indB
  -- (because indB is mZW-measurable)
  have hIndB_stronglyMeas_mZW : StronglyMeasurable[mZW] indB :=
    hIndB_mZW_meas.stronglyMeasurable
  have h_step1 : μ[indA * indB | mZW] =ᵐ[μ] μ[indA | mZW] * indB :=
    condExp_mul_of_stronglyMeasurable_right hIndB_stronglyMeas_mZW hProd_int hIndA_int

  -- Step 2: From h_drop, substitute condExp mW (indA) for condExp mZW (indA)
  have h_step2 : μ[indA | mZW] * indB =ᵐ[μ] μ[indA | mW] * indB := by
    filter_upwards [h_drop] with ω hω
    simp only [Pi.mul_apply]
    rw [hω]

  -- Combine step 1 and step 2
  have h_step12 : μ[indA * indB | mZW] =ᵐ[μ] μ[indA | mW] * indB :=
    h_step1.trans h_step2

  -- Step 3: Apply condExp mW to both sides (using h_tower_prod)
  -- condExp mW (condExp mZW (indA * indB)) =ᵐ condExp mW (indA * indB) by tower
  -- So: condExp mW (indA * indB) =ᵐ condExp mW (condExp mW (indA) * indB)
  have h_step3a : μ[μ[indA * indB | mZW] | mW] =ᵐ[μ] μ[μ[indA | mW] * indB | mW] := by
    apply condExp_congr_ae h_step12
  have h_step3 : μ[indA * indB | mW] =ᵐ[μ] μ[μ[indA | mW] * indB | mW] :=
    h_tower_prod.symm.trans h_step3a

  -- Step 4: Pull-out for mW: condExp mW (condExp mW (indA) * indB) =ᵐ condExp mW (indA) * condExp mW (indB)
  -- (because condExp mW (indA) is mW-measurable)
  have hCondExpA_stronglyMeas : StronglyMeasurable[mW] (μ[indA | mW]) :=
    stronglyMeasurable_condExp
  have h_prod_condA_indB_int : Integrable (μ[indA | mW] * indB) μ := by
    -- indB is bounded by 1, and condExp is integrable
    have hIndB_bdd : ∀ᵐ x ∂μ, ‖indB x‖ ≤ 1 := by
      filter_upwards with x
      simp only [indB, Real.norm_eq_abs]
      rw [Set.indicator_apply]
      by_cases h : x ∈ Z ⁻¹' B <;> simp [h]
    -- bdd_mul gives Integrable (indB * condExp) μ, convert using commutativity
    have h : Integrable (indB * (μ[indA | mW])) μ :=
      integrable_condExp.bdd_mul hIndB_int.aestronglyMeasurable hIndB_bdd
    convert h using 1
    ext ω
    exact mul_comm _ _
  have h_step4 : μ[μ[indA | mW] * indB | mW] =ᵐ[μ] μ[indA | mW] * μ[indB | mW] :=
    condExp_mul_of_stronglyMeasurable_left hCondExpA_stronglyMeas h_prod_condA_indB_int hIndB_int

  -- Combine step 3 and step 4 to get the conclusion
  exact h_step3.trans h_step4

end KallenbergIndicator

end  -- noncomputable section
