/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Exchangeability.Probability.CondIndep.Basic

/-!
# Conditional Independence - Extension from Indicators to Simple Functions

This file extends conditional independence from indicator functions to simple functions,
which is the first step toward the full monotone class extension to bounded measurables.

## Main results

* `condIndep_indicator`: Indicator-level factorization from `CondIndep`
* `condIndep_indicator_simpleFunc`: Extension to indicators of simple functions
* `condIndep_simpleFunc`: Factorization extends to simple functions

## References

* Kallenberg (2005), *Probabilistic Symmetries and Invariance Principles*, Section 6.1
-/

open scoped Classical

noncomputable section
open scoped MeasureTheory ENNReal
open MeasureTheory ProbabilityTheory Set Exchangeability.Probability

variable {Ω α β γ : Type*}
variable [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]




/-- **Base case: Factorization for scaled indicators.**

For φ = c • 1_A and ψ = d • 1_B, the factorization follows by extracting scalars
and applying the CondIndep definition. -/
lemma condIndep_indicator (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Ω → α) (Z : Ω → β) (W : Ω → γ)
    (hCI : CondIndep μ Y Z W)
    (c : ℝ) (A : Set α) (hA : MeasurableSet A)
    (d : ℝ) (B : Set β) (hB : MeasurableSet B) :
    μ[ ((A.indicator (fun _ => c)) ∘ Y) * ((B.indicator (fun _ => d)) ∘ Z)
       | MeasurableSpace.comap W (by infer_instance) ]
      =ᵐ[μ]
    μ[ (A.indicator (fun _ => c)) ∘ Y | MeasurableSpace.comap W (by infer_instance) ]
      * μ[ (B.indicator (fun _ => d)) ∘ Z | MeasurableSpace.comap W (by infer_instance) ] := by
  set mW := MeasurableSpace.comap W (by infer_instance)

  -- Rewrite indicators in terms of preimages
  have hY_eq : (A.indicator (fun _ => c)) ∘ Y = fun ω => A.indicator (fun _ => c) (Y ω) := rfl
  have hZ_eq : (B.indicator (fun _ => d)) ∘ Z = fun ω => B.indicator (fun _ => d) (Z ω) := rfl

  -- Rewrite product as scaled product of unit indicators
  have h_prod : ((A.indicator (fun _ => c)) ∘ Y) * ((B.indicator (fun _ => d)) ∘ Z)
      = (c * d) • (((Y ⁻¹' A).indicator (fun _ => 1)) * ((Z ⁻¹' B).indicator (fun _ => 1))) := by
    ext ω
    simp [Set.indicator, Function.comp_apply]

  -- Apply CondIndep to unit indicators
  have h_unit : μ[ ((Y ⁻¹' A).indicator (fun _ => (1 : ℝ))) * ((Z ⁻¹' B).indicator (fun _ => (1 : ℝ))) | mW ]
      =ᵐ[μ] μ[ (Y ⁻¹' A).indicator (fun _ => (1 : ℝ)) | mW ] * μ[ (Z ⁻¹' B).indicator (fun _ => (1 : ℝ)) | mW ] :=
    hCI A B hA hB

  -- Factor out scalars using condExp_smul and combine with h_unit
  calc μ[ ((A.indicator (fun _ => c)) ∘ Y) * ((B.indicator (fun _ => d)) ∘ Z) | mW ]
      = μ[ (c * d) • (((Y ⁻¹' A).indicator (fun _ => 1)) * ((Z ⁻¹' B).indicator (fun _ => 1))) | mW ] := by
        rw [h_prod]
    _ =ᵐ[μ] (c * d) • μ[ ((Y ⁻¹' A).indicator (fun _ => 1)) * ((Z ⁻¹' B).indicator (fun _ => 1)) | mW ] := by
        apply condExp_smul
    _ =ᵐ[μ] (c * d) • (μ[ (Y ⁻¹' A).indicator (fun _ => 1) | mW ] * μ[ (Z ⁻¹' B).indicator (fun _ => 1) | mW ]) := by
        refine Filter.EventuallyEq.fun_comp h_unit (fun x => (c * d) • x)
    _ =ᵐ[μ] (c • μ[ (Y ⁻¹' A).indicator (fun _ => 1) | mW ]) * (d • μ[ (Z ⁻¹' B).indicator (fun _ => 1) | mW ]) := by
        apply Filter.EventuallyEq.of_eq
        ext ω
        simp [Pi.smul_apply, Pi.mul_apply]
        ring
    _ =ᵐ[μ] μ[ c • (Y ⁻¹' A).indicator (fun _ => 1) | mW ] * μ[ d • (Z ⁻¹' B).indicator (fun _ => 1) | mW ] := by
        exact Filter.EventuallyEq.mul (condExp_smul c _ mW).symm (condExp_smul d _ mW).symm
    _ =ᵐ[μ] μ[ (A.indicator (fun _ => c)) ∘ Y | mW ] * μ[ (B.indicator (fun _ => d)) ∘ Z | mW ] := by
        -- Prove c • (Y ⁻¹' A).indicator (fun _ => 1) = (A.indicator (fun _ => c)) ∘ Y
        have hY_ind : c • (Y ⁻¹' A).indicator (fun _ => 1) = (A.indicator (fun _ => c)) ∘ Y := by
          ext ω
          simp only [Pi.smul_apply, Set.indicator, Function.comp_apply, Set.mem_preimage]
          by_cases h : Y ω ∈ A <;> simp [h]
        have hZ_ind : d • (Z ⁻¹' B).indicator (fun _ => 1) = (B.indicator (fun _ => d)) ∘ Z := by
          ext ω
          simp only [Pi.smul_apply, Set.indicator, Function.comp_apply, Set.mem_preimage]
          by_cases h : Z ω ∈ B <;> simp [h]
        rw [hY_ind, hZ_ind]

/-- **Factorization for simple functions (both arguments).**

If Y ⊥⊥_W Z for indicators, extend to simple functions via linearity.
Uses single induction avoiding nested complexity. -/
-- Helper lemma: φ = c • 1_A with arbitrary ψ
lemma condIndep_indicator_simpleFunc (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Ω → α) (Z : Ω → β) (W : Ω → γ)
    (hCI : CondIndep μ Y Z W)
    (c : ℝ) (A : Set α) (hA : MeasurableSet A)
    (ψ : SimpleFunc β ℝ)
    (hY : Measurable Y) (hZ : Measurable Z) :
    μ[ ((A.indicator (fun _ => c)) ∘ Y) * (ψ ∘ Z) | MeasurableSpace.comap W (by infer_instance) ]
      =ᵐ[μ]
    μ[ (A.indicator (fun _ => c)) ∘ Y | MeasurableSpace.comap W (by infer_instance) ]
      * μ[ ψ ∘ Z | MeasurableSpace.comap W (by infer_instance) ] := by
  -- Induct on ψ
  refine SimpleFunc.induction ?const ?add ψ
  case const =>
    intro d B hB
    exact condIndep_indicator μ Y Z W hCI c A hA d B hB
  case add =>
    intro ψ1 ψ2 hψ_disj hψ1_ih hψ2_ih
    -- Goal: μ[φY * (ψ1+ψ2)Z | mW] =ᵐ μ[φY | mW] * μ[(ψ1+ψ2)Z | mW]
    -- where φY = (A.indicator c) ∘ Y

    -- Distribute: φY * (ψ1+ψ2)Z = φY * ψ1Z + φY * ψ2Z
    have h_dist : ((A.indicator (fun _ => c)) ∘ Y) * ((ψ1 + ψ2) ∘ Z)
        = ((A.indicator (fun _ => c)) ∘ Y) * (ψ1 ∘ Z) + ((A.indicator (fun _ => c)) ∘ Y) * (ψ2 ∘ Z) := by
      ext ω; simp [Pi.add_apply, mul_add]

    -- Apply IH to get factorization for ψ1 and ψ2
    -- hψ1_ih : μ[φY * ψ1Z | mW] =ᵐ μ[φY | mW] * μ[ψ1Z | mW]
    -- hψ2_ih : μ[φY * ψ2Z | mW] =ᵐ μ[φY | mW] * μ[ψ2Z | mW]

    calc μ[((A.indicator (fun _ => c)) ∘ Y) * ((ψ1 + ψ2) ∘ Z) | MeasurableSpace.comap W (by infer_instance)]
        = μ[((A.indicator (fun _ => c)) ∘ Y) * (ψ1 ∘ Z) + ((A.indicator (fun _ => c)) ∘ Y) * (ψ2 ∘ Z)
            | MeasurableSpace.comap W (by infer_instance)] := by rw [h_dist]
      _ =ᵐ[μ] μ[((A.indicator (fun _ => c)) ∘ Y) * (ψ1 ∘ Z) | MeasurableSpace.comap W (by infer_instance)]
              + μ[((A.indicator (fun _ => c)) ∘ Y) * (ψ2 ∘ Z) | MeasurableSpace.comap W (by infer_instance)] := by
          -- Need integrability to apply condExp_add
          have hψ1_int : Integrable (ψ1 ∘ Z) μ := by
            refine Integrable.comp_measurable ?_ hZ
            exact SimpleFunc.integrable_of_isFiniteMeasure ψ1
          have hψ2_int : Integrable (ψ2 ∘ Z) μ := by
            refine Integrable.comp_measurable ?_ hZ
            exact SimpleFunc.integrable_of_isFiniteMeasure ψ2
          have h1_int : Integrable (((A.indicator (fun _ => c)) ∘ Y) * (ψ1 ∘ Z)) μ := by
            refine Integrable.bdd_mul (c := |c|) ?_ ?_ ?_
            · exact hψ1_int
            · exact ((measurable_const.indicator hA).comp hY).aestronglyMeasurable
            · filter_upwards with ω
              simp only [Function.comp_apply, Set.indicator]
              by_cases h : Y ω ∈ A <;> simp [h]
          have h2_int : Integrable (((A.indicator (fun _ => c)) ∘ Y) * (ψ2 ∘ Z)) μ := by
            refine Integrable.bdd_mul (c := |c|) ?_ ?_ ?_
            · exact hψ2_int
            · exact ((measurable_const.indicator hA).comp hY).aestronglyMeasurable
            · filter_upwards with ω
              simp only [Function.comp_apply, Set.indicator]
              by_cases h : Y ω ∈ A <;> simp [h]
          exact condExp_add h1_int h2_int _
      _ =ᵐ[μ] (μ[(A.indicator (fun _ => c)) ∘ Y | MeasurableSpace.comap W (by infer_instance)] * μ[ψ1 ∘ Z | MeasurableSpace.comap W (by infer_instance)])
              + (μ[(A.indicator (fun _ => c)) ∘ Y | MeasurableSpace.comap W (by infer_instance)] * μ[ψ2 ∘ Z | MeasurableSpace.comap W (by infer_instance)]) :=
          Filter.EventuallyEq.add hψ1_ih hψ2_ih
      _ =ᵐ[μ] μ[(A.indicator (fun _ => c)) ∘ Y | MeasurableSpace.comap W (by infer_instance)]
              * (μ[ψ1 ∘ Z | MeasurableSpace.comap W (by infer_instance)] + μ[ψ2 ∘ Z | MeasurableSpace.comap W (by infer_instance)]) := by
          apply Filter.EventuallyEq.of_eq
          simp only [mul_add]
      _ =ᵐ[μ] μ[(A.indicator (fun _ => c)) ∘ Y | MeasurableSpace.comap W (by infer_instance)]
              * μ[(ψ1 + ψ2) ∘ Z | MeasurableSpace.comap W (by infer_instance)] := by
          -- Apply condExp_add in reverse on RHS to combine ψ1 and ψ2
          have hψ1_int : Integrable (ψ1 ∘ Z) μ := by
            refine Integrable.comp_measurable ?_ hZ
            exact SimpleFunc.integrable_of_isFiniteMeasure ψ1
          have hψ2_int : Integrable (ψ2 ∘ Z) μ := by
            refine Integrable.comp_measurable ?_ hZ
            exact SimpleFunc.integrable_of_isFiniteMeasure ψ2
          exact Filter.EventuallyEq.mul Filter.EventuallyEq.rfl (condExp_add hψ1_int hψ2_int _).symm

lemma condIndep_simpleFunc (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Ω → α) (Z : Ω → β) (W : Ω → γ)
    (hCI : CondIndep μ Y Z W)
    (φ : SimpleFunc α ℝ) (ψ : SimpleFunc β ℝ)
    (hY : Measurable Y) (hZ : Measurable Z) :
    μ[ (φ ∘ Y) * (ψ ∘ Z) | MeasurableSpace.comap W (by infer_instance) ]
      =ᵐ[μ]
    μ[ φ ∘ Y | MeasurableSpace.comap W (by infer_instance) ]
      * μ[ ψ ∘ Z | MeasurableSpace.comap W (by infer_instance) ] := by
  -- Induct on φ
  refine SimpleFunc.induction ?const ?add φ
  case const =>
    intro c A hA
    exact condIndep_indicator_simpleFunc μ Y Z W hCI c A hA ψ hY hZ
  case add =>
    intro φ1 φ2 hφ_disj hφ1_ih hφ2_ih
    -- Goal: μ[(φ1+φ2)Y * ψZ | mW] =ᵐ μ[(φ1+φ2)Y | mW] * μ[ψZ | mW]

    -- Distribute: (φ1+φ2)Y * ψZ = φ1Y * ψZ + φ2Y * ψZ
    have h_dist : ((φ1 + φ2) ∘ Y) * (ψ ∘ Z)
        = ((φ1 ∘ Y) * (ψ ∘ Z)) + ((φ2 ∘ Y) * (ψ ∘ Z)) := by
      ext ω; simp [Pi.add_apply, add_mul]

    calc μ[((φ1 + φ2) ∘ Y) * (ψ ∘ Z) | MeasurableSpace.comap W (by infer_instance)]
        = μ[((φ1 ∘ Y) * (ψ ∘ Z)) + ((φ2 ∘ Y) * (ψ ∘ Z)) | MeasurableSpace.comap W (by infer_instance)] := by rw [h_dist]
      _ =ᵐ[μ] μ[(φ1 ∘ Y) * (ψ ∘ Z) | MeasurableSpace.comap W (by infer_instance)]
              + μ[(φ2 ∘ Y) * (ψ ∘ Z) | MeasurableSpace.comap W (by infer_instance)] := by
          -- Need integrability
          have hφ1_int : Integrable (φ1 ∘ Y) μ := by
            refine Integrable.comp_measurable ?_ hY
            exact SimpleFunc.integrable_of_isFiniteMeasure φ1
          have hφ2_int : Integrable (φ2 ∘ Y) μ := by
            refine Integrable.comp_measurable ?_ hY
            exact SimpleFunc.integrable_of_isFiniteMeasure φ2
          have hψ_int : Integrable (ψ ∘ Z) μ := by
            refine Integrable.comp_measurable ?_ hZ
            exact SimpleFunc.integrable_of_isFiniteMeasure ψ
          have h1_int : Integrable ((φ1 ∘ Y) * (ψ ∘ Z)) μ := by
            apply Integrable.bdd_mul hψ_int
            · exact (φ1.measurable.comp hY).aestronglyMeasurable
            · filter_upwards with x
              simp only [Function.comp_apply]
              rw [← coe_nnnorm, NNReal.coe_le_coe]
              exact Finset.le_sup (SimpleFunc.mem_range_self φ1 (Y x))
          have h2_int : Integrable ((φ2 ∘ Y) * (ψ ∘ Z)) μ := by
            apply Integrable.bdd_mul hψ_int
            · exact (φ2.measurable.comp hY).aestronglyMeasurable
            · filter_upwards with x
              simp only [Function.comp_apply]
              rw [← coe_nnnorm, NNReal.coe_le_coe]
              exact Finset.le_sup (SimpleFunc.mem_range_self φ2 (Y x))
          exact condExp_add h1_int h2_int _
      _ =ᵐ[μ] (μ[φ1 ∘ Y | MeasurableSpace.comap W (by infer_instance)] * μ[ψ ∘ Z | MeasurableSpace.comap W (by infer_instance)])
              + (μ[φ2 ∘ Y | MeasurableSpace.comap W (by infer_instance)] * μ[ψ ∘ Z | MeasurableSpace.comap W (by infer_instance)]) :=
          Filter.EventuallyEq.add hφ1_ih hφ2_ih
      _ =ᵐ[μ] (μ[φ1 ∘ Y | MeasurableSpace.comap W (by infer_instance)] + μ[φ2 ∘ Y | MeasurableSpace.comap W (by infer_instance)])
              * μ[ψ ∘ Z | MeasurableSpace.comap W (by infer_instance)] := by
          apply Filter.EventuallyEq.of_eq
          simp only [add_mul]
      _ =ᵐ[μ] μ[(φ1 + φ2) ∘ Y | MeasurableSpace.comap W (by infer_instance)]
              * μ[ψ ∘ Z | MeasurableSpace.comap W (by infer_instance)] := by
          -- Apply condExp_add in reverse on LHS
          have hφ1_int : Integrable (φ1 ∘ Y) μ := by
            refine Integrable.comp_measurable ?_ hY
            exact SimpleFunc.integrable_of_isFiniteMeasure φ1
          have hφ2_int : Integrable (φ2 ∘ Y) μ := by
            refine Integrable.comp_measurable ?_ hY
            exact SimpleFunc.integrable_of_isFiniteMeasure φ2
          exact Filter.EventuallyEq.mul (condExp_add hφ1_int hφ2_int _).symm Filter.EventuallyEq.rfl
