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

* `condIndep_of_indep_pair`: Independence Y ⊥ Z plus (Y,Z) ⊥ W implies Y ⊥⊥_W Z
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

/-!
## Conditional independence from unconditional independence
-/

/-- **Independence plus independence of pair from W implies conditional independence.**

If Y and Z are (unconditionally) independent, and the pair (Y,Z) is independent of W,
then Y ⊥⊥_W Z.

**Key insight:** Independence of (Y,Z) from W means the conditional law of (Y,Z) given W
equals the unconditional law, so the factorization E[1_A(Y)·1_B(Z)] = E[1_A(Y)]·E[1_B(Z)]
survives conditioning on W.

**Counterexample showing Y ⊥ Z alone is NOT enough:**
- Y, Z: independent fair coin flips
- W := Y + Z
- Then Y ⊥ Z unconditionally, but P(Y=1|Z=1,W=1) = 1 ≠ 1/2 = P(Y=1|W=1),
  so Y and Z are NOT conditionally independent given W.

**Proof strategy:**
1. Since (Y,Z) ⊥ W, conditional expectation of any function of (Y,Z) given σ(W)
   is the constant E[that function].
2. Apply to 1_A(Y), 1_B(Z), and their product.
3. The unconditional factorization E[1_A(Y)·1_B(Z)] = E[1_A(Y)]·E[1_B(Z)] (from Y ⊥ Z)
   transfers to the conditional expectations.
-/

-- Product of two unit indicator functions equals the indicator of the intersection.
private lemma mul_indicator_one_eq_indicator_inter {Ω : Type*} (S T : Set Ω) :
    (S.indicator (fun _ => (1 : ℝ))) * (T.indicator (fun _ => (1 : ℝ)))
      = (S ∩ T).indicator (fun _ => (1 : ℝ)) := by
  classical
  ext ω
  simp only [Pi.mul_apply]
  by_cases hS : ω ∈ S <;> by_cases hT : ω ∈ T
  · rw [Set.indicator_of_mem hS, Set.indicator_of_mem hT]
    have : ω ∈ S ∩ T := ⟨hS, hT⟩
    rw [Set.indicator_of_mem this]; norm_num
  · rw [Set.indicator_of_mem hS, Set.indicator_of_notMem hT]
    have : ω ∉ S ∩ T := fun h => hT h.2
    rw [Set.indicator_of_notMem this]; norm_num
  · rw [Set.indicator_of_notMem hS, Set.indicator_of_mem hT]
    have : ω ∉ S ∩ T := fun h => hS h.1
    rw [Set.indicator_of_notMem this]; norm_num
  · rw [Set.indicator_of_notMem hS, Set.indicator_of_notMem hT]
    have : ω ∉ S ∩ T := fun h => hS h.1
    rw [Set.indicator_of_notMem this]; norm_num

-- Product of indicators composed with functions equals indicator of product set composed with pair.
private lemma mul_indicator_comp_pair_eq_indicator_prod {Ω α β : Type*}
    (Y : Ω → α) (Z : Ω → β) (A : Set α) (B : Set β) :
    ((Y ⁻¹' A).indicator (fun _ => (1 : ℝ))) * ((Z ⁻¹' B).indicator (fun _ => (1 : ℝ)))
      = (fun p => (A ×ˢ B).indicator (fun _ => (1 : ℝ)) p) ∘ (fun ω => (Y ω, Z ω)) := by
  classical
  ext ω
  simp only [Pi.mul_apply, Function.comp_apply]
  by_cases hY : ω ∈ Y ⁻¹' A <;> by_cases hZ : ω ∈ Z ⁻¹' B
  · rw [Set.indicator_of_mem hY, Set.indicator_of_mem hZ]
    have : (Y ω, Z ω) ∈ A ×ˢ B := Set.mk_mem_prod hY hZ
    rw [Set.indicator_of_mem this]; norm_num
  · rw [Set.indicator_of_mem hY, Set.indicator_of_notMem hZ]
    have : (Y ω, Z ω) ∉ A ×ˢ B := fun h => hZ h.2
    rw [Set.indicator_of_notMem this]; norm_num
  · rw [Set.indicator_of_notMem hY, Set.indicator_of_mem hZ]
    have : (Y ω, Z ω) ∉ A ×ˢ B := fun h => hY h.1
    rw [Set.indicator_of_notMem this]; norm_num
  · rw [Set.indicator_of_notMem hY, Set.indicator_of_notMem hZ]
    have : (Y ω, Z ω) ∉ A ×ˢ B := fun h => hY h.1
    rw [Set.indicator_of_notMem this]; norm_num

theorem condIndep_of_indep_pair (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Ω → α) (Z : Ω → β) (W : Ω → γ)
    (hY : Measurable Y) (hZ : Measurable Z) (hW : Measurable W)
    (hYZ_indep : IndepFun Y Z μ)
    (hPairW_indep : IndepFun (fun ω => (Y ω, Z ω)) W μ) :
    CondIndep μ Y Z W := by
  intro A B hA hB
  -- Define the indicator functions
  let f := Set.indicator (Y ⁻¹' A) (fun _ => (1 : ℝ))
  let g := Set.indicator (Z ⁻¹' B) (fun _ => (1 : ℝ))

  -- f and g are measurable and integrable
  have hf_meas : Measurable f := measurable_const.indicator (hY hA)
  have hg_meas : Measurable g := measurable_const.indicator (hZ hB)
  have hf_int : Integrable f μ := (integrable_const (1 : ℝ)).indicator (hY hA)
  have hg_int : Integrable g μ := (integrable_const (1 : ℝ)).indicator (hZ hB)

  -- Extract Y ⊥ W and Z ⊥ W from pair independence
  have hY_W_indep : IndepFun Y W μ := IndepFun.of_comp_left_fst hPairW_indep
  have hZ_W_indep : IndepFun Z W μ := IndepFun.of_comp_left_snd hPairW_indep

  -- Key insight: f, g, and f*g are all independent of W
  -- Therefore their conditional expectations given σ(W) are constants

  -- Step 1: f is a function of Y, so f ⊥ W
  -- f = (Set.indicator A (fun _ => 1)) ∘ Y
  have hf_indep : IndepFun f W μ := by
    have : f = (Set.indicator A (fun _ => (1 : ℝ))) ∘ Y := by
      ext ω
      simp only [Function.comp_apply, Set.indicator_apply]
      rfl
    rw [this]
    exact hY_W_indep.comp (measurable_const.indicator hA) measurable_id

  -- Step 2: g is a function of Z, so g ⊥ W
  have hg_indep : IndepFun g W μ := by
    have : g = (Set.indicator B (fun _ => (1 : ℝ))) ∘ Z := by
      ext ω
      simp only [Function.comp_apply, Set.indicator_apply]
      rfl
    rw [this]
    exact hZ_W_indep.comp (measurable_const.indicator hB) measurable_id

  -- Step 3: f * g is a function of (Y,Z), so f * g ⊥ W
  have hfg_indep : IndepFun (f * g) W μ := by
    rw [show f * g = (fun p => (A ×ˢ B).indicator (fun _ => (1 : ℝ)) p) ∘ (fun ω => (Y ω, Z ω))
          from mul_indicator_comp_pair_eq_indicator_prod Y Z A B]
    exact hPairW_indep.comp (measurable_const.indicator (hA.prod hB)) measurable_id

  -- Step 4: Apply condExp_const_of_indepFun to get conditional expectations are constants
  have hf_ce : μ[f | MeasurableSpace.comap W (by infer_instance)] =ᵐ[μ] (fun _ => μ[f]) :=
    condExp_const_of_indepFun μ hf_meas hW hf_indep hf_int

  have hg_ce : μ[g | MeasurableSpace.comap W (by infer_instance)] =ᵐ[μ] (fun _ => μ[g]) :=
    condExp_const_of_indepFun μ hg_meas hW hg_indep hg_int

  have hfg_meas : Measurable (f * g) := hf_meas.mul hg_meas
  have hfg_int : Integrable (f * g) μ := by
    rw [show f * g = (Y ⁻¹' A ∩ Z ⁻¹' B).indicator (fun _ => (1 : ℝ))
          from mul_indicator_one_eq_indicator_inter (Y ⁻¹' A) (Z ⁻¹' B)]
    exact (integrable_const (1 : ℝ)).indicator ((hY hA).inter (hZ hB))
  have hfg_ce : μ[f * g | MeasurableSpace.comap W (by infer_instance)] =ᵐ[μ] (fun _ => μ[f * g]) :=
    condExp_const_of_indepFun μ hfg_meas hW hfg_indep hfg_int

  -- Step 5: Use Y ⊥ Z to get unconditional factorization E[f*g] = E[f] * E[g]
  -- Since f is a function of Y and g is a function of Z, f ⊥ g follows from Y ⊥ Z
  have hfg_indep' : IndepFun f g μ := by
    have hf_comp : f = (Set.indicator A (fun _ => (1 : ℝ))) ∘ Y := by
      ext ω
      show f ω = Set.indicator A (fun _ => 1) (Y ω)
      rfl
    have hg_comp : g = (Set.indicator B (fun _ => (1 : ℝ))) ∘ Z := by
      ext ω
      show g ω = Set.indicator B (fun _ => 1) (Z ω)
      rfl
    rw [hf_comp, hg_comp]
    exact hYZ_indep.comp (measurable_const.indicator hA) (measurable_const.indicator hB)

  have h_factor : μ[f * g] = μ[f] * μ[g] :=
    IndepFun.integral_mul_eq_mul_integral hfg_indep' hf_int.aestronglyMeasurable hg_int.aestronglyMeasurable

  -- Step 6: Combine everything
  calc μ[f * g | MeasurableSpace.comap W (by infer_instance)]
      =ᵐ[μ] (fun _ => μ[f * g]) := hfg_ce
    _ = (fun _ => μ[f] * μ[g]) := by rw [h_factor]
    _ =ᵐ[μ] (fun _ => μ[f]) * (fun _ => μ[g]) := by rfl
    _ =ᵐ[μ] μ[f | MeasurableSpace.comap W (by infer_instance)] * μ[g | MeasurableSpace.comap W (by infer_instance)] :=
        Filter.EventuallyEq.mul hf_ce.symm hg_ce.symm

/-!
## Extension to simple functions and bounded measurables (§C2)
-/

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
            refine Integrable.bdd_mul' (c := |c|) ?_ ?_ ?_
            · exact hψ1_int
            · exact ((measurable_const.indicator hA).comp hY).aestronglyMeasurable
            · filter_upwards with ω
              simp only [Function.comp_apply, Set.indicator, norm_indicator_eq_indicator_norm]
              by_cases h : Y ω ∈ A <;> simp [h, le_abs_self, abs_nonneg]
          have h2_int : Integrable (((A.indicator (fun _ => c)) ∘ Y) * (ψ2 ∘ Z)) μ := by
            refine Integrable.bdd_mul' (c := |c|) ?_ ?_ ?_
            · exact hψ2_int
            · exact ((measurable_const.indicator hA).comp hY).aestronglyMeasurable
            · filter_upwards with ω
              simp only [Function.comp_apply, Set.indicator, norm_indicator_eq_indicator_norm]
              by_cases h : Y ω ∈ A <;> simp [h, le_abs_self, abs_nonneg]
          exact condExp_add h1_int h2_int _
      _ =ᵐ[μ] (μ[(A.indicator (fun _ => c)) ∘ Y | MeasurableSpace.comap W (by infer_instance)] * μ[ψ1 ∘ Z | MeasurableSpace.comap W (by infer_instance)])
              + (μ[(A.indicator (fun _ => c)) ∘ Y | MeasurableSpace.comap W (by infer_instance)] * μ[ψ2 ∘ Z | MeasurableSpace.comap W (by infer_instance)]) :=
          Filter.EventuallyEq.add hψ1_ih hψ2_ih
      _ =ᵐ[μ] μ[(A.indicator (fun _ => c)) ∘ Y | MeasurableSpace.comap W (by infer_instance)]
              * (μ[ψ1 ∘ Z | MeasurableSpace.comap W (by infer_instance)] + μ[ψ2 ∘ Z | MeasurableSpace.comap W (by infer_instance)]) := by
          apply Filter.EventuallyEq.of_eq
          simp only [Pi.add_apply, Pi.mul_apply, mul_add]
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
            · use (φ1.range.sup (fun x => ‖x‖₊)).toReal
              intro x
              simp only [Function.comp_apply]
              rw [← coe_nnnorm, NNReal.coe_le_coe]
              exact Finset.le_sup (SimpleFunc.mem_range_self φ1 (Y x))
          have h2_int : Integrable ((φ2 ∘ Y) * (ψ ∘ Z)) μ := by
            apply Integrable.bdd_mul hψ_int
            · exact (φ2.measurable.comp hY).aestronglyMeasurable
            · use (φ2.range.sup (fun x => ‖x‖₊)).toReal
              intro x
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
          simp only [Pi.add_apply, Pi.mul_apply, add_mul]
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
