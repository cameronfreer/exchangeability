/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Probability.Kernel.Condexp
import Exchangeability.DeFinetti.ViaL2.DirectingMeasureIntegral

/-!
# Bridge: `directing_measure` is the pushforward of `condExpKernel` by `X 0`

`directing_measure X … ω` is, almost everywhere in `ω`, the pushforward of the
conditional-expectation kernel `condExpKernel μ (tailSigma X) ω` by the first coordinate
`X 0`. This identifies the directing measure as the conditional distribution of `X 0`
given the tail σ-algebra and lets downstream integration identities follow from
mathlib's kernel API. Added in isolation; downstream migrations land in a follow-up PR.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace Exchangeability.DeFinetti.ViaL2

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- The bridge identifying `directing_measure ω` with the pushforward of
`condExpKernel μ (tailSigma X) ω` by `X 0`. -/
theorem directing_measure_ae_eq_condExpKernel_map
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ) :
    (fun ω => directing_measure X hX_contract hX_meas hX_L2 ω)
      =ᵐ[μ]
    (fun ω =>
      Measure.map (X 0)
        (condExpKernel (μ := μ) (m := TailSigma.tailSigma X) ω)) := by
  classical
  have hm_le : TailSigma.tailSigma X ≤ (inferInstance : MeasurableSpace Ω) :=
    TailSigma.tailSigma_le X hX_meas
  have hX0 : Measurable (X 0) := hX_meas 0
  -- For each rational q, the Iic-q values agree a.e. via the existing local Iic-integral
  -- identity on the LHS and condExpKernel_ae_eq_condExp on the RHS, both equal to
  -- alphaIicCE X q ω.
  have h_each_q : ∀ q : ℚ, ∀ᵐ ω ∂μ,
      (directing_measure X hX_contract hX_meas hX_L2 ω) (Iic (q : ℝ))
        = (Measure.map (X 0)
            (condExpKernel (μ := μ) (m := TailSigma.tailSigma X) ω)) (Iic (q : ℝ)) := by
    intro q
    set t : ℝ := (q : ℝ) with ht_def
    have hIic_meas : MeasurableSet (Iic t) := measurableSet_Iic
    have hpreim_meas : MeasurableSet (X 0 ⁻¹' Iic t) := hX0 hIic_meas
    -- LHS in real form: ∫ (Iic t).indicator 1 ∂(directing_measure ω) =ᵐ alphaIicCE X t ω.
    have h_lhs :
        (fun ω => ∫ x, (Iic t).indicator (fun _ => (1:ℝ)) x
                        ∂(directing_measure X hX_contract hX_meas hX_L2 ω))
          =ᵐ[μ] alphaIicCE X hX_contract hX_meas hX_L2 t :=
      directing_measure_integral_Iic_ae_eq_alphaIicCE X hX_contract hX_meas hX_L2 t
    -- RHS in real form: (condExpKernel μ m ω).real (X 0 ⁻¹' Iic t)
    --   =ᵐ μ[(X 0 ⁻¹' Iic t).indicator 1 | tailSigma X] ω
    have h_rhs_real :
        (fun ω => (condExpKernel (μ := μ) (m := TailSigma.tailSigma X) ω).real
                    (X 0 ⁻¹' Iic t))
          =ᵐ[μ]
        μ[(X 0 ⁻¹' Iic t).indicator (fun _ => (1:ℝ))
            | TailSigma.tailSigma X] :=
      condExpKernel_ae_eq_condExp hm_le hpreim_meas
    -- The set indicator (X 0 ⁻¹' Iic t).indicator 1 equals indIic t ∘ X 0 as functions.
    have h_fun_eq :
        ((X 0 ⁻¹' Iic t).indicator (fun _ => (1 : ℝ)))
          = indIic t ∘ X 0 := by
      funext ω'
      simp [indIic, Set.indicator, Set.mem_preimage, Set.mem_Iic]
    -- Combine.
    filter_upwards [h_lhs, h_rhs_real] with ω hω_lhs hω_rhs
    haveI : IsProbabilityMeasure (directing_measure X hX_contract hX_meas hX_L2 ω) :=
      directing_measure_isProbabilityMeasure X hX_contract hX_meas hX_L2 ω
    haveI : IsProbabilityMeasure
        (Measure.map (X 0)
          (condExpKernel (μ := μ) (m := TailSigma.tailSigma X) ω)) :=
      Measure.isProbabilityMeasure_map hX0.aemeasurable
    -- alphaIicCE := μ[indIic t ∘ X 0 | tailSigma X]; via h_fun_eq it equals the indicator form.
    have h_alpha_eq_condProb :
        alphaIicCE X hX_contract hX_meas hX_L2 t ω
          = μ[(X 0 ⁻¹' Iic t).indicator (fun _ => (1:ℝ))
              | TailSigma.tailSigma X] ω := by
      show μ[(indIic t) ∘ X 0 | TailSigma.tailSigma X] ω = _
      rw [← h_fun_eq]
    -- Both sides have the same `.toReal`: equal to alphaIicCE t ω.
    have h_lhs_toReal :
        ((directing_measure X hX_contract hX_meas hX_L2 ω) (Iic t)).toReal
          = alphaIicCE X hX_contract hX_meas hX_L2 t ω := by
      rw [← hω_lhs]
      exact (integral_indicator_one hIic_meas).symm
    have h_rhs_toReal :
        ((Measure.map (X 0)
            (condExpKernel (μ := μ) (m := TailSigma.tailSigma X) ω)) (Iic t)).toReal
          = alphaIicCE X hX_contract hX_meas hX_L2 t ω := by
      rw [Measure.map_apply hX0 hIic_meas]
      have : ((condExpKernel (μ := μ) (m := TailSigma.tailSigma X) ω)
                (X 0 ⁻¹' Iic t)).toReal
              = (condExpKernel (μ := μ) (m := TailSigma.tailSigma X) ω).real
                  (X 0 ⁻¹' Iic t) := rfl
      rw [this, hω_rhs, ← h_alpha_eq_condProb]
    -- Lift .toReal equality back to ENNReal values (both measures are finite/probability).
    have h_lhs_ne_top :
        (directing_measure X hX_contract hX_meas hX_L2 ω) (Iic t) ≠ ⊤ :=
      measure_ne_top _ _
    have h_rhs_ne_top :
        (Measure.map (X 0)
          (condExpKernel (μ := μ) (m := TailSigma.tailSigma X) ω)) (Iic t) ≠ ⊤ :=
      measure_ne_top _ _
    rw [← ENNReal.ofReal_toReal h_lhs_ne_top, ← ENNReal.ofReal_toReal h_rhs_ne_top,
        h_lhs_toReal, h_rhs_toReal]
  -- a.e.-for-each-q ⇒ a.e.-for-all-q.
  have h_all_q : ∀ᵐ ω ∂μ, ∀ q : ℚ,
      (directing_measure X hX_contract hX_meas hX_L2 ω) (Iic (q : ℝ))
        = (Measure.map (X 0)
            (condExpKernel (μ := μ) (m := TailSigma.tailSigma X) ω)) (Iic (q : ℝ)) :=
    ae_all_iff.mpr h_each_q
  -- For each such ω, both measures are probability, agreeing on the rational Iic π-system
  -- that generates the Borel σ-algebra. Hence equal.
  filter_upwards [h_all_q] with ω hω
  haveI : IsProbabilityMeasure
      (directing_measure X hX_contract hX_meas hX_L2 ω) :=
    directing_measure_isProbabilityMeasure X hX_contract hX_meas hX_L2 ω
  haveI : IsProbabilityMeasure
      (Measure.map (X 0) (condExpKernel (μ := μ) (m := TailSigma.tailSigma X) ω)) :=
    Measure.isProbabilityMeasure_map hX0.aemeasurable
  refine MeasureTheory.ext_of_generate_finite
      (⋃ a : ℚ, {Iic (a : ℝ)})
      ?_ Real.isPiSystem_Iic_rat ?_ (by simp)
  · -- borel ℝ = generateFrom (⋃ a : ℚ, {Iic (a : ℝ)})
    rw [BorelSpace.measurable_eq (α := ℝ), Real.borel_eq_generateFrom_Iic_rat]
  · rintro s hs
    simp only [Set.mem_iUnion, Set.mem_singleton_iff] at hs
    obtain ⟨q, rfl⟩ := hs
    exact hω q

end Exchangeability.DeFinetti.ViaL2
