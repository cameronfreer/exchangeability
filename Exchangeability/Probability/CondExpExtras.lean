/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Exchangeability.Probability.CondExpBasic
import Exchangeability.Probability.CondExp
import Exchangeability.Probability.CondProb
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Conditional
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.CondVar
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondexpL2
import Mathlib.MeasureTheory.PiSystem
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-!
# Conditional Expectation Lemmas Parked for Future Use

This file gathers results about conditional expectations, conditional independence, and
martingale-style arguments that are not yet needed by the main de Finetti development.
Keeping them in a separate module lets `CondExp.lean` stay lightweight while we iterate on
potential mathlib contributions.

The main themes covered here are:

* L² identification lemmas for conditional expectations;
* distributional equality and conditional expectation relationships;
* auxiliary conditional independence characterizations via conditional probabilities;
* product formulas for conditional expectations of indicators.

**Note:** The main conditional independence characterization `condIndep_of_indicator_condexp_eq`
(used in ViaMartingale.lean) is in `CondExp.lean`, not here.

Whenever a statement from this file becomes part of mathlib or is required in the main
development, it should be moved out of this “parking lot”.
-/

noncomputable section
open scoped MeasureTheory ProbabilityTheory Topology
open MeasureTheory Filter Set Function

namespace Exchangeability.Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-! ### L² martingale lemma -/

section MartingaleL2

-- Lean needs the ambient `[MeasurableSpace Ω]` to form `Measure Ω`.
-- The lemma below only uses it through those measures, so we silence
-- `linter.unusedSectionVars` to avoid a spurious warning.
set_option linter.unusedSectionVars false

/-- L² identification lemma: if `X₂` is square-integrable and
`μ[X₂ | m₁] = X₁`, while the second moments of `X₁` and `X₂` coincide,
then `X₁ = X₂` almost everywhere.

This uses Pythagoras identity in L²: conditional expectation is orthogonal projection,
so E[(X₂ - E[X₂|m₁])²] = E[X₂²] - E[(E[X₂|m₁])²].
Use `MemLp.condExpL2_ae_eq_condExp` and `eLpNorm_condExp_le`.
-/
lemma bounded_martingale_l2_eq {m₀ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {m₁ : MeasurableSpace Ω}
    (hm₁ : m₁ ≤ m₀) [SigmaFinite (μ.trim hm₁)]
    {X₁ X₂ : Ω → ℝ} (hL2 : MemLp X₂ 2 μ)
    (hmg : μ[X₂ | m₁] =ᵐ[μ] X₁)
    (hSecond : ∫ ω, (X₂ ω)^2 ∂μ = ∫ ω, (X₁ ω)^2 ∂μ) :
    X₁ =ᵐ[μ] X₂ := by
  classical
  -- Abbreviate the conditional expectation.
  set Y : Ω → ℝ := μ[X₂ | m₁] with hY
  have hY_eq_X₁ : Y =ᵐ[μ] X₁ := by simpa [hY] using hmg
  -- Square-integrability is inherited by the conditional expectation.
  have hY_mem : MemLp Y 2 μ := by
    simpa [hY] using (MemLp.condExp (m := m₁) (μ := μ) (m₀ := m₀) hL2)
  have h_diff_mem : MemLp (fun ω => X₂ ω - Y ω) 2 μ := hL2.sub hY_mem
  have h_diff_sq_int :
      Integrable (fun ω => (X₂ ω - Y ω) ^ 2) μ := h_diff_mem.integrable_sq

  -- Integrate the variance decomposition to obtain ∫ Var = 0.
  have hVar_decomp :
      Var[X₂; μ | m₁]
        =ᵐ[μ] μ[(fun ω => (X₂ ω) ^ 2) | m₁] - μ[X₂ | m₁] ^ 2 := by
    simpa [hY] using
      ProbabilityTheory.condVar_ae_eq_condExp_sq_sub_sq_condExp
        (μ := μ) (m := m₁) (m₀ := m₀) (X := X₂) (hm := hm₁) (hX := hL2)
  have h_var_integral_zero :
      ∫ ω, Var[X₂; μ | m₁] ω ∂μ = 0 := by
    have hInt_cond_sq :
        Integrable (fun ω => μ[(fun ω => (X₂ ω) ^ 2) | m₁] ω) μ :=
      integrable_condExp (μ := μ) (m := m₁) (f := fun ω => (X₂ ω) ^ 2)
    have hInt_Y_sq :
        Integrable (fun ω => (μ[X₂ | m₁] ω) ^ 2) μ :=
      (MemLp.condExp (m := m₁) (μ := μ) (m₀ := m₀) hL2).integrable_sq
    have hInt_cond_sq_eq :
        ∫ ω, μ[(fun ω => (X₂ ω) ^ 2) | m₁] ω ∂μ
          = ∫ ω, (X₂ ω) ^ 2 ∂μ := by
      simpa using
        (integral_condExp (μ := μ) (m := m₁) (m₀ := m₀)
          (hm := hm₁) (f := fun ω => (X₂ ω) ^ 2))
    have hInt_Y_sq_eq :
        ∫ ω, (μ[X₂ | m₁] ω) ^ 2 ∂μ = ∫ ω, (X₁ ω) ^ 2 ∂μ := by
      have := integral_congr_ae (EventuallyEq.fun_comp hmg fun x => x ^ 2)
      simpa [hY] using this
    calc
      ∫ ω, Var[X₂; μ | m₁] ω ∂μ
          = ∫ ω, (μ[(fun ω => (X₂ ω) ^ 2) | m₁] ω
                - (μ[X₂ | m₁] ω) ^ 2) ∂μ := by
              exact integral_congr_ae hVar_decomp
      _ = ∫ ω, μ[(fun ω => (X₂ ω) ^ 2) | m₁] ω ∂μ
              - ∫ ω, (μ[X₂ | m₁] ω) ^ 2 ∂μ := by
              exact integral_sub hInt_cond_sq hInt_Y_sq
      _ = ∫ ω, (X₂ ω) ^ 2 ∂μ - ∫ ω, (X₁ ω) ^ 2 ∂μ := by
        simp [hInt_cond_sq_eq, hInt_Y_sq_eq]
      _ = 0 := by
        simp [hSecond]

  -- Non-negativity and integrability of the conditional variance.
  have hVar_nonneg : 0 ≤ᵐ[μ] Var[X₂; μ | m₁] := by
    have h_sq_nonneg :
        0 ≤ᵐ[μ] fun ω => (X₂ ω - Y ω) ^ 2 :=
      Eventually.of_forall fun ω => sq_nonneg _
    simpa [ProbabilityTheory.condVar, hY] using
      condExp_nonneg (μ := μ) (m := m₁) h_sq_nonneg
  have hVar_integrable :
      Integrable (Var[X₂; μ | m₁]) μ :=
    ProbabilityTheory.integrable_condVar (m := m₁) (μ := μ) (X := X₂)
  have hVar_zero :
      Var[X₂; μ | m₁] =ᵐ[μ] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hVar_nonneg hVar_integrable).1 h_var_integral_zero

  -- Relate the integral of the conditional variance to the square error.
  have h_diff_sq_int_zero :
      ∫ ω, (X₂ ω - Y ω) ^ 2 ∂μ = 0 := by
    have hset :
        ∫ ω, Var[X₂; μ | m₁] ω ∂μ
            = ∫ ω, (X₂ ω - μ[X₂ | m₁] ω) ^ 2 ∂μ := by
      simpa [setIntegral_univ] using
        ProbabilityTheory.setIntegral_condVar
          (μ := μ) (m := m₁) (X := X₂) (hm := hm₁)
          (s := Set.univ) h_diff_sq_int MeasurableSet.univ
    have hIntVar : ∫ ω, Var[X₂; μ | m₁] ω ∂μ = 0 := by
      simpa using integral_congr_ae hVar_zero
    simpa [hY] using hset.symm.trans hIntVar

  -- Deduce that the square error vanishes almost everywhere.
  have h_sq_zero :
      (fun ω => (X₂ ω - Y ω) ^ 2) =ᵐ[μ] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae
        (Eventually.of_forall fun ω => sq_nonneg _) h_diff_sq_int).1 h_diff_sq_int_zero
  have h_diff_zero :
      (fun ω => X₂ ω - Y ω) =ᵐ[μ] 0 :=
    h_sq_zero.mono fun ω hω => sq_eq_zero_iff.mp hω
  have hX₂_eq_Y : X₂ =ᵐ[μ] Y :=
    h_diff_zero.mono fun ω hω => sub_eq_zero.mp hω

  -- Combine the identities.
  exact hY_eq_X₁.symm.trans hX₂_eq_Y.symm

end MartingaleL2

/-!
### Reverse martingale convergence (future work)

Statements about reverse martingale convergence are intended to live here once the necessary
downward conditional expectation limit lemmas appear in mathlib. The placeholder remains so
the expected home for those results is easy to locate.
-/

/-! ### Distributional Equality and Conditional Expectations -/

/-- If the joint laws of `(ξ, η)` and `(ξ, ζ)` coincide, then any integrable observable of the
pair has the same expectation. -/
lemma integral_pair_eq_of_joint_eq {μ : Measure Ω}
    {ξ η ζ : Ω → α} {φ : α × α → ℝ}
    (hξ : Measurable ξ) (hη : Measurable η) (hζ : Measurable ζ)
    (hφ :
      AEStronglyMeasurable φ (Measure.map (fun ω => (ξ ω, η ω)) μ))
    (hφ_int :
      Integrable φ (Measure.map (fun ω => (ξ ω, η ω)) μ))
    (h_dist :
      Measure.map (fun ω => (ξ ω, η ω)) μ
        = Measure.map (fun ω => (ξ ω, ζ ω)) μ) :
    ∫ ω, φ (ξ ω, η ω) ∂μ = ∫ ω, φ (ξ ω, ζ ω) ∂μ := by
  classical
  set fη : Ω → α × α := fun ω => (ξ ω, η ω)
  set fζ : Ω → α × α := fun ω => (ξ ω, ζ ω)
  have hfη : AEMeasurable fη μ := (hξ.prodMk hη).aemeasurable
  have hfζ : AEMeasurable fζ μ := (hξ.prodMk hζ).aemeasurable
  have hφ_meas_zeta :
      AEStronglyMeasurable φ (Measure.map fζ μ) := by
    simpa [fη, fζ, h_dist] using hφ
  have hφ_int_zeta :
      Integrable φ (Measure.map fζ μ) := by
    simpa [fη, fζ, h_dist] using hφ_int
  have h_eta :
      ∫ ω, φ (ξ ω, η ω) ∂μ = ∫ p, φ p ∂(Measure.map fη μ) := by
    simpa [fη] using
      (MeasureTheory.integral_map (μ := μ) (φ := fη) (f := φ)
        hfη hφ).symm
  have h_zeta :
      ∫ ω, φ (ξ ω, ζ ω) ∂μ = ∫ p, φ p ∂(Measure.map fζ μ) := by
    simpa [fζ] using
      (MeasureTheory.integral_map (μ := μ) (φ := fζ) (f := φ)
        hfζ hφ_meas_zeta).symm
  calc
    ∫ ω, φ (ξ ω, η ω) ∂μ
        = ∫ p, φ p ∂(Measure.map fη μ) := h_eta
    _ = ∫ p, φ p ∂(Measure.map fζ μ) := by simp [fη, fζ, h_dist]
    _ = ∫ ω, φ (ξ ω, ζ ω) ∂μ := h_zeta.symm

/-- If `(ξ, η)` and `(ξ, ζ)` share the same joint law, then for every measurable `g` and
measurable set `s`, the mixed moments `E[g(ξ) · 𝟙_{η ∈ s}]` and `E[g(ξ) · 𝟙_{ζ ∈ s}]` agree. -/
lemma condexp_same_dist {μ : Measure Ω}
    {ξ η ζ : Ω → α} {g : α → ℝ}
    (hξ : Measurable ξ) (hη : Measurable η) (hζ : Measurable ζ)
    (hg : Measurable g) (h_int : Integrable (fun ω => g (ξ ω)) μ)
    (h_dist : Measure.map (fun ω => (ξ ω, η ω)) μ
              = Measure.map (fun ω => (ξ ω, ζ ω)) μ)
    {s : Set α} (hs : MeasurableSet s) :
    ∫ ω, g (ξ ω) * s.indicator (fun _ : α => (1 : ℝ)) (η ω) ∂μ
      = ∫ ω, g (ξ ω) * s.indicator (fun _ : α => (1 : ℝ)) (ζ ω) ∂μ := by
  classical
  set φ : α × α → ℝ :=
    fun p => g p.1 * s.indicator (fun _ : α => (1 : ℝ)) p.2
  set fη : Ω → α × α := fun ω => (ξ ω, η ω)
  set fζ : Ω → α × α := fun ω => (ξ ω, ζ ω)
  have h_comp_eta :
      (fun ω => φ (fη ω)) =
        fun ω => g (ξ ω) * s.indicator (fun _ : α => (1 : ℝ)) (η ω) := by
    funext ω
    simp [fη, φ]
  have h_comp_zeta :
      (fun ω => φ (fζ ω)) =
        fun ω => g (ξ ω) * s.indicator (fun _ : α => (1 : ℝ)) (ζ ω) := by
    funext ω
    simp [fζ, φ]
  have h_eq_eta :
      (fun ω => g (ξ ω) * s.indicator (fun _ : α => (1 : ℝ)) (η ω)) =
        Set.indicator (η ⁻¹' s) (fun ω => g (ξ ω)) := by
    funext ω
    by_cases hmem : η ω ∈ s
    · simp [Set.indicator, hmem]
    · simp [Set.indicator, hmem]
  have h_indicator_eta :
      Integrable (fun ω => g (ξ ω) * s.indicator (fun _ : α => (1 : ℝ)) (η ω)) μ := by
    simpa [h_eq_eta] using h_int.indicator (hη hs)
  have hφ_meas :
      AEStronglyMeasurable φ (Measure.map fη μ) := by
    refine (hg.comp measurable_fst).aestronglyMeasurable.mul ?_
    have h_indicator :
        AEStronglyMeasurable (fun p : α × α => s.indicator (fun _ : α => (1 : ℝ)) p.2)
          (Measure.map fη μ) :=
      (Measurable.indicator measurable_const hs).aestronglyMeasurable.comp_measurable measurable_snd
    simpa [φ] using h_indicator
  have hfη : AEMeasurable fη μ := (hξ.prodMk hη).aemeasurable
  have hφ_int :
      Integrable φ (Measure.map fη μ) :=
    (integrable_map_measure (μ := μ) (f := fη) (g := φ)
        (hg := hφ_meas) (hf := hfη)).mpr
      (by simpa [Function.comp, h_comp_eta] using h_indicator_eta)
  have h_result :=
    integral_pair_eq_of_joint_eq (μ := μ) (ξ := ξ) (η := η) (ζ := ζ)
      hξ hη hζ hφ_meas hφ_int h_dist
  simpa [h_comp_eta, h_comp_zeta] using h_result
/-! ### Utilities for the Martingale Approach -/

set_option linter.unusedSectionVars false in
/-- Given conditional probabilities agreeing, establish conditional independence.
This is immediate from Doob's characterization above.
-/
lemma condIndep_of_condProb_eq {m₀ : MeasurableSpace Ω} {μ : Measure Ω}
    [StandardBorelSpace Ω] [IsFiniteMeasure μ]
    {mF mG mH : MeasurableSpace Ω}
    (hmF : mF ≤ m₀) (hmG : mG ≤ m₀) (hmH : mH ≤ m₀)
    (h : ∀ H, MeasurableSet[mH] H →
      μ[H.indicator (fun _ => (1 : ℝ)) | mF ⊔ mG]
        =ᵐ[μ] μ[H.indicator (fun _ => (1 : ℝ)) | mG]) :
    ProbabilityTheory.CondIndep mG mF mH hmG μ :=
  condIndep_of_indicator_condexp_eq hmF hmG hmH h

/-- **Pull‑out corollary of condExp_indicator_mul_indicator_of_condIndep**:
If, in addition, `B` is `m`‑measurable then
`μ[1_B | m] = 1_B` a.e., so we can pull the right factor out (as an indicator).

Formally:
```
μ[1_{A∩B} | m] = μ[1_A | m] · 1_B     a.e.   (when B ∈ m)
```

This follows from `condExp_indicator_mul_indicator_of_condIndep` by noting that
when B is m-measurable, μ[1_B | m] = 1_B a.e. (idempotence of conditional expectation).
-/
lemma condExp_indicator_mul_indicator_of_condIndep_pullout
    {Ω : Type*} {m₀ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {m mF mH : MeasurableSpace Ω} {μ : @Measure Ω m₀}
    [IsFiniteMeasure μ]
    (hm  : m  ≤ m₀) (hmF : mF ≤ m₀) (hmH : mH ≤ m₀)
    (hCI : ProbabilityTheory.CondIndep m mF mH hm μ)
    {A B : Set Ω} (hA : MeasurableSet[mF] A) (hB : MeasurableSet[mH] B)
    (hB_m : MeasurableSet[m] B) :
  μ[(A ∩ B).indicator (fun _ => (1 : ℝ)) | m]
    =ᵐ[μ]
  (μ[A.indicator (fun _ => (1 : ℝ)) | m]
   * B.indicator (fun _ => (1 : ℝ))) := by
  -- Step 1: Apply the general product formula
  have h_prod : μ[(A ∩ B).indicator (fun _ => (1 : ℝ)) | m] =ᵐ[μ]
      (μ[A.indicator (fun _ => (1 : ℝ)) | m] * μ[B.indicator (fun _ => (1 : ℝ)) | m]) :=
    condExp_indicator_mul_indicator_of_condIndep hm hmF hmH hCI hA hB

  -- Step 2: Since B is m-measurable, μ[1_B | m] = 1_B (idempotence)
  -- Need to show B.indicator is strongly measurable w.r.t. m
  have hB_sm : StronglyMeasurable[m] (B.indicator (fun _ => (1 : ℝ))) :=
    (Measurable.indicator measurable_const hB_m).stronglyMeasurable
  have hB_int : Integrable (B.indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator (hm _ hB_m)
  have h_idem : μ[B.indicator (fun _ => (1 : ℝ)) | m] = B.indicator (fun _ => (1 : ℝ)) :=
    condExp_of_stronglyMeasurable hm hB_sm hB_int

  -- Step 3: Combine using EventuallyEq.mul
  rw [h_idem] at h_prod
  exact h_prod

end Exchangeability.Probability
