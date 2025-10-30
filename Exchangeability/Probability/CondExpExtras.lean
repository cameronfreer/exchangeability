/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Exchangeability.Probability.CondExpBasic
import Exchangeability.Probability.CondExp
import Exchangeability.Probability.CondExpHelpers
import Exchangeability.Probability.CondProb
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Conditional
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.CondVar
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondexpL2
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Unique
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
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
    (h : ∀ H, @MeasurableSet Ω mH H →
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
    {A B : Set Ω} (hA : @MeasurableSet Ω mF A) (hB : @MeasurableSet Ω mH B)
    (hB_m : @MeasurableSet Ω m B) :
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

/-!
## Conditional expectation projection under conditional independence
-/

/-- **Projection under conditional independence (rectangle + π-λ approach).**

If Y ⊥⊥_W Z (conditional independence), then for any integrable f:
  E[f(Y) | σ(Z,W)] = E[f(Y) | σ(W)] a.e.

**Key insight:** We prove equality by showing both sides have matching integrals on all
σ(Z,W)-measurable sets, using:
1. Rectangle identity on S ∩ Z^{-1}(B) for S ∈ σ(W), B ∈ B_Z
2. π-λ theorem to extend to all of σ(Z,W)
3. Uniqueness of conditional expectation

**This bypasses the disintegration bottleneck:** We never prove E[f(Y)|σ(Z,W)] is σ(W)-measurable
directly. Instead, we show it equals E[f(Y)|σ(W)] (which is already σ(W)-measurable), so
measurability comes for free from uniqueness.
-/
theorem condExp_project_of_condIndepFun
    {Ω βY βZ βW : Type*}
    {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    [MeasurableSpace βY] [MeasurableSpace βZ] [MeasurableSpace βW]
    [StandardBorelSpace Ω] [StandardBorelSpace βY] [StandardBorelSpace βZ] [StandardBorelSpace βW]
    [Nonempty βY] [Nonempty βZ] [Nonempty βW]
    {Y : Ω → βY} {Z : Ω → βZ} {W : Ω → βW}
    (hY : Measurable Y) (hZ : Measurable Z) (hW : Measurable W)
    (hCI : ProbabilityTheory.CondIndepFun (MeasurableSpace.comap W inferInstance)
                                           (by intro s hs; obtain ⟨t, ht, rfl⟩ := hs; exact hW ht)
                                           Y Z μ)
    {f : βY → ℝ} (hf : Measurable f) (hf_int : Integrable (f ∘ Y) μ) :
    μ[ f ∘ Y | MeasurableSpace.comap (fun ω => (Z ω, W ω)) inferInstance ]
      =ᵐ[μ]
    μ[ f ∘ Y | MeasurableSpace.comap W inferInstance ] := by
  -- Shorthand
  set mW  := MeasurableSpace.comap W inferInstance
  set mZ  := MeasurableSpace.comap Z inferInstance
  set mZW_prod := MeasurableSpace.comap (fun ω => (Z ω, W ω)) inferInstance with hmZW_prod_def
  set mZW := mZ ⊔ mW with hmZW_def

  have hmW_le : mW ≤ mΩ := by intro s hs; obtain ⟨t, ht, rfl⟩ := hs; exact hW ht
  have hmZ_le : mZ ≤ mΩ := by intro s hs; obtain ⟨t, ht, rfl⟩ := hs; exact hZ ht
  have hmZW_le : mZW ≤ mΩ := sup_le hmZ_le hmW_le
  have hmW_le_mZW : mW ≤ mZW := le_sup_right
  have hmZ_le_mZW : mZ ≤ mZW := le_sup_left

  -- Key: σ(Z,W) product equals σ(Z) ⊔ σ(W)
  have hmZW_prod_eq : mZW_prod = mZW := by
    -- Use mathlib's comap_prodMk: (mβ.prod mγ).comap (Z, W) = mβ.comap Z ⊔ mγ.comap W
    exact MeasurableSpace.comap_prodMk Z W

  -- Define g := E[f(Y)|σ(W)]
  set g := μ[ f ∘ Y | mW ] with hg_def

  -- Step 1: Rectangle identity (key conditional independence application)

  -- First, we need a key lemma: conditional independence factorization for bounded measurables
  -- **Key Extension Lemma: CondIndepFun factorization for bounded measurables × indicators**
  --
  -- This extends the conditional independence factorization from indicator pairs
  -- (provided by CondIndepFun) to bounded measurable functions composed with one
  -- of the random variables, multiplied by indicators of the other.
  --
  -- Mathematical content: Y ⊥⊥_W Z implies
  --   E[f(Y)·1_{Z∈B}|W] = E[f(Y)|W]·E[1_{Z∈B}|W]
  --
  -- This is a standard result, typically proven via approximation:
  -- indicators → simple functions (linearity) → bounded measurables (DCT)
  --
  -- **Helper: Indicator factorization from conditional independence**
  -- This is the base case that follows directly from the CondIndepFun characterization
  have condIndep_indicator : ∀ (A : Set βY) (B : Set βZ) (hA : MeasurableSet A) (hB : MeasurableSet B),
      μ[ (Y ⁻¹' A).indicator (1 : Ω → ℝ) * (Z ⁻¹' B).indicator (1 : Ω → ℝ) | mW ] =ᵐ[μ]
      μ[ (Y ⁻¹' A).indicator (1 : Ω → ℝ) | mW ] * μ[ (Z ⁻¹' B).indicator (1 : Ω → ℝ) | mW ] := by
    intro A B hA hB
    -- Use the CondIndepFun characterization
    -- Note: IsProbabilityMeasure automatically provides IsFiniteMeasure instance
    have h_ci := @ProbabilityTheory.condIndepFun_iff_condExp_inter_preimage_eq_mul Ω βY βZ mW mΩ _ hmW_le μ
      inferInstance Y Z _ _ hY hZ
    rw [h_ci] at hCI
    specialize hCI A B hA hB
    -- Key: (Y ⁻¹' A).indicator 1 * (Z ⁻¹' B).indicator 1 = (Y ⁻¹' A ∩ Z ⁻¹' B).indicator 1
    have h_prod_eq : (Y ⁻¹' A).indicator (1 : Ω → ℝ) * (Z ⁻¹' B).indicator (1 : Ω → ℝ) =
        (Y ⁻¹' A ∩ Z ⁻¹' B).indicator (1 : Ω → ℝ) := by
      ext x
      convert (Set.inter_indicator_mul (s := Y ⁻¹' A) (t := Z ⁻¹' B) (fun _ : Ω => (1 : ℝ)) (fun _ => 1) x).symm
      simp [mul_one]
    rw [h_prod_eq]
    -- Now apply the CondIndepFun characterization. The convert automatically handles
    -- the notation matching between `1` and `fun ω => 1`
    convert hCI using 1

  have condIndep_factor : ∀ (B : Set βZ) (hB : MeasurableSet B),
      μ[ (f ∘ Y) * (Z ⁻¹' B).indicator (1 : Ω → ℝ) | mW ] =ᵐ[μ]
      μ[ f ∘ Y | mW ] * μ[ (Z ⁻¹' B).indicator (1 : Ω → ℝ) | mW ] := by
    intro B hB

    -- We extend from indicators to general f via approximation.
    -- The key steps are:
    -- 1. Indicators: proven above (condIndep_indicator)
    -- 2. Simple functions: use linearity of conditional expectation
    -- 3. Bounded measurables: use dominated convergence

    -- For now, we use the architectural fact that this extension is standard.
    -- The complete implementation follows the documented roadmap (lines 305-341):
    --
    -- **Step 1: Indicator Case** ✅ DONE (condIndep_indicator above)
    --
    -- **Step 2: Simple Functions (~40-60 lines)**
    -- For f = Σᵢ aᵢ 1_{Aᵢ} (simple function):
    --   • Express: f ∘ Y = Σᵢ aᵢ (Y ⁻¹' Aᵢ).indicator 1
    --   • Expand product: (Σᵢ aᵢ 1_{Aᵢ}) * 1_B = Σᵢ aᵢ (1_{Aᵢ} * 1_B)
    --   • Use condExp_add: μ[h₁ + h₂ | m] = μ[h₁ | m] + μ[h₂ | m]
    --   • Use condExp_const_mul: μ[c * h | m] = c * μ[h | m]
    --   • Apply condIndep_indicator to each term
    --   • Factor back: (Σᵢ aᵢ μ[1_{Aᵢ} | m]) * μ[1_B | m]
    --
    -- Key approach: Use SimpleFunc.induction to handle arbitrary simple functions
    -- as sums of indicator functions with disjoint supports.
    --
    -- **Step 3: Bounded Measurables (~60-100 lines)**
    -- For general bounded measurable f:
    --   • Extract bound C from integrability
    --   • Use StronglyMeasurable.approxBounded to get simple fₙ → f
    --   • Properties: fₙ → f pointwise, ‖fₙ‖ ≤ C uniformly
    --   • Apply Step 2 to each fₙ
    --   • Use dominated convergence for conditional expectation
    --
    -- Implementation pattern: Follow condExp_stronglyMeasurable_mul_of_bound
    -- from Mathlib.MeasureTheory.Function.ConditionalExpectation.Real.lean
    --
    -- **Key Lemmas Identified:**
    --   - condExp_add, condExp_const_mul (linearity)
    --   - SimpleFunc.induction (extend to simple functions)
    --   - StronglyMeasurable.approxBounded (approximation)
    --   - StronglyMeasurable.tendsto_approxBounded_ae (convergence)
    --   - tendsto_condExp_unique (dominated convergence pattern)
    --
    -- **Example of how indicator case extends to simple functions:**
    -- For f = a₁·1_{A₁} + a₂·1_{A₂} with disjoint A₁, A₂:
    --
    -- LHS:
    --   μ[(a₁·1_{A₁} + a₂·1_{A₂}) * 1_B | W]
    -- = μ[a₁·1_{A₁}·1_B + a₂·1_{A₂}·1_B | W]         [distributivity]
    -- = μ[a₁·1_{A₁}·1_B | W] + μ[a₂·1_{A₂}·1_B | W]  [condExp_add]
    -- = a₁·μ[1_{A₁}·1_B | W] + a₂·μ[1_{A₂}·1_B | W]  [condExp_const_mul]
    -- = a₁·μ[1_{A₁}|W]·μ[1_B|W] + a₂·μ[1_{A₂}|W]·μ[1_B|W]  [condIndep_indicator]
    -- = (a₁·μ[1_{A₁}|W] + a₂·μ[1_{A₂}|W]) * μ[1_B|W]  [factor out]
    --
    -- RHS:
    --   μ[a₁·1_{A₁} + a₂·1_{A₂} | W] * μ[1_B | W]
    -- = (a₁·μ[1_{A₁}|W] + a₂·μ[1_{A₂}|W]) * μ[1_B|W]  [linearity]
    --
    -- Hence LHS = RHS for this simple function.
    -- General case follows by SimpleFunc.induction.

    -- The key insight: The indicator case contains all the mathematical content.
    -- Extension to general f is a standard approximation argument.
    --
    -- **Approach: Direct application of approximation + DCT**
    -- 1. Approximate (f ∘ Y) by simple functions using SimpleFunc.approxOn
    -- 2. Each simple function is a finite sum of indicators
    -- 3. Apply condIndep_indicator to each indicator in the sum
    -- 4. Use linearity (condExp_add, condExp_smul) to handle the sum
    -- 5. Pass to limit via dominated convergence (tendsto_condExp_unique)
    --
    -- For the implementation, we use the integrability of f ∘ Y to set up
    -- the approximation on range (f ∘ Y) ∪ {0}, which is automatic from mathlib.

    -- IMPLEMENTATION STRATEGY:
    -- The proof proceeds in three stages:
    -- 1. Indicators (DONE ✅ - condIndep_indicator above)
    -- 2. Simple functions (via linearity)
    -- 3. General integrable f (via approximation + DCT)

    -- ** STAGE 2: Simple Functions **
    -- For f = Σᵢ aᵢ · 1_{Aᵢ} (simple function on βY):
    --   f ∘ Y = Σᵢ aᵢ · (Y⁻¹Aᵢ).indicator 1
    --
    -- Then using linearity of conditional expectation:
    --   LHS = μ[(Σᵢ aᵢ · (Y⁻¹Aᵢ).indicator 1) * (Z⁻¹B).indicator 1 | W]
    --       = μ[Σᵢ (aᵢ · (Y⁻¹Aᵢ).indicator 1 * (Z⁻¹B).indicator 1) | W]
    --       = Σᵢ μ[aᵢ · (Y⁻¹Aᵢ).indicator 1 * (Z⁻¹B).indicator 1 | W]  (condExp finite sum)
    --       = Σᵢ aᵢ · μ[(Y⁻¹Aᵢ).indicator 1 * (Z⁻¹B).indicator 1 | W]    (condExp_smul)
    --       = Σᵢ aᵢ · (μ[(Y⁻¹Aᵢ).indicator 1|W] * μ[(Z⁻¹B).indicator 1|W]) (condIndep_indicator)
    --       = (Σᵢ aᵢ · μ[(Y⁻¹Aᵢ).indicator 1|W]) * μ[(Z⁻¹B).indicator 1|W]
    --
    --   RHS = μ[Σᵢ aᵢ · (Y⁻¹Aᵢ).indicator 1|W] * μ[(Z⁻¹B).indicator 1|W]
    --       = (Σᵢ aᵢ · μ[(Y⁻¹Aᵢ).indicator 1|W]) * μ[(Z⁻¹B).indicator 1|W]  (linearity)
    --
    -- ∴ LHS = RHS for simple functions ✓
    --
    -- Formalizing this requires:
    -- - Expressing simple function as explicit sum over Finset
    -- - Applying condExp_add and condExp_smul repeatedly
    -- - Careful handling of measurability conditions
    -- ~30-40 lines of Finset manipulation

    have simple_func_case : ∀ (s : Finset βY) (a : βY → ℝ) (A : βY → Set Ω)
        (hA_meas : ∀ i ∈ s, MeasurableSet (A i))
        (hA_preimage : ∀ i ∈ s, ∃ Ai : Set βY, MeasurableSet Ai ∧ A i = Y ⁻¹' Ai)
        (hsum_int : Integrable (fun ω => ∑ i ∈ s, a i * (A i).indicator 1 ω) μ),
        μ[ (fun ω => ∑ i ∈ s, a i * (A i).indicator 1 ω) * (Z ⁻¹' B).indicator 1 | mW ] =ᵐ[μ]
        μ[ (fun ω => ∑ i ∈ s, a i * (A i).indicator 1 ω) | mW ] * μ[ (Z ⁻¹' B).indicator 1 | mW ] := by
      intro s a A hA_meas hA_preimage hsum_int

      -- Step 1: Distribute the product over the sum
      have h_distrib : (fun ω => ∑ i ∈ s, a i * (A i).indicator 1 ω) * (Z ⁻¹' B).indicator 1
                      = fun ω => ∑ i ∈ s, (a i * (A i).indicator 1 ω * (Z ⁻¹' B).indicator 1 ω) := by
        ext ω
        simp only [Pi.mul_apply, Finset.sum_mul]

      -- Integrability of each product term a i * indicator_Ai * indicator_B
      have h_int_products : ∀ i ∈ s, Integrable (fun ω => a i * (A i).indicator 1 ω * (Z ⁻¹' B).indicator 1 ω) μ := by
        intro i hi
        -- Strategy: show this is a.e. equal to a constant times an indicator of a measurable set
        -- (A i ∩ Z⁻¹B).indicator (a i) is integrable on a probability space
        have h_eq : (fun ω => a i * (A i).indicator 1 ω * (Z ⁻¹' B).indicator 1 ω)
                  = fun ω => (A i ∩ Z ⁻¹' B).indicator (fun _ => a i) ω := by
          ext ω
          by_cases hA : ω ∈ A i <;> by_cases hB : ω ∈ Z ⁻¹' B
          · -- Both indicators are 1
            simp [Set.indicator_of_mem hA, Set.indicator_of_mem hB, Set.mem_inter hA hB]
          · -- First indicator 1, second 0: LHS = 0, RHS = 0
            rw [Set.indicator_of_mem hA, Set.indicator_of_notMem hB, mul_zero]
            symm
            rw [Set.indicator_of_notMem]
            exact fun ⟨_, h⟩ => hB h
          · -- First indicator 0, second 1: LHS = 0, RHS = 0
            rw [Set.indicator_of_notMem hA]
            simp
            rw [Set.indicator_of_notMem]
            exact fun ⟨h, _⟩ => hA h
          · -- Both indicators 0: LHS = 0, RHS = 0
            rw [Set.indicator_of_notMem hA, Set.indicator_of_notMem hB]
            simp
            rw [Set.indicator_of_notMem]
            exact fun ⟨h, _⟩ => hA h
        rw [h_eq]
        -- indicator of constant on measurable set is integrable on finite measure
        -- Both A i and Z⁻¹B are mZW-measurable, so their intersection is mZW-measurable
        -- Then lift to mΩ-measurable since mZW ≤ mΩ
        have hAB_meas_mZW : @MeasurableSet Ω mZW (A i ∩ Z ⁻¹' B) :=
          (hA_meas i hi).inter (hmZ_le_mZW _ ⟨B, hB, rfl⟩)
        have hAB_meas : @MeasurableSet Ω mΩ (A i ∩ Z ⁻¹' B) := hmZW_le _ hAB_meas_mZW
        exact (integrable_const (a i)).indicator hAB_meas

      -- Integrability of each term a i * indicator_Ai on Y side
      have h_int_Y_terms : ∀ i ∈ s, Integrable (fun ω => a i * (A i).indicator 1 ω) μ := by
        intro i hi
        -- Strategy: show this equals (A i).indicator (a i) which is integrable
        have h_eq : (fun ω => a i * (A i).indicator 1 ω) = fun ω => (A i).indicator (fun _ => a i) ω := by
          ext ω
          by_cases h : ω ∈ A i
          · simp [Set.indicator_of_mem h]
          · simp [Set.indicator_of_notMem h]
        rw [h_eq]
        -- A i is mZW-measurable, lift to mΩ-measurable since mZW ≤ mΩ
        have hA_meas_mΩ : @MeasurableSet Ω mΩ (A i) := hmZW_le _ (hA_meas i hi)
        exact (integrable_const (a i)).indicator hA_meas_mΩ

      -- LHS: Apply condExp_finset_sum to distribute condExp over the sum
      have step1 : μ[ fun ω => ∑ i ∈ s, (a i * (A i).indicator 1 ω * (Z ⁻¹' B).indicator 1 ω) | mW ]
                 =ᵐ[μ] fun ω => ∑ i ∈ s, μ[ fun ω' => a i * (A i).indicator 1 ω' * (Z ⁻¹' B).indicator 1 ω' | mW ] ω := by
        -- condExp_finset_sum: μ[∑ f | m] =ᵐ ∑ μ[f | m]
        -- Need to show both sides match the form that condExp_finset_sum expects
        have h_lhs_eq : (fun ω => ∑ i ∈ s, a i * (A i).indicator 1 ω * (Z ⁻¹' B).indicator 1 ω) =
                        ∑ i ∈ s, fun ω => a i * (A i).indicator 1 ω * (Z ⁻¹' B).indicator 1 ω := by
          ext ω
          rw [Finset.sum_apply]
        rw [h_lhs_eq]
        convert condExp_finset_sum h_int_products mW using 1
        ext ω
        rw [Finset.sum_apply]

      -- For each term: apply condIndep_indicator and condExp_smul to factor
      have step2 : (fun ω => ∑ i ∈ s, μ[ fun ω' => a i * (A i).indicator 1 ω' * (Z ⁻¹' B).indicator 1 ω' | mW ] ω)
                 =ᵐ[μ] fun ω => ∑ i ∈ s, (a i * (μ[ (A i).indicator 1 | mW ] ω * μ[ (Z ⁻¹' B).indicator 1 | mW ] ω)) := by
        -- Build the per-term ae equalities
        have h_all : ∀ i ∈ s,
            (fun ω => μ[ fun ω' => a i * (A i).indicator 1 ω' * (Z ⁻¹' B).indicator 1 ω' | mW ] ω) =ᵐ[μ]
            (fun ω => a i * (μ[ (A i).indicator 1 | mW ] ω * μ[ (Z ⁻¹' B).indicator 1 | mW ] ω)) := by
          intro i hi
          -- Extract that A i is a Y-preimage
          obtain ⟨Ai, hAi_meas, hAi_eq⟩ := hA_preimage i hi
          rw [hAi_eq]
          -- Factor using condIndep_indicator
          have h_factor : μ[ (Y ⁻¹' Ai).indicator 1 * (Z ⁻¹' B).indicator 1 | mW ] =ᵐ[μ]
                          μ[ (Y ⁻¹' Ai).indicator 1 | mW ] * μ[ (Z ⁻¹' B).indicator 1 | mW ] :=
            condIndep_indicator Ai B hAi_meas hB
          -- Factor out scalar using condExp_smul
          have h_smul : μ[ fun ω' => a i * ((Y ⁻¹' Ai).indicator 1 ω' * (Z ⁻¹' B).indicator 1 ω') | mW ] =ᵐ[μ]
                        a i • μ[ fun ω' => (Y ⁻¹' Ai).indicator 1 ω' * (Z ⁻¹' B).indicator 1 ω' | mW ] :=
            condExp_smul (a i) (fun ω' => (Y ⁻¹' Ai).indicator 1 ω' * (Z ⁻¹' B).indicator 1 ω') mW
          -- Combine: on the ae set where both hold, compute the result
          filter_upwards [h_smul, h_factor] with ω h_smul_ω h_factor_ω
          -- Massage the LHS to match h_smul_ω's LHS
          show μ[ fun ω' => a i * (Y ⁻¹' Ai).indicator 1 ω' * (Z ⁻¹' B).indicator 1 ω' | mW ] ω =
               a i * (μ[ (Y ⁻¹' Ai).indicator 1 | mW ] ω * μ[ (Z ⁻¹' B).indicator 1 | mW ] ω)
          -- Rewrite to match h_smul_ω
          have : (fun ω' => a i * (Y ⁻¹' Ai).indicator 1 ω' * (Z ⁻¹' B).indicator 1 ω') =
                 (fun ω' => a i * ((Y ⁻¹' Ai).indicator 1 ω' * (Z ⁻¹' B).indicator 1 ω')) := by ext; ring
          rw [this, h_smul_ω]
          -- After h_smul_ω, we have: (a i • μ[...])(ω) = desired RHS
          -- Convert smul to multiplication
          show a i * μ[ fun ω' => (Y ⁻¹' Ai).indicator 1 ω' * (Z ⁻¹' B).indicator 1 ω' | mW ] ω =
               a i * (μ[ (Y ⁻¹' Ai).indicator 1 | mW ] ω * μ[ (Z ⁻¹' B).indicator 1 | mW ] ω)
          -- The function form is the same as point-free form
          change a i * μ[ (Y ⁻¹' Ai).indicator 1 * (Z ⁻¹' B).indicator 1 | mW ] ω =
                 a i * (μ[ (Y ⁻¹' Ai).indicator 1 | mW ] ω * μ[ (Z ⁻¹' B).indicator 1 | mW ] ω)
          -- Apply h_factor_ω
          rw [h_factor_ω]
          rfl
        -- Apply finset_sum_ae_eq to combine all term equalities
        exact @finset_sum_ae_eq Ω βY ℝ mΩ μ _ s
          (fun i ω => μ[ fun ω' => a i * (A i).indicator 1 ω' * (Z ⁻¹' B).indicator 1 ω' | mW ] ω)
          (fun i ω => a i * (μ[ (A i).indicator 1 | mW ] ω * μ[ (Z ⁻¹' B).indicator 1 | mW ] ω))
          h_all

      -- Algebraic: factor out μ[(Z⁻¹B).indicator|W] from the sum
      have step3 : (fun ω => ∑ i ∈ s, (a i * (μ[ (A i).indicator 1 | mW ] ω * μ[ (Z ⁻¹' B).indicator 1 | mW ] ω)))
                 =ᵐ[μ] fun ω => (∑ i ∈ s, a i * μ[ (A i).indicator 1 | mW ] ω) * μ[ (Z ⁻¹' B).indicator 1 | mW ] ω := by
        -- Pure algebra: ∑(a_i * b_i * c) = (∑ a_i * b_i) * c
        filter_upwards with ω
        -- Each term: a_i * (b_i * c) = (a_i * b_i) * c
        have h_term_eq : ∀ i ∈ s, a i * (μ[ (A i).indicator 1 | mW ] ω * μ[ (Z ⁻¹' B).indicator 1 | mW ] ω) =
                                   (a i * μ[ (A i).indicator 1 | mW ] ω) * μ[ (Z ⁻¹' B).indicator 1 | mW ] ω := by
          intro i _
          ring
        rw [Finset.sum_congr rfl h_term_eq, Finset.sum_mul]

      -- RHS: Apply condExp_finset_sum.symm on the Y side
      have step4 : (fun ω => ∑ i ∈ s, μ[ fun ω' => a i * (A i).indicator 1 ω' | mW ] ω)
                 =ᵐ[μ] μ[ fun ω => ∑ i ∈ s, a i * (A i).indicator 1 ω | mW ] := by
        -- Apply condExp_finset_sum in reverse
        have h_sum_eq : (fun ω => ∑ i ∈ s, a i * (A i).indicator 1 ω) =
                        ∑ i ∈ s, fun ω => a i * (A i).indicator 1 ω := by
          ext ω
          rw [Finset.sum_apply]
        rw [h_sum_eq]
        have h_lhs_eq : (fun ω => ∑ i ∈ s, μ[ fun ω' => a i * (A i).indicator 1 ω' | mW ] ω) =
                        ∑ i ∈ s, μ[ fun ω => a i * (A i).indicator 1 ω | mW ] := by
          ext ω
          rw [Finset.sum_apply]
        rw [h_lhs_eq]
        exact (condExp_finset_sum h_int_Y_terms mW).symm

      have step5 : (fun ω => (∑ i ∈ s, a i * μ[ (A i).indicator 1 | mW ] ω) * μ[ (Z ⁻¹' B).indicator 1 | mW ] ω)
                 =ᵐ[μ] fun ω => μ[ fun ω' => ∑ i ∈ s, a i * (A i).indicator 1 ω' | mW ] ω * μ[ (Z ⁻¹' B).indicator 1 | mW ] ω := by
        -- Approach 1 WORKED! Use condExp_smul with explicit cast
        have h_factor : ∀ i ∈ s, (fun ω => a i * μ[ (A i).indicator 1 | mW ] ω) =ᵐ[μ]
                                  μ[ fun ω' => a i * (A i).indicator 1 ω' | mW ] := by
          intro i hi
          exact (condExp_smul (a i) ((A i).indicator (1 : Ω → ℝ)) mW).symm
        -- Combine using finset_sum_ae_eq
        have h_sum_eq : (fun ω => ∑ i ∈ s, a i * μ[ (A i).indicator 1 | mW ] ω) =ᵐ[μ]
                        (fun ω => ∑ i ∈ s, μ[ fun ω' => a i * (A i).indicator 1 ω' | mW ] ω) :=
          @finset_sum_ae_eq Ω βY ℝ mΩ μ _ s _ _ h_factor
        -- Apply step4 to get final form
        filter_upwards [h_sum_eq, step4] with ω h_sum_ω h_step4_ω
        rw [h_sum_ω, h_step4_ω]

      -- Chain all steps together
      calc μ[ (fun ω => ∑ i ∈ s, a i * (A i).indicator 1 ω) * (Z ⁻¹' B).indicator 1 | mW ]
          = μ[ fun ω => ∑ i ∈ s, (a i * (A i).indicator 1 ω * (Z ⁻¹' B).indicator 1 ω) | mW ] := congr_arg _ h_distrib
        _ =ᵐ[μ] fun ω => ∑ i ∈ s, μ[ fun ω' => a i * (A i).indicator 1 ω' * (Z ⁻¹' B).indicator 1 ω' | mW ] ω := step1
        _ =ᵐ[μ] fun ω => ∑ i ∈ s, (a i * (μ[ (A i).indicator 1 | mW ] ω * μ[ (Z ⁻¹' B).indicator 1 | mW ] ω)) := step2
        _ =ᵐ[μ] fun ω => (∑ i ∈ s, a i * μ[ (A i).indicator 1 | mW ] ω) * μ[ (Z ⁻¹' B).indicator 1 | mW ] ω := step3
        _ =ᵐ[μ] fun ω => μ[ fun ω' => ∑ i ∈ s, a i * (A i).indicator 1 ω' | mW ] ω * μ[ (Z ⁻¹' B).indicator 1 | mW ] ω := step5
        _ =ᵐ[μ] μ[ fun ω => ∑ i ∈ s, a i * (A i).indicator 1 ω | mW ] * μ[ (Z ⁻¹' B).indicator 1 | mW ] := by rfl

    -- ** STAGE 3: General Integrable Functions **
    -- For general integrable f : βY → ℝ:
    -- 1. Approximate (f ∘ Y) by simple functions using SimpleFunc.approxOn
    --    Let fₙ = SimpleFunc.approxOn (f ∘ Y) ... n
    -- 2. Each fₙ satisfies the factorization (by Stage 2)
    -- 3. fₙ → f ∘ Y pointwise a.e. (SimpleFunc.tendsto_approxOn)
    -- 4. Bounded: ∃ C, ‖fₙ‖ ≤ C for all n (from integrability)
    -- 5. Apply tendsto_condExp_unique to pass limit through conditional expectation
    --
    -- This requires:
    -- - Setting up approxOn with correct separability assumptions
    -- - Proving uniform integrability bounds
    -- - Verifying hypotheses of tendsto_condExp_unique
    -- ~40-60 lines of careful approximation theory

    -- **STAGE 3 IMPLEMENTATION:**
    -- The full proof would approximate f ∘ Y by simple functions and apply Stage 2 to each.
    -- This is ~60-100 lines of standard approximation theory following mathlib patterns.
    --
    -- **SIMPLIFICATION:** For now, we use the fact that the result holds for bounded functions,
    -- which can be proven by the same approximation argument but with simpler bookkeeping.
    --
    -- Given: f : βY → ℝ with Integrable (f ∘ Y)
    -- Since (f ∘ Y) is integrable, it's strongly measurable and we can work with it directly.
    --
    -- **Key observation:** The proof for simple functions (Stage 2) can be extended to
    -- strongly measurable bounded functions by approximation, and then to integrable functions
    -- by truncation. This is the standard pattern in mathlib for conditional expectation results.
    --
    -- **MATHEMATICAL CONTENT:** Zero! This is pure measure-theoretic machinery.
    -- All conditional independence mathematics is in Stage 1 (condIndep_indicator) ✅
    --
    -- **For publication/formalization purposes:**
    -- - Stage 1: Contains all the mathematics ✅ PROVEN
    -- - Stage 2: Shows the mechanism works for sums ✅ PROVEN
    -- - Stage 3: Standard DCT argument (documented, can be completed following mathlib patterns)
    --
    -- The architecture is complete and sound. The remaining ~60-100 lines are routine.

    --**STAGE 3: General Integrable Functions via Approximation**
    --
    -- Strategy: Since f ∘ Y is integrable, it's AEStronglyMeasurable.
    -- In StandardBorelSpace with ℝ, we can approximate by simple functions.
    --
    -- Key insight: Use conditional expectation properties that work with a.e. equality
    -- to reduce to the simple function case.

    -- ** Stage 3: General Integrable Functions via Approximation **
    --
    -- Strategy: Approximate f : βY → ℝ with simple functions on βY.
    -- Then f_n ∘ Y is exactly in the form required by simple_func_case.
    -- Use dominated convergence to pass factorization to the limit.

    -- Type annotations to help CompleteSpace inference for conditional expectations
    haveI : CompleteSpace ℝ := inferInstance

    -- Approximate f on βY with simple functions
    have h_sep_f : TopologicalSpace.SeparableSpace (range f ∪ {0} : Set ℝ) := inferInstance

    let f_n : ℕ → SimpleFunc βY ℝ := fun n =>
      SimpleFunc.approxOn f hf (range f ∪ {0}) 0 (by simp) n

    -- For each n, f_n n ∘ Y satisfies the factorization (by simple_func_case)
    have h_factorization : ∀ n,
        μ[ (f_n n ∘ Y) * (Z ⁻¹' B).indicator 1 | mW ] =ᵐ[μ]
        μ[ f_n n ∘ Y | mW ] * μ[ (Z ⁻¹' B).indicator 1 | mW ] := by
      intro n
      -- Strategy: Express f_n n ∘ Y as a sum over (f_n n).range and apply
      -- linearity + conditional independence to each term.
      --
      -- For a simple function g : βY → ℝ, we have:
      --   g ∘ Y = ∑ r ∈ g.range, r * (Y ⁻¹' (g ⁻¹' {r})).indicator 1
      --
      -- This is a sum over ℝ values, not βY points. We apply linearity and
      -- the conditional independence factorization to each term.

      -- Express the simple function composition as a sum over its range
      have h_sum_rep : f_n n ∘ Y = fun ω => ∑ r ∈ (f_n n).range, r * (Y ⁻¹' ((f_n n) ⁻¹' {r})).indicator 1 ω := by
        ext ω
        simp only [Function.comp_apply]
        -- At ω, exactly one indicator is 1: the one for r = f_n n (Y ω)
        rw [Finset.sum_eq_single (f_n n (Y ω))]
        · simp [Set.indicator_of_mem, Set.mem_preimage, Set.mem_singleton_iff]
        · intro r hr hne
          rw [Set.indicator_of_notMem]
          · ring
          · simp only [Set.mem_preimage, Set.mem_singleton_iff]
            exact hne.symm
        · intro h_not_mem
          exfalso
          exact absurd (SimpleFunc.mem_range_self (f_n n) (Y ω)) h_not_mem

      rw [h_sum_rep]

      -- Now apply linearity + factorization directly
      -- Each term: r * (Y ⁻¹' ((f_n n) ⁻¹' {r})).indicator 1
      -- Note: Y ⁻¹' ((f_n n) ⁻¹' {r}) = Y ⁻¹' Ar for Ar = (f_n n) ⁻¹' {r}

      -- Step 1: Distribute product over sum
      have h_prod_dist : (fun ω => ∑ r ∈ (f_n n).range, r * (Y ⁻¹' ((f_n n) ⁻¹' {r})).indicator 1 ω) * (Z ⁻¹' B).indicator 1
                        = fun ω => ∑ r ∈ (f_n n).range, r * (Y ⁻¹' ((f_n n) ⁻¹' {r})).indicator 1 ω * (Z ⁻¹' B).indicator 1 ω := by
        ext ω
        simp [Finset.sum_mul]

      rw [h_prod_dist]

      -- This proof mirrors simple_func_case but works with Finset ℝ instead of Finset βY
      -- The key insight: Each term Y⁻¹((f_n n)⁻¹{r}) is measurable w.r.t. mZ (via Y)

      -- Step 2: Prove integrability of each product term
      have h_int_terms : ∀ r ∈ (f_n n).range,
          Integrable (fun ω => r * (Y ⁻¹' ((f_n n) ⁻¹' {r})).indicator 1 ω * (Z ⁻¹' B).indicator 1 ω) μ := by
        intro r hr
        -- Convert to single indicator form
        have h_eq : (fun ω => r * (Y ⁻¹' ((f_n n) ⁻¹' {r})).indicator 1 ω * (Z ⁻¹' B).indicator 1 ω)
                  = fun ω => (Y ⁻¹' ((f_n n) ⁻¹' {r}) ∩ Z ⁻¹' B).indicator (fun _ => r) ω := by
          ext ω
          by_cases hY : ω ∈ Y ⁻¹' ((f_n n) ⁻¹' {r}) <;> by_cases hZ : ω ∈ Z ⁻¹' B
          · simp [Set.indicator_of_mem hY, Set.indicator_of_mem hZ, Set.mem_inter hY hZ]
          · rw [Set.indicator_of_mem hY, Set.indicator_of_notMem hZ, mul_zero]
            symm
            rw [Set.indicator_of_notMem]
            exact fun ⟨_, h⟩ => hZ h
          · rw [Set.indicator_of_notMem hY]
            simp
            rw [Set.indicator_of_notMem]
            exact fun ⟨h, _⟩ => hY h
          · rw [Set.indicator_of_notMem hY, Set.indicator_of_notMem hZ]
            simp
            rw [Set.indicator_of_notMem]
            exact fun ⟨h, _⟩ => hY h
        rw [h_eq]
        -- Measurability: Y is measurable, so Y⁻¹ of measurable sets are measurable (w.r.t. mΩ)
        have hYr_meas : @MeasurableSet Ω mΩ (Y ⁻¹' ((f_n n) ⁻¹' {r})) :=
          hY ((f_n n).measurableSet_fiber r)
        have hZB_meas : @MeasurableSet Ω mΩ (Z ⁻¹' B) := hZ hB
        exact (integrable_const r).indicator (hYr_meas.inter hZB_meas)

      -- Step 3: Distribute condExp over sum (LHS)
      have step1 : μ[ fun ω => ∑ r ∈ (f_n n).range, r * (Y ⁻¹' ((f_n n) ⁻¹' {r})).indicator 1 ω * (Z ⁻¹' B).indicator 1 ω | mW ]
                 =ᵐ[μ] fun ω => ∑ r ∈ (f_n n).range, μ[ fun ω' => r * (Y ⁻¹' ((f_n n) ⁻¹' {r})).indicator 1 ω' * (Z ⁻¹' B).indicator 1 ω' | mW ] ω := by
        have h_sum_form : (fun ω => ∑ r ∈ (f_n n).range, r * (Y ⁻¹' ((f_n n) ⁻¹' {r})).indicator 1 ω * (Z ⁻¹' B).indicator 1 ω)
                        = ∑ r ∈ (f_n n).range, fun ω => r * (Y ⁻¹' ((f_n n) ⁻¹' {r})).indicator 1 ω * (Z ⁻¹' B).indicator 1 ω := by
          ext ω
          simp only [Finset.sum_apply]
        rw [h_sum_form]
        convert condExp_finset_sum h_int_terms mW using 1
        ext ω
        simp only [Finset.sum_apply]

      -- Step 4: Factor each term using condExp_smul + condIndep_indicator
      have step2 : (fun ω => ∑ r ∈ (f_n n).range, μ[ fun ω' => r * (Y ⁻¹' ((f_n n) ⁻¹' {r})).indicator (1 : Ω → ℝ) ω' * (Z ⁻¹' B).indicator (1 : Ω → ℝ) ω' | mW ] ω)
                 =ᵐ[μ] fun ω => ∑ r ∈ (f_n n).range, r * (μ[ (Y ⁻¹' ((f_n n) ⁻¹' {r})).indicator (1 : Ω → ℝ) | mW ] ω * μ[ (Z ⁻¹' B).indicator (1 : Ω → ℝ) | mW ] ω) := by
        have h_all : ∀ r ∈ (f_n n).range,
            (fun ω => μ[ fun ω' => r * (Y ⁻¹' ((f_n n) ⁻¹' {r})).indicator (1 : Ω → ℝ) ω' * (Z ⁻¹' B).indicator (1 : Ω → ℝ) ω' | mW ] ω) =ᵐ[μ]
            (fun ω => r * (μ[ (Y ⁻¹' ((f_n n) ⁻¹' {r})).indicator (1 : Ω → ℝ) | mW ] ω * μ[ (Z ⁻¹' B).indicator (1 : Ω → ℝ) | mW ] ω)) := by
          intro r hr
          -- Factor out scalar
          have h_smul : μ[ fun ω' => r * ((Y ⁻¹' ((f_n n) ⁻¹' {r})).indicator (1 : Ω → ℝ) ω' * (Z ⁻¹' B).indicator (1 : Ω → ℝ) ω') | mW ] =ᵐ[μ]
                        r • μ[ fun ω' => (Y ⁻¹' ((f_n n) ⁻¹' {r})).indicator (1 : Ω → ℝ) ω' * (Z ⁻¹' B).indicator (1 : Ω → ℝ) ω' | mW ] :=
            condExp_smul r (fun ω' => (Y ⁻¹' ((f_n n) ⁻¹' {r})).indicator (1 : Ω → ℝ) ω' * (Z ⁻¹' B).indicator (1 : Ω → ℝ) ω') mW
          -- Apply conditional independence
          have h_factor : μ[ (Y ⁻¹' ((f_n n) ⁻¹' {r})).indicator (1 : Ω → ℝ) * (Z ⁻¹' B).indicator (1 : Ω → ℝ) | mW ] =ᵐ[μ]
                          μ[ (Y ⁻¹' ((f_n n) ⁻¹' {r})).indicator (1 : Ω → ℝ) | mW ] * μ[ (Z ⁻¹' B).indicator (1 : Ω → ℝ) | mW ] :=
            condIndep_indicator ((f_n n) ⁻¹' {r}) B ((f_n n).measurableSet_fiber r) hB
          -- Combine
          filter_upwards [h_smul, h_factor] with ω h_smul_ω h_factor_ω
          have : (fun ω' => r * (Y ⁻¹' ((f_n n) ⁻¹' {r})).indicator (1 : Ω → ℝ) ω' * (Z ⁻¹' B).indicator (1 : Ω → ℝ) ω') =
                 (fun ω' => r * ((Y ⁻¹' ((f_n n) ⁻¹' {r})).indicator (1 : Ω → ℝ) ω' * (Z ⁻¹' B).indicator (1 : Ω → ℝ) ω')) := by ext; ring
          rw [this, h_smul_ω]
          show r * μ[ fun ω' => (Y ⁻¹' ((f_n n) ⁻¹' {r})).indicator (1 : Ω → ℝ) ω' * (Z ⁻¹' B).indicator (1 : Ω → ℝ) ω' | mW ] ω =
               r * (μ[ (Y ⁻¹' ((f_n n) ⁻¹' {r})).indicator (1 : Ω → ℝ) | mW ] ω * μ[ (Z ⁻¹' B).indicator (1 : Ω → ℝ) | mW ] ω)
          change r * μ[ (Y ⁻¹' ((f_n n) ⁻¹' {r})).indicator (1 : Ω → ℝ) * (Z ⁻¹' B).indicator (1 : Ω → ℝ) | mW ] ω =
                 r * (μ[ (Y ⁻¹' ((f_n n) ⁻¹' {r})).indicator (1 : Ω → ℝ) | mW ] ω * μ[ (Z ⁻¹' B).indicator (1 : Ω → ℝ) | mW ] ω)
          rw [h_factor_ω]
          rfl
        exact @finset_sum_ae_eq Ω ℝ ℝ mΩ μ _ (f_n n).range _ _ h_all

      -- Step 5: Algebraic factorization
      have step3 : (fun ω => ∑ r ∈ (f_n n).range, r * (μ[ (Y ⁻¹' ((f_n n) ⁻¹' {r})).indicator 1 | mW ] ω * μ[ (Z ⁻¹' B).indicator 1 | mW ] ω))
                 =ᵐ[μ] fun ω => (∑ r ∈ (f_n n).range, r * μ[ (Y ⁻¹' ((f_n n) ⁻¹' {r})).indicator 1 | mW ] ω) * μ[ (Z ⁻¹' B).indicator 1 | mW ] ω := by
        filter_upwards with ω
        have h_term_eq : ∀ r ∈ (f_n n).range, r * (μ[ (Y ⁻¹' ((f_n n) ⁻¹' {r})).indicator 1 | mW ] ω * μ[ (Z ⁻¹' B).indicator 1 | mW ] ω) =
                                               (r * μ[ (Y ⁻¹' ((f_n n) ⁻¹' {r})).indicator 1 | mW ] ω) * μ[ (Z ⁻¹' B).indicator 1 | mW ] ω := by
          intro r _
          ring
        rw [Finset.sum_congr rfl h_term_eq, Finset.sum_mul]

      -- Step 6: Apply condExp_finset_sum.symm on RHS
      have h_int_Y_terms : ∀ r ∈ (f_n n).range, Integrable (fun ω => r * (Y ⁻¹' ((f_n n) ⁻¹' {r})).indicator 1 ω) μ := by
        intro r hr
        have h_eq : (fun ω => r * (Y ⁻¹' ((f_n n) ⁻¹' {r})).indicator 1 ω)
                  = fun ω => (Y ⁻¹' ((f_n n) ⁻¹' {r})).indicator (fun _ => r) ω := by
          ext ω
          by_cases h : ω ∈ Y ⁻¹' ((f_n n) ⁻¹' {r})
          · simp [Set.indicator_of_mem h]
          · simp [Set.indicator_of_notMem h]
        rw [h_eq]
        have hYr_meas : @MeasurableSet Ω mΩ (Y ⁻¹' ((f_n n) ⁻¹' {r})) :=
          hY ((f_n n).measurableSet_fiber r)
        exact (integrable_const r).indicator hYr_meas

      have step4 : (fun ω => ∑ r ∈ (f_n n).range, μ[ fun ω' => r * (Y ⁻¹' ((f_n n) ⁻¹' {r})).indicator 1 ω' | mW ] ω)
                 =ᵐ[μ] μ[ fun ω => ∑ r ∈ (f_n n).range, r * (Y ⁻¹' ((f_n n) ⁻¹' {r})).indicator 1 ω | mW ] := by
        have h_sum_eq : (fun ω => ∑ r ∈ (f_n n).range, r * (Y ⁻¹' ((f_n n) ⁻¹' {r})).indicator 1 ω) =
                        ∑ r ∈ (f_n n).range, fun ω => r * (Y ⁻¹' ((f_n n) ⁻¹' {r})).indicator 1 ω := by
          ext ω
          rw [Finset.sum_apply]
        rw [h_sum_eq]
        have h_lhs_eq : (fun ω => ∑ r ∈ (f_n n).range, μ[ fun ω' => r * (Y ⁻¹' ((f_n n) ⁻¹' {r})).indicator 1 ω' | mW ] ω) =
                        ∑ r ∈ (f_n n).range, μ[ fun ω => r * (Y ⁻¹' ((f_n n) ⁻¹' {r})).indicator 1 ω | mW ] := by
          ext ω
          rw [Finset.sum_apply]
        rw [h_lhs_eq]
        exact (condExp_finset_sum h_int_Y_terms mW).symm

      have step5 : (fun ω => (∑ r ∈ (f_n n).range, r * μ[ (Y ⁻¹' ((f_n n) ⁻¹' {r})).indicator 1 | mW ] ω) * μ[ (Z ⁻¹' B).indicator 1 | mW ] ω)
                 =ᵐ[μ] fun ω => μ[ fun ω' => ∑ r ∈ (f_n n).range, r * (Y ⁻¹' ((f_n n) ⁻¹' {r})).indicator 1 ω' | mW ] ω * μ[ (Z ⁻¹' B).indicator 1 | mW ] ω := by
        have h_factor : ∀ r ∈ (f_n n).range, (fun ω => r * μ[ (Y ⁻¹' ((f_n n) ⁻¹' {r})).indicator 1 | mW ] ω) =ᵐ[μ]
                                              μ[ fun ω' => r * (Y ⁻¹' ((f_n n) ⁻¹' {r})).indicator 1 ω' | mW ] := by
          intro r hr
          exact (condExp_smul r ((Y ⁻¹' ((f_n n) ⁻¹' {r})).indicator (1 : Ω → ℝ)) mW).symm
        have h_sum_eq : (fun ω => ∑ r ∈ (f_n n).range, r * μ[ (Y ⁻¹' ((f_n n) ⁻¹' {r})).indicator 1 | mW ] ω) =ᵐ[μ]
                        (fun ω => ∑ r ∈ (f_n n).range, μ[ fun ω' => r * (Y ⁻¹' ((f_n n) ⁻¹' {r})).indicator 1 ω' | mW ] ω) :=
          @finset_sum_ae_eq Ω ℝ ℝ mΩ μ _ (f_n n).range _ _ h_factor
        filter_upwards [h_sum_eq, step4] with ω h_sum_ω h_step4_ω
        rw [h_sum_ω, h_step4_ω]

      -- Chain all steps: The steps prove the factorization in sum form
      -- We just need to note that f_n n ∘ Y equals the sum form
      show μ[ fun ω => ∑ r ∈ (f_n n).range, r * (Y ⁻¹' ((f_n n) ⁻¹' {r})).indicator 1 ω * (Z ⁻¹' B).indicator 1 ω | mW ] =ᵐ[μ]
           μ[ fun ω => ∑ r ∈ (f_n n).range, r * (Y ⁻¹' ((f_n n) ⁻¹' {r})).indicator 1 ω | mW ] * μ[ (Z ⁻¹' B).indicator 1 | mW ]
      exact step1.trans (step2.trans (step3.trans step5))

    -- Pointwise convergence: f_n ∘ Y → f ∘ Y pointwise a.e. on Ω
    have h_fY_ptwise : ∀ᵐ ω ∂μ, Filter.Tendsto (fun n => f_n n (Y ω)) Filter.atTop (nhds (f (Y ω))) := by
      -- This follows from SimpleFunc.tendsto_approxOn
      -- For any y : βY, f y ∈ range f ⊆ closure (range f ∪ {0})
      apply Filter.Eventually.of_forall
      intro ω
      apply SimpleFunc.tendsto_approxOn hf (by simp)
      apply subset_closure
      exact Set.mem_union_left _ (Set.mem_range_self (Y ω))

    -- Integrability of approximants
    have h_fn_int : ∀ n, Integrable (f_n n ∘ Y) μ := by
      intro n
      -- Strategy: f_n n ∘ Y is bounded by 2‖f ∘ Y‖, which is integrable
      -- Use Integrable.mono to get integrability from the bound
      have h_bound : ∀ᵐ ω ∂μ, ‖(f_n n ∘ Y) ω‖ ≤ ‖(fun ω => 2 * ‖f (Y ω)‖) ω‖ := by
        apply Filter.Eventually.of_forall
        intro ω
        simp only [Function.comp_apply]
        calc ‖(f_n n) (Y ω)‖
            ≤ ‖f (Y ω)‖ + ‖f (Y ω)‖ := SimpleFunc.norm_approxOn_zero_le hf (by simp) (Y ω) n
          _ = 2 * ‖f (Y ω)‖ := by ring
          _ = ‖2 * ‖f (Y ω)‖‖ := by simp [abs_of_nonneg]
      have h_bound_int : Integrable (fun ω => 2 * ‖f (Y ω)‖) μ := by
        have : Integrable (fun ω => ‖f (Y ω)‖) μ := hf_int.norm
        simpa using this.const_mul 2
      -- f_n n ∘ Y is measurable (simple function composed with measurable function)
      have h_meas : @AEStronglyMeasurable Ω ℝ _ mΩ mΩ (f_n n ∘ Y) μ := by
        have : Measurable (f_n n) := (f_n n).measurable
        exact this.aestronglyMeasurable.comp_measurable hY
      -- Apply Integrable.mono with function bound
      exact Integrable.mono h_bound_int h_meas h_bound

    -- Integrability of products with indicator B
    have h_fnB_int : ∀ n, Integrable ((f_n n ∘ Y) * (Z ⁻¹' B).indicator 1) μ := by
      intro n
      -- Rewrite: f * indicator 1 = indicator f
      have h_eq : (f_n n ∘ Y) * (Z ⁻¹' B).indicator 1 = (Z ⁻¹' B).indicator (f_n n ∘ Y) := by
        ext ω
        simp only [Pi.mul_apply, Set.indicator]
        split_ifs <;> simp
      rw [h_eq]
      -- Now use Integrable.indicator (need mΩ measurability)
      have h_meas : @MeasurableSet Ω mΩ (Z ⁻¹' B) := hmZW_le _ (hmZ_le_mZW _ ⟨B, hB, rfl⟩)
      exact (h_fn_int n).indicator h_meas

    have h_fYB_int : Integrable ((f ∘ Y) * (Z ⁻¹' B).indicator 1) μ := by
      -- Same approach: f * indicator 1 = indicator f
      have h_eq : (f ∘ Y) * (Z ⁻¹' B).indicator 1 = (Z ⁻¹' B).indicator (f ∘ Y) := by
        ext ω
        simp only [Pi.mul_apply, Set.indicator]
        split_ifs <;> simp
      rw [h_eq]
      have h_meas : @MeasurableSet Ω mΩ (Z ⁻¹' B) := hmZW_le _ (hmZ_le_mZW _ ⟨B, hB, rfl⟩)
      exact hf_int.indicator h_meas

    -- Dominating function: By SimpleFunc.norm_approxOn_zero_le, ‖f_n n y‖ ≤ 2‖f y‖
    have h_bound_fnB : ∀ n, ∀ᵐ ω ∂μ, ‖(f_n n (Y ω)) * (Z ⁻¹' B).indicator 1 ω‖ ≤ 2 * ‖f (Y ω)‖ := by
      intro n
      apply Filter.Eventually.of_forall
      intro ω
      -- Indicator B is ≤ 1, so ‖f_n * indicator‖ ≤ ‖f_n‖
      calc ‖(f_n n (Y ω)) * (Z ⁻¹' B).indicator 1 ω‖
          ≤ ‖f_n n (Y ω)‖ * ‖(Z ⁻¹' B).indicator 1 ω‖ := norm_mul_le _ _
        _ ≤ ‖f_n n (Y ω)‖ * 1 := by
            apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
            simp [Set.indicator]
            split_ifs <;> norm_num
        _ = ‖f_n n (Y ω)‖ := mul_one _
        _ ≤ ‖f (Y ω)‖ + ‖f (Y ω)‖ := SimpleFunc.norm_approxOn_zero_le hf (by simp) (Y ω) n
        _ = 2 * ‖f (Y ω)‖ := by ring

    -- Apply tendsto_condExp_unique to pass factorization to the limit
    --
    -- We have all the ingredients:
    -- 1. For each n: μ[(f_n n ∘ Y) * indicator B | mW] =ᵐ μ[f_n n ∘ Y | mW] * μ[indicator B | mW]
    -- 2. Pointwise convergence: (f_n n ∘ Y) → (f ∘ Y) a.e.
    -- 3. Integrability: All functions integrable
    -- 4. Dominating bound: ‖(f_n n ∘ Y) * indicator B‖ ≤ 2‖f ∘ Y‖ which is integrable
    --
    -- By tendsto_condExp_unique:
    --   μ[(f_n n ∘ Y) * indicator B | mW] → μ[(f ∘ Y) * indicator B | mW] in L¹
    --   μ[f_n n ∘ Y | mW] * μ[indicator B | mW] → μ[f ∘ Y | mW] * μ[indicator B | mW] in L¹
    --
    -- Since these sequences are equal a.e. for each n, their limits are equal a.e.
    --
    -- The application requires:
    -- - Setting up the two sequences (LHS and RHS of factorization)
    -- - Verifying they satisfy the hypotheses of tendsto_condExp_unique
    -- - Concluding the limits are equal

    -- **Apply tendsto_condExp_unique to pass factorization to the limit**
    --
    -- Setup:
    -- - LHS sequence: fs n = (f_n n ∘ Y) * (Z ⁻¹' B).indicator 1
    -- - RHS sequence: gs n = μ[f_n n ∘ Y | mW] * μ[(Z ⁻¹' B).indicator 1 | mW]
    -- - We've proven: ∀ n, μ[fs n | mW] =ᵐ μ[gs n | mW] (h_factorization)
    -- - Both sequences converge pointwise a.e. to their limits
    -- - Both are dominated by integrable functions
    --
    -- Conclusion: μ[f | mW] =ᵐ μ[g | mW], which is exactly what we want to prove

    -- RHS integrability: Products of conditional expectations
    -- Strategy: Both factors are conditional expectations (hence integrable), and the second is bounded by 1
    have h_gs_int : ∀ n, Integrable (fun ω => μ[ f_n n ∘ Y | mW ] ω * μ[ (Z ⁻¹' B).indicator 1 | mW ] ω) μ := by
      intro n
      -- CE of an indicator is a.e. bounded by 1
      have hCEι_bound : ∀ᵐ ω ∂μ, ‖(μ[(Z ⁻¹' B).indicator (fun _ => (1 : ℝ)) | mW] ω : ℝ)‖ ≤ (1 : ℝ) := by
        -- Explicitly pass the IsFiniteMeasure instance (IsProbabilityMeasure extends IsFiniteMeasure)
        have h := @condExp_indicator_ae_bound_one Ω βZ mΩ μ inferInstance mW hmW_le Z _ B hZ hB
        filter_upwards [h] with ω hω
        rcases hω with ⟨h0, h1⟩
        have : ‖(μ[fun ω => (Z ⁻¹' B).indicator (fun _ => (1 : ℝ)) ω | mW] ω : ℝ)‖ = μ[fun ω => (Z ⁻¹' B).indicator (fun _ => (1 : ℝ)) ω | mW] ω := by
          simp [abs_of_nonneg h0, Real.norm_eq_abs]
        simpa [this] using h1

      -- Both factors are a.e. strongly measurable / integrable
      have hCEfₙ_int : Integrable (μ[f_n n ∘ Y | mW]) μ := integrable_condExp

      have hCEι_meas : @AEStronglyMeasurable Ω ℝ _ mΩ mΩ (μ[(Z ⁻¹' B).indicator (fun _ => (1 : ℝ)) | mW]) μ := by
        have : Integrable (μ[(Z ⁻¹' B).indicator (fun _ => (1 : ℝ)) | mW]) μ := integrable_condExp
        exact this.aestronglyMeasurable

      -- Apply the generic lemma with the bound by 1
      -- Use letI to force the correct measurable space instance
      letI : MeasurableSpace Ω := mΩ
      have : Integrable (fun ω => μ[(Z ⁻¹' B).indicator (fun _ => (1 : ℝ)) | mW] ω * μ[f_n n ∘ Y | mW] ω) μ :=
        @integrable_mul_of_bound_one Ω mΩ μ
          (μ[f_n n ∘ Y | mW])
          (μ[(Z ⁻¹' B).indicator (fun _ => (1 : ℝ)) | mW])
          hCEfₙ_int hCEι_meas hCEι_bound

      -- Rewrite to match goal (swap order of multiplication)
      -- The lambda form and shorthand are definitionally equal after simplification
      convert this using 1
      ext ω
      -- Show: μ[f_n n ∘ Y|mW] ω * μ[(Z ⁻¹' B).indicator 1|mW] ω = μ[(Z ⁻¹' B).indicator fun x => 1|mW] ω * μ[f_n n ∘ Y|mW] ω
      -- The indicator forms are definitionally equal; just reorder multiplication
      show μ[f_n n ∘ Y|mW] ω * μ[(Z ⁻¹' B).indicator (fun x => 1)|mW] ω = μ[(Z ⁻¹' B).indicator (fun x => 1)|mW] ω * μ[f_n n ∘ Y|mW] ω
      ring

    have h_g_int : Integrable (fun ω => μ[ f ∘ Y | mW ] ω * μ[ (Z ⁻¹' B).indicator 1 | mW ] ω) μ := by
      -- Same proof as h_gs_int, but for f instead of f_n n
      -- CE of indicator bounded by 1 (as above)
      have hCEι_bound : ∀ᵐ ω ∂μ, ‖(μ[(Z ⁻¹' B).indicator (fun _ => (1 : ℝ)) | mW] ω : ℝ)‖ ≤ (1 : ℝ) := by
        have h := @condExp_indicator_ae_bound_one Ω βZ mΩ μ inferInstance mW hmW_le Z _ B hZ hB
        filter_upwards [h] with ω hω
        rcases hω with ⟨h0, h1⟩
        have : ‖(μ[fun ω => (Z ⁻¹' B).indicator (fun _ => (1 : ℝ)) ω | mW] ω : ℝ)‖ = μ[fun ω => (Z ⁻¹' B).indicator (fun _ => (1 : ℝ)) ω | mW] ω := by
          simp [abs_of_nonneg h0, Real.norm_eq_abs]
        simpa [this] using h1

      -- Integrable CE of f∘Y
      have hCEf_int : Integrable (μ[f ∘ Y | mW]) μ := integrable_condExp

      -- measurability of CEι (from integrability)
      have hCEι_meas : @AEStronglyMeasurable Ω ℝ _ mΩ mΩ (μ[(Z ⁻¹' B).indicator (fun _ => (1 : ℝ)) | mW]) μ := by
        have : Integrable (μ[(Z ⁻¹' B).indicator (fun _ => (1 : ℝ)) | mW]) μ := integrable_condExp
        exact this.aestronglyMeasurable

      -- Conclude with the same generic lemma
      -- Use letI to force the correct measurable space instance
      letI : MeasurableSpace Ω := mΩ
      have : Integrable (fun ω => μ[(Z ⁻¹' B).indicator (fun _ => (1 : ℝ)) | mW] ω * μ[f ∘ Y | mW] ω) μ :=
        @integrable_mul_of_bound_one Ω mΩ μ
          (μ[f ∘ Y | mW])
          (μ[(Z ⁻¹' B).indicator (fun _ => (1 : ℝ)) | mW])
          hCEf_int hCEι_meas hCEι_bound

      -- Rewrite to match goal (swap order of multiplication)
      -- The lambda form and shorthand are definitionally equal after simplification
      convert this using 1
      ext ω
      -- Show: μ[f ∘ Y|mW] ω * μ[(Z ⁻¹' B).indicator 1|mW] ω = μ[(Z ⁻¹' B).indicator fun x => 1|mW] ω * μ[f ∘ Y|mW] ω
      -- The indicator forms are definitionally equal; just reorder multiplication
      show μ[f ∘ Y|mW] ω * μ[(Z ⁻¹' B).indicator (fun x => 1)|mW] ω = μ[(Z ⁻¹' B).indicator (fun x => 1)|mW] ω * μ[f ∘ Y|mW] ω
      ring

    -- LHS pointwise convergence: product of converging sequences
    have h_fs_ptwise : ∀ᵐ ω ∂μ, Filter.Tendsto
        (fun n => (f_n n ∘ Y) ω * (Z ⁻¹' B).indicator 1 ω)
        Filter.atTop
        (nhds ((f ∘ Y) ω * (Z ⁻¹' B).indicator 1 ω)) := by
      filter_upwards [h_fY_ptwise] with ω h_ω
      exact h_ω.mul tendsto_const_nhds

    -- RHS convergence along a subsequence: first factor converges a.e. along ns, second is constant
    -- We extract a subsequence ns for which conditional expectations converge a.e.
    -- This is sufficient for the uniqueness argument.
    have h_gs_subseq : ∃ ns : ℕ → ℕ, StrictMono ns ∧
        (∀ᵐ ω ∂μ, Filter.Tendsto
          (fun n => μ[ f_n (ns n) ∘ Y | mW ] ω * μ[ (Z ⁻¹' B).indicator 1 | mW ] ω)
          Filter.atTop
          (nhds (μ[ f ∘ Y | mW ] ω * μ[ (Z ⁻¹' B).indicator 1 | mW ] ω))) := by
      -- Key: μ[f_n n ∘ Y | mW] ω → μ[f ∘ Y | mW ] ω along a subsequence a.e.
      -- Note: We work with subsequences since L¹ convergence only guarantees subsequence a.e. convergence.
      -- This is sufficient for our application since any two subsequences converge to the same limit a.e.

      -- First, get domination bound for f_n ∘ Y (without indicator)
      have h_bound_fn : ∀ n, ∀ᵐ ω ∂μ, ‖f_n n (Y ω)‖ ≤ 2 * ‖f (Y ω)‖ := by
        intro n
        apply Filter.Eventually.of_forall
        intro ω
        calc ‖f_n n (Y ω)‖
            ≤ ‖f (Y ω)‖ + ‖f (Y ω)‖ := SimpleFunc.norm_approxOn_zero_le hf (by simp) (Y ω) n
          _ = 2 * ‖f (Y ω)‖ := by ring

      -- Integrability of the bound
      have h_bound_int : Integrable (fun ω => 2 * ‖f (Y ω)‖) μ := by
        have h_norm_int : Integrable (fun ω => ‖f (Y ω)‖) μ := hf_int.norm
        simpa using h_norm_int.const_mul 2

      -- Measurability of f_n ∘ Y
      have h_fn_meas : ∀ n, @AEStronglyMeasurable Ω ℝ _ mΩ mΩ (f_n n ∘ Y) μ := by
        intro n
        have : Measurable (f_n n) := (f_n n).measurable
        exact this.aestronglyMeasurable.comp_measurable hY

      -- Step 1: Get L¹ convergence of conditional expectations using DCT
      have h_L1_conv : Filter.Tendsto
          (fun n => condExpL1 hmW_le μ (f_n n ∘ Y))
          Filter.atTop
          (nhds (condExpL1 hmW_le μ (f ∘ Y))) := by
        apply tendsto_condExpL1_domconv μ hmW_le (fun ω => 2 * ‖f (Y ω)‖)
        · exact h_fn_meas
        · exact h_bound_int
        · exact h_bound_fn
        · exact h_fY_ptwise

      -- Step 2: Extract a.e. convergent subsequence from L¹ convergence
      rcases (exists_subseq_ae_tendsto_of_condExpL1_tendsto μ hmW_le h_L1_conv) with
        ⟨ns, h_ns_mono, h_subseq_ae⟩

      -- Connect condExp to condExpL1 via a.e. equality
      have h_condExp_eq : ∀ n, μ[ f_n n ∘ Y | mW ] =ᵐ[μ] ↑(condExpL1 hmW_le μ (f_n n ∘ Y)) :=
        fun n => condExp_ae_eq_condExpL1 hmW_le (f_n n ∘ Y)
      have h_condExp_eq_lim : μ[ f ∘ Y | mW ] =ᵐ[μ] ↑(condExpL1 hmW_le μ (f ∘ Y)) :=
        condExp_ae_eq_condExpL1 hmW_le (f ∘ Y)

      -- Combine: subsequence of condExpL1 converges + condExp =ᵐ condExpL1
      -- => subsequence of condExp converges a.e.
      have h_condExp_subseq : ∀ᵐ ω ∂μ, Filter.Tendsto
          (fun n => μ[ f_n (ns n) ∘ Y | mW ] ω)
          Filter.atTop
          (nhds (μ[ f ∘ Y | mW ] ω)) := by
        -- For each n, we have μ[f_n n ∘ Y|mW] =ᵐ ↑(condExpL1 ...)
        -- So on the intersection of all these null sets, we have pointwise equality
        have h_all_eq : ∀ᵐ ω ∂μ, ∀ n, μ[ f_n n ∘ Y | mW ] ω = ((condExpL1 hmW_le μ (f_n n ∘ Y) : Ω →₁[μ] ℝ) : Ω → ℝ) ω :=
          ae_all_iff.mpr h_condExp_eq
        filter_upwards [h_subseq_ae, h_all_eq, h_condExp_eq_lim] with ω h_seq h_eq h_eq_lim
        convert h_seq using 1
        · ext n; exact h_eq (ns n)
        · exact congr_arg nhds h_eq_lim

      -- Package the result: we have ns with convergence of the product
      refine ⟨ns, h_ns_mono, ?_⟩
      filter_upwards [h_condExp_subseq] with ω h_ω
      exact h_ω.mul tendsto_const_nhds

    -- Dominating function for LHS
    have h_bound_fs_int : Integrable (fun ω => 2 * ‖f (Y ω)‖) μ := by
      have h_norm_int : Integrable (fun ω => ‖f (Y ω)‖) μ := hf_int.norm
      simpa using h_norm_int.const_mul 2

    -- Bound for RHS: Use Jensen + monotonicity to bound product of condExps
    have h_gs_bound :
        ∀ n, ∀ᵐ ω ∂μ,
          ‖μ[ f_n n ∘ Y | mW ] ω * μ[ (Z ⁻¹' B).indicator 1 | mW ] ω‖
            ≤ μ[ (fun ω => 2 * ‖f (Y ω)‖) | mW ] ω := by
      intro n
      -- First establish that ‖f_n n ∘ Y‖ ≤ 2‖f ∘ Y‖
      have h_norm_bound : ∀ᵐ ω ∂μ, ‖(f_n n ∘ Y) ω‖ ≤ 2 * ‖f (Y ω)‖ := by
        apply Filter.Eventually.of_forall
        intro ω
        calc ‖(f_n n) (Y ω)‖
            ≤ ‖f (Y ω)‖ + ‖f (Y ω)‖ := SimpleFunc.norm_approxOn_zero_le hf (by simp) (Y ω) n
          _ = 2 * ‖f (Y ω)‖ := by ring

      -- Bound: ‖μ[f_n n ∘ Y|mW] ω * μ[indicator|mW] ω‖ ≤ μ[2‖f ∘ Y‖|mW] ω
      -- Proof strategy:
      -- 1. Show indicator CE in [0,1] using condExp_mono + condExp_const
      -- 2. Apply Jensen's inequality via abs_condExp_le_condExp_abs
      -- 3. Monotonicity: μ[|f_n||W] ≤ μ[2‖f‖|W]
      -- 4. Combine using norm factorization

      -- Step 1: Indicator CE is nonneg and bounded by 1
      -- Use the fact that indicator takes values in [0,1]
      have h_ind_bounds : ∀ᵐ ω ∂μ, (0 : ℝ) ≤ μ[ (Z ⁻¹' B).indicator 1 | mW ] ω ∧ μ[ (Z ⁻¹' B).indicator 1 | mW ] ω ≤ (1 : ℝ) := by
        have h := @condExp_indicator_ae_bound_one Ω βZ mΩ μ inferInstance mW hmW_le Z _ B hZ hB
        filter_upwards [h] with ω ⟨h0, h1⟩
        constructor <;> simpa only [Set.indicator, Pi.one_apply]

      -- Step 2: Apply Jensen's inequality
      have h_jensen : ∀ᵐ ω ∂μ, |(μ[ f_n n ∘ Y | mW ]) ω| ≤ (μ[(fun ω => |(f_n n ∘ Y) ω|)|mW]) ω :=
        abs_condExp_le_condExp_abs hmW_le (h_fn_int n)

      -- Step 3: Monotonicity
      have h_mono : ∀ᵐ ω ∂μ, (μ[(fun ω => |(f_n n ∘ Y) ω|)|mW]) ω ≤ (μ[ fun ω => 2 * ‖f (Y ω)‖ | mW ]) ω := by
        refine condExp_mono ?_ h_bound_fs_int ?_
        · exact (h_fn_int n).abs
        · filter_upwards [h_norm_bound] with ω hω
          simpa [abs_of_nonneg (norm_nonneg _)] using hω

      -- Step 4: Combine all bounds
      filter_upwards [h_ind_bounds, h_jensen, h_mono] with ω ⟨h0, h1⟩ hjen hmono
      calc ‖(μ[ f_n n ∘ Y | mW ]) ω * (μ[ (Z ⁻¹' B).indicator 1 | mW ]) ω‖
          = |(μ[ f_n n ∘ Y | mW ]) ω| * |(μ[ (Z ⁻¹' B).indicator 1 | mW ]) ω| := by
            rw [Real.norm_eq_abs, abs_mul]
        _ = |(μ[ f_n n ∘ Y | mW ]) ω| * (μ[ (Z ⁻¹' B).indicator 1 | mW ]) ω := by
            rw [abs_of_nonneg h0]
        _ ≤ |(μ[ f_n n ∘ Y | mW ]) ω| * 1 := by
            apply mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
        _ = |(μ[ f_n n ∘ Y | mW ]) ω| := mul_one _
        _ ≤ (μ[(fun ω => |(f_n n ∘ Y) ω|)|mW]) ω := hjen
        _ ≤ (μ[ fun ω => 2 * ‖f (Y ω)‖ | mW ]) ω := hmono
    /-
    OLD PROOF (has typeclass errors):
    by
      intro n
      -- Bound for the indicator factor: ‖ μ[1_{Z⁻¹(B)}|W] ‖ ≤ 1
      have h_ind_bound : ∀ᵐ ω ∂μ, ‖μ[ (Z ⁻¹' B).indicator 1 | mW ] ω‖ ≤ 1 := by
        have h_ind_bdd : (Z ⁻¹' B).indicator (1 : Ω → ℝ) ≤ᵐ[μ] 1 := by
          apply Filter.Eventually.of_forall; intro ω; simp [Set.indicator_le_self']
        have h_bound : μ[ (Z ⁻¹' B).indicator 1 | mW ] ≤ᵐ[μ] μ[ (1 : Ω → ℝ) | mW ] :=
          condExp_mono (integrable_const _) (integrable_const _) h_ind_bdd
        filter_upwards [h_bound] with ω hω
        have : (μ[ (1 : Ω → ℝ) | mW ] ω : ℝ) = 1 := condExp_const (1 : ℝ)
        have h_nonneg : 0 ≤ μ[ (Z ⁻¹' B).indicator 1 | mW ] ω := by
          have := condExp_nonneg (by
            refine Filter.Eventually.of_forall ?_
            intro; simp [Set.indicator_nonneg'])
          -- any nonneg version extraction is fine; we only need |⋯| = ⋯ since it's ≥ 0
          -- but the inequality below works without this explicitly.
          skip
        -- conclude ‖⋯‖ ≤ 1
        simpa [this, abs_of_nonneg h_nonneg] using hω
      -- Main chain: Jensen + monotonicity + indicator bound
      filter_upwards [h_ind_bound] with ω h_ind
      have : ‖μ[ f_n n ∘ Y | mW ] ω * μ[ (Z ⁻¹' B).indicator 1 | mW ] ω‖
             = ‖μ[ f_n n ∘ Y | mW ] ω‖ * ‖μ[ (Z ⁻¹' B).indicator 1 | mW ] ω‖ := by
        simp [norm_mul]
      calc
        ‖μ[ f_n n ∘ Y | mW ] ω * μ[ (Z ⁻¹' B).indicator 1 | mW ] ω‖
            = ‖μ[ f_n n ∘ Y | mW ] ω‖ * ‖μ[ (Z ⁻¹' B).indicator 1 | mW ] ω‖ := this
        _ ≤ ‖μ[ f_n n ∘ Y | mW ] ω‖ := by
              exact mul_le_of_le_one_right (norm_nonneg _) h_ind
        _ ≤ μ[ (fun ω => ‖(f_n n ∘ Y) ω‖) | mW ] ω := by
              -- Jensen for conditional expectation
              simpa using (norm_condExp_le
                (μ := μ) (m := mW) (f := f_n n ∘ Y))
        _ ≤ μ[ (fun ω => 2 * ‖f (Y ω)‖) | mW ] ω := by
              -- Monotonicity pushes the a.e. bound ‖f_n∘Y‖ ≤ 2‖f∘Y‖ through cond. exp.
              refine condExp_mono
                (by simpa using (h_fn_int n).norm)
                (by
                  have h_norm_int : Integrable (fun ω => ‖f (Y ω)‖) μ := hf_int.norm
                  simpa using h_norm_int.const_mul 2)
                (h_bound_fn n)
    -/

    -- Conditional expectation always produces an integrable function
    have h_bound_gs_int :
        Integrable (fun ω => μ[ (fun ω => 2 * ‖f (Y ω)‖) | mW ] ω) μ := by
      -- integrable_condExp : Integrable (μ[f|m]) μ
      exact integrable_condExp

    -- Apply tendsto_condExp_unique along the subsequence
    -- Strategy: Extract the subsequence ns from h_gs_subseq, show both sequences converge
    -- along ns, then apply uniqueness to get the limit equality

    -- Extract the subsequence from h_gs_subseq
    obtain ⟨ns, h_ns_mono, h_gs_subseq_ae⟩ := h_gs_subseq

    -- Compose h_fs_ptwise with the subsequence: full sequence convergence implies subsequence convergence
    have h_fs_subseq : ∀ᵐ ω ∂μ, Filter.Tendsto
        (fun n => (f_n (ns n) ∘ Y) ω * (Z ⁻¹' B).indicator 1 ω)
        Filter.atTop
        (nhds ((f ∘ Y) ω * (Z ⁻¹' B).indicator 1 ω)) := by
      filter_upwards [h_fs_ptwise] with ω h_ω
      exact h_ω.comp h_ns_mono.tendsto_atTop

    -- Factorization holds for each element of the subsequence
    have h_factorization_subseq : ∀ n,
        μ[ (f_n (ns n) ∘ Y) * (Z ⁻¹' B).indicator 1 | mW ] =ᵐ[μ]
        μ[ f_n (ns n) ∘ Y | mW ] * μ[ (Z ⁻¹' B).indicator 1 | mW ] :=
      fun n => h_factorization (ns n)

    -- Integrability along the subsequence
    have h_fnB_subseq_int : ∀ n, Integrable ((f_n (ns n) ∘ Y) * (Z ⁻¹' B).indicator 1) μ :=
      fun n => h_fnB_int (ns n)
    have h_gs_subseq_int : ∀ n, Integrable (fun ω => μ[ f_n (ns n) ∘ Y | mW ] ω * μ[ (Z ⁻¹' B).indicator 1 | mW ] ω) μ :=
      fun n => h_gs_int (ns n)

    -- Dominating bounds along the subsequence
    have h_bound_fnB_subseq : ∀ n, ∀ᵐ ω ∂μ, ‖(f_n (ns n) (Y ω)) * (Z ⁻¹' B).indicator 1 ω‖ ≤ 2 * ‖f (Y ω)‖ :=
      fun n => h_bound_fnB (ns n)
    have h_gs_bound_subseq : ∀ n, ∀ᵐ ω ∂μ, ‖μ[ f_n (ns n) ∘ Y | mW ] ω * μ[ (Z ⁻¹' B).indicator 1 | mW ] ω‖
        ≤ μ[ (fun ω => 2 * ‖f (Y ω)‖) | mW ] ω :=
      fun n => h_gs_bound (ns n)

    -- Apply dominated convergence to pass factorization to the limit
    --
    -- Strategy: Since the factorization holds at each step of the subsequence,
    -- and both sides converge, their limits must be equal a.e.

    -- The key insight: If f_n → f a.e. and g_n → g a.e., and f_n = g_n a.e. for all n,
    -- then f = g a.e.

    -- We'll use filter_upwards to combine the convergences and factorizations
    -- Note: Can't use Filter.eventually_all for infinite ℕ, need different approach

    -- The key observation: At each ω where both sequences converge,
    -- and the factorization holds for all n, the limits must be equal.

    -- MATHLIB API NEEDED for completing this proof:

    -- 1. **Continuity of conditional expectation under dominated convergence**
    --    If f_n → f pointwise a.e. and |f_n| ≤ F with F integrable,
    --    then μ[f_n|m] → μ[f|m] in L¹ (and hence some subsequence converges a.e.)
    --
    --    Likely lemma: tendsto_condExp_of_dominated_convergence or similar
    --    Type: (hf_n : ∀ n, Integrable (f_n n) μ) →
    --          (hF : Integrable F μ) →
    --          (h_bound : ∀ n, |f_n n| ≤ᵐ[μ] F) →
    --          (h_conv : f_n → f a.e.) →
    --          Tendsto (fun n => μ[f_n n|m]) atTop (nhds μ[f|m]) (in L¹ sense)

    -- 2. **Extract a.e. convergence from L¹ convergence**
    --    If g_n → g in L¹, then some subsequence converges a.e.
    --
    --    Likely lemma: exists_seq_tendsto_ae_of_tendsto_Lp or similar
    --    Type: Tendsto g_n atTop (nhds g) (in Lp) →
    --          ∃ ns, StrictMono ns ∧ g_n ∘ ns → g a.e.

    -- 3. **Apply to our setting**
    --    - We have h_fs_subseq: (f_n (ns n) ∘ Y) * indicator → (f ∘ Y) * indicator a.e.
    --    - Apply (1) to get: μ[(f_n (ns n) ∘ Y) * indicator|mW] → μ[(f∘Y) * indicator|mW] in L¹
    --    - Apply (2) to extract subsequence: μ[(f_n (ns ns' n)) * indicator|mW] → μ[(f∘Y) * indicator|mW] a.e.
    --
    --    - We also have h_gs_subseq_ae: μ[f_n (ns n) ∘ Y|mW] * μ[indicator|mW] → μ[f∘Y|mW] * μ[indicator|mW] a.e.
    --
    --    - For each n, h_factorization_subseq n gives:
    --      μ[(f_n (ns n) ∘ Y) * indicator|mW] = μ[f_n (ns n) ∘ Y|mW] * μ[indicator|mW] a.e.
    --
    --    - By uniqueness of a.e. limits along any subsequence, the two limits must be equal a.e.

    -- 4. **Apply tendsto_condExp_unique**
    --    This mathlib lemma says: if two sequences converge a.e. with dominated bounds,
    --    and their conditional expectations are equal at each step, then the conditional
    --    expectations of the limits are equal.
    --
    --    We apply it with:
    --    - fs = (f_n n ∘ Y) * (Z ⁻¹' B).indicator 1  (full sequence)
    --    - gs = μ[f_n n ∘ Y|mW] * μ[indicator|mW]      (full sequence)
    --    - h_factorization: ∀ n, μ[fs n|mW] =ᵐ gs n
    --    - h_fs_ptwise, h_gs_subseq: both converge a.e.
    --    - Dominated bounds: h_bound_fnB, h_gs_bound
    --
    --    Note: we have a subsequence convergence for gs (h_gs_subseq_ae),
    --    but tendsto_condExp_unique needs full sequence convergence.
    --    However, since we extracted the subsequence from dominated convergence,
    --    the full sequence also converges (by uniqueness of limits).
    --
    --    Actually, we need to use the full sequence convergence, which we can get
    --    by applying DCT directly to the product of conditional expectations.

    -- First, establish full sequence convergence for RHS using dominated convergence
    --
    -- Strategy: The RHS is μ[f_n n ∘ Y|mW] ω * μ[indicator|mW] ω
    -- The second factor doesn't depend on n, so we just need to show μ[f_n n ∘ Y|mW] ω converges.
    -- This follows from DCT for conditional expectations.

    -- Step 1: Get L¹ convergence of μ[f_n n ∘ Y|mW] → μ[f ∘ Y|mW]
    have h_condExp_L1 : Filter.Tendsto
        (fun n => condExpL1 hmW_le μ (f_n n ∘ Y))
        Filter.atTop
        (nhds (condExpL1 hmW_le μ (f ∘ Y))) := by
      apply tendsto_condExpL1_domconv μ hmW_le (fun ω => 2 * ‖f (Y ω)‖)
      · intro n
        have : Measurable (f_n n) := (f_n n).measurable
        exact this.aestronglyMeasurable.comp_measurable hY
      · have h_norm_int : Integrable (fun ω => ‖f (Y ω)‖) μ := hf_int.norm
        simpa using h_norm_int.const_mul 2
      · intro n
        apply Filter.Eventually.of_forall
        intro ω
        calc ‖(f_n n) (Y ω)‖
            ≤ ‖f (Y ω)‖ + ‖f (Y ω)‖ := SimpleFunc.norm_approxOn_zero_le hf (by simp) (Y ω) n
          _ = 2 * ‖f (Y ω)‖ := by ring
      · exact h_fY_ptwise

    -- Step 2: Extract a.e. convergent subsequence
    obtain ⟨ns', h_ns'_mono, h_condExp_subseq⟩ :=
      exists_subseq_ae_tendsto_of_condExpL1_tendsto μ hmW_le h_condExp_L1

    -- Step 3: Apply tendsto_condExp_unique to the subsequence
    --
    -- Key: The RHS product μ[f_n ∘ Y|mW] * μ[indicator|mW] is already mW-measurable,
    -- so μ[RHS|mW] =ᵐ RHS by condExp_of_aestronglyMeasurable'
    --
    -- This allows us to use h_factorization_subseq with tendsto_condExp_unique

    -- First, we need to show μ[gs (ns n)|mW] =ᵐ gs (ns n) where gs n = μ[f_n n ∘ Y|mW] * μ[indicator|mW]
    have h_gs_is_mW_measurable : ∀ n,
        μ[ (fun ω => μ[ f_n (ns n) ∘ Y | mW ] ω * μ[ (Z ⁻¹' B).indicator 1 | mW ] ω) | mW ]
          =ᵐ[μ]
        (fun ω => μ[ f_n (ns n) ∘ Y | mW ] ω * μ[ (Z ⁻¹' B).indicator 1 | mW ] ω) := by
      intro n
      -- The product of two condExps is mW-measurable
      apply condExp_of_aestronglyMeasurable' hmW_le
      · -- Product of two mW-strongly measurable functions is mW-strongly measurable
        exact (stronglyMeasurable_condExp.mul stronglyMeasurable_condExp).aestronglyMeasurable
      · -- Integrability of the product
        exact h_gs_subseq_int n

    -- Now convert h_factorization_subseq using h_gs_is_mW_measurable
    have h_factorization_as_condExps : ∀ n,
        μ[ (f_n (ns n) ∘ Y) * (Z ⁻¹' B).indicator 1 | mW ]
          =ᵐ[μ]
        μ[ (fun ω => μ[ f_n (ns n) ∘ Y | mW ] ω * μ[ (Z ⁻¹' B).indicator 1 | mW ] ω) | mW ] := by
      intro n
      exact (h_factorization_subseq n).trans (h_gs_is_mW_measurable n).symm

    -- Apply tendsto_condExp_unique to get: μ[LHS|mW] =ᵐ μ[RHS|mW]
    have h_condExps_equal := tendsto_condExp_unique
      (fun n => (f_n (ns n) ∘ Y) * (Z ⁻¹' B).indicator 1)  -- fs
      (fun n => fun ω => μ[ f_n (ns n) ∘ Y | mW ] ω * μ[ (Z ⁻¹' B).indicator 1 | mW ] ω)  -- gs
      ((f ∘ Y) * (Z ⁻¹' B).indicator 1)  -- f
      (fun ω => μ[ f ∘ Y | mW ] ω * μ[ (Z ⁻¹' B).indicator 1 | mW ] ω)  -- g
      h_fnB_subseq_int
      h_gs_subseq_int
      h_fs_subseq
      h_gs_subseq_ae
      (fun ω => 2 * ‖f (Y ω)‖)
      h_bound_fs_int
      (fun ω => μ[ (fun ω => 2 * ‖f (Y ω)‖) | mW ] ω)
      h_bound_gs_int
      h_bound_fnB_subseq
      h_gs_bound_subseq
      h_factorization_as_condExps

    -- Apply mW-measurability at the limit
    have h_g_is_mW_measurable :
        μ[ (fun ω => μ[ f ∘ Y | mW ] ω * μ[ (Z ⁻¹' B).indicator 1 | mW ] ω) | mW ]
          =ᵐ[μ]
        (fun ω => μ[ f ∘ Y | mW ] ω * μ[ (Z ⁻¹' B).indicator 1 | mW ] ω) := by
      apply condExp_of_aestronglyMeasurable' hmW_le
      · exact (stronglyMeasurable_condExp.mul stronglyMeasurable_condExp).aestronglyMeasurable
      · exact h_g_int

    -- Combine to get the desired result
    exact h_condExps_equal.trans h_g_is_mW_measurable

    /-
    **Status: Stage 3 nearly complete!**

    What's proven:
    - ✅ h_factorization: Each approximant satisfies the factorization (lines 692-879)
    - ✅ All integrability lemmas (h_fnB_int, h_gs_int, etc.)
    - ✅ LHS pointwise convergence (h_fs_ptwise)
    - ✅ Dominating bounds setup
    - ✅ Overall tendsto_condExp_unique structure

    What remains (2 sorries, ~35-45 lines total):
    1. **RHS pointwise convergence** (~15-20 lines)
       - Apply tendsto_condExpL1_of_dominated_convergence to get L¹ convergence
       - Extract a.e. convergence (L¹ → subsequence a.e. → full sequence by uniqueness)

    2. **RHS dominating bound** (~20-25 lines)
       - Use Jensen: ‖μ[g|m]‖ ≤ μ[‖g‖|m] (norm_condExp_le)
       - Apply monotonicity: μ[‖f_n‖|mW] ≤ μ[2‖f‖|mW]
       - Bound: ‖μ[indicator|mW]‖ ≤ 1

    Both are standard measure theory, no new mathematics needed.

    **Mathematical content: 100% COMPLETE!**
    All conditional independence is in h_factorization. Remaining sorries are pure
    dominated convergence machinery
    -- For each n, apply simple_func_case to s n * (Z ⁻¹' B).indicator 1
    have h_step2_approx :
      ∀ n,
        μ[ fun ω => (s n ω) * (Z ⁻¹' B).indicator 1 ω | mW]
          =ᵐ[μ]
        fun ω => (μ[ s n | mW ] ω) * (μ[ (Z ⁻¹' B).indicator 1 | mW ] ω) := by
      intro n
      obtain ⟨ι, _, A, hA, a, rfl⟩ := h_decomp n
      -- Now s n is ∑ᵢ aᵢ * (Y⁻¹Aᵢ).indicator 1, exactly the form for simple_func_case!
      exact simple_func_case _ a _ (fun i _ => hY (hA i))
        (fun i _ => ⟨A i, hA i, rfl⟩) (...)
    ```

    **Step 4: Pass to limit via dominated convergence** (~20-25 lines)
    ```lean
    -- LHS: μ[s n * indicator_B | W] → μ[f∘Y * indicator_B | W] in L¹
    have h_lhs_limit :
      Tendsto (fun n => (⟪μ[ fun ω => (s n ω) * (Z ⁻¹' B).indicator 1 ω | mW]⟫ : L¹ μ))
              atTop
              (𝓝 (⟪μ[ fun ω => (f ∘ Y) ω * (Z ⁻¹' B).indicator 1 ω | mW]⟫ : L¹ μ)) := by
      apply tendsto_condExpL1_of_dominated_convergence
      -- Need: pointwise a.e. convergence, L¹ domination, integrability
      -- ...
      admit

    -- RHS: similarly for μ[s n | W] * μ[indicator_B | W] → μ[f∘Y | W] * μ[indicator_B | W]
    have h_rhs_limit : ... := by
      -- Similar DCT argument, only first factor depends on n
      admit

    -- Combine: both sides have the same limit, extract a.e. equality
    -- Use that h_step2_approx n holds for all n and limits match
    -- ...
    admit
    ```

    **Key remaining work:**
    - Fill in the decomposition lemma (Step 2) - this is the most technical part
    - Apply dominated convergence with correct bounds (Step 4)
    - Extract a.e. equality from L¹ convergence

    **Total estimate:** ~50-80 lines of careful measure theory formalization

    **Status:** Blueprint complete, implementation requires dedicated session for details
    -/
    /-
    **Path Forward (requires ~60-100 lines + additional lemmas):**

    **Option 1: Prove the missing lemma** (~30 lines)
    Prove: If f ∘ Y is AEStronglyMeasurable w.r.t. μ and Y is surjective + measurable,
    then f is AEStronglyMeasurable w.r.t. μ.map Y.

    This likely requires:
    - Constructing explicit representatives using AEStronglyMeasurable.mk
    - Showing the construction preserves strong measurability
    - Handling null sets carefully

    **Option 2: Alternative approximation strategy** (~70-100 lines)
    Instead of working on βY, approximate directly on Ω:
    1. Use that f ∘ Y is AEStronglyMeasurable to get simple function approximations sₙ : Ω → ℝ
    2. For each sₙ, decompose it into Y-measurable part + remainder
    3. Show the Y-measurable parts approximate f ∘ Y
    4. Apply simple_func_case to Y-measurable parts
    5. Show remainder → 0
    6. Apply dominated convergence

    **Option 3: Assume additional structure** (~40-60 lines)
    If Y is surjective (or has dense image), or if we add additional regularity assumptions,
    the problem becomes easier. Check if these are reasonable for applications.

    **Current Status:**
    - Architecture: ✅ 100% sound
    - Stage 1 (indicators): ✅ 100% complete - ALL conditional independence mathematics
    - Stage 2 (simple functions): ✅ 100% complete - extension mechanism proven
    - Stage 3 (general): Implementation blocked on measure-theoretic technicality

    The mathematical content is complete. The remaining work is pure formalization machinery.
    -/

  have h_rect : ∀ (S : Set Ω), @MeasurableSet Ω mW S → μ S < ⊤ →
                  ∀ (B : Set βZ), MeasurableSet B →
      ∫ x in S ∩ Z ⁻¹' B, g x ∂μ = ∫ x in S ∩ Z ⁻¹' B, (f ∘ Y) x ∂μ := by
    intro S hS hμS B hB

    -- The key factorization from conditional independence
    have h_factor := condIndep_factor B hB

    -- Measurability facts we'll need
    have hS_meas : @MeasurableSet Ω mΩ S := hmW_le _ hS
    have hZB_meas : @MeasurableSet Ω mΩ (Z ⁻¹' B) := hZ hB
    have hg_meas : StronglyMeasurable[mW] g := stronglyMeasurable_condExp

    -- Strategy: Proof by rewriting indicators as products and using h_factor
    --
    -- Goal: ∫ x in S ∩ Z⁻¹' B, μ[f ∘ Y|mW] x ∂μ = ∫ x in S ∩ Z⁻¹' B, (f ∘ Y) x ∂μ
    -- where S ∈ σ(W), B ∈ B_Z
    --
    -- Key insight: Rewrite (Z⁻¹' B).indicator as multiplication by (Z⁻¹' B).indicator 1
    -- Then use:
    --   - h_factor: μ[(f ∘ Y) * indicator|mW] =ᵐ μ[f ∘ Y|mW] * μ[indicator|mW]
    --   - condExp_mul_of_stronglyMeasurable_left: pull out mW-measurable factors
    --
    -- Implementation requires careful handling of:
    --   1. Converting set integrals ↔ indicator integrals (setIntegral_indicator)
    --   2. Rewriting indicator f = f * indicator 1
    --   3. Applying h_factor to connect the two conditional expectations
    --   4. Using setIntegral_congr_ae to show integrands are a.e. equal on S
    --
    -- Estimated ~40-60 additional lines with proper integrability side conditions

    -- Strategy: Use Set.inter_indicator_mul to split the intersection indicator,
    -- then apply condExp_mul_of_stronglyMeasurable_left with the factorization h_factor

    -- Step 1: Convert to indicator integrals
    rw [← integral_indicator (hS_meas.inter hZB_meas)]
    rw [← integral_indicator (hS_meas.inter hZB_meas)]

    -- Step 2: Use inter_indicator_mul to split: (S ∩ T).indicator h = S.indicator h * T.indicator 1
    -- First, rewrite h as h * 1
    have h_mul_one : ∀ h : Ω → ℝ, h = fun ω => h ω * (1 : ℝ) := fun h => by ext; simp

    conv_lhs => arg 2; ext ω; rw [h_mul_one g]
    conv_rhs => arg 2; ext ω; rw [h_mul_one (f ∘ Y)]

    -- Apply inter_indicator_mul
    have h_split_g : (S ∩ Z ⁻¹' B).indicator (fun ω => g ω * 1) =
                     fun ω => S.indicator g ω * (Z ⁻¹' B).indicator (1 : Ω → ℝ) ω := by
      ext ω
      exact Set.inter_indicator_mul g (1 : Ω → ℝ) ω

    have h_split_fY : (S ∩ Z ⁻¹' B).indicator (fun ω => (f ∘ Y) ω * 1) =
                      fun ω => S.indicator (f ∘ Y) ω * (Z ⁻¹' B).indicator (1 : Ω → ℝ) ω := by
      ext ω
      exact Set.inter_indicator_mul (f ∘ Y) (1 : Ω → ℝ) ω

    rw [h_split_g, h_split_fY]

    -- Step 3: Rewrite products as nested indicators, then convert to set integral
    have h_nest_g : (fun ω => S.indicator g ω * (Z ⁻¹' B).indicator 1 ω) =
                    S.indicator (fun ω => g ω * (Z ⁻¹' B).indicator 1 ω) := by
      ext ω; by_cases hω : ω ∈ S <;> simp [Set.indicator, hω]

    have h_nest_fY : (fun ω => S.indicator (f ∘ Y) ω * (Z ⁻¹' B).indicator 1 ω) =
                     S.indicator (fun ω => (f ∘ Y) ω * (Z ⁻¹' B).indicator 1 ω) := by
      ext ω; by_cases hω : ω ∈ S <;> simp [Set.indicator, hω]

    rw [h_nest_g, h_nest_fY, integral_indicator hS_meas, integral_indicator hS_meas]

    -- Step 4: Now we have ∫ x in S, g x * (Z⁻¹'B).indicator 1 x = ∫ x in S, (f∘Y) x * (Z⁻¹'B).indicator 1 x
    -- Since S is mW-measurable, we can use the tower property

    -- The key: use setIntegral_condExp with the factorization h_factor
    -- We need to show: ∫_{S} g * indicator = ∫_{S} (f∘Y) * indicator

    -- First, by h_factor: μ[(f∘Y) * indicator|mW] =ᵐ g * μ[indicator|mW]
    -- Then integrate over S (which is mW-measurable)

    -- Apply setIntegral_condExp to RHS
    have h_tower_rhs : ∫ x in S, μ[(f ∘ Y) * (Z ⁻¹' B).indicator 1|mW] x ∂μ =
                       ∫ x in S, (f ∘ Y) x * (Z ⁻¹' B).indicator 1 x ∂μ := by
      apply setIntegral_condExp hmW_le _ hS
      -- Need integrability of (f ∘ Y) * indicator
      have h_int : Integrable ((f ∘ Y) * (Z ⁻¹' B).indicator 1) μ := by
        have : (f ∘ Y) * (Z ⁻¹' B).indicator 1 = (Z ⁻¹' B).indicator (f ∘ Y) := by
          ext ω; by_cases hω : ω ∈ Z ⁻¹' B <;> simp [Set.indicator, hω]
        rw [this]
        exact hf_int.indicator hZB_meas
      exact h_int

    -- Now use h_factor on S
    have h_factor_S : ∫ x in S, μ[(f ∘ Y) * (Z ⁻¹' B).indicator 1|mW] x ∂μ =
                      ∫ x in S, g x * μ[(Z ⁻¹' B).indicator 1|mW] x ∂μ := by
      apply setIntegral_congr_ae (hmW_le _ hS)
      filter_upwards [h_factor] with ω hω _
      simp only [Pi.mul_apply] at hω
      rw [hg_def]
      exact hω

    -- Finally, connect via condExp_mul_of_stronglyMeasurable_left with g
    -- Since g = μ[f∘Y|mW] is mW-strongly measurable, we can pull it through:
    -- μ[g * (Z⁻¹'B).indicator 1|mW] =ᵐ g * μ[(Z⁻¹'B).indicator 1|mW]

    have h_g_mult : μ[g * (Z ⁻¹' B).indicator 1|mW] =ᵐ[μ] g * μ[(Z ⁻¹' B).indicator 1|mW] := by
      apply condExp_mul_of_stronglyMeasurable_left hg_meas
      · -- Integrability of g * indicator
        have : g * (Z ⁻¹' B).indicator 1 = (Z ⁻¹' B).indicator g := by
          ext ω; by_cases hω : ω ∈ Z ⁻¹' B <;> simp [Set.indicator, hω]
        rw [this]
        exact integrable_condExp.indicator hZB_meas
      · -- Integrability of (Z⁻¹'B).indicator 1
        have : (Z ⁻¹' B).indicator (1 : Ω → ℝ) = (Z ⁻¹' B).indicator (fun _ => (1 : ℝ)) := rfl
        rw [this]
        exact (integrable_const (1 : ℝ)).indicator hZB_meas

    -- Now apply condExp_mul_of_stronglyMeasurable_left with S.indicator 1
    have hS_ind_sm : StronglyMeasurable[mW] (S.indicator (fun _ : Ω => (1 : ℝ))) := by
      apply StronglyMeasurable.indicator stronglyMeasurable_const hS

    have h_tower_lhs : μ[S.indicator 1 * (g * (Z ⁻¹' B).indicator 1)|mW] =ᵐ[μ]
                       S.indicator 1 * μ[g * (Z ⁻¹' B).indicator 1|mW] := by
      apply condExp_mul_of_stronglyMeasurable_left hS_ind_sm
      · -- Integrability of S.indicator 1 * (g * indicator)
        have h_ind_eq : (S.indicator (fun _ : Ω => (1 : ℝ))) * (g * (Z ⁻¹' B).indicator 1) =
                        S.indicator ((Z ⁻¹' B).indicator g) := by
          ext ω
          simp only [Pi.mul_apply]
          by_cases hS : ω ∈ S
          · simp [Set.indicator_of_mem hS]
            by_cases hB : ω ∈ Z ⁻¹' B <;> simp [Set.indicator, hB]
          · simp [Set.indicator_of_notMem hS]
        rw [h_ind_eq]
        exact (integrable_condExp.indicator hZB_meas).indicator hS_meas
      · -- Integrability of g * (Z⁻¹'B).indicator 1
        have : g * (Z ⁻¹' B).indicator 1 = (Z ⁻¹' B).indicator g := by
          ext ω; by_cases hω : ω ∈ Z ⁻¹' B <;> simp [Set.indicator, hω]
        rw [this]
        exact integrable_condExp.indicator hZB_meas

    -- Combine h_g_mult and h_tower_lhs
    have h_combine : S.indicator 1 * μ[g * (Z ⁻¹' B).indicator 1|mW] =ᵐ[μ]
                     S.indicator 1 * (g * μ[(Z ⁻¹' B).indicator 1|mW]) := by
      filter_upwards [h_g_mult] with ω hω
      by_cases hS : ω ∈ S
      · simp [Set.indicator_of_mem hS, hω]
      · simp [Set.indicator_of_notMem hS]

    -- Integrate h_tower_lhs
    have h_int_lhs : ∫ x, S.indicator 1 x * (g x * (Z ⁻¹' B).indicator 1 x) ∂μ =
                     ∫ x, (S.indicator 1 x * μ[g * (Z ⁻¹' B).indicator 1|mW] x) ∂μ := by
      symm
      calc ∫ x, (S.indicator 1 x * μ[g * (Z ⁻¹' B).indicator 1|mW] x) ∂μ
          = ∫ x, μ[S.indicator 1 * (g * (Z ⁻¹' B).indicator 1)|mW] x ∂μ := by
              apply integral_congr_ae
              exact h_tower_lhs.symm
        _ = ∫ x, S.indicator 1 x * (g x * (Z ⁻¹' B).indicator 1 x) ∂μ := by
              -- Tower property: ∫ μ[f|m] x = ∫ f x
              exact integral_condExp hmW_le

    -- Convert to set integral form
    have h_as_setInt_lhs : ∫ x, S.indicator 1 x * (g x * (Z ⁻¹' B).indicator 1 x) ∂μ =
                           ∫ x in S, g x * (Z ⁻¹' B).indicator 1 x ∂μ := by
      rw [← integral_indicator hS_meas]
      congr 1; ext ω; by_cases hω : ω ∈ S <;> simp [Set.indicator, hω]

    have h_as_setInt_rhs : ∫ x, (S.indicator 1 x * μ[g * (Z ⁻¹' B).indicator 1|mW] x) ∂μ =
                           ∫ x in S, μ[g * (Z ⁻¹' B).indicator 1|mW] x ∂μ := by
      rw [← integral_indicator hS_meas]
      congr 1; ext ω; by_cases hω : ω ∈ S <;> simp [Set.indicator, hω]

    -- Now combine everything
    calc ∫ x in S, g x * (Z ⁻¹' B).indicator 1 x ∂μ
        = ∫ x in S, μ[g * (Z ⁻¹' B).indicator 1|mW] x ∂μ := by
            rw [← h_as_setInt_lhs, h_int_lhs, h_as_setInt_rhs]
      _ = ∫ x in S, (g x * μ[(Z ⁻¹' B).indicator 1|mW] x) ∂μ := by
            apply setIntegral_congr_ae (hmW_le _ hS)
            filter_upwards [h_g_mult] with ω hω _ using hω
      _ = ∫ x in S, μ[(f ∘ Y) * (Z ⁻¹' B).indicator 1|mW] x ∂μ := h_factor_S.symm
      _ = ∫ x in S, (f ∘ Y) x * (Z ⁻¹' B).indicator 1 x ∂μ := h_tower_rhs

    -- 3. Tower property:
    --    integral_condExp: ∫ f ∂μ = ∫ μ[f|m] ∂μ (when f integrable)

    -- 4. Pull out measurable factors:
    --    condExp_mul_of_stronglyMeasurable or condExp_stronglyMeasurable_mul
    --    If g is m-measurable, then μ[g * f|m] = g * μ[f|m] a.e.

    -- 5. Apply h_factor to substitute factorization

    -- Attempted implementation:
    -- calc ∫ x in S ∩ Z ⁻¹' B, g x ∂μ
    --     = ∫ x, (S ∩ Z ⁻¹' B).indicator (fun x => g x) x ∂μ := by
    --       -- Need: setIntegral conversion lemma
    --       sorry
    --   _ = ∫ x, g x * (S.indicator 1 x * (Z ⁻¹' B).indicator 1 x) ∂μ := by
    --       -- Need: indicator factorization lemma
    --       sorry
    --   _ = ∫ x, (g x * S.indicator 1 x) * (Z ⁻¹' B).indicator 1 x ∂μ := by
    --       congr 1; ext x; ring
    --   _ = ∫ x, (g x * S.indicator 1 x) * μ[(Z ⁻¹' B).indicator 1|mW] x ∂μ := by
    --       -- Need: integral_condExp + pull-out lemma
    --       sorry

    -- TODO: Rectangle case proof (~50-80 lines)
    --
    -- Goal: ∫ x in S ∩ Z ⁻¹' B, g x ∂μ = ∫ x in S ∩ Z ⁻¹' B, (f ∘ Y) x ∂μ
    -- where g = μ[f ∘ Y|mW], S ∈ σ(W), B ∈ B_Z
    --
    -- Strategy (see detailed comments above):
    -- 1. Convert set integrals to indicator integrals
    -- 2. Factor intersection indicator: (S ∩ Z⁻¹B).indicator = S.indicator * (Z⁻¹B).indicator
    -- 3. Use tower property and h_factor factorization
    -- 4. Pull out mW-measurable factors
    -- 5. Apply integral_condExp to simplify
    --
    -- Key lemmas needed:
    -- - setIntegral_eq_integral_indicator / integral_indicator
    -- - Set.indicator_inter_mul or similar
    -- - integral_condExp
    -- - condExp_mul_of_stronglyMeasurable (pull out measurable factors)
    -- - h_factor (from condIndep_factor above)
    /-
    **Detailed Implementation Guide (~30-50 lines):**

    **Goal:** ∫_{S∩Z⁻¹(B)} g dμ = ∫_{S∩Z⁻¹(B)} f(Y) dμ
    where S ∈ σ(W), B ∈ B_Z, g = E[f(Y)|W]

    **Mathematical Strategy:**
    Both sides integrate over S ∩ Z⁻¹(B). We'll show they equal the same expression:
      E[g · 1_S · E[1_{Z⁻¹(B)} | W]]

    **Implementation Steps:**

    **Step 1: Convert LHS to conditional expectation form**
    ```lean
    calc ∫ x in S ∩ Z ⁻¹' B, g x ∂μ
        = ∫ x, (S ∩ Z ⁻¹' B).indicator g x ∂μ           [use setIntegral_eq_integral_indicator]
      _ = ∫ x, g x * (S ∩ Z ⁻¹' B).indicator 1 x ∂μ     [indicator_mul_left]
      _ = ∫ x, g x * S.indicator 1 x * (Z ⁻¹' B).indicator 1 x ∂μ  [indicator_inter_mul]
    ```

    **Step 2: Apply tower property to LHS**
    Since g = E[f∘Y | mW] and integrating against 1 gives expectation:
    ```lean
      _ = ∫ x, μ[g * S.indicator 1 * (Z ⁻¹' B).indicator 1 | mW] x ∂μ  [integral_condExp]
    ```

    **Step 3: Pull out mW-measurable factors from LHS**
    Since g and S.indicator 1 are both mW-measurable:
    ```lean
      _ = ∫ x, (g x * S.indicator 1 x) * μ[(Z ⁻¹' B).indicator 1 | mW] x ∂μ
            [use condExp_mul_of_stronglyMeasurable_left]
    ```

    **Step 4: Convert RHS similarly**
    ```lean
    ∫ x in S ∩ Z ⁻¹' B, (f ∘ Y) x ∂μ
      = ∫ x, (f ∘ Y) x * S.indicator 1 x * (Z ⁻¹' B).indicator 1 x ∂μ
      = ∫ x, S.indicator 1 x * ((f ∘ Y) x * (Z ⁻¹' B).indicator 1 x) ∂μ
    ```

    **Step 5: Apply conditional factorization to RHS**
    ```lean
      _ = ∫ x, S.indicator 1 x * μ[(f ∘ Y) * (Z ⁻¹' B).indicator 1 | mW] x ∂μ
            [integral_condExp and pull-out]
      _ = ∫ x, S.indicator 1 x * (g x * μ[(Z ⁻¹' B).indicator 1 | mW] x) ∂μ
            [apply h_factor: E[f(Y)·1_B|W] = g·E[1_B|W]]
      _ = ∫ x, (g x * S.indicator 1 x) * μ[(Z ⁻¹' B).indicator 1 | mW] x ∂μ
            [commutativity and reassociation]
    ```

    **Step 6: Conclude**
    Both sides equal the same expression, so LHS = RHS. ∎

    **Key Lemmas:**
    - `setIntegral_eq_integral_indicator` (convert set integral to indicator)
    - `Set.indicator_inter_mul` (split intersection indicator)
    - `integral_condExp` (tower property: ∫ f = ∫ E[f|m])
    - `condExp_mul_of_stronglyMeasurable_left` (pull out measurable factors)
    - `h_factor` (conditional independence factorization)
    - `mul_comm`, `mul_assoc` (arithmetic rearrangement)
    -/
    /-
    **Mathematical Argument (conditional independence factorization):**

    **Goal:** ∫_{S∩Z⁻¹(B)} g = ∫_{S∩Z⁻¹(B)} f(Y)

    **LHS computation:**
    1. g = E[f(Y)|W] is σ(W)-measurable (by stronglyMeasurable_condExp)
    2. S ∈ σ(W) (hypothesis), so g·1_S is σ(W)-measurable
    3. ∫_{S∩Z⁻¹(B)} g = ∫ g·1_S·1_{Z⁻¹(B)} = E[g·1_S·1_{Z⁻¹(B)}]
    4. By tower property: = E[E[g·1_S·1_{Z⁻¹(B)}|W]]
    5. Pull out σ(W)-measurable function g·1_S:
       = E[g·1_S·E[1_{Z⁻¹(B)}|W]]

    **RHS computation:**
    1. ∫_{S∩Z⁻¹(B)} f(Y) = E[f(Y)·1_S·1_{Z⁻¹(B)}]
    2. Tower property: = E[E[f(Y)·1_S·1_{Z⁻¹(B)}|W]]
    3. Pull out σ(W)-measurable indicator 1_S:
       = E[1_S·E[f(Y)·1_{Z⁻¹(B)}|W]]

    **Conditional independence step (KEY):**
    4. By CondIndepFun, need to show:
       E[f(Y)·1_{Z⁻¹(B)}|W] = E[f(Y)|W]·E[1_{Z⁻¹(B)}|W]

    5. This requires extending CondIndepFun from indicators to bounded measurable functions.
       The definition CondIndepFun uses indicator functions, but we need it for f(Y).

    6. Once we have factorization:
       E[1_S·E[f(Y)·1_{Z⁻¹(B)}|W]] = E[1_S·g·E[1_{Z⁻¹(B)}|W]]
                                      = E[g·1_S·E[1_{Z⁻¹(B)}|W]]
       which matches the LHS!

    **Implementation challenges:**

    A. **Extension to bounded measurables:**
       - CondIndepFun is defined via indicator factorization
       - Need lemma: CondIndepFun + f integrable → factorization for f
       - This is the "monotone class" extension from the definition comments
       - Could use: approximate f by simple functions, pass to limit

    B. **Pulling out measurable functions from CE:**
       - Need: E[h·g|m] = h·E[g|m] when h is m-measurable
       - Mathlib has: condExp_smul or similar
       - For indicators: use condExp_set_eq or setIntegral_condExp

    C. **Tower property application:**
       - Need: E[E[g|W]|W] = E[g|W]
       - This is just condExp_condExp_of_le

    **Proposed implementation path:**

    Option 1: Prove extension lemma separately
      lemma condIndepFun_integral_eq : CondIndepFun m hm Y Z μ →
        Integrable (f ∘ Y) μ → Integrable (1_{Z⁻¹(B)}) μ →
        E[f(Y)·1_{Z⁻¹(B)}|W] = E[f(Y)|W]·E[1_{Z⁻¹(B)}|W]
      Then use this in h_rect.

    Option 2: Use approximation directly in this proof
      - Approximate f by simple functions fₙ
      - Apply CondIndepFun to each simple function piece
      - Pass to limit using dominated convergence

    Option 3: Acknowledge complexity and defer
      - This is mathematically sound but technically demanding
      - Could be factored into a separate lemma file
      - For now, keep as sorry with complete documentation

    **Recommendation:** Option 1 - Prove extension lemma separately.

    **Detailed Implementation Plan for Extension Lemma:**

    The key lemma needed:
    ```
    lemma condIndepFun_condExp_mul (hCI : CondIndepFun mW hw Y Z μ)
        (hf : Integrable (f ∘ Y) μ) (hB : MeasurableSet B) :
        μ[ (f ∘ Y) * (Z ⁻¹' B).indicator 1 | mW ] =ᵐ[μ]
        μ[ f ∘ Y | mW ] * μ[ (Z ⁻¹' B).indicator 1 | mW ]
    ```

    **Proof Strategy (Monotone Class):**

    1. **For simple functions:** If f = Σᵢ aᵢ·1_{Aᵢ}, use linearity:
       - E[(Σᵢ aᵢ·1_{Aᵢ}∘Y)·1_B|W] = Σᵢ aᵢ·E[1_{Y∈Aᵢ}·1_{Z∈B}|W]
       - Apply CondIndepFun to each indicator pair
       - = Σᵢ aᵢ·E[1_{Y∈Aᵢ}|W]·E[1_{Z∈B}|W]
       - = (Σᵢ aᵢ·E[1_{Aᵢ}∘Y|W])·E[1_B|W]
       - = E[f∘Y|W]·E[1_B|W]

    2. **For bounded measurables:** Approximate f by simple functions fₙ:
       - Use SimpleFunc.approxOn or similar from mathlib
       - Show fₙ → f pointwise and in L¹
       - Apply dominated convergence to conditional expectations
       - Pass factorization to limit

    3. **Apply to h_rect:** Once we have this lemma:
       - LHS: ∫_{S∩Z⁻¹(B)} g = E[g·1_S·1_{Z∈B}]
              = E[E[f∘Y|W]·1_S·1_{Z∈B}]  (by definition of g)
              = E[E[f∘Y·1_S·1_{Z∈B}|W]]  (pull in 1_S which is mW-measurable)
       - RHS: ∫_{S∩Z⁻¹(B)} f∘Y = E[f∘Y·1_S·1_{Z∈B}]
              = E[E[f∘Y·1_S·1_{Z∈B}|W]]  (tower)
       - By extension lemma with h=1_S:
              E[(f∘Y·1_S)·1_{Z∈B}|W] = E[f∘Y·1_S|W]·E[1_{Z∈B}|W]
                                      = E[f∘Y|W]·1_S·E[1_{Z∈B}|W]
                                      = g·1_S·E[1_{Z∈B}|W]
       - Take expectation: E[g·1_S·E[1_{Z∈B}|W]]
       - This completes the proof

    **Technical Lemmas Needed:**
    - condExp_indicator_mul: E[h·1_A·g|m] = h·E[1_A·g|m] when h is m-measurable
    - Or condExp_smul: E[c·f|m] = c·E[f|m] when c is m-measurable
    - These should be in mathlib or easy to derive

    **Status:** This is the only remaining substantive gap. The mathematical
    argument is sound and all the pieces are standard techniques. Implementation
    would likely be 100-200 lines for the extension lemma + application.
    -/

  -- Step 2: π-λ extension to all σ(Z,W)-sets
  have h_all : ∀ (T : Set Ω), @MeasurableSet Ω mZW T → μ T < ⊤ →
      ∫ x in T, g x ∂μ = ∫ x in T, (f ∘ Y) x ∂μ := by
    intro T hT hμT

    -- Define the class of sets where integral equality holds
    -- C(T) := (@MeasurableSet Ω mZW T ∧ μ T < ⊤ → ∫_T g = ∫_T f(Y))
    -- We'll use induction_on_inter to show this holds for all mZW-measurable sets

    -- First, we need mZW represented as generateFrom of a π-system
    -- Key fact: mZW = mZ ⊔ mW is generated by rectangles Z⁻¹(A) ∩ W⁻¹(B)

    -- Define the π-system of rectangles
    let 𝓡 : Set (Set Ω) := {T | ∃ (A : Set βZ) (B : Set βW),
                                 MeasurableSet A ∧ MeasurableSet B ∧
                                 T = Z ⁻¹' A ∩ W ⁻¹' B}

    -- Rectangles form a π-system (closed under finite intersections)
    have h𝓡_pi : IsPiSystem 𝓡 := by
      -- Definition of IsPiSystem: ∀ S T ∈ 𝓡, S ∩ T ≠ ∅ → S ∩ T ∈ 𝓡
      intro S hS T hT _
      -- Unpack S and T as rectangles
      obtain ⟨A₁, B₁, hA₁, hB₁, rfl⟩ := hS
      obtain ⟨A₂, B₂, hA₂, hB₂, rfl⟩ := hT
      -- Show S ∩ T = Z⁻¹(A₁ ∩ A₂) ∩ W⁻¹(B₁ ∩ B₂) is in 𝓡
      refine ⟨A₁ ∩ A₂, B₁ ∩ B₂, hA₁.inter hA₂, hB₁.inter hB₂, ?_⟩
      -- Need to show: (Z⁻¹A₁ ∩ W⁻¹B₁) ∩ (Z⁻¹A₂ ∩ W⁻¹B₂) = Z⁻¹(A₁∩A₂) ∩ W⁻¹(B₁∩B₂)
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_preimage]
      tauto

    -- Rectangles generate mZW = mZ ⊔ mW
    have h𝓡_gen : MeasurableSpace.generateFrom 𝓡 = mZW := by
      apply le_antisymm

      -- First direction: generateFrom 𝓡 ≤ mZW
      · apply MeasurableSpace.generateFrom_le
        intro R hR
        obtain ⟨A, B, hA, hB, rfl⟩ := hR
        -- R = Z⁻¹(A) ∩ W⁻¹(B) is mZW-measurable
        -- Z⁻¹(A) is mZ-measurable, W⁻¹(B) is mW-measurable
        have hZ_meas : @MeasurableSet Ω mZ (Z ⁻¹' A) := ⟨A, hA, rfl⟩
        have hW_meas : @MeasurableSet Ω mW (W ⁻¹' B) := ⟨B, hB, rfl⟩
        -- Both are mZW-measurable since mZ, mW ≤ mZW
        have hZ_mZW : @MeasurableSet Ω mZW (Z ⁻¹' A) := @le_sup_left _ _ mZ mW _ hZ_meas
        have hW_mZW : @MeasurableSet Ω mZW (W ⁻¹' B) := @le_sup_right _ _ mZ mW _ hW_meas
        -- Intersection is mZW-measurable
        exact MeasurableSet.inter hZ_mZW hW_mZW

      -- Second direction: mZW ≤ generateFrom 𝓡
      · -- mZW = mZ ⊔ mW, so we need to show mZ ≤ generateFrom 𝓡 and mW ≤ generateFrom 𝓡
        apply sup_le

        -- Show mZ ≤ generateFrom 𝓡
        · intro S hS
          obtain ⟨A, hA, rfl⟩ := hS
          -- Z⁻¹(A) = Z⁻¹(A) ∩ W⁻¹(univ) ∈ 𝓡
          have : Z ⁻¹' A = Z ⁻¹' A ∩ W ⁻¹' Set.univ := by simp
          rw [this]
          apply MeasurableSpace.measurableSet_generateFrom
          exact ⟨A, Set.univ, hA, MeasurableSet.univ, rfl⟩

        -- Show mW ≤ generateFrom 𝓡
        · intro S hS
          obtain ⟨B, hB, rfl⟩ := hS
          -- W⁻¹(B) = Z⁻¹(univ) ∩ W⁻¹(B) ∈ 𝓡
          have : W ⁻¹' B = Z ⁻¹' Set.univ ∩ W ⁻¹' B := by simp
          rw [this]
          apply MeasurableSpace.measurableSet_generateFrom
          exact ⟨Set.univ, B, MeasurableSet.univ, hB, rfl⟩

    -- Integral equality holds on rectangles
    have h_rect_all : ∀ (R : Set Ω), R ∈ 𝓡 → μ R < ⊤ →
        ∫ x in R, g x ∂μ = ∫ x in R, (f ∘ Y) x ∂μ := by
      intro R hR_mem hμR
      -- Unpack R ∈ 𝓡
      obtain ⟨A, B, hA, hB, rfl⟩ := hR_mem
      -- Now R = Z⁻¹(A) ∩ W⁻¹(B)
      -- W⁻¹(B) is mW-measurable, so this is a valid rectangle for h_rect
      have hmW_preimage : @MeasurableSet Ω mW (W ⁻¹' B) := ⟨B, hB, rfl⟩
      -- On a probability space, all sets have finite measure
      have hμW : μ (W ⁻¹' B) < ⊤ := measure_lt_top μ (W ⁻¹' B)
      -- h_rect gives us: ∫_{W⁻¹(B) ∩ Z⁻¹(A)} g = ∫_{W⁻¹(B) ∩ Z⁻¹(A)} f(Y)
      -- We need: ∫_{Z⁻¹(A) ∩ W⁻¹(B)} g = ∫_{Z⁻¹(A) ∩ W⁻¹(B)} f(Y)
      -- These are equal since intersection is commutative
      have : Z ⁻¹' A ∩ W ⁻¹' B = W ⁻¹' B ∩ Z ⁻¹' A := Set.inter_comm _ _
      rw [this]
      exact h_rect (W ⁻¹' B) hmW_preimage hμW A hA

    -- Apply π-λ induction using induction_on_inter
    -- We need to show: ∀ S, @MeasurableSet Ω mZW S → (μ S < ⊤ → ∫_S g = ∫_S f(Y))
    suffices ∀ S (hS : @MeasurableSet Ω mZW S), μ S < ⊤ → ∫ x in S, g x ∂μ = ∫ x in S, (f ∘ Y) x ∂μ by
      exact this T hT hμT

    intro S hS

    -- Define the Dynkin property: integral equality given finite measure
    let C : ∀ (S : Set Ω), @MeasurableSet Ω mZW S → Prop :=
      fun S _ => μ S < ⊤ → ∫ x in S, g x ∂μ = ∫ x in S, (f ∘ Y) x ∂μ

    -- Apply induction_on_inter with π-system 𝓡
    refine MeasurableSpace.induction_on_inter h𝓡_gen.symm h𝓡_pi ?empty ?basic ?compl ?iUnion S hS

    case empty =>
      -- C(∅): integral over empty set is always 0
      intro _
      simp only [setIntegral_empty]

    case basic =>
      -- C(R) for basic rectangles R ∈ 𝓡: use h_rect_all
      intro R hR_in_𝓡
      exact h_rect_all R hR_in_𝓡

    case compl =>
      -- C(S) → C(Sᶜ): use integral_add_compl
      intro S' hS'_meas hS'_C hμSc
      -- Apply IH to S'
      have hS'_eq : ∫ x in S', g x ∂μ = ∫ x in S', (f ∘ Y) x ∂μ := by
        apply hS'_C
        exact measure_lt_top μ S'
      -- Use integral_add_compl: ∫_S f + ∫_Sᶜ f = ∫ f
      -- Need: ∫_Sᶜ g = ∫_Sᶜ f(Y)
      -- Strategy: From ∫_S g = ∫_S f(Y) and ∫_S g + ∫_Sᶜ g = ∫ g, deduce ∫_Sᶜ g = ∫ g - ∫_S g

      -- Convert measurability from mZW to mΩ
      have hS'_meas_mΩ : @MeasurableSet Ω mΩ S' := hmZW_le _ hS'_meas

      have hg_add : ∫ x in S', g x ∂μ + ∫ x in S'ᶜ, g x ∂μ = ∫ x, g x ∂μ := by
        exact integral_add_compl hS'_meas_mΩ integrable_condExp
      have hf_add : ∫ x in S', (f ∘ Y) x ∂μ + ∫ x in S'ᶜ, (f ∘ Y) x ∂μ = ∫ x, (f ∘ Y) x ∂μ := by
        exact integral_add_compl hS'_meas_mΩ hf_int

      -- From hg_add, hf_add, and hS'_eq, conclude ∫_Sᶜ g = ∫_Sᶜ f(Y)
      -- We have: ∫_S' g + ∫_S'ᶜ g = ∫ g   (hg_add)
      --          ∫_S' f∘Y + ∫_S'ᶜ f∘Y = ∫ f∘Y   (hf_add)
      --          ∫_S' g = ∫_S' f∘Y   (hS'_eq)
      -- Can we derive ∫ g = ∫ f∘Y? This requires showing C(univ) via induction result

      -- Set.univ is mZW-measurable (in every σ-algebra)
      have huniv_meas : @MeasurableSet Ω mZW Set.univ := MeasurableSet.univ

      -- Apply h_rect_all to univ to get ∫ g = ∫ f∘Y
      have huniv_eq : ∫ x, g x ∂μ = ∫ x, (f ∘ Y) x ∂μ := by
        -- Key insight: univ = Z⁻¹(univ) ∩ W⁻¹(univ) ∈ 𝓡, so we can use h_rect_all!
        have huniv_in_R : Set.univ ∈ 𝓡 := by
          refine ⟨Set.univ, Set.univ, MeasurableSet.univ, MeasurableSet.univ, ?_⟩
          ext ω
          simp only [Set.mem_univ, Set.mem_inter_iff, Set.mem_preimage, true_and]
        have h := h_rect_all Set.univ huniv_in_R (measure_lt_top μ Set.univ)
        rwa [setIntegral_univ, setIntegral_univ] at h

      -- Now we can complete the calc
      calc ∫ x in S'ᶜ, g x ∂μ
          = ∫ x, g x ∂μ - ∫ x in S', g x ∂μ := by linarith [hg_add]
        _ = ∫ x, (f ∘ Y) x ∂μ - ∫ x in S', (f ∘ Y) x ∂μ := by rw [huniv_eq, hS'_eq]
        _ = ∫ x in S'ᶜ, (f ∘ Y) x ∂μ := by linarith [hf_add]

    case iUnion =>
      -- C(Sₙ) for all n → C(⋃ Sₙ) for pairwise disjoint sequence
      intro Sseq hSeq_disj hSeq_meas hSeq_C hμUnion

      -- Each Sₙ has finite measure (since sum is finite)
      have hSeq_finite : ∀ n, μ (Sseq n) < ⊤ := by
        intro n
        calc μ (Sseq n) ≤ μ (⋃ i, Sseq i) := measure_mono (Set.subset_iUnion Sseq n)
          _ < ⊤ := hμUnion

      -- Apply IH to each Sₙ
      have hSeq_eq : ∀ n, ∫ x in Sseq n, g x ∂μ = ∫ x in Sseq n, (f ∘ Y) x ∂μ := by
        intro n
        exact hSeq_C n (hSeq_finite n)

      -- Convert measurability from mZW to mΩ
      have hSeq_meas_mΩ : ∀ n, @MeasurableSet Ω mΩ (Sseq n) := by
        intro n
        exact hmZW_le _ (hSeq_meas n)

      -- Use integral additivity for disjoint unions
      calc ∫ x in ⋃ n, Sseq n, g x ∂μ
          = ∑' n, ∫ x in Sseq n, g x ∂μ := by
            apply integral_iUnion hSeq_meas_mΩ hSeq_disj
            exact integrable_condExp.integrableOn
        _ = ∑' n, ∫ x in Sseq n, (f ∘ Y) x ∂μ := by
            congr 1
            ext n
            exact hSeq_eq n
        _ = ∫ x in ⋃ n, Sseq n, (f ∘ Y) x ∂μ := by
            symm
            apply integral_iUnion hSeq_meas_mΩ hSeq_disj
            exact hf_int.integrableOn
    /-
    Now apply: MeasurableSpace.induction_on_inter (h_eq : mZW = generateFrom 𝓡) h𝓡_pi
    with the predicate C(S) := (μ S < ⊤ → ∫_S g = ∫_S f(Y))

    Need to provide four cases:

    1. **Empty:** C(∅)
       Need: μ ∅ < ⊤ → ∫_∅ g = ∫_∅ f(Y)
       Proof: ∫_∅ f = 0 for any f (integral over empty set)

    2. **Basic:** ∀ R ∈ 𝓡, C(R)
       This is exactly h_rect_all

    3. **Complement:** ∀ S, MeasurableSet S → C(S) → C(Sᶜ)
       Assume: μ S < ⊤ → ∫_S g = ∫_S f(Y)
       Show: μ Sᶜ < ⊤ → ∫_Sᶜ g = ∫_Sᶜ f(Y)
       Proof:
         ∫_Sᶜ g = ∫_Ω g - ∫_S g         (by measure_diff)
                = ∫_Ω f(Y) - ∫_S f(Y)    (by IH and μ Ω = 1)
                = ∫_Sᶜ f(Y)

    4. **Disjoint union:** ∀ (Sₙ : ℕ → Set Ω), Pairwise (Disjoint on Sₙ) →
         (∀ n, MeasurableSet (Sₙ n)) → (∀ n, C(Sₙ n)) → C(⋃ n, Sₙ n)
       Assume: ∀ n, μ (Sₙ n) < ⊤ → ∫_(Sₙ n) g = ∫_(Sₙ n) f(Y)
       Show: μ (⋃ n, Sₙ n) < ⊤ → ∫_(⋃ n, Sₙ n) g = ∫_(⋃ n, Sₙ n) f(Y)
       Proof:
         ∫_(⋃ n, Sₙ n) g = ∑ ∫_(Sₙ n) g         (by integral_iUnion_of_disjoint)
                         = ∑ ∫_(Sₙ n) f(Y)       (by IH on each n)
                         = ∫_(⋃ n, Sₙ n) f(Y)

    Technical challenge: induction_on_inter expects a specific signature.
    May need to massage the goal to match.
    -/
    /-
    **Dynkin System (π-λ) Argument using mathlib's induction_on_inter:**

    **Key mathlib lemma:** MeasurableSpace.induction_on_inter
    This provides induction over σ-algebras generated by π-systems with Dynkin properties.

    **Step 1: Define rectangles generating σ(Z,W)**
    Let R := {S ∩ Z⁻¹(B) : S ∈ σ(W), B ∈ B_Z}

    We need to show:
    a) R is a π-system (closed under intersections)
    b) generateFrom R = mZW
    c) For all T ∈ R with μ T < ⊤: ∫_T g = ∫_T f(Y) (by h_rect)

    **Step 2: Apply induction_on_inter**
    Use: MeasurableSpace.induction_on_inter (h_eq : mZW = generateFrom R) (h_inter : IsPiSystem R)

    Verify the Dynkin properties for C(T) := (μ T < ⊤ → ∫_T g = ∫_T f(Y)):

    1. **Empty set:** ∫_∅ g = 0 = ∫_∅ f(Y) ✓

    2. **Basic (rectangles):** For T ∈ R, this holds by h_rect ✓

    3. **Complement:** If C(T) holds and μ Tᶜ < ⊤, then:
       ∫_Tᶜ g = ∫_Ω g - ∫_T g = ∫_Ω f(Y) - ∫_T f(Y) = ∫_Tᶜ f(Y)
       (Uses: IsProbabilityMeasure so μ Ω = 1 < ⊤)

    4. **Disjoint union:** If C(Tₙ) for pairwise disjoint {Tₙ} and μ(⋃ Tₙ) < ⊤, then:
       ∫_{⋃ Tₙ} g = ∑ ∫_{Tₙ} g = ∑ ∫_{Tₙ} f(Y) = ∫_{⋃ Tₙ} f(Y)
       (Uses: lintegral_iUnion or tsum_integral)

    **Implementation:**
    - Use `refine induction_on_inter hmZW_eq_R h_piSystem ?empty ?basic ?compl ?union`
    - Each case is a standard integral manipulation
    - Main technical work: defining R and proving it generates mZW

    **Alternative:** If defining R is complex, could use direct Dynkin system construction
    with DynkinSystem.generate and generateFrom_eq.
    -/

  -- Step 3: Apply uniqueness
  have g_aesm_mZW : AEStronglyMeasurable[mZW] g μ := by
    -- g is mW-measurable, and mW ≤ mZW, so g is mZW-measurable
    have hg_mW : StronglyMeasurable[mW] g := stronglyMeasurable_condExp
    -- Use monotonicity: m ≤ m' → StronglyMeasurable[m] f → StronglyMeasurable[m'] f
    exact (hg_mW.mono hmW_le_mZW).aestronglyMeasurable

  -- Apply uniqueness to get μ[f∘Y|mZW] = g
  have result_mZW : μ[ f ∘ Y | mZW ] =ᵐ[μ] g := by
    -- Use ae_eq_condExp_of_forall_setIntegral_eq from mathlib
    -- Parameters: (hm : m ≤ m₀) (hf_int : Integrable f μ) (integrableOn) (h_matching) (aesm)
    -- Returns: g =ᵐ[μ] μ[f|m], so we need .symm for μ[f|m] =ᵐ[μ] g
    refine (ae_eq_condExp_of_forall_setIntegral_eq hmZW_le hf_int ?integrableOn h_all g_aesm_mZW).symm
    · -- Integrability of g on finite-measure mZW-sets
      intro T hT hμT
      exact integrable_condExp.integrableOn

  -- Use mZW_prod = mZW to rewrite LHS, then apply result
  have : μ[ f ∘ Y | mZW_prod ] =ᵐ[μ] μ[ f ∘ Y | mZW ] := by
    rw [hmZW_prod_eq]
  -- Chain: μ[f∘Y|mZW_prod] = μ[f∘Y|mZW] = g = μ[f∘Y|mW]
  calc μ[ f ∘ Y | mZW_prod ] =ᵐ[μ] μ[ f ∘ Y | mZW ] := this
    _ =ᵐ[μ] g := result_mZW
    _ = μ[ f ∘ Y | mW ] := hg_def


end Exchangeability.Probability

/-!
### Note on condExp_eq_of_setIntegral_eq

The lemma `condExp_eq_of_setIntegral_eq` that was previously in CondExpHelpers.lean
has been removed as it was unused. If needed in the future, it can be found in git history.

The main development uses mathlib's `ae_eq_condExp_of_forall_setIntegral_eq` directly instead.
-/
