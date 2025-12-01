/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer, Claude (Anthropic)
-/
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Cesàro Convergence Helper Lemmas

Utility lemmas for proving L² convergence of Cesàro (block) averages to conditional
expectations. These helpers reduce friction in the main convergence proofs.

## Main Results

* `cesaroCoeff`: Coefficients for block average weighted sums
* `cesaroCoeff_sup_le`: Bound on supremum of coefficient differences
* `tendsto_eLpNorm_sub_of_tendsto_in_Lp`: Convert Lp metric convergence to eLpNorm form
* `setIntegral_le_eLpNorm_mul_measure`: Cauchy-Schwarz on set integrals

These lemmas support the proof that block averages of exchangeable sequences converge
to conditional expectations (Kallenberg Lemma 1.3 / de Finetti via L²).
-/

noncomputable section

open scoped BigOperators
open MeasureTheory Filter Topology

namespace Exchangeability.Probability.CesaroHelpers

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-! ### Cesàro Coefficients -/

/-- **Cesàro weights for block averages.**

The coefficient for index i in a block average starting at N with length n:
- 0 if i < N (before block)
- 1/n if N ≤ i < N+n (in block)
- 0 if i ≥ N+n (after block)

Used to express block average differences as weighted sums. -/
def cesaroCoeff (N n i : ℕ) : ℝ :=
  if i < N then 0 else if i < N + n then (1 : ℝ) / n else 0

lemma cesaroCoeff_of_lt_start {N n i : ℕ} (h : i < N) :
    cesaroCoeff N n i = 0 := by
  simp only [cesaroCoeff, h, ↓reduceIte]

lemma cesaroCoeff_of_in_block {N n i : ℕ} (h1 : N ≤ i) (h2 : i < N + n) :
    cesaroCoeff N n i = (1 : ℝ) / n := by
  simp only [cesaroCoeff]
  split_ifs with h3 _
  · exact absurd h1 (not_le_of_gt h3)
  · rfl

lemma cesaroCoeff_of_ge_end {N n i : ℕ} (h : N + n ≤ i) :
    cesaroCoeff N n i = 0 := by
  simp only [cesaroCoeff]
  split_ifs with h1 h2
  · rfl
  · exact absurd h (not_le_of_gt h2)
  · rfl

/-- **Supremum bound on Cesàro coefficient differences.**

For block averages starting at 0 with lengths n and n', the supremum of
coefficient differences is bounded by max(1/n, 1/n').

This is the key estimate for applying Kallenberg's L² bound to show Cauchy property. -/
lemma cesaroCoeff_sup_le (n n' : ℕ) (hn : n ≠ 0) (hn' : n' ≠ 0) :
    ⨆ i : ℕ, |cesaroCoeff 0 n i - cesaroCoeff 0 n' i| ≤ max ((1 : ℝ) / n) (1 / n') := by
  -- TODO: Fix Nat vs Real division issues
  sorry

/-! ### Lp Convergence Utilities -/

/-- **Convert Lp metric convergence to eLpNorm form.**

If a sequence in Lp converges in the metric topology, then the eLpNorm
of differences from the limit tends to 0.

This bridges the gap between abstract Lp convergence and concrete eLpNorm bounds. -/
lemma tendsto_eLpNorm_sub_of_tendsto_in_Lp
    {μ : Measure Ω} [IsProbabilityMeasure μ] {p : ENNReal}
    [Fact (1 ≤ p)]
    {u : ℕ → Lp ℝ p μ} {v : Lp ℝ p μ}
    (hp_top : p ≠ ⊤)
    (h : Tendsto u atTop (𝓝 v)) :
    Tendsto (fun n => eLpNorm (u n - v) p μ) atTop (𝓝 0) := by
  -- TODO: Fill this sorry
  sorry

/-- **Cauchy-Schwarz on set integrals (probability measure).**

For a set A and function g ∈ L²(μ), the absolute value of ∫_A g is bounded
by the L² norm of g times √(μ A).

On probability spaces with μ A ≤ 1, this simplifies to |∫_A g| ≤ ‖g‖₂. -/
lemma setIntegral_le_eLpNorm_mul_measure
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (A : Set Ω) (hA : MeasurableSet A) {g : Ω → ℝ}
    (hg : MemLp g 2 μ) :
    |∫ x in A, g x ∂μ| ≤ (eLpNorm g 2 μ).toReal * (μ A).toReal ^ (1/2 : ℝ) := by
  -- PROOF STRATEGY (Cauchy-Schwarz via inner product):
  --
  -- Step 1: Lift g to Lp element using MemLp.toLp
  --   g_lp : Lp ℝ 2 μ := hg.toLp g
  --
  -- Step 2: Express set integral as inner product (L2.inner_indicatorConstLp_one)
  --   ∫ x in A, g x ∂μ = ⟪indicatorConstLp 2 hA hμA 1, g_lp⟫
  --   where hμA : μ A ≠ ∞ (from IsProbabilityMeasure)
  --
  -- Step 3: Apply Cauchy-Schwarz (norm_inner_le_norm)
  --   |⟪indicator, g_lp⟫| ≤ ‖indicator‖ * ‖g_lp‖
  --
  -- Step 4: Compute indicator norm (norm_indicatorConstLp)
  --   ‖indicatorConstLp 2 hA hμA 1‖ = ‖1‖ * (μ A).toReal^(1/2) = (μ A).toReal^(1/2)
  --
  -- KEY MATHLIB LEMMAS:
  -- - MeasureTheory.L2.inner_indicatorConstLp_one: ⟪indicator_s 1, f⟫ = ∫_s f
  -- - norm_inner_le_norm: |⟪x, y⟫| ≤ ‖x‖ * ‖y‖ (Cauchy-Schwarz)
  -- - norm_indicatorConstLp: ‖indicatorConstLp p hs hμs c‖ = ‖c‖ * μ.real s^(1/p.toReal)
  -- - MemLp.toLp_coeFn: coercion of toLp equals original function a.e.

  -- μ A ≠ ⊤ since μ is a probability measure
  have hμA : μ A ≠ ⊤ := (measure_lt_top μ A).ne

  -- Lift g to Lp element
  let g_lp : Lp ℝ 2 μ := hg.toLp g

  -- The set integral of g equals the set integral of g_lp
  have h_integral_eq : ∫ x in A, g x ∂μ = ∫ x in A, g_lp x ∂μ := by
    apply setIntegral_congr_ae hA
    filter_upwards [hg.coeFn_toLp] with x hx _
    exact hx.symm

  -- Express set integral as inner product: ⟨indicatorConstLp 1, g_lp⟩ = ∫_A g_lp
  have h_inner := L2.inner_indicatorConstLp_one hA hμA g_lp

  -- Apply Cauchy-Schwarz: ‖⟪x,y⟫‖ ≤ ‖x‖ * ‖y‖
  have h_CS : ‖inner ℝ (indicatorConstLp 2 hA hμA (1 : ℝ)) g_lp‖ ≤
      ‖indicatorConstLp 2 hA hμA (1 : ℝ)‖ * ‖g_lp‖ :=
    norm_inner_le_norm (indicatorConstLp 2 hA hμA (1 : ℝ)) g_lp

  -- For reals, ‖r‖ = |r|
  rw [Real.norm_eq_abs] at h_CS

  -- Compute indicator norm: ‖indicatorConstLp 2 hA hμA 1‖ = (μ A).toReal^(1/2)
  have h_indicator_norm : ‖indicatorConstLp 2 hA hμA (1 : ℝ)‖ = (μ A).toReal ^ (1/2 : ℝ) := by
    have hp0 : (2 : ENNReal) ≠ 0 := by norm_num
    have hptop : (2 : ENNReal) ≠ ⊤ := by norm_num
    rw [norm_indicatorConstLp hp0 hptop, norm_one, one_mul, Measure.real, ENNReal.toReal_ofNat]

  -- g_lp norm equals eLpNorm g: ‖hg.toLp g‖ = (eLpNorm g 2 μ).toReal
  have h_g_norm : ‖g_lp‖ = (eLpNorm g 2 μ).toReal := Lp.norm_toLp g hg

  -- Chain the inequalities
  calc |∫ x in A, g x ∂μ|
      = |∫ x in A, (g_lp : Ω → ℝ) x ∂μ| := by rw [h_integral_eq]
    _ = |inner ℝ (indicatorConstLp 2 hA hμA (1 : ℝ)) g_lp| := by rw [h_inner]
    _ ≤ ‖indicatorConstLp 2 hA hμA (1 : ℝ)‖ * ‖g_lp‖ := h_CS
    _ = (μ A).toReal ^ (1/2 : ℝ) * ‖g_lp‖ := by rw [h_indicator_norm]
    _ = (μ A).toReal ^ (1/2 : ℝ) * (eLpNorm g 2 μ).toReal := by rw [h_g_norm]
    _ = (eLpNorm g 2 μ).toReal * (μ A).toReal ^ (1/2 : ℝ) := mul_comm _ _

/-- **Simplified set integral bound for probability measures.**

On a probability space, |∫_A g| ≤ ‖g‖₂ since μ A ≤ 1. -/
lemma setIntegral_le_eLpNorm
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (A : Set Ω) (hA : MeasurableSet A) {g : Ω → ℝ}
    (hg : MemLp g 2 μ) :
    |∫ x in A, g x ∂μ| ≤ (eLpNorm g 2 μ).toReal := by
  have h_base := setIntegral_le_eLpNorm_mul_measure A hA hg
  have h_sqrt_le : (μ A).toReal ^ (1/2 : ℝ) ≤ 1 := by
    have h_le : μ A ≤ 1 := prob_le_one
    have h_toReal_le : (μ A).toReal ≤ 1 := by
      have := ENNReal.toReal_mono ENNReal.one_ne_top h_le
      simp only [ENNReal.toReal_one] at this
      exact this
    exact Real.rpow_le_one ENNReal.toReal_nonneg h_toReal_le (by norm_num : (0 : ℝ) ≤ 1/2)
  have h_step2 : (eLpNorm g 2 μ).toReal * (μ A).toReal ^ (1/2 : ℝ) ≤ (eLpNorm g 2 μ).toReal * 1 :=
    mul_le_mul_of_nonneg_left h_sqrt_le ENNReal.toReal_nonneg
  simp only [mul_one] at h_step2
  exact le_trans h_base h_step2

end Exchangeability.Probability.CesaroHelpers
