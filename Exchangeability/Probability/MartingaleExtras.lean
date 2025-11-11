/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.MeasureTheory.MeasurableSpace.Prod
import Mathlib.MeasureTheory.Function.FactorsThrough

/-!
# Martingale Helper Lemmas (Fully Proved)

This file contains **fully-proved** helper lemmas related to martingales and conditional expectations.
These are extracted from exploratory work and may be useful for future developments.

**All lemmas here are complete** - no axioms, no sorries.

## Contents

1. **Reverse conditional expectation helpers**:
   - `revCE`: Definition of reverse martingale along decreasing filtration
   - `revCE_tower`: Tower property for reverse conditional expectations
   - `revCE_L1_bdd`: L¹ boundedness

2. **de la Vallée-Poussin infrastructure**:
   - `deLaValleePoussin_eventually_ge_id`: Extract threshold from superlinear growth

3. **Fatou-type lemmas**:
   - `lintegral_fatou_ofReal_norm`: Fatou's lemma for `ENNReal.ofReal ∘ ‖·‖`

**Note:** Incomplete conditional distribution lemmas have been moved to `MartingaleUnused.lean`.

## References

* Durrett, *Probability: Theory and Examples* (2019), Section 5.5
* Williams, *Probability with Martingales* (1991)
-/

noncomputable section
open scoped MeasureTheory ProbabilityTheory Topology
open MeasureTheory Filter Set Function

namespace Exchangeability.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## Reverse Conditional Expectation Helpers -/

/-- Reverse martingale along a decreasing chain: `X n := condExp μ (F n) f`. -/
def revCE (μ : Measure Ω) (F : ℕ → MeasurableSpace Ω) (f : Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  μ[f | F n]

/-- Tower property in the reverse direction: for `m ≥ n`, `E[X_n | F_m] = X_m`. -/
lemma revCE_tower
    [IsProbabilityMeasure μ]
    {F : ℕ → MeasurableSpace Ω} (hF : Antitone F)
    (h_le : ∀ n, F n ≤ (inferInstance : MeasurableSpace Ω))
    (f : Ω → ℝ) {n m : ℕ} (hmn : n ≤ m) :
    μ[revCE μ F f n | F m] =ᵐ[μ] revCE μ F f m := by
  simp only [revCE]
  exact condExp_condExp_of_le (hF hmn) (h_le n)

/-- L¹ boundedness of the reverse martingale. -/
lemma revCE_L1_bdd
    [IsProbabilityMeasure μ]
    {F : ℕ → MeasurableSpace Ω}
    (h_le : ∀ n, F n ≤ (inferInstance : MeasurableSpace Ω))
    (f : Ω → ℝ) (hf : Integrable f μ) :
    ∀ n, eLpNorm (revCE μ F f n) 1 μ ≤ eLpNorm f 1 μ := by
  intro n
  simp only [revCE]
  exact eLpNorm_one_condExp_le_eLpNorm f

/-! ## de la Vallée-Poussin Infrastructure -/

/-- From the de la Vallée-Poussin tail condition `Φ(t)/t → ∞`, extract a threshold `R > 0`
such that `t ≤ Φ t` for all `t ≥ R`.

This is used to control the small-values region when applying the de la Vallée-Poussin
criterion for uniform integrability. -/
lemma deLaValleePoussin_eventually_ge_id
    (Φ : ℝ → ℝ)
    (hΦ_tail : Tendsto (fun t : ℝ => Φ t / t) atTop atTop) :
    ∃ R > 0, ∀ ⦃t⦄, t ≥ R → t ≤ Φ t := by
  have h := (tendsto_atTop_atTop.1 hΦ_tail) 1
  rcases h with ⟨R, hR⟩
  refine ⟨max R 1, by positivity, ?_⟩
  intro t ht
  have ht' : t ≥ R := le_trans (le_max_left _ _) ht
  have hΦ_ge : Φ t / t ≥ 1 := hR t ht'
  have hpos : 0 < t := by linarith [le_max_right R 1]
  have : 1 ≤ Φ t / t := hΦ_ge
  calc t = t * 1 := by ring
       _ ≤ t * (Φ t / t) := by exact mul_le_mul_of_nonneg_left this (le_of_lt hpos)
       _ = Φ t := by field_simp

/-! ## Fatou-Type Lemmas -/

/-- Fatou's lemma on `ENNReal.ofReal ∘ ‖·‖` along an a.e. pointwise limit.

If `u n x → g x` a.e., then `∫⁻ ‖g‖ ≤ liminf (∫⁻ ‖u n‖)`. -/
lemma lintegral_fatou_ofReal_norm
  {α β : Type*} [MeasurableSpace α] {μ : Measure α}
  [MeasurableSpace β] [NormedAddCommGroup β] [BorelSpace β]
  {u : ℕ → α → β} {g : α → β}
  (hae : ∀ᵐ x ∂μ, Tendsto (fun n => u n x) atTop (nhds (g x)))
  (hu_meas : ∀ n, AEMeasurable (fun x => ENNReal.ofReal ‖u n x‖) μ)
  (hg_meas : AEMeasurable (fun x => ENNReal.ofReal ‖g x‖) μ) :
  ∫⁻ x, ENNReal.ofReal ‖g x‖ ∂μ
    ≤ liminf (fun n => ∫⁻ x, ENNReal.ofReal ‖u n x‖ ∂μ) atTop := by
  have hae_ofReal :
      ∀ᵐ x ∂μ,
        Tendsto (fun n => ENNReal.ofReal ‖u n x‖) atTop
                (nhds (ENNReal.ofReal ‖g x‖)) :=
    hae.mono (fun x hx =>
      ((ENNReal.continuous_ofReal.comp continuous_norm).tendsto _).comp hx)
  calc ∫⁻ x, ENNReal.ofReal ‖g x‖ ∂μ
      = ∫⁻ x, liminf (fun n => ENNReal.ofReal ‖u n x‖) atTop ∂μ :=
          lintegral_congr_ae (hae_ofReal.mono fun x hx => hx.liminf_eq.symm)
    _ ≤ liminf (fun n => ∫⁻ x, ENNReal.ofReal ‖u n x‖ ∂μ) atTop :=
          lintegral_liminf_le' hu_meas

end Exchangeability.Probability
