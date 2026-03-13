/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

/-!
# Conditional Expectation Equality from Distributional Equality

This file provides the key bridge lemma connecting distributional equality
to conditional expectation equality.

## Main Results

* `condexp_indicator_eq_of_pair_law_eq`: If `(Y, Z)` and `(Y', Z)` have the
  same joint distribution, then for any measurable set B:
  ```
  E[1_{Y ∈ B} | σ(Z)] = E[1_{Y' ∈ B} | σ(Z)]  a.e.
  ```

## Mathematical Context

This is a key bridge lemma for exchangeability proofs. The strategy is:
1. For any bounded h measurable w.r.t. σ(Z), the equality of joint distributions
   implies `∫ 1_{Y ∈ B} · h ∘ Z dμ = ∫ 1_{Y' ∈ B} · h ∘ Z dμ`
2. This equality holds for all σ(Z)-measurable test functions h
3. By uniqueness of conditional expectation, the conditional expectations agree

In the de Finetti theorem context, this is used with Y = X_m, Y' = X_k,
Z = shiftRV X (m+1), where the equality of joint distributions comes from
contractability.

## Suggested Mathlib Location

`Mathlib.Probability.ConditionalExpectation.Distributional` or
`Mathlib.MeasureTheory.Function.ConditionalExpectation.Distributional`

## References

* Kallenberg (2005), *Probabilistic Symmetries and Invariance Principles*, §1
* Williams (1991), *Probability with Martingales*, §9.7
-/

open MeasureTheory Filter Set Function
open scoped MeasureTheory ProbabilityTheory

namespace ProbabilityTheory

variable {Ω α β : Type*} [mΩ : MeasurableSpace Ω]
    [MeasurableSpace α] [mβ : MeasurableSpace β]

/-- **Conditional expectation bridge lemma.**

If `(Y, Z)` and `(Y', Z)` have the same law, then for every measurable `B`,
```
E[1_{Y ∈ B} | σ(Z)] = E[1_{Y' ∈ B} | σ(Z)]  a.e.
```
-/
theorem condexp_indicator_eq_of_pair_law_eq
    {μ : Measure Ω} [IsFiniteMeasure μ]
    (Y Y' : Ω → α) (Z : Ω → β)
    (hY : Measurable Y) (hY' : Measurable Y') (hZ : Measurable Z)
    (hpair : Measure.map (fun ω => (Y ω, Z ω)) μ
           = Measure.map (fun ω => (Y' ω, Z ω)) μ)
    {B : Set α} (hB : MeasurableSet B) :
    μ[(indicator B (fun _ => (1:ℝ))) ∘ Y | MeasurableSpace.comap Z mβ]
      =ᵐ[μ]
    μ[(indicator B (fun _ => (1:ℝ))) ∘ Y' | MeasurableSpace.comap Z mβ] := by
  classical
  -- Rewrite indicator compositions as preimage indicators via indicator_comp_right
  have hf_eq : (indicator B fun _ => (1:ℝ)) ∘ Y = (Y ⁻¹' B).indicator fun _ => (1:ℝ) :=
    funext fun _ => (indicator_comp_right Y).symm
  have hf'_eq : (indicator B fun _ => (1:ℝ)) ∘ Y' = (Y' ⁻¹' B).indicator fun _ => (1:ℝ) :=
    funext fun _ => (indicator_comp_right Y').symm
  simp_rw [hf_eq, hf'_eq]
  set mZ := MeasurableSpace.comap Z mβ
  have hf_int : Integrable ((Y ⁻¹' B).indicator fun _ => (1:ℝ)) μ :=
    (integrable_const 1).indicator (hY hB)
  have hf'_int : Integrable ((Y' ⁻¹' B).indicator fun _ => (1:ℝ)) μ :=
    (integrable_const 1).indicator (hY' hB)
  refine (ae_eq_condExp_of_forall_setIntegral_eq hZ.comap_le hf_int
    (fun _ _ _ => integrable_condExp.integrableOn) ?_
    stronglyMeasurable_condExp.aestronglyMeasurable).symm
  intro A hA _
  obtain ⟨E, hE, rfl⟩ := hA
  -- Key measure equality from distributional assumption
  have h_meas_eq : μ (Y ⁻¹' B ∩ Z ⁻¹' E) = μ (Y' ⁻¹' B ∩ Z ⁻¹' E) := by
    have := congr_arg (· (B ×ˢ E)) hpair
    simp only [Measure.map_apply (hY.prodMk hZ) (hB.prod hE),
               Measure.map_apply (hY'.prodMk hZ) (hB.prod hE), mk_preimage_prod] at this
    exact this
  -- LHS via setIntegral_indicator + setIntegral_const
  have h_lhs : ∫ ω in Z ⁻¹' E, (Y ⁻¹' B).indicator (fun _ => (1:ℝ)) ω ∂μ =
      μ.real (Y ⁻¹' B ∩ Z ⁻¹' E) := by
    rw [setIntegral_indicator (hY hB), setIntegral_const, smul_eq_mul, mul_one, inter_comm]
  -- RHS via CE property + setIntegral_indicator + setIntegral_const
  have h_rhs_ce :
      ∫ ω in Z ⁻¹' E, μ[(Y' ⁻¹' B).indicator (fun _ => (1:ℝ)) | mZ] ω ∂μ =
        ∫ ω in Z ⁻¹' E, (Y' ⁻¹' B).indicator (fun _ => (1:ℝ)) ω ∂μ :=
    setIntegral_condExp hZ.comap_le hf'_int ⟨E, hE, rfl⟩
  have h_rhs : ∫ ω in Z ⁻¹' E, (Y' ⁻¹' B).indicator (fun _ => (1:ℝ)) ω ∂μ =
      μ.real (Y' ⁻¹' B ∩ Z ⁻¹' E) := by
    rw [setIntegral_indicator (hY' hB), setIntegral_const, smul_eq_mul, mul_one, inter_comm]
  rw [h_rhs_ce, h_rhs, h_lhs, Measure.real, Measure.real, h_meas_eq]

end ProbabilityTheory
