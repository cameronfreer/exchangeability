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

**Proof strategy:**
1. For any bounded h measurable w.r.t. σ(Z), we have
   `∫ 1_{Y ∈ B} · h ∘ Z dμ = ∫ 1_{Y' ∈ B} · h ∘ Z dμ`
   by the equality of joint push-forward measures on rectangles B × E.

2. This equality holds for all σ(Z)-measurable test functions h.

3. By uniqueness of conditional expectation (`ae_eq_condExp_of_forall_setIntegral_eq`),
   `E[1_{Y ∈ B} | σ(Z)] = E[1_{Y' ∈ B} | σ(Z)]  a.e.`
-/
theorem condexp_indicator_eq_of_pair_law_eq
    {μ : Measure Ω} [IsFiniteMeasure μ]
    (Y Y' : Ω → α) (Z : Ω → β)
    (hY : Measurable Y) (hY' : Measurable Y') (hZ : Measurable Z)
    (hpair : Measure.map (fun ω => (Y ω, Z ω)) μ
           = Measure.map (fun ω => (Y' ω, Z ω)) μ)
    {B : Set α} (hB : MeasurableSet B) :
    μ[(Set.indicator B (fun _ => (1:ℝ))) ∘ Y | MeasurableSpace.comap Z mβ]
      =ᵐ[μ]
    μ[(Set.indicator B (fun _ => (1:ℝ))) ∘ Y' | MeasurableSpace.comap Z mβ] := by
  classical
  set f := (Set.indicator B (fun _ => (1:ℝ))) ∘ Y
  set f' := (Set.indicator B (fun _ => (1:ℝ))) ∘ Y'
  set mZ := MeasurableSpace.comap Z mβ

  have hmZ_le : mZ ≤ mΩ := by
    intro s hs
    rcases hs with ⟨E, hE, rfl⟩
    exact hZ hE

  have hf_int : Integrable f μ := (integrable_const (1:ℝ)).indicator (hY hB)
  have hf'_int : Integrable f' μ := (integrable_const (1:ℝ)).indicator (hY' hB)

  refine (MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq
    (hm := hmZ_le)
    (f := f)
    (g := μ[f' | mZ])
    (hf := hf_int)
    (hg_int_finite := ?hg_int_finite)
    (hg_eq := ?hg_eq)
    (hgm := MeasureTheory.stronglyMeasurable_condExp.aestronglyMeasurable)).symm

  case hg_int_finite =>
    intro s _ _
    exact integrable_condExp.integrableOn

  case hg_eq =>
    intro A hA _
    obtain ⟨E, hE, rfl⟩ := hA

    have h_meas_eq : μ (Y ⁻¹' B ∩ Z ⁻¹' E) = μ (Y' ⁻¹' B ∩ Z ⁻¹' E) := by
      have := congr_arg (fun ν => ν (B ×ˢ E)) hpair
      simp only [Measure.map_apply (hY.prodMk hZ) (hB.prod hE),
                 Measure.map_apply (hY'.prodMk hZ) (hB.prod hE)] at this
      simp only [Set.mk_preimage_prod] at this
      exact this

    have h_lhs : ∫ ω in Z ⁻¹' E, f ω ∂μ = (μ (Y ⁻¹' B ∩ Z ⁻¹' E)).toReal := by
      have hf_eq : f = (Y ⁻¹' B).indicator (fun _ => (1:ℝ)) := by
        ext ω
        simp only [f, Function.comp_apply, Set.indicator, Set.mem_preimage]
      simp_rw [hf_eq, integral_indicator (hY hB)]
      simp only [integral_const]
      simp_rw [Measure.restrict_restrict (hY hB)]
      simp only [smul_eq_mul, mul_one]
      simp [Measure.real, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]

    have h_rhs_ce :
        ∫ ω in Z ⁻¹' E, μ[f' | mZ] ω ∂μ = ∫ ω in Z ⁻¹' E, f' ω ∂μ :=
      setIntegral_condExp hmZ_le hf'_int ⟨E, hE, rfl⟩

    have h_rhs : ∫ ω in Z ⁻¹' E, f' ω ∂μ = (μ (Y' ⁻¹' B ∩ Z ⁻¹' E)).toReal := by
      have hf'_eq : f' = (Y' ⁻¹' B).indicator (fun _ => (1:ℝ)) := by
        ext ω
        simp only [f', Function.comp_apply, Set.indicator, Set.mem_preimage]
      simp_rw [hf'_eq, integral_indicator (hY' hB)]
      simp only [integral_const]
      simp_rw [Measure.restrict_restrict (hY' hB)]
      simp only [smul_eq_mul, mul_one]
      simp [Measure.real, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]

    simp_rw [h_lhs, h_rhs_ce, h_rhs, h_meas_eq]

end ProbabilityTheory
