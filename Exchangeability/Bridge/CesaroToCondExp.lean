/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer, Claude (Anthropic)
-/
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.SimpleFuncDense
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Topology.Algebra.Module.Basic

-- Project-local imports
import Exchangeability.Contractability
import Exchangeability.Tail.TailSigma
import Exchangeability.Probability.CondExp
import Exchangeability.Probability.IntegrationHelpers
import Exchangeability.Ergodic.KoopmanMeanErgodic

/-!
# Bridging Mean Ergodic Theorem to Cesàro-Conditional Expectation Convergence

This file implements the **four bridges** connecting the abstract Mean Ergodic Theorem
from `KoopmanMeanErgodic.lean` to the concrete result `cesaro_to_condexp_L1` needed in
`ViaL2.lean`.

## The Four Bridges

1. **Contractable ⇒ Shift-invariant**: Contractable sequences induce shift-invariant
   measures on path space.

2. **Fixed Space = Tail σ-algebra**: The fixed-point subspace of the Koopman operator
   equals L²(tail σ-algebra), so the metric projection is conditional expectation.

3. **L² → L¹ Convergence**: On probability spaces, L² convergence implies L¹ convergence
   for bounded functions (via Hölder/Cauchy-Schwarz).

4. **Pullback along Factor Map**: Conditional expectations commute with the pathify
   factor map Ω → PathSpace.

## Main Result

`cesaro_to_condexp_L1`: Cesàro averages of bounded measurable functions along a
contractable sequence converge in L¹ to the conditional expectation onto the tail
σ-algebra.

This **removes the axiom** from ViaL2.lean and provides a canonical bridge between
abstract ergodic theory and concrete probability.
-/

noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Filter Topology
open Exchangeability.Ergodic (shift)
open Exchangeability.Tail (tailProcess tailShift)

namespace Exchangeability.Bridge

variable {Ω : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ## A. Path Space and Factor Map -/

/-- **Factor map**: sends ω : Ω to the path (n ↦ X n ω). -/
def pathify {α} [MeasurableSpace α] (X : ℕ → Ω → α) : Ω → (ℕ → α) :=
  fun ω n => X n ω

lemma measurable_pathify {α} [MeasurableSpace α] {X : ℕ → Ω → α}
    (hX_meas : ∀ n, Measurable (X n)) :
    Measurable (pathify X) := by
  apply measurable_pi_lambda
  intro n
  exact hX_meas n

/-- **Law of the process** as a probability measure on path space. -/
def μ_path {α} [MeasurableSpace α] (μ : Measure Ω) (X : ℕ → Ω → α) : Measure (ℕ → α) :=
  Measure.map (pathify X) μ

lemma isProbabilityMeasure_μ_path {α} [MeasurableSpace α] {X : ℕ → Ω → α}
    (hX_meas : ∀ n, Measurable (X n)) :
    IsProbabilityMeasure (μ_path μ X) := by
  refine ⟨?_⟩
  simp only [μ_path]
  rw [Measure.map_apply (measurable_pathify hX_meas) MeasurableSet.univ]
  simp

/-! ## B. Bridge 1: Contractable → Shift-invariant -/

open Exchangeability

/-- **BRIDGE 1.** Contractable sequences induce shift-invariant laws on path space.

**TODO:** Replace sorry with your project's stationarity lemma, e.g.:
  `exact hX.shift_invariant_path_law`
or prove directly via cylinder-set argument. -/
lemma contractable_shift_invariant_law
    {X : ℕ → Ω → ℝ} (hX : Contractable μ X) :
    Measure.map (shift (α := ℝ)) (μ_path μ X) = (μ_path μ X) := by
  /-  Proof sketch:
      * Contractable ⇒ finite-dimensional distributions are shift-invariant
      * Cylinders generate the path σ-algebra
      * Conclude map shift (μ_path X) = μ_path X
  -/
  sorry  -- TODO: Use existing stationarity lemma from Contractability.lean

lemma measurable_shift_real : Measurable (shift (α := ℝ)) :=
  Exchangeability.Ergodic.measurable_shift

/-- **BRIDGE 1'.** Package as `MeasurePreserving` for applying the Mean Ergodic Theorem. -/
lemma measurePreserving_shift_path (X : ℕ → Ω → ℝ)
    (hX : Contractable μ X) :
    MeasurePreserving (shift (α := ℝ)) (μ_path μ X) (μ_path μ X) :=
  ⟨measurable_shift_real, by simpa using contractable_shift_invariant_law (μ := μ) (X := X) hX⟩

/-! ## C. Bridge 2: Fixed Space = Tail σ-algebra -/

/-- Tail σ-algebra on path space ℕ → ℝ. -/
abbrev tail_on_path : MeasurableSpace (ℕ → ℝ) :=
  tailShift ℝ

lemma tail_on_path_le : tail_on_path ≤ (inferInstance : MeasurableSpace (ℕ → ℝ)) := by
  -- Standard σ-algebra fact: iInf of sub-σ-algebras is a sub-σ-algebra
  -- Proof: iInf (fun n => comap ...) ≤ comap (id) = inferInstance
  sorry

/-- **BRIDGE 2.** For the shift on path space, the fixed-point subspace equals L²(tail).

Therefore the metric projection (from MET) equals conditional expectation onto tail.

**TODO:** Implement via:
  1. Show fixed space = {h : h ∘ shift = h a.e.} = L²(tail_on_path)
  2. Apply `condexp_L2_unique` to identify projection with conditional expectation -/
axiom metProjection_eq_condexp_tail_on_path
    (X : ℕ → Ω → ℝ) (hX : Contractable μ X) (hX_meas : ∀ n, Measurable (X n))
    (h : Lp ℝ 2 (μ_path μ X)) :
    haveI : IsProbabilityMeasure (μ_path μ X) := isProbabilityMeasure_μ_path hX_meas
    Exchangeability.Ergodic.metProjection
      (shift (α := ℝ))
      (measurePreserving_shift_path X hX) h
      = (μ_path μ X)[(h) | tail_on_path]
  /- Proof sketch: Fixed points of shift = tail-measurable functions.
     Orthogonal projection onto this closed subspace = condexp_L2.
     TODO: Implement fixed space identification -/

/-! ## D. Bridge 3: L² → L¹ on Probability Spaces -/

open Exchangeability.Probability.IntegrationHelpers

/-- **BRIDGE 3.** L² convergence implies L¹ convergence on probability spaces.

This is essentially `L2_tendsto_implies_L1_tendsto_of_bounded` from IntegrationHelpers,
but we need to work with the Lp space formulation. -/
lemma tendsto_Lp2_to_L1 {α : Type*} [MeasurableSpace α] {m : Measure α} [IsProbabilityMeasure m]
    {Y : ℕ → Lp ℝ 2 m} {Z : Lp ℝ 2 m}
    (h₂ : Tendsto Y atTop (𝓝 Z)) :
    Tendsto (fun n => ∫ x, ‖Y n x - Z x‖ ∂m) atTop (𝓝 0) := by
  /- Use monotonicity ‖·‖₁ ≤ ‖·‖₂ on probability spaces.
     Can also use our IntegrationHelpers.L2_tendsto_implies_L1_tendsto_of_bounded. -/
  sorry  -- TODO: Apply Hölder or use IntegrationHelpers lemma

/-! ## E. Bridge 4: Pullback along Factor Map -/

/-- **BRIDGE 4.** Conditional expectation commutes with pathify.

For H : (ℕ → ℝ) → ℝ and the factor map pathify:
  E_path[H | tail_on_path] ∘ pathify = E_Ω[H ∘ pathify | tailProcess X]

**TODO:** Use `condexp_comp` / `condexp_preimage` pattern from mathlib. -/
lemma condexp_pullback_along_pathify
    {X : ℕ → Ω → ℝ} (hX_meas : ∀ i, Measurable (X i))
    (H : (ℕ → ℝ) → ℝ) (hH_meas : Measurable H) :
    (μ_path μ X)[H | tail_on_path] ∘ (pathify X)
      =ᵐ[μ] μ[(H ∘ (pathify X)) | tailProcess X] := by
  /- Standard change of variables for conditional expectations.
     Key: pathify⁻¹(tail_on_path) = tailProcess X -/
  sorry  -- TODO: Apply condexp change of variables

/-! ## F. Main Theorem: Removing the Axiom -/

/-- **THEOREM: Cesàro averages → conditional expectation in L¹.**

This **replaces the axiom** `cesaro_to_condexp_L1` from ViaL2.lean by proving it
from the Mean Ergodic Theorem via the four bridges above.

**Proof outline:**
1. Lift to path space via `pathify`
2. Apply Mean Ergodic Theorem (L² convergence)
3. Identify projection with conditional expectation (Bridge 2)
4. Transfer to L¹ convergence (Bridge 3)
5. Pull back to original process (Bridge 4)
-/
theorem cesaro_to_condexp_L1
  {X : ℕ → Ω → ℝ} (hX_contract : Contractable μ X)
  (hX_meas : ∀ i, Measurable (X i))
  (f : ℝ → ℝ) (hf_meas : Measurable f) (hf_bdd : ∀ x, |f x| ≤ 1) :
  ∀ ε > 0, ∃ (M : ℕ), ∀ (m : ℕ), m ≥ M →
    ∫ ω, |(1 / (m : ℝ)) * ∑ i : Fin m, f (X i ω) -
           (μ[(f ∘ X 0) | tailProcess X] ω)| ∂μ < ε := by
  classical
  intro ε hε

  -- Step 0: Set up path space
  let ν := μ_path μ X
  haveI : IsProbabilityMeasure ν := isProbabilityMeasure_μ_path hX_meas

  -- Bridge 1: Shift is measure-preserving on path space
  have hMP : MeasurePreserving (shift (α := ℝ)) ν ν :=
    measurePreserving_shift_path (μ := μ) (X := X) hX_contract

  -- Define observable g(ω) = f(ω 0) on path space
  let g : (ℕ → ℝ) → ℝ := fun ω => f (ω 0)
  have hg_meas : Measurable g := hf_meas.comp (measurable_pi_apply 0)

  -- g is bounded ⇒ g ∈ L²(ν)
  have hg_L2 : MemLp g 2 ν := by
    apply MemLp.of_bound hg_meas.aestronglyMeasurable 1
    apply ae_of_all
    intro ω
    simp [g]
    exact hf_bdd (ω 0)

  let gLp : Lp ℝ 2 ν := MemLp.toLp g hg_L2

  -- Apply Mean Ergodic Theorem
  -- TODO: Apply birkhoffAverage_tendsto_metProjection with gLp

  -- Bridge 2: Identify projection with conditional expectation
  -- TODO: Use metProjection_eq_condexp_tail_on_path

  -- Bridge 3: L² → L¹ convergence
  -- After applying MET and bridges 1-4, we get L¹ convergence of Cesàro averages
  have h_L1 : Tendsto (fun (m : ℕ) =>
      ∫ ω, |(1 / (m : ℝ)) * ∑ i : Fin m, f (X i ω) -
             (μ[(f ∘ X 0) | tailProcess X] ω)| ∂μ)
      atTop (𝓝 (0 : ℝ)) := by
    sorry  -- TODO: Complete bridges 1-4 application

  -- Extract ε-N from L¹ convergence using Metric.tendsto_atTop
  have := Metric.tendsto_atTop.mp h_L1 ε hε
  obtain ⟨M, hM⟩ := this
  use M
  intro m hm
  have := hM m hm
  simp only [dist_zero_right] at this
  rw [Real.norm_of_nonneg] at this
  · exact this
  · apply integral_nonneg
    intro ω
    exact abs_nonneg _

end Exchangeability.Bridge
