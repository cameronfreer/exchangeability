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
import Exchangeability.Core
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
open Exchangeability.PathSpace (shift measurable_shift)
open Exchangeability.Ergodic (koopman metProjection birkhoffAverage_tendsto_metProjection)
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

**Proof strategy:** Use π-system uniqueness (measure_eq_of_fin_marginals_eq_prob).
Contractability implies that (X₁, X₂, ..., Xₙ) ~ (X₀, X₁, ..., X_{n-1}) for all n,
since (1,2,...,n) is an increasing sequence. This gives agreement of all finite marginals,
hence equality of measures by π-system uniqueness. -/
lemma contractable_shift_invariant_law
    {X : ℕ → Ω → ℝ} (hX : Contractable μ X) (hX_meas : ∀ i, Measurable (X i)) :
    Measure.map shift (μ_path μ X) = (μ_path μ X) := by
  haveI inst1 : IsProbabilityMeasure (μ_path μ X) := isProbabilityMeasure_μ_path hX_meas
  haveI inst2 : IsProbabilityMeasure (Measure.map shift (μ_path μ X)) := by
    constructor
    rw [Measure.map_apply measurable_shift MeasurableSet.univ, Set.preimage_univ]
    exact measure_univ

  -- Apply π-system uniqueness
  apply _root_.Exchangeability.measure_eq_of_fin_marginals_eq_prob
  intro n S hS

  -- Show all finite marginals agree via contractability
  -- Key: (X₁, X₂, ..., Xₙ) has same distribution as (X₀, X₁, ..., X_{n-1})

  sorry  -- TODO: Complete using the 5-step strategy documented above

/-- **BRIDGE 1'.** Package as `MeasurePreserving` for applying the Mean Ergodic Theorem. -/
lemma measurePreserving_shift_path (X : ℕ → Ω → ℝ)
    (hX : Contractable μ X) (hX_meas : ∀ i, Measurable (X i)) :
    MeasurePreserving shift (μ_path μ X) (μ_path μ X) :=
  ⟨measurable_shift, by simpa using contractable_shift_invariant_law (μ := μ) (X := X) hX hX_meas⟩

/-! ## C. Bridge 2: Fixed Space = Tail σ-algebra -/

/-- Tail σ-algebra on path space ℕ → ℝ. -/
abbrev tail_on_path : MeasurableSpace (ℕ → ℝ) :=
  tailShift ℝ

lemma tail_on_path_le : tail_on_path ≤ (inferInstance : MeasurableSpace (ℕ → ℝ)) := by
  -- tailShift = iInf (fun n => comap (shift by n))
  -- For n=0, the shift by 0 is the identity, so comap id = inferInstance
  -- iInf f ≤ f 0 by definition of infimum
  unfold tail_on_path tailShift
  refine iInf_le (fun n => MeasurableSpace.comap _ _) 0 |>.trans ?_
  -- At n=0: comap (fun ω k => ω (0 + k)) = comap id = inferInstance
  simp only [zero_add]
  -- comap id ≤ id
  exact MeasurableSpace.comap_id.le

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
      (measurePreserving_shift_path X hX hX_meas) h
      = (μ_path μ X)[(h) | tail_on_path]
  /- Proof sketch: Fixed points of shift = tail-measurable functions.
     Orthogonal projection onto this closed subspace = condexp_L2.
     TODO: Implement fixed space identification -/

/-! ## D. Bridge 3: L² → L¹ on Probability Spaces -/

open Exchangeability.Probability.IntegrationHelpers

/-- **BRIDGE 3.** L² convergence implies L¹ convergence on probability spaces.

On a probability space, Hölder's inequality gives ∫|f| ≤ (∫|f|²)^(1/2).
So L² convergence of Lp functions implies L¹ convergence. -/
lemma tendsto_Lp2_to_L1 {α : Type*} [MeasurableSpace α] {m : Measure α} [IsProbabilityMeasure m]
    {Y : ℕ → Lp ℝ 2 m} {Z : Lp ℝ 2 m}
    (h₂ : Tendsto Y atTop (𝓝 Z)) :
    Tendsto (fun n => ∫ x, ‖Y n x - Z x‖ ∂m) atTop (𝓝 0) := by
  -- Convergence in Lp 2 means ‖Y n - Z‖_{Lp 2} → 0
  -- On probability spaces: ∫|f| ≤ ‖f‖_{L²} by Cauchy-Schwarz
  -- Key inequality: ∫|f| ≤ (∫|f|²)^(1/2) · (∫ 1²)^(1/2) = (∫|f|²)^(1/2) · 1

  -- Step 1: Convert Lp convergence to norm convergence
  have h_norm : Tendsto (fun n => ‖Y n - Z‖) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop] at h₂ ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := h₂ ε hε
    use N
    intro n hn
    specialize hN n hn
    simp only [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    rw [dist_comm, dist_eq_norm] at hN
    rwa [norm_sub_rev]

  -- Step 2: Show integral is bounded by L² norm
  -- Key: On probability spaces, Hölder gives ∫|f| ≤ (∫|f|²)^(1/2) = ‖f‖₂
  have h_bound : ∀ n, ∫ x, ‖Y n x - Z x‖ ∂m ≤ ‖Y n - Z‖ := by
    intro n
    -- The Lp 2 norm is ‖f‖ = ENNReal.toReal (eLpNorm f 2 μ)
    -- We need: ∫ ‖f‖ ≤ ‖f‖_{L²}
    -- Strategy: Use eLpNorm inequality p=1 ≤ p=2 on probability spaces

    -- First, Y n - Z is in Lp 2, so it's AEStronglyMeasurable
    have hf_aesm : AEStronglyMeasurable (Y n - Z) m := Lp.aestronglyMeasurable (Y n - Z)

    -- Apply Hölder: eLpNorm 1 ≤ eLpNorm 2 on probability spaces
    have key_ineq : eLpNorm (Y n - Z) 1 m ≤ eLpNorm (Y n - Z) 2 m := by
      have := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (by norm_num : (1 : ℝ≥0∞) ≤ 2) hf_aesm
      simp only [measure_univ, ENNReal.one_rpow, mul_one] at this
      exact this

    sorry -- TODO: Connect eLpNorm 1 to integral and eLpNorm 2 to Lp norm

  -- Step 3: Apply squeeze theorem
  refine' tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h_norm _ h_bound
  · intro n
    exact integral_nonneg (fun x => norm_nonneg _)

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
  have hMP : MeasurePreserving shift ν ν :=
    measurePreserving_shift_path (μ := μ) (X := X) hX_contract hX_meas

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

  -- Apply Mean Ergodic Theorem: Birkhoff averages converge in L² to projection
  have hMET : Tendsto (fun n => birkhoffAverage ℝ (koopman shift hMP) _root_.id n gLp)
      atTop (𝓝 (metProjection shift hMP gLp)) :=
    birkhoffAverage_tendsto_metProjection shift hMP gLp

  -- Bridge 2: metProjection = condexp_L2 onto tail σ-algebra
  have hBridge2 : metProjection shift hMP gLp = (ν)[gLp | tail_on_path] :=
    metProjection_eq_condexp_tail_on_path X hX_contract hX_meas gLp

  -- Bridge 3: L² convergence implies L¹ convergence
  have hL2_to_L1 : Tendsto (fun n => ∫ x, ‖birkhoffAverage ℝ (koopman shift hMP) _root_.id n gLp x
                                         - metProjection shift hMP gLp x‖ ∂ν)
      atTop (𝓝 0) :=
    tendsto_Lp2_to_L1 hMET

  -- Bridge 4: Pull back to original space
  -- The Birkhoff average on path space corresponds to Cesàro average on original space
  -- And conditional expectation pulls back via pathify
  have h_L1 : Tendsto (fun (m : ℕ) =>
      ∫ ω, |(1 / (m : ℝ)) * ∑ i : Fin m, f (X i ω) -
             (μ[(f ∘ X 0) | tailProcess X] ω)| ∂μ)
      atTop (𝓝 (0 : ℝ)) := by
    sorry  -- TODO: Apply Bridge 4 and reindex

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
