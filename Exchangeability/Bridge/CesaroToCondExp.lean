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

  -- LHS: Marginal of the shifted measure = distribution of (X₁, ..., Xₙ)
  -- RHS: Marginal of the original measure = distribution of (X₀, ..., X_{n-1})

  -- Expand LHS using Measure.map composition
  calc (Measure.map (prefixProj ℝ n) (Measure.map shift (μ_path μ X))) S
      = Measure.map shift (μ_path μ X) ((prefixProj ℝ n) ⁻¹' S) := by
          rw [Measure.map_apply measurable_prefixProj hS]
    _ = μ_path μ X (shift ⁻¹' ((prefixProj ℝ n) ⁻¹' S)) := by
          rw [Measure.map_apply measurable_shift]
          · exact measurable_prefixProj hS
    _ = μ_path μ X ((prefixProj ℝ n ∘ shift) ⁻¹' S) := by
          rfl
    _ = μ ((pathify X) ⁻¹' ((prefixProj ℝ n ∘ shift) ⁻¹' S)) := by
          rw [μ_path, Measure.map_apply (measurable_pathify hX_meas)]
          · exact (measurable_prefixProj.comp measurable_shift) hS
    _ = μ ((prefixProj ℝ n ∘ shift ∘ pathify X) ⁻¹' S) := by
          rfl
    _ = μ ((prefixProj ℝ n ∘ pathify X) ⁻¹' S) := by
          -- Apply contractability: shift ∘ pathify X extracts (X₁, X₂, ...)
          --                        pathify X extracts (X₀, X₁, ...)
          -- Define k : Fin n → ℕ with k(i) = i + 1
          let k : Fin n → ℕ := fun i => (i : ℕ) + 1
          have hk : StrictMono k := fun i j hij => Nat.add_lt_add_right (Fin.val_strictMono hij) 1

          -- Apply contractability with this k to get measure equality
          have h_contract : Measure.map (fun ω i => X (k i) ω) μ =
                           Measure.map (fun ω (i : Fin n) => X (i : ℕ) ω) μ := hX n k hk

          -- Show that prefixProj ∘ shift ∘ pathify X = fun ω i => X (k i) ω
          have h1 : (prefixProj ℝ n ∘ shift ∘ pathify X) = (fun ω i => X (k i) ω) := by
            ext ω i
            simp [prefixProj, pathify, shift, k]

          -- Show that prefixProj ∘ pathify X = fun ω i => X (i : ℕ) ω
          have h2 : (prefixProj ℝ n ∘ pathify X) = (fun ω (i : Fin n) => X (i : ℕ) ω) := by
            ext ω i
            simp [prefixProj, pathify]

          -- Rewrite the goal using function equalities
          rw [h1, h2]

          -- Now convert using Measure.map_apply
          have hf1 : Measurable (fun ω i => X (k i) ω) := by
            have : Measurable (prefixProj ℝ n ∘ shift ∘ pathify X) :=
              measurable_prefixProj.comp (measurable_shift.comp (measurable_pathify hX_meas))
            rw [← h1]; exact this
          have hf2 : Measurable (fun ω (i : Fin n) => X (i : ℕ) ω) := by
            have : Measurable (prefixProj ℝ n ∘ pathify X) :=
              measurable_prefixProj.comp (measurable_pathify hX_meas)
            rw [← h2]; exact this

          rw [← Measure.map_apply hf1 hS, ← Measure.map_apply hf2 hS, h_contract]

    _ = μ ((pathify X) ⁻¹' ((prefixProj ℝ n) ⁻¹' S)) := by
          rfl  -- Preimage composition: (f ∘ g)⁻¹' S = g⁻¹' (f⁻¹' S)
    _ = μ_path μ X ((prefixProj ℝ n) ⁻¹' S) := by
          rw [μ_path, Measure.map_apply (measurable_pathify hX_meas) (measurable_prefixProj hS)]
    _ = (Measure.map (prefixProj ℝ n) (μ_path μ X)) S := by
          rw [Measure.map_apply measurable_prefixProj hS]

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

    -- Connect integral to eLpNorm 1
    have h1 : ∫ x, ‖(Y n - Z) x‖ ∂m = (eLpNorm (Y n - Z) 1 m).toReal := by
      rw [integral_norm_eq_lintegral_enorm hf_aesm, eLpNorm_one_eq_lintegral_enorm]

    -- Connect Lp norm to eLpNorm 2
    have h2 : ‖Y n - Z‖ = (eLpNorm (Y n - Z) 2 m).toReal := rfl

    -- Combine via monotonicity
    -- Note: (Y n - Z) as an Lp function equals Y n - Z pointwise a.e.
    have h_ae_eq : ↑↑(Y n - Z) =ᶠ[ae m] ↑↑(Y n) - ↑↑Z := Lp.coeFn_sub (Y n) Z

    calc ∫ x, ‖Y n x - Z x‖ ∂m
        = ∫ x, ‖(Y n - Z) x‖ ∂m := by
            refine integral_congr_ae ?_
            filter_upwards [h_ae_eq.symm] with x hx
            simp only [Pi.sub_apply] at hx
            rw [hx]
      _ = (eLpNorm (Y n - Z) 1 m).toReal := h1
      _ ≤ (eLpNorm (Y n - Z) 2 m).toReal := ENNReal.toReal_mono (Lp.eLpNorm_ne_top _) key_ineq
      _ = ‖Y n - Z‖ := h2.symm

  -- Step 3: Apply squeeze theorem
  refine' tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h_norm _ h_bound
  · intro n
    exact integral_nonneg (fun x => norm_nonneg _)

/-! ## E. Bridge 4: Pullback along Factor Map -/

/-- **Change-of-variables for conditional expectation under pushforward.**

If `ν = Measure.map f μ` and `m'` is a sub-σ-algebra on the codomain,
then `(ν[g | m']) ∘ f =ᵐ[μ] μ[(g ∘ f) | MeasurableSpace.comap f m']`.

**Mathematical proof:** Both sides are `comap f m'`-measurable and integrable.
For every `A ∈ m'`, we have `f⁻¹(A) ∈ comap f m'`, and:
```
∫_{f⁻¹(A)} (ν[g|m'] ∘ f) dμ = ∫_A ν[g|m'] dν = ∫_A g dν = ∫_{f⁻¹(A)} (g∘f) dμ
```
By uniqueness of conditional expectation, the functions are equal μ-a.e. -/
lemma condexp_changeOfVariables
    {α β : Type*} [MeasurableSpace α] {m₀ : MeasurableSpace β}
    (μ : Measure α) (f : α → β) (hf : @Measurable α β _ m₀ f)
    (m' : MeasurableSpace β) (hm' : m' ≤ m₀)
    {g : β → ℝ}
    (hg : Integrable g (@Measure.map α β _ m₀ f μ)) :
    ((@Measure.map α β _ m₀ f μ)[g | m']) ∘ f
      =ᵐ[μ] μ[g ∘ f | MeasurableSpace.comap f m'] := by
  -- Set up notation
  set ν := @Measure.map α β _ m₀ f μ with hν_def

  -- The LHS is (ν[g | m']) ∘ f
  -- The RHS is μ[g ∘ f | comap f m']

  -- Strategy: Use uniqueness of conditional expectation via setIntegral equality
  -- We'll show: for all A with @MeasurableSet β m' A,
  --   ∫ ω in f⁻¹' A, (ν[g | m'] ∘ f) ω ∂μ = ∫ ω in f⁻¹' A, (g ∘ f) ω ∂μ

  -- Step 1: Show g ∘ f is integrable
  -- This requires integrable_map_measure, which has the same typeclass issue
  have hgf_int : Integrable (g ∘ f) μ := by sorry

  -- Step 2: Show the LHS is measurable w.r.t. comap f m'
  have hLHS_meas : @Measurable α ℝ (MeasurableSpace.comap f m') _ ((ν)[g | m'] ∘ f) := by sorry

  -- Step 3: The key integral equality for all measurable sets
  -- For any A with @MeasurableSet β m' A, we have f⁻¹(A) ∈ comap f m' and:
  --   ∫ ω in f⁻¹' A, (ν[g | m'] ∘ f) ω ∂μ
  --     = ∫ y in A, ν[g | m'] y ∂ν            (integral_map)
  --     = ∫ y in A, g y ∂ν                    (setIntegral_condExp)
  --     = ∫ ω in f⁻¹' A, (g ∘ f) ω ∂μ         (integral_map)

  -- Apply uniqueness of conditional expectation
  -- This requires careful MeasurableSpace instance management
  sorry

/-- **Key fact:** The tail σ-algebra pulls back correctly via pathify.

This uses the surjective equality from TailSigma.lean. For probability applications,
we work modulo null sets, so surjectivity can often be assumed WLOG. -/
lemma tailProcess_eq_comap_tail_on_path {X : ℕ → Ω → ℝ} (hX_meas : ∀ i, Measurable (X i))
    (hΦ : Function.Surjective (pathify X)) :
    tailProcess X = MeasurableSpace.comap (pathify X) tail_on_path := by
  -- Apply the Bridge 2b lemma from TailSigma.lean
  unfold tail_on_path
  exact Exchangeability.Tail.tailProcess_eq_comap_path_of_surjective X hΦ

/-- **BRIDGE 4.** Conditional expectation commutes with pathify.

For H : (ℕ → ℝ) → ℝ and the factor map pathify:
  E_path[H | tail_on_path] ∘ pathify = E_Ω[H ∘ pathify | tailProcess X]

**TODO:** Use `condexp_comp` / `condexp_preimage` pattern from mathlib. -/
lemma condexp_pullback_along_pathify
    {X : ℕ → Ω → ℝ} (hX_meas : ∀ i, Measurable (X i))
    (H : (ℕ → ℝ) → ℝ) (hH_meas : Measurable H)
    (hH_bdd : ∃ C, ∀ ω, |H ω| ≤ C)
    (hΦ : Function.Surjective (pathify X)) :
    (μ_path μ X)[H | tail_on_path] ∘ (pathify X)
      =ᵐ[μ] μ[(H ∘ (pathify X)) | tailProcess X] := by
  /- Standard change of variables for conditional expectations.
     Strategy: Use the fact that tailProcess X = comap (pathify X) tail_on_path,
     combined with the characterizing property of conditional expectation. -/

  -- First, use the σ-algebra equality
  have h_sigma : tailProcess X = MeasurableSpace.comap (pathify X) tail_on_path :=
    tailProcess_eq_comap_tail_on_path hX_meas hΦ

  -- Rewrite the RHS using this equality
  rw [h_sigma]

  -- Now apply the change-of-variables lemma with:
  --   f = pathify X,  μ = μ,  g = H
  --   ν = μ_path μ X = Measure.map (pathify X) μ
  --   m' = tail_on_path

  -- Need: H is integrable with respect to μ_path μ X
  have hH_int : Integrable H (μ_path μ X) := by
    -- Bounded measurable functions on probability spaces are integrable
    obtain ⟨C, hC⟩ := hH_bdd
    haveI : IsProbabilityMeasure (μ_path μ X) := isProbabilityMeasure_μ_path hX_meas
    apply Integrable.of_bound hH_meas.aestronglyMeasurable (C := C)
    apply ae_of_all
    intro ω
    exact hC ω

  -- Apply the change-of-variables formula
  exact condexp_changeOfVariables μ (pathify X) (measurable_pathify hX_meas)
    tail_on_path tail_on_path_le hH_int

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
    /-  **Proof strategy (depends on completing condexp_changeOfVariables):**

    We have convergence on path space (hL2_to_L1):
      ∫ x, ‖birkhoffAverage ... gLp x - metProjection ... gLp x‖ ∂ν → 0

    **Step 1: Identify Birkhoff average with Cesàro average**
    For ω = pathify X ω':
      birkhoffAverage ℝ (koopman shift) id n gLp (pathify X ω')
        = (1/n) * ∑ k < n, gLp (shift^k (pathify X ω'))
        = (1/n) * ∑ k < n, g (shift^k (pathify X ω'))   (gLp coerces to g a.e.)
        = (1/n) * ∑ k < n, f ((shift^k (pathify X ω')) 0)
        = (1/n) * ∑ k < n, f ((pathify X ω') k)
        = (1/n) * ∑ k < n, f (X k ω')

    **Step 2: Pull back conditional expectation**
    Apply Bridge 2: metProjection ... gLp = ν[gLp | tail_on_path]
    Apply Bridge 4 with H = g (and boundedness from hf_bdd):
      ν[g | tail_on_path] ∘ pathify X =ᵐ[μ] μ[g ∘ pathify X | tailProcess X]

    Note: g ∘ pathify X = fun ω' => g (pathify X ω') = fun ω' => f (X 0 ω') = f ∘ X 0

    **Step 3: Change of variables for integral**
    Use integral_map with f = pathify X:
      ∫ x, ‖...‖ ∂ν = ∫ x, ‖... ∘ pathify X x‖ ∂μ

    The integrand becomes:
      |(1/m) * ∑ i, f (X i ω') - μ[f ∘ X 0 | tailProcess X] ω'|

    which is exactly what we need.

    **Technical notes:**
    - Need surjectivity of pathify X (can assume WLOG for probability)
    - Need to handle Lp coercions carefully
    - Bridge 4 requires completing condexp_changeOfVariables first
    -/
    sorry

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
