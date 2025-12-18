/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Exchangeability.DeFinetti.ViaL2.BlockAverages
import Exchangeability.DeFinetti.ViaL2.CesaroConvergence
import Exchangeability.DeFinetti.ViaL2.MainConvergence
import Exchangeability.DeFinetti.L2Helpers
import Exchangeability.Contractability
import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# Additional L² Helpers and Incomplete Lemmas

This file contains technical lemmas and placeholder definitions that support
the L² proof of de Finetti's theorem. Some lemmas have `sorry` placeholders
that will eventually be replaced with proper proofs from mathlib or local implementations.

## Contents

* Elementary helpers (clip01, Lipschitz properties)
* L¹ convergence helpers
* Boundedness helpers
* AE strong measurability helpers
* Deep results requiring further work (marked with sorry)

## Note

The incomplete lemmas in this file are placeholders for complex proofs that are deferred
to allow the main proof structure to be complete. Each sorry can be replaced with
a proper proof.
-/

noncomputable section

namespace Exchangeability.DeFinetti.ViaL2

open MeasureTheory ProbabilityTheory BigOperators Filter Topology
open Exchangeability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-! ## Forward declarations and placeholders

This section contains forward declarations and placeholder definitions for deep results.
Each sorry can be replaced with a proper proof from mathlib or a local implementation.
-/

-- Note: The definitions alphaIic, cdf_from_alpha, directing_measure, alphaIic_measurable,
-- and weighted_sums_converge_L1 are in MainConvergence.lean and will be available when
-- MainConvergence imports MoreL2Helpers.

-- Forward declaration for alphaFrom (not yet implemented in MainConvergence)
-- TODO: Define as the L¹ limit of block averages, or as conditional expectation
def alphaFrom {Ω : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  (X : ℕ → Ω → ℝ) (_hX_contract : Contractable μ X)
  (_hX_meas : ∀ i, Measurable (X i)) (_hX_L2 : ∀ i, MemLp (X i) 2 μ)
  (_f : ℝ → ℝ) : Ω → ℝ :=
  fun _ => 0  -- Placeholder definition; the actual value requires construction

-- Axiom for CDF limit behavior.
--
-- **MATHEMATICAL NOTE:** This axiom requires the CDF limits to hold for ALL ω.
-- However, from the L¹ construction of `alphaIic`, we can only prove a.e. convergence:
-- - `alphaIic_ae_tendsto_zero_at_bot` in MainConvergence.lean
-- - `alphaIic_ae_tendsto_one_at_top` in MainConvergence.lean
--
/-- CDF limits at ±∞: F(t) → 0 as t → -∞ and F(t) → 1 as t → +∞.

This is now trivial because `cdf_from_alpha` is defined via `stieltjesOfMeasurableRat`,
which guarantees these limits for ALL ω (not just a.e.) by construction.

The `stieltjesOfMeasurableRat` construction automatically patches the null set where
the raw L¹ limit `alphaIic` would fail to have proper CDF limits. -/
lemma cdf_from_alpha_limits {Ω : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
  (hX_meas : ∀ i, Measurable (X i)) (hX_L2 : ∀ i, MemLp (X i) 2 μ)
  (ω : Ω) :
  Tendsto (cdf_from_alpha X hX_contract hX_meas hX_L2 ω) atBot (𝓝 0) ∧
  Tendsto (cdf_from_alpha X hX_contract hX_meas hX_L2 ω) atTop (𝓝 1) := by
  constructor
  · exact ProbabilityTheory.tendsto_stieltjesOfMeasurableRat_atBot
      (measurable_alphaIicRat X hX_contract hX_meas hX_L2) ω
  · exact ProbabilityTheory.tendsto_stieltjesOfMeasurableRat_atTop
      (measurable_alphaIicRat X hX_contract hX_meas hX_L2) ω

namespace Helpers

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Elementary helpers -/

/-- Clip a real to the interval `[0,1]`. -/
@[simp] def clip01 (x : ℝ) : ℝ := max 0 (min 1 x)

lemma clip01_range (x : ℝ) : 0 ≤ clip01 x ∧ clip01 x ≤ 1 := by
  unfold clip01
  constructor
  · exact le_max_left _ _
  · apply max_le
    · linarith
    · exact min_le_left _ _

/-- `clip01` is 1-Lipschitz. -/
lemma clip01_1Lipschitz : LipschitzWith 1 clip01 := by
  -- clip01 x = max 0 (min 1 x) = projIcc 0 1
  -- Projection onto [0,1] is 1-Lipschitz by mathlib's LipschitzWith.projIcc
  -- We compose: min 1 is 1-Lipschitz, then max 0 is 1-Lipschitz
  exact (LipschitzWith.id.const_min 1).const_max 0

/-- Pointwise contraction from the 1-Lipschitzness. -/
lemma abs_clip01_sub_le (x y : ℝ) : |clip01 x - clip01 y| ≤ |x - y| := by
  simpa [Real.dist_eq] using (clip01_1Lipschitz.dist_le_mul x y)

/-- `clip01` is continuous. -/
lemma continuous_clip01 : Continuous clip01 :=
  clip01_1Lipschitz.continuous

/-- **L¹-stability under 1-Lipschitz post-composition.**
If `∫ |fₙ - f| → 0`, then `∫ |clip01 ∘ fₙ - clip01 ∘ f| → 0`.

This follows from mathlib's `LipschitzWith.norm_compLp_sub_le`: Since `clip01` is 1-Lipschitz
and maps 0 to 0, we have `‖clip01 ∘ f - clip01 ∘ g‖₁ ≤ 1 * ‖f - g‖₁`. -/
lemma l1_convergence_under_clip01
    {μ : Measure Ω} {fn : ℕ → Ω → ℝ} {f : Ω → ℝ}
    (h_meas : ∀ n, AEMeasurable (fn n) μ) (hf : AEMeasurable f μ)
    (h_integrable : ∀ n, Integrable (fun ω => fn n ω - f ω) μ)
    (h : Tendsto (fun n => ∫ ω, |fn n ω - f ω| ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, |clip01 (fn n ω) - clip01 (f ω)| ∂μ) atTop (𝓝 0) := by
  -- clip01 is 1-Lipschitz, so |clip01 x - clip01 y| ≤ |x - y|
  -- Thus ∫ |clip01 ∘ fn - clip01 ∘ f| ≤ ∫ |fn - f|
  -- By squeeze theorem, if ∫ |fn - f| → 0, then ∫ |clip01 ∘ fn - clip01 ∘ f| → 0
  have hmono (n : ℕ) : ∫ ω, |clip01 (fn n ω) - clip01 (f ω)| ∂μ ≤ ∫ ω, |fn n ω - f ω| ∂μ := by
    apply integral_mono_ae
    · -- |clip01(...) - clip01(...)| is integrable, dominated by |fn n - f| which is integrable
      -- Use Integrable.mono: since |clip01 x - clip01 y| ≤ |x - y| pointwise
      apply Integrable.mono (h_integrable n).abs
      · -- AE strongly measurable: clip01 is continuous, compositions preserve ae measurability
        have h1 : AEStronglyMeasurable (fun ω => clip01 (fn n ω)) μ :=
          continuous_clip01.comp_aestronglyMeasurable (h_meas n).aestronglyMeasurable
        have h2 : AEStronglyMeasurable (fun ω => clip01 (f ω)) μ :=
          continuous_clip01.comp_aestronglyMeasurable hf.aestronglyMeasurable
        exact (h1.sub h2).norm
      · filter_upwards with ω
        simp [Real.norm_eq_abs]
        exact abs_clip01_sub_le (fn n ω) (f ω)
    · exact (h_integrable n).abs
    · filter_upwards with ω
      exact abs_clip01_sub_le (fn n ω) (f ω)
  refine squeeze_zero ?_ hmono h
  intro n
  apply integral_nonneg
  intro ω
  exact abs_nonneg _

/-! ### L¹ Convergence Helpers -/

/-- **L¹ uniqueness of limit:** If fₙ → f and fₙ → g in L¹, then f =ᵐ g.

Uses triangle inequality and `eLpNorm_eq_zero_iff`. -/
private lemma L1_unique_of_two_limits
  {μ : Measure Ω} {f g : Ω → ℝ}
  (hf : Integrable f μ) (hg : Integrable g μ)
  {fn : ℕ → Ω → ℝ}
  (hfn : ∀ n, AEStronglyMeasurable (fn n) μ)
  (h1 : Tendsto (fun n => eLpNorm (fn n - f) 1 μ) atTop (𝓝 0))
  (h2 : Tendsto (fun n => eLpNorm (fn n - g) 1 μ) atTop (𝓝 0)) :
  f =ᵐ[μ] g := by
  -- Strategy: Show eLpNorm (f - g) 1 μ = 0 using triangle inequality
  -- ‖f - g‖₁ ≤ ‖f - fn‖₁ + ‖fn - g‖₁ → 0 as n → ∞
  -- Then use eLpNorm_eq_zero_iff to convert to f =ᵐ g

  -- Get AEStronglyMeasurable for f and g from Integrable
  have hf_aesm : AEStronglyMeasurable f μ := hf.aestronglyMeasurable
  have hg_aesm : AEStronglyMeasurable g μ := hg.aestronglyMeasurable

  -- Key: eLpNorm (f - g) 1 μ ≤ eLpNorm (f - fn n) 1 μ + eLpNorm (fn n - g) 1 μ for all n
  -- And both terms on the right go to 0
  have h_bound : ∀ n, eLpNorm (f - g) 1 μ ≤ eLpNorm (fn n - f) 1 μ + eLpNorm (fn n - g) 1 μ := by
    intro n
    calc eLpNorm (f - g) 1 μ
        = eLpNorm ((f - fn n) + (fn n - g)) 1 μ := by ring_nf
      _ ≤ eLpNorm (f - fn n) 1 μ + eLpNorm (fn n - g) 1 μ :=
          eLpNorm_add_le (hf_aesm.sub (hfn n)) ((hfn n).sub hg_aesm) le_rfl
      _ = eLpNorm (fn n - f) 1 μ + eLpNorm (fn n - g) 1 μ := by
          rw [← eLpNorm_neg (f - fn n)]
          simp only [neg_sub]

  -- The sum eLpNorm (fn n - f) 1 μ + eLpNorm (fn n - g) 1 μ → 0
  have h_sum_tendsto : Tendsto (fun n => eLpNorm (fn n - f) 1 μ + eLpNorm (fn n - g) 1 μ) atTop (𝓝 0) := by
    convert h1.add h2
    simp only [add_zero]

  -- Since eLpNorm (f - g) 1 μ is constant and bounded by something going to 0, it must be 0
  have h_zero : eLpNorm (f - g) 1 μ = 0 := by
    by_contra h_ne
    have h_pos : 0 < eLpNorm (f - g) 1 μ := pos_iff_ne_zero.mpr h_ne
    -- The bound goes to 0, so eventually it's < eLpNorm (f - g) 1 μ
    -- Use that if a sequence tends to 0 and ε > 0, eventually the sequence is < ε
    have h_ev : ∀ᶠ n in atTop, eLpNorm (fn n - f) 1 μ + eLpNorm (fn n - g) 1 μ < eLpNorm (f - g) 1 μ :=
      (tendsto_order.mp h_sum_tendsto).2 _ h_pos
    obtain ⟨N, hN⟩ := h_ev.exists
    -- At n = N, we have h_bound N and hN
    have h_lt : eLpNorm (fn N - f) 1 μ + eLpNorm (fn N - g) 1 μ < eLpNorm (f - g) 1 μ := hN
    have h_le : eLpNorm (f - g) 1 μ ≤ eLpNorm (fn N - f) 1 μ + eLpNorm (fn N - g) 1 μ := h_bound N
    exact (lt_irrefl _ (lt_of_le_of_lt h_le h_lt))

  -- Apply eLpNorm_eq_zero_iff to conclude f - g =ᵐ 0
  rw [eLpNorm_eq_zero_iff (hf_aesm.sub hg_aesm) (one_ne_zero)] at h_zero
  filter_upwards [h_zero] with x hx using sub_eq_zero.mp hx

/-- **L¹ convergence under clipping:** If fₙ → f in L¹, then clip01∘fₙ → clip01∘f in L¹. -/
private lemma L1_tendsto_clip01
  {μ : Measure Ω} {fn : ℕ → Ω → ℝ} {f : Ω → ℝ}
  (h : Tendsto (fun n => eLpNorm (fn n - f) 1 μ) atTop (𝓝 0)) :
  Tendsto (fun n => eLpNorm ((fun ω => clip01 (fn n ω))
                          - (fun ω => clip01 (f ω))) 1 μ)
          atTop (𝓝 0) := by
  -- Pointwise: |clip01 x - clip01 y| ≤ |x - y| (1-Lipschitz)
  have hmono (n : ℕ) :
      eLpNorm ((fun ω => clip01 (fn n ω)) - (fun ω => clip01 (f ω))) 1 μ
      ≤ eLpNorm (fn n - f) 1 μ := by
    refine eLpNorm_mono_ae ?_
    filter_upwards with ω
    simpa [Pi.sub_apply] using abs_clip01_sub_le (fn n ω) (f ω)
  -- pass to limit
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h ?_ ?_
  · apply Eventually.of_forall; intro n; exact zero_le _
  · apply Eventually.of_forall; intro n; exact hmono n

/-! ### Boundedness Helpers -/

/-- If ∀ n, aₙ(ω) ≤ 1, then ⨅ₙ aₙ(ω) ≤ 1. -/
private lemma iInf_le_one_of_le_one {ι : Type*} [Nonempty ι]
  (a : ι → ℝ) (h : ∀ i, a i ≤ 1) (hbdd : BddBelow (Set.range a)) : ⨅ i, a i ≤ 1 := by
  have ⟨i⟩ := ‹Nonempty ι›
  exact (ciInf_le hbdd i).trans (h i)

/-- If ∀ n, aₙ(ω) ≤ 1, then ⨆ₙ aₙ(ω) ≤ 1. -/
private lemma iSup_le_one_of_le_one {ι : Type*} [Nonempty ι]
  (a : ι → ℝ) (h : ∀ i, a i ≤ 1) : ⨆ i, a i ≤ 1 := by
  exact ciSup_le h

/-! ### AE Strong Measurability for iInf/iSup -/

/-- iInf of countably many AE-strongly-measurable real functions is AE-strongly-measurable. -/
private lemma aestrong_iInf_real
  {μ : Measure Ω} {ι : Type*} [Countable ι]
  (f : ι → Ω → ℝ)
  (h : ∀ i, AEStronglyMeasurable (f i) μ) :
  AEStronglyMeasurable (fun ω => ⨅ i, f i ω) μ := by
  -- AE-measurable version exists via countable iInf
  have h_ae : AEMeasurable (fun ω => ⨅ i, f i ω) μ := by
    refine (AEMeasurable.iInf fun i => ?_)
    exact (h i).aemeasurable
  -- Real is second-countable, so AE-measurable implies AE-strongly-measurable
  exact h_ae.aestronglyMeasurable

/-- iSup of countably many AE-strongly-measurable real functions is AE-strongly-measurable. -/
private lemma aestrong_iSup_real
  {μ : Measure Ω} {ι : Type*} [Countable ι]
  (f : ι → Ω → ℝ)
  (h : ∀ i, AEStronglyMeasurable (f i) μ) :
  AEStronglyMeasurable (fun ω => ⨆ i, f i ω) μ := by
  have h_ae : AEMeasurable (fun ω => ⨆ i, f i ω) μ := by
    refine (AEMeasurable.iSup fun i => ?_)
    exact (h i).aemeasurable
  exact h_ae.aestronglyMeasurable

/-! ### Incomplete lemmas for deep steps

These are the genuinely hard parts (reverse martingale, kernel measurability,
endpoint limits, identification). Keep them here so the main file stays tidy.
Replace the sorries with real proofs when available.
-/

/-- **Kernel measurability (TODO):**
For every measurable set `s`, the map ω ↦ ν(ω)(s) is measurable.

This follows from `directing_measure_measurable` defined below for measurable sets.
For non-measurable sets, the sorry in `directing_measure_measurable` needs resolution. -/
lemma directing_measure_eval_measurable
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  (X : ℕ → Ω → ℝ) (hX_contract : Exchangeability.Contractable μ X)
  (hX_meas : ∀ i, Measurable (X i)) (hX_L2 : ∀ i, MemLp (X i) 2 μ) :
  ∀ s : Set ℝ, MeasurableSet s → Measurable
    (fun ω => directing_measure X hX_contract hX_meas hX_L2 ω s) := by
  -- Uses directing_measure_measurable defined below via π-λ theorem
  sorry

/-- **Identification (TODO):**
For bounded measurable `f`, α_f(ω) agrees a.e. with `∫ f dν(ω)`.

This requires completing the monotone class argument in `directing_measure_integral`. -/
lemma directing_measure_identification
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  (X : ℕ → Ω → ℝ) (hX_contract : Exchangeability.Contractable μ X)
  (hX_meas : ∀ i, Measurable (X i)) (hX_L2 : ∀ i, MemLp (X i) 2 μ)
  (f : ℝ → ℝ) (_hf_meas : Measurable f) (_hf_bdd : ∀ x, |f x| ≤ 1) :
  ∀ᵐ ω ∂μ, alphaFrom X hX_contract hX_meas hX_L2 f ω
             = ∫ x, f x ∂(directing_measure X hX_contract hX_meas hX_L2 ω) := by
  sorry

end Helpers

/-- For each fixed t, ω ↦ ν(ω)((-∞,t]) is measurable.
This is the base case for the π-λ theorem. -/
lemma directing_measure_eval_Iic_measurable
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ)
    (t : ℝ) :
    Measurable (fun ω => directing_measure X hX_contract hX_meas hX_L2 ω (Set.Iic t)) := by
  -- With the new definition via stieltjesOfMeasurableRat, measurability comes directly
  -- from ProbabilityTheory.measurable_stieltjesOfMeasurableRat
  have hmeas : Measurable (fun ω => cdf_from_alpha X hX_contract hX_meas hX_L2 ω t) :=
    ProbabilityTheory.measurable_stieltjesOfMeasurableRat
      (measurable_alphaIicRat X hX_contract hX_meas hX_L2) t
  -- directing_measure ω (Iic t) = F_ω.measure (Iic t) = ofReal (F_ω t)
  -- where F_ω is the StieltjesFunction from stieltjesOfMeasurableRat with limit 0 at -∞
  have h_eq : ∀ ω, directing_measure X hX_contract hX_meas hX_L2 ω (Set.Iic t) =
      ENNReal.ofReal (cdf_from_alpha X hX_contract hX_meas hX_L2 ω t) := by
    intro ω
    have h_lim := (cdf_from_alpha_limits X hX_contract hX_meas hX_L2 ω).1
    unfold directing_measure cdf_from_alpha
    rw [StieltjesFunction.measure_Iic _ h_lim t]
    simp only [sub_zero]
  simp_rw [h_eq]
  exact ENNReal.measurable_ofReal.comp hmeas

/-- For each set s, the map ω ↦ ν(ω)(s) is measurable.

This is the key measurability property needed for complete_from_directing_measure.

For measurable sets: Uses monotone class theorem (π-λ theorem) - prove for intervals,
extend to all Borel sets.

For non-measurable sets: The measure is 0 by outer regularity, so the function is
the constant zero function (hence measurable).
-/
lemma directing_measure_measurable
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ)
    (s : Set ℝ) :
    Measurable (fun ω => directing_measure X hX_contract hX_meas hX_L2 ω s) := by
  classical
  by_cases hs : MeasurableSet s
  ·
    -- π–λ theorem approach:
    -- Define the class of "good" measurable sets G = {s measurable | ω ↦ ν(ω)(s) is measurable}
    -- We restrict to measurable sets so that measure properties (compl, union) can be used
    let G : Set (Set ℝ) :=
      {s | MeasurableSet s ∧ Measurable (fun ω => directing_measure X hX_contract hX_meas hX_L2 ω s)}

    -- Step 1: Show G contains the π-system of half-lines
    have h_pi : ∀ t : ℝ, Set.Iic t ∈ G := by
      intro t
      constructor
      · exact measurableSet_Iic
      · exact directing_measure_eval_Iic_measurable X hX_contract hX_meas hX_L2 t

    -- Step 2: Show G is a Dynkin system (λ-system)
    have h_empty : ∅ ∈ G := by
      constructor
      · exact MeasurableSet.empty
      · change Measurable (fun ω => directing_measure X hX_contract hX_meas hX_L2 ω ∅)
        simp only [measure_empty]
        exact measurable_const

    have h_compl : ∀ s ∈ G, sᶜ ∈ G := by
      intro s ⟨hs_meas, hs_eval⟩
      constructor
      · exact hs_meas.compl
      · -- ν(ω)(sᶜ) = ν(ω)(univ) - ν(ω)(s) = 1 - ν(ω)(s)
        -- Since ν(ω) is a probability measure, ν(ω)(univ) = 1
        -- ω ↦ ν(ω)(s) is measurable by hs_eval
        -- ω ↦ 1 - ν(ω)(s) is measurable as difference of measurable functions
        have h_univ_s : ∀ ω, directing_measure X hX_contract hX_meas hX_L2 ω (sᶜ) =
            directing_measure X hX_contract hX_meas hX_L2 ω Set.univ -
            directing_measure X hX_contract hX_meas hX_L2 ω s := by
          intro ω
          -- directing_measure ω is a measure (StieltjesFunction.measure), so measure_compl applies
          -- Need IsFiniteMeasure instance - follows from IsProbabilityMeasure (once that's proved)
          haveI : IsFiniteMeasure (directing_measure X hX_contract hX_meas hX_L2 ω) := by
            haveI := directing_measure_isProbabilityMeasure X hX_contract hX_meas hX_L2 ω
            infer_instance
          rw [measure_compl hs_meas (measure_ne_top _ s)]
        simp_rw [h_univ_s]
        -- ω ↦ ν(ω)(univ) is constant 1 (probability measure), so measurable
        -- ω ↦ ν(ω)(s) is measurable by hs_eval
        -- Their difference is measurable
        have h_univ_const : ∀ ω, directing_measure X hX_contract hX_meas hX_L2 ω Set.univ = 1 := by
          intro ω
          have hprob := directing_measure_isProbabilityMeasure X hX_contract hX_meas hX_L2 ω
          simpa using hprob.measure_univ
        simp_rw [h_univ_const]
        -- (fun ω => 1 - ν(ω)(s)) is measurable
        -- Constant 1 minus measurable function
        exact Measurable.const_sub hs_eval 1

    have h_iUnion : ∀ (f : ℕ → Set ℝ),
        (∀ i j, i ≠ j → Disjoint (f i) (f j)) →
        (∀ n, f n ∈ G) →
        (⋃ n, f n) ∈ G := by
      intro f hdisj hf
      constructor
      · -- ⋃ n, f n is measurable as countable union of measurable sets
        exact MeasurableSet.iUnion (fun n => (hf n).1)
      · -- ω ↦ ν(ω)(⋃ f n) is measurable
        -- ν(ω)(⋃ f n) = ∑ n, ν(ω)(f n) by σ-additivity (since f n are pairwise disjoint and measurable)
        have h_union_eq : ∀ ω, directing_measure X hX_contract hX_meas hX_L2 ω (⋃ n, f n) =
            ∑' n, directing_measure X hX_contract hX_meas hX_L2 ω (f n) := by
          intro ω
          -- directing_measure ω is a measure (StieltjesFunction.measure), so measure_iUnion applies
          exact measure_iUnion hdisj (fun n => (hf n).1)
        simp_rw [h_union_eq]
        -- ∑' n, ν(ω)(f n) is measurable as tsum of measurable functions
        exact Measurable.ennreal_tsum (fun n => (hf n).2)

    -- Step 3: Apply π-λ theorem (induction_on_inter)
    -- The Borel σ-algebra on ℝ is generated by half-lines {Iic t | t ∈ ℝ}
    -- G contains this π-system and is a Dynkin system,
    -- hence G contains all Borel sets
    -- Since s is measurable (by hypothesis hs), we need to show s ∈ G

    -- Define the property: C(t) = "t ∈ G"
    let C : ∀ (t : Set ℝ), MeasurableSet t → Prop := fun t _ => t ∈ G

    -- Apply π-λ theorem with π-system = range Iic
    -- Define the generating set
    let S : Set (Set ℝ) := Set.range (Set.Iic : ℝ → Set ℝ)

    -- Prove the necessary facts about S
    have h_gen : (inferInstance : MeasurableSpace ℝ) = MeasurableSpace.generateFrom S :=
      @borel_eq_generateFrom_Iic ℝ _ _ _ _

    have h_pi_S : IsPiSystem S := by
      -- {Iic t | t ∈ ℝ} is a π-system
      -- For any Iic s, Iic t: if (Iic s) ∩ (Iic t) is nonempty, then it's in S
      -- (Iic s) ∩ (Iic t) = Iic (min s t)
      intro u hu v hv _
      -- u ∈ S means u = Iic s for some s
      -- v ∈ S means v = Iic t for some t
      obtain ⟨s, rfl⟩ := hu
      obtain ⟨t, rfl⟩ := hv
      -- Need to show: Iic s ∩ Iic t ∈ S
      use min s t
      exact Set.Iic_inter_Iic.symm

    -- Apply the π-λ theorem
    have h_induction : ∀ t (htm : MeasurableSet t), C t htm := fun t htm =>
      MeasurableSpace.induction_on_inter h_gen h_pi_S
        h_empty
        (fun u ⟨r, hr⟩ => hr ▸ h_pi r)
        (fun u hum hu => h_compl u hu)
        (fun f hdisj hfm hf => h_iUnion f hdisj hf)
        t htm

    -- Apply to s to conclude
    exact (h_induction s hs).2
  ·
    -- NON-MEASURABLE CASE: s is not a measurable set
    --
    -- Context: directing_measure ω is defined as F_ω.measure where F_ω is a StieltjesFunction.
    -- In Lean, StieltjesFunction.measure extends to a complete measure via Carathéodory's
    -- extension theorem, so it's defined on ALL sets (not just measurable ones).
    --
    -- Mathematical fact: For non-measurable sets, the measure equals the outer measure:
    --   μ(s) = inf{μ(A) : A ⊇ s, A measurable}
    --
    -- The function ω ↦ directing_measure ω s should be measurable because:
    -- 1. The construction is uniform in ω (same Stieltjes CDF process for all ω)
    -- 2. The outer measure is σ-additive from below, inheriting measurability
    -- 3. For each ω, F_ω is constructed from cdf_from_alpha ω, which is measurable in ω
    --
    -- To prove this rigorously would require:
    -- - Showing outer measures preserve measurability in parameters
    -- - Using that the Carathéodory extension is functorial in the base measure
    -- - Possibly: showing the function equals a measurable function a.e.
    --
    -- This is a deep result in measure theory about parameter-dependent measures.
    -- For now, accept as sorry:
    sorry

/-- The directing measure integrates to give α_f.

For any bounded measurable f, we have α_f(ω) = ∫ f dν(ω) a.e.
This is the fundamental bridge property.
-/
lemma directing_measure_integral
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ)
    (f : ℝ → ℝ) (hf_meas : Measurable f)
    (hf_bdd : ∃ M, ∀ x, |f x| ≤ M) :
    ∃ (alpha : Ω → ℝ),
      Measurable alpha ∧ MemLp alpha 1 μ ∧
      (∀ n, ∀ ε > 0, ∃ M : ℕ, ∀ m : ℕ, m ≥ M →
        ∫ ω, |(1/(m:ℝ)) * ∑ k : Fin m, f (X (n + k.val + 1) ω) - alpha ω| ∂μ < ε) ∧
      (∀ᵐ ω ∂μ, alpha ω = ∫ x, f x ∂(directing_measure X hX_contract hX_meas hX_L2 ω)) := by
  classical
  -- α_f from Step 2 convergence:
  obtain ⟨alpha, hα_meas, hα_L1, hα_conv⟩ :=
    weighted_sums_converge_L1 X hX_contract hX_meas hX_L2 f hf_meas hf_bdd
  refine ⟨alpha, hα_meas, hα_L1, hα_conv, ?_⟩

  -- Identification α_f = ∫ f dν(·) a.e. via monotone class theorem

  -- Step 1: Base case for indicators of half-lines
  have base : ∀ t : ℝ,
      ∀ᵐ ω ∂μ, alphaIic X hX_contract hX_meas hX_L2 t ω
        = ∫ x, (Set.Iic t).indicator (fun _ => (1 : ℝ)) x
            ∂(directing_measure X hX_contract hX_meas hX_L2 ω) := by
    intro t
    -- TODO: Prove alphaIic t ω = ∫ 1_{Iic t} dν(ω) a.e.
    --
    -- PROOF STRATEGY (3 steps):
    --
    -- STEP 1: Integral of indicator equals measure
    -- For any measure ν and measurable set S:
    --   ∫ 1_S dν = ν(S)
    -- This is a fundamental property: MeasureTheory.integral_indicator_one
    -- Applied here:
    --   ∫ 1_{Iic t} d(directing_measure ω) = directing_measure ω (Iic t)
    --
    -- STEP 2: Directing measure value equals CDF
    -- By construction of directing_measure via Measure.ofCDF:
    --   directing_measure ω (Iic t) = cdf_from_alpha ω t
    -- This follows from the definition of Measure.ofCDF applied to the
    -- Stieltjes function cdf_from_alpha ω.
    -- Required lemma: Measure.ofCDF_of_Iic or similar
    --
    -- STEP 3: alphaIic approximates cdf_from_alpha
    -- By definition, alphaIic t ω is constructed as:
    --   alphaIic t ω = inf { cdf_from_alpha ω q | q ∈ ℚ, q ≥ t }
    -- For right-continuous CDFs (which cdf_from_alpha is), we have:
    --   F(t) = inf { F(q) | q ∈ ℚ, q > t } = lim_{q↓t, q∈ℚ} F(q)
    -- This gives alphaIic t ω = cdf_from_alpha ω t.
    --
    -- REQUIRED MATHLIB LEMMAS:
    -- - MeasureTheory.integral_indicator_one: ∫ 1_S dν = ν(S)
    -- - StieltjesFunction.measure_Iic: ν(Iic t) = F(t) for Stieltjes measure
    -- - Filter.tendsto_atTop_ciInf: infimum over rationals equals limit
    -- - Right-continuity property of CDFs
    sorry

  -- TODO: Complete monotone class argument
  --
  -- STEP 2: Define the good class C
  -- C := {f : ℝ → ℝ bounded Borel | ∀ᵐ ω ∂μ, α_f(ω) = ∫ f dν(ω)}
  -- where α_f is the L¹ limit of blockAvg f X m n.
  --
  -- STEP 3: Show C contains indicators of half-lines
  -- From Step 1 (base case above), we have:
  --   ∀ t, 1_{Iic t} ∈ C
  -- These indicators form a π-system (closed under intersection):
  --   Iic s ∩ Iic t = Iic (min s t)
  -- This π-system generates the Borel σ-algebra on ℝ.
  --
  -- STEP 4: Show C is a vector space
  -- Need to verify:
  -- a) If f, g ∈ C, then f + g ∈ C
  --    Uses linearity: ∫ (f+g) dν = ∫ f dν + ∫ g dν
  --    And linearity of blockAvg and L¹ limits
  -- b) If f ∈ C and c ∈ ℝ, then c·f ∈ C
  --    Uses ∫ (c·f) dν = c · ∫ f dν
  --
  -- STEP 5: Show C is closed under bounded monotone convergence
  -- If f_n ∈ C, |f_n| ≤ M, and f_n ↗ f (or f_n ↘ f), then f ∈ C.
  -- This uses:
  -- - Dominated/monotone convergence theorem for integrals: ∫ f_n dν → ∫ f dν
  -- - Corresponding convergence for blockAvg using uniform bounds
  -- - L¹ limit interchange: lim lim = lim (via diagonal argument)
  --
  -- STEP 6: Apply monotone class theorem
  -- Mathlib has versions in MeasureTheory.Function.SimpleFunc or similar.
  -- The theorem states: If C is a vector space containing a π-system P
  -- and closed under bounded monotone limits, then C contains σ(P).
  -- Since P = {indicators of half-lines} generates Borel(ℝ),
  -- we get C = all bounded Borel functions.
  --
  -- REQUIRED MATHLIB LEMMAS:
  -- - MeasureTheory.integral_add, integral_const_mul: integral linearity
  -- - MeasureTheory.tendsto_integral_of_monotone_convergence
  -- - IsPiSystem.of_measurableSet_indicators: half-lines form π-system
  -- - MonotoneClass theorem (may need to prove variant or use existing API)
  sorry

/-- The integral of `alphaIic` equals the marginal probability.

By the L¹ convergence property of the Cesàro averages and contractability
(which implies all marginals are equal), we have:
  ∫ alphaIic(t, ω) dμ = μ(X_0 ∈ Iic t)

This is a key step in proving the bridge property.

**Proof outline**:
1. alphaIic is the clipped L¹ limit of Cesàro averages of 1_{Iic t}(X_i)
2. By L¹ convergence: ∫ (limit) dμ = lim ∫ (Cesàro average) dμ
3. By contractability: each μ(X_i ∈ Iic t) = μ(X_0 ∈ Iic t)
4. Therefore: ∫ alphaIic dμ = μ(X_0 ∈ Iic t)
-/
lemma integral_alphaIic_eq_marginal
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ)
    (t : ℝ) :
    ∫ ω, alphaIic X hX_contract hX_meas hX_L2 t ω ∂μ =
      (μ (X 0 ⁻¹' Set.Iic t)).toReal := by
  -- Define local indicator (same as private indIic in MainConvergence.lean)
  let ind : ℝ → ℝ := (Set.Iic t).indicator (fun _ => (1 : ℝ))
  have ind_meas : Measurable ind := measurable_const.indicator measurableSet_Iic
  have ind_bdd : ∀ x, |ind x| ≤ 1 := by
    intro x; by_cases hx : x ≤ t <;> simp [ind, Set.indicator, hx, abs_of_nonneg]

  -- Get the L¹ limit from weighted_sums_converge_L1
  let limit := (weighted_sums_converge_L1 X hX_contract hX_meas hX_L2
      ind ind_meas ⟨1, ind_bdd⟩).choose
  have h_spec := (weighted_sums_converge_L1 X hX_contract hX_meas hX_L2
      ind ind_meas ⟨1, ind_bdd⟩).choose_spec
  have h_meas_limit : Measurable limit := h_spec.1
  have _h_L1 : MemLp limit 1 μ := h_spec.2.1
  have h_conv : ∀ n, ∀ ε > 0, ∃ M : ℕ, ∀ m : ℕ, m ≥ M →
      ∫ ω, |(1/(m:ℝ)) * ∑ k : Fin m, ind (X (n + k.val + 1) ω) - limit ω| ∂μ < ε :=
    h_spec.2.2

  -- Step 1: alphaIic = max 0 (min 1 limit'), and we need to show this equals limit a.e.
  -- This follows from two facts:
  -- (a) limit' =ᵐ limit (both are L¹ limits of the same Cesàro averages)
  -- (b) limit ∈ [0,1] a.e. (as L¹ limit of averages in [0,1])
  have h_alphaIic_eq : ∀ᵐ ω ∂μ, alphaIic X hX_contract hX_meas hX_L2 t ω = limit ω := by
    -- alphaIic uses its own .choose witness, which may differ from our limit
    -- But both converge to the same L¹ limit, so they're a.e. equal
    -- Then clipping has no effect since the limit is a.e. in [0,1]
    --
    -- The detailed proof would require:
    -- 1. Show limit' from alphaIic's definition equals limit a.e. (L¹ uniqueness)
    -- 2. Show limit ∈ [0,1] a.e. (as L¹ limit of averages bounded in [0,1])
    -- 3. Conclude max 0 (min 1 limit') = limit' = limit a.e.
    --
    -- For now, accept this as it's a technical boundedness/uniqueness argument
    -- The key mathematical content is correct
    sorry

  -- Step 2: Show ∫ limit = μ(X_0 ∈ Iic t).toReal
  -- The Cesàro average integrates to the marginal probability
  have h_cesaro_integral : ∀ n m : ℕ, m > 0 →
      ∫ ω, (1/(m:ℝ)) * ∑ k : Fin m, ind (X (n + k.val + 1) ω) ∂μ =
        (μ (X 0 ⁻¹' Set.Iic t)).toReal := by
    intro n m hm
    -- The integral of the average = average of the integrals
    have h_int_sum : ∫ ω, (1/(m:ℝ)) * ∑ k : Fin m, ind (X (n + k.val + 1) ω) ∂μ =
        (1/(m:ℝ)) * ∑ k : Fin m, ∫ ω, ind (X (n + k.val + 1) ω) ∂μ := by
      rw [integral_mul_left]
      congr 1
      rw [integral_finset_sum]
      intro k _
      -- ind is bounded by 1 and measurable, so it's integrable
      have h_meas_comp : Measurable (fun ω => ind (X (n + k.val + 1) ω)) :=
        ind_meas.comp (hX_meas _)
      have h_bdd : ∀ ω, ‖ind (X (n + k.val + 1) ω)‖ ≤ 1 := by
        intro ω
        rw [Real.norm_eq_abs]
        exact ind_bdd _
      exact Integrable.of_bound h_meas_comp.aestronglyMeasurable 1 (Filter.Eventually.of_forall h_bdd)
    rw [h_int_sum]
    -- Each integral equals μ(X_j ∈ Iic t)
    have h_each : ∀ k : Fin m, ∫ ω, ind (X (n + k.val + 1) ω) ∂μ =
        (μ (X (n + k.val + 1) ⁻¹' Set.Iic t)).toReal := by
      intro k
      -- integral of indicator = measure of set
      -- ind x = 1 if x ≤ t, 0 otherwise
      -- So ∫ ind(X_j ω) dμ = ∫_{X_j ≤ t} 1 dμ = μ{X_j ≤ t}
      have h_ind_eq : ∀ ω, ind (X (n + k.val + 1) ω) =
          (X (n + k.val + 1) ⁻¹' Set.Iic t).indicator (fun _ => (1 : ℝ)) ω := by
        intro ω
        simp only [ind, Set.indicator, Set.mem_Iic, Set.mem_preimage]
      simp_rw [h_ind_eq]
      rw [integral_indicator (hX_meas (n + k.val + 1) measurableSet_Iic)]
      -- ∫ 1 dμ.restrict S = μ(S).toReal
      rw [setIntegral_const, smul_eq_mul, mul_one]
      -- μ.real s = (μ s).toReal by definition
      rfl
    simp_rw [h_each]
    -- By contractability, all marginals are equal
    have h_marginal_eq : ∀ j : ℕ, μ (X j ⁻¹' Set.Iic t) = μ (X 0 ⁻¹' Set.Iic t) := by
      intro j
      have h_map := L2Helpers.contractable_map_single X hX_contract hX_meas (i := j)
      -- μ(X j ⁻¹' S) = (map X_j μ)(S) = (map X_0 μ)(S) = μ(X 0 ⁻¹' S)
      rw [← Measure.map_apply (hX_meas j) measurableSet_Iic]
      rw [h_map]
      rw [Measure.map_apply (hX_meas 0) measurableSet_Iic]
    simp_rw [h_marginal_eq]
    -- Sum of m copies of the same value
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp

  -- Step 3: Use L¹ convergence to show ∫ limit = ∫ Cesàro (which = marginal)
  have h_limit_integral : ∫ ω, limit ω ∂μ = (μ (X 0 ⁻¹' Set.Iic t)).toReal := by
    -- The Cesàro average has constant integral, and converges to limit in L¹
    -- By the continuity of integral under L¹ convergence, ∫ limit = limit of ∫ Cesàro
    -- Since all ∫ Cesàro = μ(X_0 ∈ Iic t), we get ∫ limit = μ(X_0 ∈ Iic t)
    --
    -- Proof: For any ε > 0, eventually |∫ A_m - ∫ limit| < ε
    -- Since ∫ A_m = μ(X_0 ∈ Iic t) for all m > 0, we have ∫ limit = μ(X_0 ∈ Iic t)
    by_contra h_ne
    -- If ∫ limit ≠ marginal, then there's a positive gap
    have h_gap : ∃ δ > 0, |∫ ω, limit ω ∂μ - (μ (X 0 ⁻¹' Set.Iic t)).toReal| ≥ δ := by
      use |∫ ω, limit ω ∂μ - (μ (X 0 ⁻¹' Set.Iic t)).toReal|
      constructor
      · exact abs_pos.mpr (sub_ne_zero.mpr h_ne)
      · exact le_refl _
    obtain ⟨δ, hδ_pos, hδ⟩ := h_gap
    -- By L¹ convergence at n=0, eventually |∫ |A_m - limit|| < δ/2
    have h_eventually := h_conv 0 (δ/2) (by linarith)
    obtain ⟨M, hM⟩ := h_eventually
    -- For large enough m, we have |∫ A_m - ∫ limit| < δ
    have h_int_close : ∀ m ≥ M, m > 0 →
        |∫ ω, (1/(m:ℝ)) * ∑ k : Fin m, ind (X (0 + k.val + 1) ω) ∂μ - ∫ ω, limit ω ∂μ| < δ := by
      intro m hm hm_pos
      -- |∫ (A_m - limit)| ≤ ∫ |A_m - limit| < δ/2 < δ
      have h_bound := hM m hm
      calc |∫ ω, (1/(m:ℝ)) * ∑ k : Fin m, ind (X (0 + k.val + 1) ω) ∂μ - ∫ ω, limit ω ∂μ|
          = |∫ ω, ((1/(m:ℝ)) * ∑ k : Fin m, ind (X (0 + k.val + 1) ω) - limit ω) ∂μ| := by
            congr 1
            rw [integral_sub]
            · have h_meas_cesaro : Measurable (fun ω => (1/(m:ℝ)) * ∑ k : Fin m, ind (X (0 + k.val + 1) ω)) := by
                apply Measurable.const_mul
                apply Finset.measurable_sum
                intro k _
                exact ind_meas.comp (hX_meas _)
              have h_bdd_cesaro : ∀ ω, ‖(1/(m:ℝ)) * ∑ k : Fin m, ind (X (0 + k.val + 1) ω)‖ ≤ 1 := by
                intro ω
                rw [Real.norm_eq_abs, abs_mul]
                have h_sum_bdd : |∑ k : Fin m, ind (X (0 + k.val + 1) ω)| ≤ m := by
                  -- Use triangle inequality: |∑ f| ≤ ∑ |f|, then ∑ |f| ≤ card * 1 = m
                  calc |∑ k : Fin m, ind (X (0 + k.val + 1) ω)|
                      ≤ ∑ k : Fin m, |ind (X (0 + k.val + 1) ω)| := Finset.abs_sum_le_sum_abs _ _
                    _ ≤ Finset.univ.card • (1 : ℝ) := Finset.sum_le_card_nsmul _ _ 1 (fun k _ => ind_bdd _)
                    _ = (m : ℝ) := by simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
                have hm_inv_pos : (1 : ℝ) / m > 0 := by positivity
                calc |1/(m:ℝ)| * |∑ k : Fin m, ind (X (0 + k.val + 1) ω)|
                    ≤ |1/(m:ℝ)| * m := mul_le_mul_of_nonneg_left h_sum_bdd (abs_nonneg _)
                  _ = 1 := by rw [abs_of_pos hm_inv_pos]; field_simp
              exact Integrable.of_bound h_meas_cesaro.aestronglyMeasurable 1
                (Filter.Eventually.of_forall h_bdd_cesaro)
            · -- limit is bounded a.e. since it's an L¹ limit of bounded functions
              -- This follows from: L¹ convergence → convergence in measure → a.e. conv of subsequence
              -- And pointwise limit of bounded functions is bounded
              have h_limit_bdd : ∀ᵐ ω ∂μ, ‖limit ω‖ ≤ 1 := by
                -- The limit is in MemLp 1, and is the limit of averages bounded by 1
                -- Technical argument using L¹ properties
                sorry
              exact Integrable.of_bound h_meas_limit.aestronglyMeasurable 1 h_limit_bdd
        _ ≤ ∫ ω, |(1/(m:ℝ)) * ∑ k : Fin m, ind (X (0 + k.val + 1) ω) - limit ω| ∂μ :=
            abs_integral_le_integral_abs
        _ < δ/2 := h_bound
        _ < δ := by linarith
    -- Get contradiction at m' = max(M, 1)
    let m' := max M 1
    have hm'_ge_M : m' ≥ M := le_max_left M 1
    have hm'_pos : m' > 0 := Nat.lt_of_lt_of_le (by decide : 0 < 1) (le_max_right M 1)
    have h_int_eq := h_cesaro_integral 0 m' hm'_pos
    have h_close := h_int_close m' hm'_ge_M hm'_pos
    rw [h_int_eq] at h_close
    -- Now: |marginal - ∫ limit| < δ but also |∫ limit - marginal| ≥ δ
    rw [abs_sub_comm] at h_close
    linarith

  -- Step 4: Combine: ∫ alphaIic = ∫ limit = μ(X_0 ∈ Iic t)
  calc ∫ ω, alphaIic X hX_contract hX_meas hX_L2 t ω ∂μ
      = ∫ ω, limit ω ∂μ := by
        refine integral_congr_ae ?_
        exact h_alphaIic_eq
    _ = (μ (X 0 ⁻¹' Set.Iic t)).toReal := h_limit_integral

/-- The bridge property: E[∏ᵢ 𝟙_{Bᵢ}(X_{k(i)})] = E[∏ᵢ ν(·)(Bᵢ)].

This is the key property needed for complete_from_directing_measure.
It follows from contractability and the fact that α_{𝟙_B} = ν(·)(B).
-/
lemma directing_measure_bridge
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ)
    {m : ℕ} (k : Fin m → ℕ) (B : Fin m → Set ℝ)
    (hB : ∀ i, MeasurableSet (B i)) :
    ∫⁻ ω, ∏ i : Fin m,
        ENNReal.ofReal ((B i).indicator (fun _ => (1 : ℝ)) (X (k i) ω)) ∂μ
      = ∫⁻ ω, ∏ i : Fin m,
        directing_measure X hX_contract hX_meas hX_L2 ω (B i) ∂μ := by
  classical
  -- Proof by induction on m (number of factors)
  induction m with
  | zero =>
      -- Base case: empty product = 1
      simp [Finset.prod_empty]
  | succ m IH =>
      -- TODO: Complete bridge property inductive step
      --
      -- INDUCTIVE STEP STRATEGY (5 steps):
      --
      -- STEP 1: Reorder to make k(m) maximal
      -- Let N = max_{i ≤ m} k(i), and assume k(m) = N (WLOG by contractability).
      -- If not, use contractability to permute indices: since μ is contractable,
      -- we can swap k(j) ↔ k(m) for any j without changing the distribution.
      -- This requires:
      -- - Identifying the maximum index
      -- - Constructing an appropriate permutation σ with σ(m) giving max
      -- - Applying contractability: μ ∘ X_σ⁻¹ = μ ∘ X
      --
      -- STEP 2: Factor the product
      -- Write:
      --   ∏_{i : Fin (m+1)} 1_{B_i}(X_{k(i)}) = H · 1_{B_m}(X_N)
      -- where H := ∏_{i : Fin m} 1_{B_i}(X_{k(i)}) is the product of first m terms.
      -- Similarly factor the directing measure product:
      --   ∏_{i : Fin (m+1)} ν(·)(B_i) = (∏_{i : Fin m} ν(·)(B_i)) · ν(·)(B_m)
      --
      -- STEP 3: Use directing_measure_integral for the last factor
      -- From directing_measure_integral applied to f = 1_{B_m}:
      --   ∀ᵐ ω, α_{1_{B_m}}(ω) = ∫ 1_{B_m} d(ν(ω)) = ν(ω)(B_m)
      -- where α_{1_{B_m}} is the L¹ limit of blockAvg (1_{B_m}) X n k.
      -- By the L¹ convergence property, we can replace 1_{B_m}(X_N(ω))
      -- with ν(ω)(B_m) in expectation (up to approximation).
      --
      -- STEP 4: Apply tower property (iterated conditioning)
      -- H is measurable w.r.t. σ(X_j | j ≤ N-1) (the "past").
      -- X_N is "future" relative to this σ-algebra.
      -- By contractability/exchangeability:
      --   E[H · 1_{B_m}(X_N)] = E[H · E[1_{B_m}(X_N) | σ(X_j, j ≤ N-1)]]
      --                       = E[H · ν(·)(B_m)]
      -- This uses the tower property of conditional expectation:
      --   E[Y·Z | ℱ] = Y · E[Z | ℱ] when Y is ℱ-measurable
      --
      -- STEP 5: Apply induction hypothesis
      -- By IH applied to the product of m terms:
      --   ∫⁻ ω, H ω · ν(ω)(B_m) ∂μ = ∫⁻ ω, (∏_{i : Fin m} ν(ω)(B_i)) · ν(ω)(B_m) ∂μ
      -- Combining Steps 2-5 gives the result.
      --
      -- REQUIRED MATHLIB LEMMAS:
      -- - Finset.prod_bij: bijection between products (for reindexing)
      -- - MeasureTheory.condExp_of_stronglyMeasurable: tower property
      -- - ENNReal.lintegral_const_mul: factor out measurable functions
      -- - Contractable.reindex: permutation invariance (may need to prove)
      sorry

/-- **Main packaging theorem for L² proof.**

This theorem packages all the directing measure properties needed by
`CommonEnding.complete_from_directing_measure`:

1. `ν` is a probability measure for all ω
2. `ω ↦ ν(ω)(s)` is measurable for all measurable sets s
3. The bridge property: E[∏ᵢ 1_{Bᵢ}(X_{k(i)})] = E[∏ᵢ ν(·)(Bᵢ)]

This enables the final step of the L² proof of de Finetti's theorem.
-/
theorem directing_measure_satisfies_requirements
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_meas : ∀ i, Measurable (X i))
    (hX_contract : Contractable μ X)
    (hX_L2 : ∀ i, MemLp (X i) 2 μ) :
    ∃ (ν : Ω → Measure ℝ),
      (∀ ω, IsProbabilityMeasure (ν ω)) ∧
      (∀ s, MeasurableSet s → Measurable (fun ω => ν ω s)) ∧
      (∀ {m : ℕ} (k : Fin m → ℕ), Function.Injective k → ∀ (B : Fin m → Set ℝ),
        (∀ i, MeasurableSet (B i)) →
          ∫⁻ ω, ∏ i : Fin m,
              ENNReal.ofReal ((B i).indicator (fun _ => (1 : ℝ)) (X (k i) ω)) ∂μ
            = ∫⁻ ω, ∏ i : Fin m, ν ω (B i) ∂μ) := by
  -- Use the directing measure constructed via stieltjesOfMeasurableRat
  let ν := directing_measure X hX_contract hX_meas hX_L2
  refine ⟨ν, ?_, ?_, ?_⟩
  -- Property 1: ν(ω) is a probability measure for all ω
  · exact directing_measure_isProbabilityMeasure X hX_contract hX_meas hX_L2
  -- Property 2: ω ↦ ν(ω)(s) is measurable for measurable s
  · intro s hs
    exact directing_measure_measurable X hX_contract hX_meas hX_L2 s
  -- Property 3: Bridge property (injectivity not actually needed)
  · intro m k _hk_inj B hB
    exact directing_measure_bridge X hX_contract hX_meas hX_L2 k B hB

end Exchangeability.DeFinetti.ViaL2

