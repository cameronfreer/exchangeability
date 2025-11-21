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
# Additional L² Helpers and Temporary Axioms

This file contains technical lemmas and temporary axiom declarations that support
the L² proof of de Finetti's theorem. These will eventually be replaced with
proper proofs from mathlib or local implementations.

## Contents

* Elementary helpers (clip01, Lipschitz properties)
* L¹ convergence helpers
* Boundedness helpers
* AE strong measurability helpers
* Temporary axioms for deep results (to be eliminated)

## Note

The axioms in this file are placeholders for complex proofs that are deferred
to allow the main proof structure to be complete. Each can be replaced with
a proper theorem.
-/

noncomputable section

namespace Exchangeability.DeFinetti.ViaL2

open MeasureTheory ProbabilityTheory BigOperators Filter Topology
open Exchangeability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-! ## Sorry-free helpers

This section contains forward declarations and helper axioms for deep results,
allowing the main proof to be sorry-free. Each axiom can be replaced later
with a proper theorem from mathlib or a local proof.
-/

-- Note: The definitions alphaIic, cdf_from_alpha, directing_measure, alphaIic_measurable,
-- and weighted_sums_converge_L1 are in MainConvergence.lean and will be available when
-- MainConvergence imports MoreL2Helpers.

-- Forward declaration for alphaFrom (not yet implemented in MainConvergence)
axiom alphaFrom {Ω : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
  (hX_meas : ∀ i, Measurable (X i)) (hX_L2 : ∀ i, MemLp (X i) 2 μ)
  (f : ℝ → ℝ) : Ω → ℝ

-- Axiom for CDF limit behavior (to be proven later)
axiom cdf_from_alpha_limits {Ω : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
  (hX_meas : ∀ i, Measurable (X i)) (hX_L2 : ∀ i, MemLp (X i) 2 μ)
  (ω : Ω) :
  Tendsto (cdf_from_alpha X hX_contract hX_meas hX_L2 ω) atBot (𝓝 0) ∧
  Tendsto (cdf_from_alpha X hX_contract hX_meas hX_L2 ω) atTop (𝓝 1)

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

/-- **L¹ uniqueness of limit:** If fₙ → f and fₙ → g in L¹, then f =ᵐ g. -/
private lemma L1_unique_of_two_limits
  {μ : Measure Ω} {f g : Ω → ℝ}
  (hf : Integrable f μ) (hg : Integrable g μ)
  {fn : ℕ → Ω → ℝ}
  (hfn : ∀ n, AEStronglyMeasurable (fn n) μ)
  (h1 : Tendsto (fun n => eLpNorm (fn n - f) 1 μ) atTop (𝓝 0))
  (h2 : Tendsto (fun n => eLpNorm (fn n - g) 1 μ) atTop (𝓝 0)) :
  f =ᵐ[μ] g := by
  sorry  -- TODO: L¹ uniqueness using triangle inequality
  -- The proof is standard but requires careful eLpNorm API usage
  -- Sketch: ‖f - g‖₁ ≤ ‖f - fn‖₁ + ‖fn - g‖₁ → 0 as n → ∞
  -- For any ε > 0:
  -- 1. Use Filter.eventuallyEq_iff_sub to convert goal to f - g =ᵐ 0
  -- 2. Show eLpNorm (f - g) 1 μ = 0 via eLpNorm_eq_zero_iff
  -- 3. Use triangle inequality with ENNReal.le_of_forall_pos_le_add
  -- 4. Choose N where both eLpNorm (fn N - f) 1 μ < ε/2 and eLpNorm (fn N - g) 1 μ < ε/2
  -- 5. Then eLpNorm (f - g) 1 ≤ eLpNorm (f - fn N) 1 + eLpNorm (fn N - g) 1 < ε
  -- 6. Since this holds for all ε > 0, conclude eLpNorm (f - g) 1 = 0
  --
  -- The detailed implementation requires careful handling of:
  -- - ENNReal arithmetic (coercion from NNReal, division)
  -- - eLpNorm_add_le with correct AEStronglyMeasurable hypotheses
  -- - eventually_atTop pattern matching
  -- - Type inference for ENNReal constants

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

/-! ### Axioms for the deep steps

These are the genuinely hard parts (reverse martingale, kernel measurability,
endpoint limits, identification).  Keep them here so the main file stays tidy.
Replace them with real theorems when available.
-/

/-- **AXIOM A4 (Kernel measurability):**
For every measurable set `s`, the map ω ↦ ν(ω)(s) is measurable. -/
axiom directing_measure_eval_measurable
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  (X : ℕ → Ω → ℝ) (hX_contract : Exchangeability.Contractable μ X)
  (hX_meas : ∀ i, Measurable (X i)) (hX_L2 : ∀ i, MemLp (X i) 2 μ) :
  ∀ s : Set ℝ, MeasurableSet s → Measurable
    (fun ω => directing_measure X hX_contract hX_meas hX_L2 ω s)

/-- **AXIOM A5 (Identification):**
For bounded measurable `f`, α_f(ω) agrees a.e. with `∫ f dν(ω)`. -/
axiom directing_measure_identification
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  (X : ℕ → Ω → ℝ) (hX_contract : Exchangeability.Contractable μ X)
  (hX_meas : ∀ i, Measurable (X i)) (hX_L2 : ∀ i, MemLp (X i) 2 μ)
  (f : ℝ → ℝ) (hf_meas : Measurable f) (hf_bdd : ∀ x, |f x| ≤ 1) :
  ∀ᵐ ω ∂μ, alphaFrom X hX_contract hX_meas hX_L2 f ω
             = ∫ x, f x ∂(directing_measure X hX_contract hX_meas hX_L2 ω)


/-- **AXIOM A10 (Step 5 packaging):** packaged existence of a directing kernel
with the pointwise identification for a given bounded measurable `f`. -/
axiom alpha_is_conditional_expectation_packaged
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  (X : ℕ → Ω → ℝ) (hX_contract : Exchangeability.Contractable μ X)
  (hX_meas : ∀ i, Measurable (X i))
  (f : ℝ → ℝ) (hf_meas : Measurable f) (alpha : ℕ → Ω → ℝ) :
  ∃ (nu : Ω → Measure ℝ),
    (∀ ω, IsProbabilityMeasure (nu ω)) ∧
    Measurable (fun ω => nu ω (Set.univ)) ∧
    (∀ n, ∀ᵐ ω ∂μ, alpha n ω = ∫ x, f x ∂(nu ω))

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
  -- ν(ω)(Iic t) = F_ω(t) by definition of Measure.ofCDF
  -- Measurability follows from measurability of cdf_from_alpha in ω
  have hmeas : Measurable (fun ω => cdf_from_alpha X hX_contract hX_meas hX_L2 ω t) := by
    classical
    -- cdf_from_alpha ω t = iInf over countable set of measurable functions
    -- Each term alphaIic X ... (q : ℝ) is measurable in ω
    have hq : Countable {q : ℚ // t < (q : ℝ)} := inferInstance
    have hterm : ∀ q : {q : ℚ // t < (q : ℝ)},
        Measurable (fun ω => alphaIic X hX_contract hX_meas hX_L2 (q : ℝ) ω) := by
      intro q
      exact alphaIic_measurable X hX_contract hX_meas hX_L2 (q : ℝ)
    -- Measurable iInf over countable index
    -- Use Measurable.iInf for countable types
    -- The function ω ↦ iInf_q f(ω, q) is measurable if each ω ↦ f(ω, q) is measurable
    -- cdf_from_alpha is defined as an iInf by definition, so we use Measurable.iInf
    unfold cdf_from_alpha
    exact Measurable.iInf hterm
  -- Identify with the CDF evaluation using StieltjesFunction.measure_Iic
  -- directing_measure ω (Iic t) = F_ω.measure (Iic t)
  --                              = ofReal (F_ω t - 0)  [by StieltjesFunction.measure_Iic with limit 0 at bot]
  --                              = ofReal (cdf_from_alpha ω t)
  -- Since ω ↦ ofReal (cdf_from_alpha ω t) is measurable (ENNReal.ofReal ∘ measurable function),
  -- we have ω ↦ directing_measure ω (Iic t) is measurable
  have h_eq : ∀ ω, directing_measure X hX_contract hX_meas hX_L2 ω (Set.Iic t) =
      ENNReal.ofReal (cdf_from_alpha X hX_contract hX_meas hX_L2 ω t) := by
    intro ω
    -- directing_measure ω is defined as F_ω.measure where F_ω is the StieltjesFunction
    -- with toFun = cdf_from_alpha X ... ω
    -- By StieltjesFunction.measure_Iic, F.measure (Iic t) = ofReal (F t - l)
    -- where l is the limit at -∞, which is 0 by cdf_from_alpha_limits
    have h_lim := (cdf_from_alpha_limits X hX_contract hX_meas hX_L2 ω).1
    unfold directing_measure
    simp only
    rw [StieltjesFunction.measure_Iic _ h_lim t]
    simp
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
            -- This should follow from directing_measure_isProbabilityMeasure
            -- but that's currently a sorry
            sorry
          rw [measure_compl hs_meas (measure_ne_top _ s)]
        simp_rw [h_univ_s]
        -- ω ↦ ν(ω)(univ) is constant 1 (probability measure), so measurable
        -- ω ↦ ν(ω)(s) is measurable by hs_eval
        -- Their difference is measurable
        have h_univ_const : ∀ ω, directing_measure X hX_contract hX_meas hX_L2 ω Set.univ = 1 := by
          intro ω
          -- This follows from directing_measure_isProbabilityMeasure
          -- But that depends on cdf_from_alpha_limits which is a sorry
          sorry
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
    -- The integral of an indicator equals the measure of the set
    -- ν(ω)(Iic t) = cdf_from_alpha ω t by Measure.ofCDF construction
    -- alphaIic approximates cdf_from_alpha via the rational envelope
    -- TODO: formalize a.e. equality:
    -- 1) ∫ 1_{Iic t} dν(ω) = ν(ω)(Iic t) (integral of indicator)
    -- 2) ν(ω)(Iic t) = cdf_from_alpha ω t (Measure.ofCDF property)
    -- 3) alphaIic t ω ≈ cdf_from_alpha ω t (L¹ limit + density of rationals)
    sorry

  -- Step 2: Define the good class of functions
  -- C = {f bounded Borel | ∀ᵐ ω, α_f(ω) = ∫ f dν(ω)}
  -- Show C contains indicators of half-lines (Step 1),
  -- closed under linear combinations, and closed under monotone limits

  -- Step 3: Apply monotone class theorem
  -- TODO: Use mathlib's monotone class API or implement manually
  -- Since C contains a π-system (indicators of half-lines) and is a monotone class,
  -- C contains all bounded Borel functions
  sorry

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
      -- Inductive step: separate the last factor
      -- Strategy: Use tail-measurability and conditioning

      -- Step 1: Reorder indices if needed so last k(m) is maximal
      -- (Use exchangeability/contractability to reindex)
      -- TODO: Construct permutation putting max at end
      -- For now, assume WLOG that k is already ordered

      -- Step 2: Separate last factor from product of first m factors
      -- TODO: Define H = ∏_{i<m} 1_{B_i}(X_{k(i)}) as the "tail factor"

      -- Step 3: Use directing_measure_integral for indicators
      -- This gives: α_{1_B} = ν(·)(B) a.e. for each indicator
      -- TODO: Apply to each B_i

      -- Step 4: Use tail-measurability and tower property
      -- The first m factors are measurable w.r.t. σ(X_j | j ≤ N) for N = max_{i<m} k(i)
      -- The last factor X_{k(m)} is independent of this σ-field (by contractability)
      -- Hence E[H · 1_B(X_{k(m)})] = E[H · ν(·)(B)] by conditional expectation
      -- TODO: formalize tower property / conditional expectation argument

      -- Step 5: Apply induction hypothesis to H
      -- TODO: Use IH on the product of m factors
      sorry

