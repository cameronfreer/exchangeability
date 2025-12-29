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
import Mathlib.Data.Finset.Sort
import Mathlib.Analysis.SpecialFunctions.Choose

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

/-- For each measurable set s, the map ω ↦ ν(ω)(s) is measurable.

This is the key measurability property needed for complete_from_directing_measure.
Uses monotone class theorem (π-λ theorem) - prove for intervals, extend to all Borel sets.
-/
lemma directing_measure_measurable
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ)
    (s : Set ℝ) (hs : MeasurableSet s) :
    Measurable (fun ω => directing_measure X hX_contract hX_meas hX_L2 ω s) := by
  classical
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

/-! ### L¹ Limit Uniqueness

The following lemma establishes that L¹ limits are unique up to a.e. equality.
This is used to prove the linearity lemmas below.
-/

/-- If a sequence converges in L¹ to two limits, they are a.e. equal.

This follows from the triangle inequality: ‖g - h‖₁ ≤ ‖g - f_n‖₁ + ‖f_n - h‖₁,
and both terms go to 0.
-/
lemma ae_eq_of_tendsto_L1 {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : ℕ → Ω → ℝ} {g h : Ω → ℝ}
    (_hf_meas : ∀ n, Measurable (f n))
    (_hg_meas : Measurable g) (_hh_meas : Measurable h)
    (hf_int : ∀ n, Integrable (f n) μ)
    (hg_int : Integrable g μ) (hh_int : Integrable h μ)
    (hfg : ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∫ ω, |f n ω - g ω| ∂μ < ε)
    (hfh : ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∫ ω, |f n ω - h ω| ∂μ < ε) :
    g =ᵐ[μ] h := by
  -- Strategy: show ∫|g - h| = 0 using squeeze argument

  have h_diff_int : Integrable (fun ω => g ω - h ω) μ := hg_int.sub hh_int
  have h_abs_int : Integrable (fun ω => |g ω - h ω|) μ := h_diff_int.abs

  have h_integral_zero : ∫ ω, |g ω - h ω| ∂μ = 0 := by
    by_contra h_ne
    have h_nonneg : 0 ≤ ∫ ω, |g ω - h ω| ∂μ := integral_nonneg (fun _ => abs_nonneg _)
    have h_pos : 0 < ∫ ω, |g ω - h ω| ∂μ := lt_of_le_of_ne h_nonneg (Ne.symm h_ne)

    set ε := (∫ ω, |g ω - h ω| ∂μ) / 2 with hε_def
    have hε_pos : ε > 0 := by linarith
    obtain ⟨N₁, hN₁⟩ := hfg ε hε_pos
    obtain ⟨N₂, hN₂⟩ := hfh ε hε_pos

    set n := max N₁ N₂ with _hn_def
    have hn₁ : n ≥ N₁ := le_max_left _ _
    have hn₂ : n ≥ N₂ := le_max_right _ _

    have h_triangle : ∀ ω, |g ω - h ω| ≤ |g ω - f n ω| + |f n ω - h ω| := fun ω => by
      calc |g ω - h ω| = |(g ω - f n ω) + (f n ω - h ω)| := by ring_nf
        _ ≤ |g ω - f n ω| + |f n ω - h ω| := abs_add_le _ _

    have h_sum_int : Integrable (fun ω => |g ω - f n ω| + |f n ω - h ω|) μ :=
      ((hg_int.sub (hf_int n)).abs).add (((hf_int n).sub hh_int).abs)
    have h_int_triangle : ∫ ω, |g ω - h ω| ∂μ ≤ ∫ ω, |g ω - f n ω| ∂μ + ∫ ω, |f n ω - h ω| ∂μ := by
      calc ∫ ω, |g ω - h ω| ∂μ
          ≤ ∫ ω, (|g ω - f n ω| + |f n ω - h ω|) ∂μ := by
            exact integral_mono h_abs_int h_sum_int (fun ω => h_triangle ω)
        _ = ∫ ω, |g ω - f n ω| ∂μ + ∫ ω, |f n ω - h ω| ∂μ := by
            exact integral_add (hg_int.sub (hf_int n)).abs ((hf_int n).sub hh_int).abs

    have h_symm : ∫ ω, |g ω - f n ω| ∂μ = ∫ ω, |f n ω - g ω| ∂μ := by
      congr 1; ext ω; rw [abs_sub_comm]

    have h_lt : ∫ ω, |g ω - h ω| ∂μ < 2 * ε := by
      calc ∫ ω, |g ω - h ω| ∂μ ≤ ∫ ω, |g ω - f n ω| ∂μ + ∫ ω, |f n ω - h ω| ∂μ := h_int_triangle
        _ = ∫ ω, |f n ω - g ω| ∂μ + ∫ ω, |f n ω - h ω| ∂μ := by rw [h_symm]
        _ < ε + ε := by linarith [hN₁ n hn₁, hN₂ n hn₂]
        _ = 2 * ε := by ring

    simp only [hε_def] at h_lt
    linarith

  have h_nonneg_ae : 0 ≤ᵐ[μ] fun ω => |g ω - h ω| := by
    filter_upwards with ω; exact abs_nonneg _
  have h_ae_zero : (fun ω => |g ω - h ω|) =ᵐ[μ] (0 : Ω → ℝ) := by
    rwa [← integral_eq_zero_iff_of_nonneg_ae h_nonneg_ae h_abs_int]
  filter_upwards [h_ae_zero] with ω hω
  simp only [Pi.zero_apply, abs_eq_zero, sub_eq_zero] at hω
  exact hω

/-! ### Linearity of L¹ Limits

The following lemmas establish that the L¹ limit functional from `weighted_sums_converge_L1`
is linear: if f and g have L¹ limits α_f and α_g, then f + g has limit α_f + α_g,
and c * f has limit c * α_f.

These are essential for the functional monotone class argument that extends from
indicators of half-lines to all bounded measurable functions.
-/

-- LINEARITY LEMMAS for the functional monotone class argument
--
-- These lemmas establish that the L¹ limit functional from `weighted_sums_converge_L1`
-- is linear and continuous. They are essential for extending the base case
-- (indicators of half-lines) to all bounded measurable functions.
--
-- PROOF STRATEGY: Each follows from:
-- 1. The Cesàro averages satisfy the algebraic identity
--    (e.g., (1/N) Σ c*f(X_k) = c * (1/N) Σ f(X_k))
-- 2. L¹ limits are unique up to a.e. equality
-- 3. Therefore the limits satisfy the same identity
--
-- These are routine but require careful handling of the existential .choose

/-- Scalar multiplication of L¹ limits: if f has L¹ limit α, then c*f has L¹ limit c*α. -/
lemma weighted_sums_converge_L1_smul
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ)
    (f : ℝ → ℝ) (hf_meas : Measurable f)
    (hf_bdd : ∃ M, ∀ x, |f x| ≤ M)
    (c : ℝ)
    (hcf_bdd : ∃ M, ∀ x, |c * f x| ≤ M) :
    let alpha := (weighted_sums_converge_L1 X hX_contract hX_meas hX_L2 f hf_meas hf_bdd).choose
    let alpha_c := (weighted_sums_converge_L1 X hX_contract hX_meas hX_L2
        (fun x => c * f x) (measurable_const.mul hf_meas) hcf_bdd).choose
    alpha_c =ᵐ[μ] fun ω => c * alpha ω := by
  intro alpha alpha_c
  -- Key: (1/m) * Σ c*f(X_k) = c * (1/m) * Σ f(X_k)
  -- So the Cesàro averages of c*f equal c times the Cesàro averages of f

  -- Get specs for both limits
  have h_spec := (weighted_sums_converge_L1 X hX_contract hX_meas hX_L2 f hf_meas hf_bdd).choose_spec
  have h_spec_c := (weighted_sums_converge_L1 X hX_contract hX_meas hX_L2
      (fun x => c * f x) (measurable_const.mul hf_meas) hcf_bdd).choose_spec

  have h_alpha_meas : Measurable alpha := h_spec.1
  have h_alpha_L1 : MemLp alpha 1 μ := h_spec.2.1
  have h_conv := h_spec.2.2

  have h_alpha_c_meas : Measurable alpha_c := h_spec_c.1
  have h_alpha_c_L1 : MemLp alpha_c 1 μ := h_spec_c.2.1
  have h_conv_c := h_spec_c.2.2

  -- Integrability
  have h_alpha_int : Integrable alpha μ := h_alpha_L1.integrable le_rfl
  have h_alpha_c_int : Integrable alpha_c μ := h_alpha_c_L1.integrable le_rfl
  have h_c_alpha_int : Integrable (fun ω => c * alpha ω) μ := h_alpha_int.const_mul c
  have h_diff_int : Integrable (fun ω => alpha_c ω - c * alpha ω) μ := h_alpha_c_int.sub h_c_alpha_int
  have h_abs_int : Integrable (fun ω => |alpha_c ω - c * alpha ω|) μ := h_diff_int.abs

  -- Key algebraic identity: avg of c*f = c * avg of f
  have h_avg_eq : ∀ n (m : ℕ), ∀ ω,
      (1 / (m : ℝ)) * ∑ k : Fin m, (c * f (X (n + k.val + 1) ω)) =
      c * ((1 / (m : ℝ)) * ∑ k : Fin m, f (X (n + k.val + 1) ω)) := by
    intro n m ω
    -- Pull c out of the sum: ∑ k, c * f(...) = c * ∑ k, f(...)
    rw [← Finset.mul_sum]
    ring

  -- Show ∫|alpha_c - c*alpha| = 0 by showing it can be made arbitrarily small
  have h_integral_zero : ∫ ω, |alpha_c ω - c * alpha ω| ∂μ = 0 := by
    by_contra h_ne
    have h_nonneg : 0 ≤ ∫ ω, |alpha_c ω - c * alpha ω| ∂μ := integral_nonneg (fun ω => abs_nonneg _)
    have h_pos : 0 < ∫ ω, |alpha_c ω - c * alpha ω| ∂μ := lt_of_le_of_ne h_nonneg (Ne.symm h_ne)

    -- Choose ε = (∫|alpha_c - c*alpha|) / 4
    set ε := (∫ ω, |alpha_c ω - c * alpha ω| ∂μ) / 4 with hε_def
    have hε_pos : ε > 0 := by linarith

    -- Get M₁ from h_conv_c (convergence of c*f averages to alpha_c)
    obtain ⟨M₁, hM₁⟩ := h_conv_c 0 ε hε_pos

    -- Get M₂ from h_conv (convergence of f averages to alpha)
    -- Need: ∫|avg_f - alpha| < ε / (|c| + 1) to handle scaling
    have hε' : ε / (|c| + 1) > 0 := div_pos hε_pos (by linarith [abs_nonneg c])
    obtain ⟨M₂, hM₂⟩ := h_conv 0 (ε / (|c| + 1)) hε'

    set m := max 1 (max M₁ M₂) with hm_def
    have hm_pos : m > 0 := Nat.lt_of_lt_of_le (by norm_num) (le_max_left _ _)
    have hm_ge_M₁ : m ≥ M₁ := le_trans (le_max_left _ _) (le_max_right _ _)
    have hm_ge_M₂ : m ≥ M₂ := le_trans (le_max_right _ _) (le_max_right _ _)

    -- From hM₁: ∫|avg_{c*f} - alpha_c| < ε
    specialize hM₁ m hm_ge_M₁
    -- From hM₂: ∫|avg_f - alpha| < ε / (|c| + 1)
    specialize hM₂ m hm_ge_M₂

    -- By triangle inequality:
    -- ∫|alpha_c - c*alpha| ≤ ∫|alpha_c - avg_{c*f}| + ∫|avg_{c*f} - c*alpha|
    --                      = ∫|alpha_c - avg_{c*f}| + ∫|c*(avg_f - alpha)|
    --                      ≤ ∫|alpha_c - avg_{c*f}| + |c| * ∫|avg_f - alpha|
    --                      < ε + |c| * (ε / (|c| + 1))
    --                      < ε + ε = 2ε = (∫|alpha_c - c*alpha|) / 2

    -- Simplify: at starting index 0, the sum starts at index 0 + k + 1 = k + 1
    simp only [zero_add] at hM₁ hM₂

    -- KEY ARGUMENT: By triangle inequality and h_avg_eq (avg_{c*f} = c * avg_f),
    -- ∫|alpha_c - c*alpha| ≤ ∫|alpha_c - avg_{c*f}| + |c| * ∫|avg_f - alpha|
    --                      < ε + |c| * (ε / (|c| + 1))
    --                      < ε + ε = 2ε = (∫|alpha_c - c*alpha|) / 2
    -- This is a contradiction, so ∫|alpha_c - c*alpha| = 0.

    -- The algebraic identity: avg_{c*f} = c * avg_f
    have _h_avg_eq' : ∀ ω,
        (1 / (m : ℝ)) * ∑ k : Fin m, (c * f (X (k.val + 1) ω)) =
        c * ((1 / (m : ℝ)) * ∑ k : Fin m, f (X (k.val + 1) ω)) := by
      intro ω; rw [← Finset.mul_sum]; ring

    -- The key bound: |c| * (ε / (|c| + 1)) < ε
    have _h_bound : |c| * (ε / (|c| + 1)) < ε := by
      have h1 : |c| / (|c| + 1) < 1 := by
        rw [div_lt_one (by linarith [abs_nonneg c])]
        linarith [abs_nonneg c]
      calc |c| * (ε / (|c| + 1)) = (|c| / (|c| + 1)) * ε := by ring
        _ < 1 * ε := by nlinarith [abs_nonneg c]
        _ = ε := one_mul ε

    -- Integrability of Cesàro averages
    have h_avg_cf_int : Integrable (fun ω => (1 / (m : ℝ)) * ∑ k : Fin m, (c * f (X (k.val + 1) ω))) μ := by
      apply Integrable.const_mul
      apply integrable_finset_sum
      intro k _
      obtain ⟨Mcf, hMcf⟩ := hcf_bdd
      apply Integrable.mono' (integrable_const Mcf)
      · exact (measurable_const.mul hf_meas).comp (hX_meas _) |>.aestronglyMeasurable
      · filter_upwards with ω; simp only [Real.norm_eq_abs]; exact hMcf _
    have h_avg_f_int : Integrable (fun ω => (1 / (m : ℝ)) * ∑ k : Fin m, f (X (k.val + 1) ω)) μ := by
      apply Integrable.const_mul
      apply integrable_finset_sum
      intro k _
      obtain ⟨Mf, hMf⟩ := hf_bdd
      apply Integrable.mono' (integrable_const Mf)
      · exact hf_meas.comp (hX_meas _) |>.aestronglyMeasurable
      · filter_upwards with ω; simp only [Real.norm_eq_abs]; exact hMf _

    -- Pointwise triangle inequality
    have h_pw : ∀ ω, |alpha_c ω - c * alpha ω| ≤
        |(1 / (m : ℝ)) * ∑ k : Fin m, (c * f (X (k.val + 1) ω)) - alpha_c ω| +
        |c| * |(1 / (m : ℝ)) * ∑ k : Fin m, f (X (k.val + 1) ω) - alpha ω| := fun ω => by
      have h_eq : c * alpha ω - alpha_c ω =
          (c * ((1 / (m : ℝ)) * ∑ k : Fin m, f (X (k.val + 1) ω)) - alpha_c ω) +
          c * (alpha ω - (1 / (m : ℝ)) * ∑ k : Fin m, f (X (k.val + 1) ω)) := by ring
      calc |alpha_c ω - c * alpha ω|
          = |c * alpha ω - alpha_c ω| := abs_sub_comm _ _
        _ = |(c * ((1 / (m : ℝ)) * ∑ k : Fin m, f (X (k.val + 1) ω)) - alpha_c ω) +
            c * (alpha ω - (1 / (m : ℝ)) * ∑ k : Fin m, f (X (k.val + 1) ω))| := by rw [h_eq]
        _ ≤ |c * ((1 / (m : ℝ)) * ∑ k : Fin m, f (X (k.val + 1) ω)) - alpha_c ω| +
            |c * (alpha ω - (1 / (m : ℝ)) * ∑ k : Fin m, f (X (k.val + 1) ω))| := abs_add_le _ _
        _ = |c * ((1 / (m : ℝ)) * ∑ k : Fin m, f (X (k.val + 1) ω)) - alpha_c ω| +
            |c| * |alpha ω - (1 / (m : ℝ)) * ∑ k : Fin m, f (X (k.val + 1) ω)| := by rw [abs_mul]
        _ = |(1 / (m : ℝ)) * ∑ k : Fin m, (c * f (X (k.val + 1) ω)) - alpha_c ω| +
            |c| * |(1 / (m : ℝ)) * ∑ k : Fin m, f (X (k.val + 1) ω) - alpha ω| := by
          rw [_h_avg_eq', abs_sub_comm]

    -- Integrate the pointwise bound
    have h_int_bound : ∫ ω, |alpha_c ω - c * alpha ω| ∂μ ≤
        ∫ ω, |(1 / (m : ℝ)) * ∑ k : Fin m, (c * f (X (k.val + 1) ω)) - alpha_c ω| ∂μ +
        |c| * ∫ ω, |(1 / (m : ℝ)) * ∑ k : Fin m, f (X (k.val + 1) ω) - alpha ω| ∂μ := by
      have h_sum_int : Integrable (fun ω =>
          |(1 / (m : ℝ)) * ∑ k : Fin m, (c * f (X (k.val + 1) ω)) - alpha_c ω| +
          |c| * |(1 / (m : ℝ)) * ∑ k : Fin m, f (X (k.val + 1) ω) - alpha ω|) μ :=
        ((h_avg_cf_int.sub h_alpha_c_int).abs).add ((h_avg_f_int.sub h_alpha_int).abs.const_mul _)
      calc ∫ ω, |alpha_c ω - c * alpha ω| ∂μ
          ≤ ∫ ω, (|(1 / (m : ℝ)) * ∑ k : Fin m, (c * f (X (k.val + 1) ω)) - alpha_c ω| +
              |c| * |(1 / (m : ℝ)) * ∑ k : Fin m, f (X (k.val + 1) ω) - alpha ω|) ∂μ :=
            integral_mono h_abs_int h_sum_int h_pw
        _ = ∫ ω, |(1 / (m : ℝ)) * ∑ k : Fin m, (c * f (X (k.val + 1) ω)) - alpha_c ω| ∂μ +
            |c| * ∫ ω, |(1 / (m : ℝ)) * ∑ k : Fin m, f (X (k.val + 1) ω) - alpha ω| ∂μ := by
          rw [integral_add (h_avg_cf_int.sub h_alpha_c_int).abs
              ((h_avg_f_int.sub h_alpha_int).abs.const_mul _)]
          rw [integral_mul_left]

    -- Final bound: < ε + |c| * (ε / (|c| + 1)) < 2ε
    calc ∫ ω, |alpha_c ω - c * alpha ω| ∂μ
        ≤ ∫ ω, |(1 / (m : ℝ)) * ∑ k : Fin m, (c * f (X (k.val + 1) ω)) - alpha_c ω| ∂μ +
          |c| * ∫ ω, |(1 / (m : ℝ)) * ∑ k : Fin m, f (X (k.val + 1) ω) - alpha ω| ∂μ := h_int_bound
      _ < ε + |c| * (ε / (|c| + 1)) := by linarith [hM₁, hM₂]
      _ < ε + ε := by linarith [_h_bound]
      _ = 2 * ε := by ring
      _ < 4 * ε := by linarith
      _ = ∫ ω, |alpha_c ω - c * alpha ω| ∂μ := by simp [hε_def]

  -- From ∫|alpha_c - c*alpha| = 0, conclude alpha_c =ᵐ c*alpha
  have h_nonneg_ae : 0 ≤ᵐ[μ] fun ω => |alpha_c ω - c * alpha ω| := by
    filter_upwards with ω
    exact abs_nonneg _
  have h_ae_zero : (fun ω => |alpha_c ω - c * alpha ω|) =ᵐ[μ] (0 : Ω → ℝ) := by
    rwa [← integral_eq_zero_iff_of_nonneg_ae h_nonneg_ae h_abs_int]
  filter_upwards [h_ae_zero] with ω hω
  simp only [Pi.zero_apply, abs_eq_zero, sub_eq_zero] at hω
  exact hω

/-- Addition of L¹ limits: if f has limit α_f and g has limit α_g, then f+g has limit α_f + α_g. -/
lemma weighted_sums_converge_L1_add
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ)
    (f g : ℝ → ℝ) (hf_meas : Measurable f) (hg_meas : Measurable g)
    (hf_bdd : ∃ M, ∀ x, |f x| ≤ M) (hg_bdd : ∃ M, ∀ x, |g x| ≤ M)
    (hfg_bdd : ∃ M, ∀ x, |f x + g x| ≤ M) :
    let alpha_f := (weighted_sums_converge_L1 X hX_contract hX_meas hX_L2 f hf_meas hf_bdd).choose
    let alpha_g := (weighted_sums_converge_L1 X hX_contract hX_meas hX_L2 g hg_meas hg_bdd).choose
    let alpha_fg := (weighted_sums_converge_L1 X hX_contract hX_meas hX_L2
        (fun x => f x + g x) (hf_meas.add hg_meas) hfg_bdd).choose
    alpha_fg =ᵐ[μ] fun ω => alpha_f ω + alpha_g ω := by
  intro alpha_f alpha_g alpha_fg

  -- Get convergence specs
  have h_spec_f := (weighted_sums_converge_L1 X hX_contract hX_meas hX_L2 f hf_meas hf_bdd).choose_spec
  have h_spec_g := (weighted_sums_converge_L1 X hX_contract hX_meas hX_L2 g hg_meas hg_bdd).choose_spec
  have h_spec_fg := (weighted_sums_converge_L1 X hX_contract hX_meas hX_L2
      (fun x => f x + g x) (hf_meas.add hg_meas) hfg_bdd).choose_spec

  have h_conv_f := h_spec_f.2.2
  have h_conv_g := h_spec_g.2.2
  have h_conv_fg := h_spec_fg.2.2

  -- Integrability
  have h_alpha_f_int : Integrable alpha_f μ := (h_spec_f.2.1).integrable le_rfl
  have h_alpha_g_int : Integrable alpha_g μ := (h_spec_g.2.1).integrable le_rfl
  have h_alpha_fg_int : Integrable alpha_fg μ := (h_spec_fg.2.1).integrable le_rfl
  have h_sum_int : Integrable (fun ω => alpha_f ω + alpha_g ω) μ := h_alpha_f_int.add h_alpha_g_int
  have h_diff_int : Integrable (fun ω => alpha_fg ω - (alpha_f ω + alpha_g ω)) μ := h_alpha_fg_int.sub h_sum_int
  have h_abs_int : Integrable (fun ω => |alpha_fg ω - (alpha_f ω + alpha_g ω)|) μ := h_diff_int.abs

  -- KEY ALGEBRAIC IDENTITY: (1/N) Σ (f+g)(X_k) = (1/N) Σ f(X_k) + (1/N) Σ g(X_k)
  have _h_avg_add : ∀ n (m : ℕ) ω,
      (1 / (m : ℝ)) * ∑ k : Fin m, ((f + g) (X (n + k.val + 1) ω)) =
      (1 / (m : ℝ)) * ∑ k : Fin m, f (X (n + k.val + 1) ω) +
      (1 / (m : ℝ)) * ∑ k : Fin m, g (X (n + k.val + 1) ω) := by
    intro n m ω
    simp only [Pi.add_apply, Finset.sum_add_distrib, mul_add]

  -- Show ∫|alpha_fg - (alpha_f + alpha_g)| = 0 by showing it can be made arbitrarily small
  have h_integral_zero : ∫ ω, |alpha_fg ω - (alpha_f ω + alpha_g ω)| ∂μ = 0 := by
    by_contra h_ne
    have h_nonneg : 0 ≤ ∫ ω, |alpha_fg ω - (alpha_f ω + alpha_g ω)| ∂μ := integral_nonneg (fun _ => abs_nonneg _)
    have h_pos : 0 < ∫ ω, |alpha_fg ω - (alpha_f ω + alpha_g ω)| ∂μ := lt_of_le_of_ne h_nonneg (Ne.symm h_ne)

    -- Choose ε = (∫|alpha_fg - (alpha_f + alpha_g)|) / 4
    set ε := (∫ ω, |alpha_fg ω - (alpha_f ω + alpha_g ω)| ∂μ) / 4 with hε_def
    have hε_pos : ε > 0 := by linarith

    -- Get M_fg, M_f, M_g from convergence
    obtain ⟨M_fg, hM_fg⟩ := h_conv_fg 0 ε hε_pos
    obtain ⟨M_f, hM_f⟩ := h_conv_f 0 ε hε_pos
    obtain ⟨M_g, hM_g⟩ := h_conv_g 0 ε hε_pos

    set m := max 1 (max M_fg (max M_f M_g)) with hm_def
    have hm_pos : m > 0 := Nat.lt_of_lt_of_le (by norm_num) (le_max_left _ _)
    have hm_ge_fg : m ≥ M_fg := le_trans (le_max_left _ _) (le_max_right _ _)
    have hm_ge_f : m ≥ M_f := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
    have hm_ge_g : m ≥ M_g := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)

    specialize hM_fg m hm_ge_fg
    specialize hM_f m hm_ge_f
    specialize hM_g m hm_ge_g

    simp only [zero_add] at hM_fg hM_f hM_g

    -- Integrability of Cesàro averages
    have h_avg_fg_int : Integrable (fun ω => (1 / (m : ℝ)) * ∑ k : Fin m, (f + g) (X (k.val + 1) ω)) μ := by
      apply Integrable.const_mul
      apply integrable_finset_sum
      intro k _
      obtain ⟨Mfg, hMfg⟩ := hfg_bdd
      apply Integrable.mono' (integrable_const Mfg)
      · exact (hf_meas.add hg_meas).comp (hX_meas _) |>.aestronglyMeasurable
      · filter_upwards with ω; simp only [Real.norm_eq_abs]; exact hMfg _
    have h_avg_f_int : Integrable (fun ω => (1 / (m : ℝ)) * ∑ k : Fin m, f (X (k.val + 1) ω)) μ := by
      apply Integrable.const_mul
      apply integrable_finset_sum
      intro k _
      obtain ⟨Mf, hMf⟩ := hf_bdd
      apply Integrable.mono' (integrable_const Mf)
      · exact hf_meas.comp (hX_meas _) |>.aestronglyMeasurable
      · filter_upwards with ω; simp only [Real.norm_eq_abs]; exact hMf _
    have h_avg_g_int : Integrable (fun ω => (1 / (m : ℝ)) * ∑ k : Fin m, g (X (k.val + 1) ω)) μ := by
      apply Integrable.const_mul
      apply integrable_finset_sum
      intro k _
      obtain ⟨Mg, hMg⟩ := hg_bdd
      apply Integrable.mono' (integrable_const Mg)
      · exact hg_meas.comp (hX_meas _) |>.aestronglyMeasurable
      · filter_upwards with ω; simp only [Real.norm_eq_abs]; exact hMg _

    -- Algebraic identity for this specific m
    have h_avg_eq : ∀ ω,
        (1 / (m : ℝ)) * ∑ k : Fin m, (f + g) (X (k.val + 1) ω) =
        (1 / (m : ℝ)) * ∑ k : Fin m, f (X (k.val + 1) ω) +
        (1 / (m : ℝ)) * ∑ k : Fin m, g (X (k.val + 1) ω) := fun ω => by
      simp only [Pi.add_apply, Finset.sum_add_distrib, mul_add]

    -- Pointwise triangle inequality
    have h_pw : ∀ ω, |alpha_fg ω - (alpha_f ω + alpha_g ω)| ≤
        |(1 / (m : ℝ)) * ∑ k : Fin m, (f + g) (X (k.val + 1) ω) - alpha_fg ω| +
        |(1 / (m : ℝ)) * ∑ k : Fin m, f (X (k.val + 1) ω) - alpha_f ω| +
        |(1 / (m : ℝ)) * ∑ k : Fin m, g (X (k.val + 1) ω) - alpha_g ω| := fun ω => by
      -- Rewrite using avg_{f+g} = avg_f + avg_g
      have h_rewrite : alpha_fg ω - (alpha_f ω + alpha_g ω) =
          -((1 / (m : ℝ)) * ∑ k : Fin m, (f + g) (X (k.val + 1) ω) - alpha_fg ω) +
          ((1 / (m : ℝ)) * ∑ k : Fin m, f (X (k.val + 1) ω) - alpha_f ω) +
          ((1 / (m : ℝ)) * ∑ k : Fin m, g (X (k.val + 1) ω) - alpha_g ω) := by
        rw [h_avg_eq]; ring
      calc |alpha_fg ω - (alpha_f ω + alpha_g ω)|
          = |-((1 / (m : ℝ)) * ∑ k : Fin m, (f + g) (X (k.val + 1) ω) - alpha_fg ω) +
            ((1 / (m : ℝ)) * ∑ k : Fin m, f (X (k.val + 1) ω) - alpha_f ω) +
            ((1 / (m : ℝ)) * ∑ k : Fin m, g (X (k.val + 1) ω) - alpha_g ω)| := by rw [h_rewrite]
        _ ≤ |-((1 / (m : ℝ)) * ∑ k : Fin m, (f + g) (X (k.val + 1) ω) - alpha_fg ω)| +
            |(1 / (m : ℝ)) * ∑ k : Fin m, f (X (k.val + 1) ω) - alpha_f ω +
             (1 / (m : ℝ)) * ∑ k : Fin m, g (X (k.val + 1) ω) - alpha_g ω| := abs_add_le _ _
        _ ≤ |-((1 / (m : ℝ)) * ∑ k : Fin m, (f + g) (X (k.val + 1) ω) - alpha_fg ω)| +
            |(1 / (m : ℝ)) * ∑ k : Fin m, f (X (k.val + 1) ω) - alpha_f ω| +
            |(1 / (m : ℝ)) * ∑ k : Fin m, g (X (k.val + 1) ω) - alpha_g ω| := by
          have := abs_add_le ((1 / (m : ℝ)) * ∑ k : Fin m, f (X (k.val + 1) ω) - alpha_f ω)
              ((1 / (m : ℝ)) * ∑ k : Fin m, g (X (k.val + 1) ω) - alpha_g ω)
          linarith
        _ = |(1 / (m : ℝ)) * ∑ k : Fin m, (f + g) (X (k.val + 1) ω) - alpha_fg ω| +
            |(1 / (m : ℝ)) * ∑ k : Fin m, f (X (k.val + 1) ω) - alpha_f ω| +
            |(1 / (m : ℝ)) * ∑ k : Fin m, g (X (k.val + 1) ω) - alpha_g ω| := by rw [abs_neg]

    -- Integrate the pointwise bound
    have h_int_bound : ∫ ω, |alpha_fg ω - (alpha_f ω + alpha_g ω)| ∂μ ≤
        ∫ ω, |(1 / (m : ℝ)) * ∑ k : Fin m, (f + g) (X (k.val + 1) ω) - alpha_fg ω| ∂μ +
        ∫ ω, |(1 / (m : ℝ)) * ∑ k : Fin m, f (X (k.val + 1) ω) - alpha_f ω| ∂μ +
        ∫ ω, |(1 / (m : ℝ)) * ∑ k : Fin m, g (X (k.val + 1) ω) - alpha_g ω| ∂μ := by
      have h_three_int : Integrable (fun ω =>
          |(1 / (m : ℝ)) * ∑ k : Fin m, (f + g) (X (k.val + 1) ω) - alpha_fg ω| +
          |(1 / (m : ℝ)) * ∑ k : Fin m, f (X (k.val + 1) ω) - alpha_f ω| +
          |(1 / (m : ℝ)) * ∑ k : Fin m, g (X (k.val + 1) ω) - alpha_g ω|) μ :=
        ((h_avg_fg_int.sub h_alpha_fg_int).abs.add (h_avg_f_int.sub h_alpha_f_int).abs).add
          (h_avg_g_int.sub h_alpha_g_int).abs
      calc ∫ ω, |alpha_fg ω - (alpha_f ω + alpha_g ω)| ∂μ
          ≤ ∫ ω, (|(1 / (m : ℝ)) * ∑ k : Fin m, (f + g) (X (k.val + 1) ω) - alpha_fg ω| +
              |(1 / (m : ℝ)) * ∑ k : Fin m, f (X (k.val + 1) ω) - alpha_f ω| +
              |(1 / (m : ℝ)) * ∑ k : Fin m, g (X (k.val + 1) ω) - alpha_g ω|) ∂μ :=
            integral_mono h_abs_int h_three_int h_pw
        _ = ∫ ω, |(1 / (m : ℝ)) * ∑ k : Fin m, (f + g) (X (k.val + 1) ω) - alpha_fg ω| ∂μ +
            ∫ ω, |(1 / (m : ℝ)) * ∑ k : Fin m, f (X (k.val + 1) ω) - alpha_f ω| ∂μ +
            ∫ ω, |(1 / (m : ℝ)) * ∑ k : Fin m, g (X (k.val + 1) ω) - alpha_g ω| ∂μ := by
          rw [integral_add, integral_add]
          · exact (h_avg_fg_int.sub h_alpha_fg_int).abs
          · exact (h_avg_f_int.sub h_alpha_f_int).abs
          · exact (h_avg_fg_int.sub h_alpha_fg_int).abs.add (h_avg_f_int.sub h_alpha_f_int).abs
          · exact (h_avg_g_int.sub h_alpha_g_int).abs

    -- Final bound: < ε + ε + ε = 3ε < 4ε
    calc ∫ ω, |alpha_fg ω - (alpha_f ω + alpha_g ω)| ∂μ
        ≤ ∫ ω, |(1 / (m : ℝ)) * ∑ k : Fin m, (f + g) (X (k.val + 1) ω) - alpha_fg ω| ∂μ +
          ∫ ω, |(1 / (m : ℝ)) * ∑ k : Fin m, f (X (k.val + 1) ω) - alpha_f ω| ∂μ +
          ∫ ω, |(1 / (m : ℝ)) * ∑ k : Fin m, g (X (k.val + 1) ω) - alpha_g ω| ∂μ := h_int_bound
      _ < ε + ε + ε := by linarith [hM_fg, hM_f, hM_g]
      _ = 3 * ε := by ring
      _ < 4 * ε := by linarith
      _ = ∫ ω, |alpha_fg ω - (alpha_f ω + alpha_g ω)| ∂μ := by simp [hε_def]

  -- From ∫|alpha_fg - (alpha_f + alpha_g)| = 0, conclude alpha_fg =ᵐ alpha_f + alpha_g
  have h_nonneg_ae : 0 ≤ᵐ[μ] fun ω => |alpha_fg ω - (alpha_f ω + alpha_g ω)| := by
    filter_upwards with ω
    exact abs_nonneg _
  have h_ae_zero : (fun ω => |alpha_fg ω - (alpha_f ω + alpha_g ω)|) =ᵐ[μ] (0 : Ω → ℝ) := by
    rwa [← integral_eq_zero_iff_of_nonneg_ae h_nonneg_ae h_abs_int]
  filter_upwards [h_ae_zero] with ω hω
  simp only [Pi.zero_apply, abs_eq_zero, sub_eq_zero] at hω
  exact hω

/-- Subtraction/complement: L¹ limit of (1 - f) is (1 - limit of f).

This is used for the complement step in the π-λ argument:
1_{Sᶜ} = 1 - 1_S, so the limit for the complement is 1 minus the limit for the set. -/
lemma weighted_sums_converge_L1_one_sub
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ)
    (f : ℝ → ℝ) (hf_meas : Measurable f)
    (hf_bdd : ∃ M, ∀ x, |f x| ≤ M)
    (hsub_bdd : ∃ M, ∀ x, |1 - f x| ≤ M) :
    let alpha := (weighted_sums_converge_L1 X hX_contract hX_meas hX_L2 f hf_meas hf_bdd).choose
    let alpha_1 := (weighted_sums_converge_L1 X hX_contract hX_meas hX_L2
        (fun _ => (1 : ℝ)) measurable_const ⟨1, fun _ => by norm_num⟩).choose
    let alpha_sub := (weighted_sums_converge_L1 X hX_contract hX_meas hX_L2
        (fun x => 1 - f x) (measurable_const.sub hf_meas) hsub_bdd).choose
    alpha_sub =ᵐ[μ] fun ω => alpha_1 ω - alpha ω := by
  intro alpha alpha_1 alpha_sub

  -- Note: alpha_1 = 1 a.e. can be shown by weighted_sums_converge_L1_const_one (defined below)
  -- For this proof, we work directly with alpha_1 and alpha_sub

  -- Get convergence specs
  have h_spec := (weighted_sums_converge_L1 X hX_contract hX_meas hX_L2 f hf_meas hf_bdd).choose_spec
  have h_spec_1 := (weighted_sums_converge_L1 X hX_contract hX_meas hX_L2
      (fun _ => (1 : ℝ)) measurable_const ⟨1, fun _ => by norm_num⟩).choose_spec
  have h_spec_sub := (weighted_sums_converge_L1 X hX_contract hX_meas hX_L2
      (fun x => 1 - f x) (measurable_const.sub hf_meas) hsub_bdd).choose_spec

  have h_conv := h_spec.2.2
  have h_conv_1 := h_spec_1.2.2
  have h_conv_sub := h_spec_sub.2.2

  -- Integrability
  have h_alpha_int : Integrable alpha μ := (h_spec.2.1).integrable le_rfl
  have h_alpha_1_int : Integrable alpha_1 μ := (h_spec_1.2.1).integrable le_rfl
  have h_alpha_sub_int : Integrable alpha_sub μ := (h_spec_sub.2.1).integrable le_rfl
  have h_diff_int : Integrable (fun ω => alpha_1 ω - alpha ω) μ := h_alpha_1_int.sub h_alpha_int
  have h_result_int : Integrable (fun ω => alpha_sub ω - (alpha_1 ω - alpha ω)) μ := h_alpha_sub_int.sub h_diff_int
  have h_abs_int : Integrable (fun ω => |alpha_sub ω - (alpha_1 ω - alpha ω)|) μ := h_result_int.abs

  -- KEY ALGEBRAIC IDENTITY: (1/N) Σ (1 - f)(X_k) = (1/N) Σ 1 - (1/N) Σ f(X_k)
  have _h_avg_sub : ∀ n (m : ℕ) ω, m > 0 →
      (1 / (m : ℝ)) * ∑ k : Fin m, (1 - f (X (n + k.val + 1) ω)) =
      (1 / (m : ℝ)) * ∑ k : Fin m, (1 : ℝ) -
      (1 / (m : ℝ)) * ∑ k : Fin m, f (X (n + k.val + 1) ω) := by
    intro n m ω _hm
    simp only [Finset.sum_sub_distrib, mul_sub]

  -- Show ∫|alpha_sub - (alpha_1 - alpha)| = 0
  have h_integral_zero : ∫ ω, |alpha_sub ω - (alpha_1 ω - alpha ω)| ∂μ = 0 := by
    by_contra h_ne
    have h_nonneg : 0 ≤ ∫ ω, |alpha_sub ω - (alpha_1 ω - alpha ω)| ∂μ := integral_nonneg (fun _ => abs_nonneg _)
    have h_pos : 0 < ∫ ω, |alpha_sub ω - (alpha_1 ω - alpha ω)| ∂μ := lt_of_le_of_ne h_nonneg (Ne.symm h_ne)

    set ε := (∫ ω, |alpha_sub ω - (alpha_1 ω - alpha ω)| ∂μ) / 4 with hε_def
    have hε_pos : ε > 0 := by linarith

    obtain ⟨M_sub, hM_sub⟩ := h_conv_sub 0 ε hε_pos
    obtain ⟨M_1, hM_1⟩ := h_conv_1 0 ε hε_pos
    obtain ⟨M, hM⟩ := h_conv 0 ε hε_pos

    set m := max 1 (max M_sub (max M_1 M)) with hm_def
    have _hm_pos : m > 0 := Nat.lt_of_lt_of_le (by norm_num) (le_max_left _ _)
    have hm_ge_sub : m ≥ M_sub := le_trans (le_max_left _ _) (le_max_right _ _)
    have hm_ge_1 : m ≥ M_1 := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
    have hm_ge : m ≥ M := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)

    specialize hM_sub m hm_ge_sub
    specialize hM_1 m hm_ge_1
    specialize hM m hm_ge

    simp only [zero_add] at hM_sub hM_1 hM

    -- Use the algebraic identity: A_{1-f} = A_1 - A_f
    -- So: alpha_sub - (alpha_1 - alpha)
    --   ≈ (alpha_sub - A_{1-f}) + (A_{1-f} - (alpha_1 - alpha))
    --   = (alpha_sub - A_{1-f}) + ((A_1 - A_f) - (alpha_1 - alpha))
    --   = (alpha_sub - A_{1-f}) + (A_1 - alpha_1) - (A_f - alpha)
    -- By triangle inequality, integrating gives < ε + ε + ε = 3ε < 4ε

    -- First establish the algebraic identity for this specific m
    have h_alg : ∀ ω, (1 / (m : ℝ)) * ∑ k : Fin m, (1 - f (X (k.val + 1) ω)) =
        (1 / (m : ℝ)) * ∑ _k : Fin m, (1 : ℝ) -
        (1 / (m : ℝ)) * ∑ k : Fin m, f (X (k.val + 1) ω) := fun ω => by
      simp only [Finset.sum_sub_distrib, mul_sub]

    -- Integrability of Cesàro averages (bounded functions on probability space are integrable)
    have h_avg_sub_int : Integrable (fun ω => (1 / (m : ℝ)) * ∑ k : Fin m, (1 - f (X (k.val + 1) ω))) μ := by
      apply Integrable.const_mul
      apply integrable_finset_sum
      intro k _
      obtain ⟨Ms, hMs⟩ := hsub_bdd
      apply Integrable.mono' (integrable_const Ms)
      · exact (measurable_const.sub hf_meas).comp (hX_meas _) |>.aestronglyMeasurable
      · filter_upwards with ω
        simp only [Real.norm_eq_abs]
        exact hMs _
    have h_avg_1_int : Integrable (fun ω => (1 / (m : ℝ)) * ∑ _k : Fin m, (1 : ℝ)) μ := integrable_const _
    have h_avg_f_int : Integrable (fun ω => (1 / (m : ℝ)) * ∑ k : Fin m, f (X (k.val + 1) ω)) μ := by
      apply Integrable.const_mul
      apply integrable_finset_sum
      intro k _
      obtain ⟨Mf, hMf⟩ := hf_bdd
      apply Integrable.mono' (integrable_const Mf)
      · exact hf_meas.comp (hX_meas _) |>.aestronglyMeasurable
      · filter_upwards with ω
        simp only [Real.norm_eq_abs]
        exact hMf _

    -- The key bound via triangle inequality
    have h_bound : ∫ ω, |alpha_sub ω - (alpha_1 ω - alpha ω)| ∂μ <
        ε + ε + ε := by
      -- Pointwise triangle inequality
      have h_pw : ∀ ω, |alpha_sub ω - (alpha_1 ω - alpha ω)| ≤
          |(1 / (m : ℝ)) * ∑ k : Fin m, (1 - f (X (k.val + 1) ω)) - alpha_sub ω| +
          |(1 / (m : ℝ)) * ∑ _k : Fin m, (1 : ℝ) - alpha_1 ω| +
          |(1 / (m : ℝ)) * ∑ k : Fin m, f (X (k.val + 1) ω) - alpha ω| := fun ω => by
        -- alpha_sub - (alpha_1 - alpha)
        --   = (alpha_sub - A_{1-f}) + (A_{1-f} - (alpha_1 - alpha))
        --   = (alpha_sub - A_{1-f}) + ((A_1 - A_f) - (alpha_1 - alpha))
        --   = (alpha_sub - A_{1-f}) + (A_1 - alpha_1) - (A_f - alpha)
        have h_rewrite : alpha_sub ω - (alpha_1 ω - alpha ω) =
            -(((1 / (m : ℝ)) * ∑ k : Fin m, (1 - f (X (k.val + 1) ω))) - alpha_sub ω) +
            (((1 / (m : ℝ)) * ∑ _k : Fin m, (1 : ℝ)) - alpha_1 ω) -
            (((1 / (m : ℝ)) * ∑ k : Fin m, f (X (k.val + 1) ω)) - alpha ω) := by
          rw [h_alg]; ring
        calc |alpha_sub ω - (alpha_1 ω - alpha ω)|
            = |-(((1 / (m : ℝ)) * ∑ k : Fin m, (1 - f (X (k.val + 1) ω))) - alpha_sub ω) +
              (((1 / (m : ℝ)) * ∑ _k : Fin m, (1 : ℝ)) - alpha_1 ω) -
              (((1 / (m : ℝ)) * ∑ k : Fin m, f (X (k.val + 1) ω)) - alpha ω)| := by rw [h_rewrite]
          _ ≤ |-(((1 / (m : ℝ)) * ∑ k : Fin m, (1 - f (X (k.val + 1) ω))) - alpha_sub ω)| +
              |(((1 / (m : ℝ)) * ∑ _k : Fin m, (1 : ℝ)) - alpha_1 ω) -
               (((1 / (m : ℝ)) * ∑ k : Fin m, f (X (k.val + 1) ω)) - alpha ω)| := abs_add_le _ _
          _ ≤ |-(((1 / (m : ℝ)) * ∑ k : Fin m, (1 - f (X (k.val + 1) ω))) - alpha_sub ω)| +
              |(((1 / (m : ℝ)) * ∑ _k : Fin m, (1 : ℝ)) - alpha_1 ω)| +
              |(((1 / (m : ℝ)) * ∑ k : Fin m, f (X (k.val + 1) ω)) - alpha ω)| := by
            have := abs_sub_le (((1 / (m : ℝ)) * ∑ _k : Fin m, (1 : ℝ)) - alpha_1 ω) 0
                (((1 / (m : ℝ)) * ∑ k : Fin m, f (X (k.val + 1) ω)) - alpha ω)
            simp only [sub_zero] at this
            linarith [abs_add_le (((1 / (m : ℝ)) * ∑ _k : Fin m, (1 : ℝ)) - alpha_1 ω)
                (-(((1 / (m : ℝ)) * ∑ k : Fin m, f (X (k.val + 1) ω)) - alpha ω))]
          _ = |(1 / (m : ℝ)) * ∑ k : Fin m, (1 - f (X (k.val + 1) ω)) - alpha_sub ω| +
              |(1 / (m : ℝ)) * ∑ _k : Fin m, (1 : ℝ) - alpha_1 ω| +
              |(1 / (m : ℝ)) * ∑ k : Fin m, f (X (k.val + 1) ω) - alpha ω| := by rw [abs_neg]

      -- Integrate the pointwise bound
      have h_int_bound : ∫ ω, |alpha_sub ω - (alpha_1 ω - alpha ω)| ∂μ ≤
          ∫ ω, |(1 / (m : ℝ)) * ∑ k : Fin m, (1 - f (X (k.val + 1) ω)) - alpha_sub ω| ∂μ +
          ∫ ω, |(1 / (m : ℝ)) * ∑ _k : Fin m, (1 : ℝ) - alpha_1 ω| ∂μ +
          ∫ ω, |(1 / (m : ℝ)) * ∑ k : Fin m, f (X (k.val + 1) ω) - alpha ω| ∂μ := by
        have h_sum_int : Integrable (fun ω =>
            |(1 / (m : ℝ)) * ∑ k : Fin m, (1 - f (X (k.val + 1) ω)) - alpha_sub ω| +
            |(1 / (m : ℝ)) * ∑ _k : Fin m, (1 : ℝ) - alpha_1 ω| +
            |(1 / (m : ℝ)) * ∑ k : Fin m, f (X (k.val + 1) ω) - alpha ω|) μ :=
          (((h_avg_sub_int.sub h_alpha_sub_int).abs).add ((h_avg_1_int.sub h_alpha_1_int).abs)).add
            ((h_avg_f_int.sub h_alpha_int).abs)
        calc ∫ ω, |alpha_sub ω - (alpha_1 ω - alpha ω)| ∂μ
            ≤ ∫ ω, (|(1 / (m : ℝ)) * ∑ k : Fin m, (1 - f (X (k.val + 1) ω)) - alpha_sub ω| +
                |(1 / (m : ℝ)) * ∑ _k : Fin m, (1 : ℝ) - alpha_1 ω| +
                |(1 / (m : ℝ)) * ∑ k : Fin m, f (X (k.val + 1) ω) - alpha ω|) ∂μ := by
              exact integral_mono h_abs_int h_sum_int h_pw
          _ = ∫ ω, |(1 / (m : ℝ)) * ∑ k : Fin m, (1 - f (X (k.val + 1) ω)) - alpha_sub ω| ∂μ +
              ∫ ω, |(1 / (m : ℝ)) * ∑ _k : Fin m, (1 : ℝ) - alpha_1 ω| ∂μ +
              ∫ ω, |(1 / (m : ℝ)) * ∑ k : Fin m, f (X (k.val + 1) ω) - alpha ω| ∂μ := by
            rw [integral_add, integral_add]
            · exact (h_avg_sub_int.sub h_alpha_sub_int).abs
            · exact (h_avg_1_int.sub h_alpha_1_int).abs
            · exact ((h_avg_sub_int.sub h_alpha_sub_int).abs).add ((h_avg_1_int.sub h_alpha_1_int).abs)
            · exact (h_avg_f_int.sub h_alpha_int).abs

      calc ∫ ω, |alpha_sub ω - (alpha_1 ω - alpha ω)| ∂μ
          ≤ ∫ ω, |(1 / (m : ℝ)) * ∑ k : Fin m, (1 - f (X (k.val + 1) ω)) - alpha_sub ω| ∂μ +
            ∫ ω, |(1 / (m : ℝ)) * ∑ _k : Fin m, (1 : ℝ) - alpha_1 ω| ∂μ +
            ∫ ω, |(1 / (m : ℝ)) * ∑ k : Fin m, f (X (k.val + 1) ω) - alpha ω| ∂μ := h_int_bound
        _ < ε + ε + ε := by linarith [hM_sub, hM_1, hM]

    -- But 3ε < 4ε = ∫|...| gives contradiction
    linarith

  -- Conclude alpha_sub =ᵐ alpha_1 - alpha
  have h_nonneg_ae : 0 ≤ᵐ[μ] fun ω => |alpha_sub ω - (alpha_1 ω - alpha ω)| := by
    filter_upwards with ω
    exact abs_nonneg _
  have h_ae_zero : (fun ω => |alpha_sub ω - (alpha_1 ω - alpha ω)|) =ᵐ[μ] (0 : Ω → ℝ) := by
    rwa [← integral_eq_zero_iff_of_nonneg_ae h_nonneg_ae h_abs_int]
  filter_upwards [h_ae_zero] with ω hω
  simp only [Pi.zero_apply, abs_eq_zero, sub_eq_zero] at hω
  exact hω

/-- The L¹ limit of the constant function 1 is 1 a.e.

This is immediate since the Cesàro average of constant 1 is exactly 1:
(1/N) Σ_k 1 = (1/N) * N = 1. -/
lemma weighted_sums_converge_L1_const_one
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ) :
    (weighted_sums_converge_L1 X hX_contract hX_meas hX_L2
        (fun _ => (1 : ℝ)) measurable_const ⟨1, fun _ => by norm_num⟩).choose
    =ᵐ[μ] fun _ => (1 : ℝ) := by
  -- (1/m) * m = 1 for all m > 0, so L¹ limit is exactly 1.
  let alpha := (weighted_sums_converge_L1 X hX_contract hX_meas hX_L2
      (fun _ => (1 : ℝ)) measurable_const ⟨1, fun _ => by norm_num⟩).choose
  have h_spec := (weighted_sums_converge_L1 X hX_contract hX_meas hX_L2
      (fun _ => (1 : ℝ)) measurable_const ⟨1, fun _ => by norm_num⟩).choose_spec
  have h_alpha_L1 : MemLp alpha 1 μ := h_spec.2.1
  have h_conv := h_spec.2.2

  -- Key: the Cesàro average of constant 1 equals 1 exactly for m > 0
  have h_avg_eq_one : ∀ n (m : ℕ), m > 0 →
      ∀ ω, (1 / (m : ℝ)) * ∑ k : Fin m, (fun _ => (1 : ℝ)) (X (n + k.val + 1) ω) = 1 := by
    intro n m hm ω
    simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul, mul_one]
    have hm_ne : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)
    field_simp

  -- Use h_conv at starting index 0
  have h_conv_0 := h_conv 0

  -- The integral ∫|1 - alpha| is constant in m (doesn't depend on m)
  -- but by h_conv, for any ε > 0, we can make ∫|A_m - alpha| < ε for large m
  -- Since A_m = 1 exactly, we have ∫|1 - alpha| < ε for any ε > 0
  -- Therefore ∫|1 - alpha| = 0, so alpha =ᵐ 1

  have h_alpha_int : Integrable alpha μ := h_alpha_L1.integrable le_rfl
  have h_one_int : Integrable (fun _ : Ω => (1 : ℝ)) μ := integrable_const 1
  have h_diff_int : Integrable (fun ω => 1 - alpha ω) μ := h_one_int.sub h_alpha_int
  have h_abs_int : Integrable (fun ω => |1 - alpha ω|) μ := h_diff_int.abs

  -- Goal: show ∫|1 - alpha| = 0
  -- Strategy: show ∫|1 - alpha| < ε for all ε > 0
  have h_integral_zero : ∫ ω, |1 - alpha ω| ∂μ = 0 := by
    by_contra h_ne
    have h_nonneg : 0 ≤ ∫ ω, |1 - alpha ω| ∂μ := integral_nonneg (fun ω => abs_nonneg _)
    have h_pos : 0 < ∫ ω, |1 - alpha ω| ∂μ := lt_of_le_of_ne h_nonneg (Ne.symm h_ne)
    -- Get M such that for m ≥ M, ∫|A_m - alpha| < (∫|1 - alpha|) / 2
    set ε := (∫ ω, |1 - alpha ω| ∂μ) / 2 with hε_def
    have hε_pos : ε > 0 := by linarith
    obtain ⟨M, hM⟩ := h_conv_0 ε hε_pos
    -- Choose m = max 1 M to ensure m ≥ M and m > 0
    set m := max 1 M with hm_def
    have hm_pos : m > 0 := Nat.lt_of_lt_of_le (by norm_num) (le_max_left _ _)
    have hm_ge_M : m ≥ M := le_max_right _ _
    specialize hM m hm_ge_M
    -- hM says: ∫|(1/m) * Σ_{k<m} 1 - alpha| < ε
    -- Since (1/m) * m = 1, this simplifies to ∫|1 - alpha| < ε
    -- Simplify hM: Σ_{k : Fin m} 1 = m, so (1/m) * m = 1
    have hm_ne : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm_pos)
    simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul, mul_one,
               one_div, inv_mul_cancel₀ hm_ne] at hM
    -- Now hM : ∫|1 - alpha| < ε = (∫|1 - alpha|) / 2
    -- This contradicts ∫|1 - alpha| > 0
    linarith

  -- Now use that ∫|f| = 0 and f ≥ 0 implies f =ᵐ 0
  have h_nonneg_ae : 0 ≤ᵐ[μ] fun ω => |1 - alpha ω| := by
    filter_upwards with ω
    exact abs_nonneg _
  have h_ae_zero : (fun ω => |1 - alpha ω|) =ᵐ[μ] (0 : Ω → ℝ) := by
    rwa [← integral_eq_zero_iff_of_nonneg_ae h_nonneg_ae h_abs_int]
  -- From |1 - alpha| =ᵐ 0, get 1 - alpha =ᵐ 0, i.e., alpha =ᵐ 1
  have h_diff_zero : (fun ω => 1 - alpha ω) =ᵐ[μ] (0 : Ω → ℝ) := by
    filter_upwards [h_ae_zero] with ω hω
    simp only [Pi.zero_apply, abs_eq_zero] at hω ⊢
    exact hω
  -- Therefore alpha =ᵐ 1
  filter_upwards [h_diff_zero] with ω hω
  simp only [Pi.zero_apply] at hω
  linarith [hω]

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
    -- The proof uses three key identities:
    -- 1. ∫ 1_{Iic t} dν = ν.real (Iic t) = (ν (Iic t)).toReal  [integral_indicator_one]
    -- 2. directing_measure ω (Iic t) = ofReal (F_ω t) where F_ω is the Stieltjes CDF
    --    [measure_stieltjesOfMeasurableRat_Iic]
    -- 3. F_ω t = alphaIic t ω a.e. (Stieltjes extension agrees with alphaIic)
    --
    -- Combined: ∫ 1_{Iic t} dν(ω) = (ofReal (F_ω t)).toReal = F_ω t = alphaIic t ω (a.e.)

    -- Step 1: Simplify the integral using integral_indicator_one
    have h_integral_eq : ∀ ω, ∫ x, (Set.Iic t).indicator (fun _ => (1 : ℝ)) x
        ∂(directing_measure X hX_contract hX_meas hX_L2 ω) =
        (directing_measure X hX_contract hX_meas hX_L2 ω (Set.Iic t)).toReal := by
      intro ω
      -- (fun _ => 1) = 1 for indicator purposes
      have h_eq : (Set.Iic t).indicator (fun _ : ℝ => (1 : ℝ)) = (Set.Iic t).indicator 1 := rfl
      rw [h_eq, integral_indicator_one measurableSet_Iic, Measure.real_def]

    -- Step 2: The directing measure value on Iic t equals F_ω t (Stieltjes CDF)
    -- This follows from measure_stieltjesOfMeasurableRat_Iic
    have h_meas_eq : ∀ ω, (directing_measure X hX_contract hX_meas hX_L2 ω (Set.Iic t)).toReal =
        (ProbabilityTheory.stieltjesOfMeasurableRat
          (alphaIicRat X hX_contract hX_meas hX_L2)
          (measurable_alphaIicRat X hX_contract hX_meas hX_L2) ω) t := by
      intro ω
      unfold directing_measure
      rw [ProbabilityTheory.measure_stieltjesOfMeasurableRat_Iic]
      -- ofReal applied to a nonneg value, then toReal gives back the value
      have h_nonneg : 0 ≤ (ProbabilityTheory.stieltjesOfMeasurableRat
            (alphaIicRat X hX_contract hX_meas hX_L2)
            (measurable_alphaIicRat X hX_contract hX_meas hX_L2) ω) t :=
        ProbabilityTheory.stieltjesOfMeasurableRat_nonneg _ _ _
      exact ENNReal.toReal_ofReal h_nonneg

    -- Step 3: The Stieltjes extension equals alphaIic a.e.
    -- This is the key technical step: stieltjesOfMeasurableRat agrees with alphaIicRat
    -- at rational points, and both are right-continuous, so they agree everywhere.
    have h_stieltjes_eq : ∀ᵐ ω ∂μ, alphaIic X hX_contract hX_meas hX_L2 t ω =
        (ProbabilityTheory.stieltjesOfMeasurableRat
          (alphaIicRat X hX_contract hX_meas hX_L2)
          (measurable_alphaIicRat X hX_contract hX_meas hX_L2) ω) t := by
      -- PROOF STRATEGY:
      -- The Stieltjes function at t is defined as ⨅ r > t (r ∈ ℚ), toRatCDF alphaIicRat ω r.
      -- At Stieltjes points (where IsRatStieltjesPoint holds), toRatCDF = alphaIicRat.
      -- We need to show that for a.e. ω, this infimum equals alphaIic t ω.
      --
      -- KEY STEPS:
      -- 1. For a.e. ω, alphaIic is monotone nondecreasing in t (from alphaIicCE_mono)
      -- 2. For a.e. ω, alphaIic q ω satisfies IsRatStieltjesPoint conditions on rationals
      -- 3. At such ω, the Stieltjes extension agrees with the original function
      --
      -- Since this is a deep result about conditional CDFs being right-continuous a.e.,
      -- we defer to the standard theory: stieltjesOfMeasurableRat handles the null set
      -- where pointwise properties fail by replacing with defaultRatCDF.
      --
      -- For the main theorem, what matters is that the integral identity holds a.e.,
      -- which follows from the construction. The detailed proof uses:
      -- - Countable intersection of a.e. monotonicity (alphaIicCE_mono)
      -- - Monotone convergence for conditional expectations at rationals
      -- - The fact that ℚ is countable, so properties holding a.e. for each q ∈ ℚ
      --   hold simultaneously for all q ∈ ℚ for a.e. ω

      -- PROOF STRUCTURE:
      -- 1. alphaIic t =ᵐ alphaIicCE t (by alphaIic_ae_eq_alphaIicCE)
      -- 2. alphaIicCE is monotone (by alphaIicCE_mono)
      -- 3. For a.e. ω, alphaIicRat ω is an IsRatStieltjesPoint:
      --    a. Monotone: from alphaIicCE_mono + countable intersection over ℚ×ℚ
      --    b. Limits at ±∞: from dominated convergence for condExp (indicator → 0 or 1)
      --    c. Right-continuity at rationals (iInf_rat_gt_eq): from monotone convergence
      -- 4. At Stieltjes points: stieltjesOfMeasurableRat = infimum of alphaIicRat
      -- 5. The infimum equals alphaIicCE t (by right-continuity of conditional CDF)
      -- 6. alphaIicCE t = alphaIic t a.e. (by identification lemma)
      --
      -- KEY TOOLS:
      -- - condExp_mono: μ[f|m] ≤ᵐ μ[g|m] when f ≤ᵐ g (Mathlib)
      -- - condExp_nonneg: 0 ≤ᵐ μ[f|m] when 0 ≤ᵐ f (Mathlib)
      -- - alphaIic_ae_eq_alphaIicCE: identification lemma (MainConvergence.lean)
      -- - alphaIicCE_mono: monotonicity a.e. (MainConvergence.lean)
      --
      -- For the a.e. result, we use that alphaIic bounds imply the function is a CDF a.e.
      have h_bdd := alphaIic_bound X hX_contract hX_meas hX_L2

      -- The key is that stieltjesOfMeasurableRat takes the infimum over rationals > t
      -- For a monotone bounded function, this infimum equals the right limit
      -- For a.e. ω, alphaIic is right-continuous (as a conditional CDF)

      -- ═══════════════════════════════════════════════════════════════════════════════
      -- IMPLEMENTATION: Show alphaIicRat ω is an IsRatStieltjesPoint for a.e. ω
      -- ═══════════════════════════════════════════════════════════════════════════════

      -- Step A: alphaIic = alphaIicCE a.e. at all rationals (countable intersection)
      have h_ae_eq_rat : ∀ᵐ ω ∂μ, ∀ q : ℚ,
          alphaIic X hX_contract hX_meas hX_L2 (q : ℝ) ω =
          alphaIicCE X hX_contract hX_meas hX_L2 (q : ℝ) ω := by
        rw [ae_all_iff]
        intro q
        exact alphaIic_ae_eq_alphaIicCE X hX_contract hX_meas hX_L2 (q : ℝ)

      -- Step B: Monotonicity on ℚ (from alphaIicCE_mono + countable intersection)
      have h_mono_rat : ∀ᵐ ω ∂μ, ∀ q₁ q₂ : ℚ, q₁ ≤ q₂ →
          alphaIicRat X hX_contract hX_meas hX_L2 ω q₁ ≤
          alphaIicRat X hX_contract hX_meas hX_L2 ω q₂ := by
        -- Countable intersection over all pairs (q₁, q₂) with q₁ ≤ q₂
        have h_pairs : ∀ q₁ q₂ : ℚ, q₁ ≤ q₂ → ∀ᵐ ω ∂μ,
            alphaIicCE X hX_contract hX_meas hX_L2 (q₁ : ℝ) ω ≤
            alphaIicCE X hX_contract hX_meas hX_L2 (q₂ : ℝ) ω := by
          intro q₁ q₂ hq
          exact alphaIicCE_mono X hX_contract hX_meas hX_L2 (q₁ : ℝ) (q₂ : ℝ) (by exact_mod_cast hq)
        -- Take countable intersection
        rw [ae_all_iff]; intro q₁
        rw [ae_all_iff]; intro q₂
        by_cases hq : q₁ ≤ q₂
        · filter_upwards [h_ae_eq_rat, h_pairs q₁ q₂ hq] with ω h_eq h_le _
          simp only [alphaIicRat]
          rw [h_eq q₁, h_eq q₂]
          exact h_le
        · filter_upwards with ω hq'
          exact absurd hq' hq

      -- Step C: Limit 0 at -∞ (from alphaIic_ae_tendsto_zero_at_bot)
      -- PROOF STRATEGY:
      -- 1. Use tendsto_atBot_ciInf: for monotone f with bdd below range, lim = inf
      -- 2. Show inf = 0: bounded below by 0, and alphaIicRat(-(n:ℤ)) → 0
      --
      -- KEY FACTS:
      -- - alphaIicRat(-(n:ℤ):ℚ) = alphaIic(-(n:ℝ)) by definition
      -- - h_int_lim: alphaIic(-(n:ℝ)) → 0 as n → ∞
      -- - h_mono: alphaIicRat is monotone
      -- - h_bdd: 0 ≤ alphaIicRat ≤ 1
      --
      -- MATHLIB: tendsto_atBot_ciInf, csInf_eq_bot_iff, or squeeze argument
      have h_tendsto_bot : ∀ᵐ ω ∂μ, Tendsto (alphaIicRat X hX_contract hX_meas hX_L2 ω) atBot (𝓝 0) := by
        filter_upwards [h_mono_rat, alphaIic_ae_tendsto_zero_at_bot X hX_contract hX_meas hX_L2,
                        h_ae_eq_rat] with ω h_mono h_int_lim _
        -- Bounded below by 0
        have h_bdd_below : BddBelow (Set.range (alphaIicRat X hX_contract hX_meas hX_L2 ω)) := by
          use 0; intro y ⟨q, hq⟩; rw [← hq]; exact (h_bdd (q : ℝ) ω).1
        -- By tendsto_atBot_ciInf, limit = infimum
        have h_lim := tendsto_atBot_ciInf h_mono h_bdd_below
        -- Show infimum = 0:
        -- 1. 0 ≤ inf (0 is lower bound)
        -- 2. inf ≤ 0: alphaIicRat(-(n:ℤ)) = alphaIic(-(n:ℝ)) → 0, so inf ≤ liminf = 0
        -- Key: alphaIicRat(-(n:ℤ):ℚ) = alphaIic(-(n:ℝ)) by definition of alphaIicRat
        have h_inf_eq : ⨅ q : ℚ, alphaIicRat X hX_contract hX_meas hX_L2 ω q = 0 := by
          -- Key: alphaIicRat(-(n:ℤ)) = alphaIic(-(n:ℝ)) by definition
          have h_int_eq : ∀ n : ℕ, alphaIicRat X hX_contract hX_meas hX_L2 ω (-(n : ℤ) : ℚ) =
              alphaIic X hX_contract hX_meas hX_L2 (-(n : ℝ)) ω := by
            intro n; simp only [alphaIicRat]; congr 1
            simp only [Int.cast_natCast, Rat.cast_neg, Rat.cast_natCast]
          -- h_int_lim in terms of alphaIicRat: alphaIicRat(-(n:ℤ)) → 0
          have h_rat_lim : Tendsto (fun n : ℕ => alphaIicRat X hX_contract hX_meas hX_L2 ω
              (-(n : ℤ) : ℚ)) atTop (𝓝 0) := by
            convert h_int_lim using 1; ext n; exact h_int_eq n
          -- The sequence -(n:ℤ) tends to atBot in ℚ as n → ∞
          have h_neg_tendsto : Tendsto (fun n : ℕ => (-(n : ℤ) : ℚ)) atTop atBot := by
            simp only [Int.cast_natCast]
            exact tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop
          -- Compose: alphaIicRat along -(n:ℤ) → iInf (by h_lim.comp h_neg_tendsto)
          have h_lim_seq := h_lim.comp h_neg_tendsto
          -- Two limits for same sequence: 0 and iInf
          -- By uniqueness of limits in T2 space: iInf = 0
          exact tendsto_nhds_unique h_lim_seq h_rat_lim
        rw [h_inf_eq] at h_lim; exact h_lim

      -- Step D: Limit 1 at +∞ (symmetric to Step C)
      -- PROOF STRATEGY: Use tendsto_atTop_ciSup, show sup = 1
      have h_tendsto_top : ∀ᵐ ω ∂μ, Tendsto (alphaIicRat X hX_contract hX_meas hX_L2 ω) atTop (𝓝 1) := by
        filter_upwards [h_mono_rat, alphaIic_ae_tendsto_one_at_top X hX_contract hX_meas hX_L2,
                        h_ae_eq_rat] with ω h_mono h_int_lim _
        -- Bounded above by 1
        have h_bdd_above : BddAbove (Set.range (alphaIicRat X hX_contract hX_meas hX_L2 ω)) := by
          use 1; intro y ⟨q, hq⟩; rw [← hq]; exact (h_bdd (q : ℝ) ω).2
        -- By tendsto_atTop_ciSup, limit = supremum
        have h_lim := tendsto_atTop_ciSup h_mono h_bdd_above
        -- Show supremum = 1:
        -- 1. sup ≤ 1 (1 is upper bound)
        -- 2. 1 ≤ sup: alphaIicRat(n:ℤ) = alphaIic(n:ℝ) → 1, so limsup ≤ sup
        -- Key: alphaIicRat(n:ℤ:ℚ) = alphaIic(n:ℝ) by definition
        have h_sup_eq : ⨆ q : ℚ, alphaIicRat X hX_contract hX_meas hX_L2 ω q = 1 := by
          -- Key: alphaIicRat(n:ℤ) = alphaIic(n:ℝ) by definition
          have h_int_eq : ∀ n : ℕ, alphaIicRat X hX_contract hX_meas hX_L2 ω ((n : ℤ) : ℚ) =
              alphaIic X hX_contract hX_meas hX_L2 (n : ℝ) ω := by
            intro n; simp only [alphaIicRat, Int.cast_natCast, Rat.cast_natCast]
          -- h_int_lim in terms of alphaIicRat: alphaIicRat(n:ℤ) → 1
          have h_rat_lim : Tendsto (fun n : ℕ => alphaIicRat X hX_contract hX_meas hX_L2 ω
              ((n : ℤ) : ℚ)) atTop (𝓝 1) := by
            simp only [h_int_eq]; exact h_int_lim
          -- The sequence (n:ℤ) tends to atTop in ℚ as n → ∞
          have h_pos_tendsto : Tendsto (fun n : ℕ => ((n : ℤ) : ℚ)) atTop atTop :=
            tendsto_natCast_atTop_atTop.comp tendsto_natCast_atTop_atTop
          -- Compose: alphaIicRat along (n:ℤ) → iSup (by h_lim.comp h_pos_tendsto)
          have h_lim_seq := h_lim.comp h_pos_tendsto
          -- Two limits for same sequence: 1 and iSup
          -- By uniqueness of limits in T2 space: iSup = 1
          exact tendsto_nhds_unique h_lim_seq h_rat_lim
        rw [h_sup_eq] at h_lim; exact h_lim

      -- Step E: Right-continuity at each rational (⨅ r > q, f r = f q)
      --
      -- PROOF STRATEGY:
      -- alphaIicCE(t, ω) = μ[1_{Iic t} | tailSigma](ω) is a conditional CDF
      -- Conditional CDFs satisfy right-continuity a.e. by kernel disintegration theory
      --
      -- KEY MATHLIB LEMMAS:
      -- - IsRatCondKernelCDF.iInf_rat_gt_eq: conditional kernel CDFs are right-cont a.e.
      -- - Monotone.tendsto_nhdsGT: monotone functions have right limits = infimum
      --
      -- PROOF OUTLINE:
      -- 1. alphaIicCE corresponds to a conditional kernel CDF structure
      -- 2. By IsRatCondKernelCDF.iInf_rat_gt_eq, right-continuity holds a.e.
      -- 3. Transfer via alphaIic =ᵐ alphaIicCE at rationals
      have h_right_cont : ∀ᵐ ω ∂μ, ∀ q : ℚ,
          ⨅ r : Set.Ioi q, alphaIicRat X hX_contract hX_meas hX_L2 ω r =
          alphaIicRat X hX_contract hX_meas hX_L2 ω q := by
        -- PROOF STRATEGY:
        -- For a monotone bounded function f : ℚ → [0,1], right-continuity at q means
        -- ⨅_{r > q} f(r) = f(q). We prove this using:
        --
        -- 1. The lower bound f(q) ≤ ⨅_{r > q} f(r) holds by monotonicity.
        -- 2. For the upper bound, we use dominated convergence for conditional expectations:
        --    - For r_n = q + 1/(n+1) ∈ ℚ, the indicators 1_{Iic r_n} ↘ 1_{Iic q} pointwise
        --    - By dominated convergence: E[1_{Iic r_n}(X_0) | G] → E[1_{Iic q}(X_0) | G] in L¹
        --    - Since the sequence is monotone decreasing, L¹ convergence implies a.e. convergence
        --    - Therefore alphaIicCE(r_n) → alphaIicCE(q) a.e.
        -- 3. Since alphaIic = alphaIicCE a.e. at rationals, the result transfers.
        --
        -- TECHNICAL DETAIL: The key mathlib lemma is tendsto_condExpL1_of_dominated_convergence
        -- combined with the fact that monotone L¹-convergent sequences converge a.e.
        --
        -- For now, we document this approach and mark as requiring dominated convergence.
        -- The implementation requires setting up the tailSigma machinery for condexp.
        --
        -- SIMPLIFICATION: Since alphaIicRat is defined via stieltjesOfMeasurableRat
        -- applied to the same underlying data, the right-continuity follows from
        -- the construction of Stieltjes functions which are right-continuous by definition.
        --
        -- The key insight is that at IsRatStieltjesPoint, the stieltjes regularization
        -- agrees with the input function, and the input function (alphaIicRat) inherits
        -- right-continuity from the conditional expectation structure.
        rw [ae_all_iff]
        intro q
        -- For this fixed q, we need a.e. right-continuity of alphaIicCE at q
        -- This follows from dominated convergence for conditional expectations:
        -- - indIic(q + 1/n) ↘ indIic(q) pointwise
        -- - By dominated convergence: E[indIic(q + 1/n) | G] → E[indIic(q) | G] in L¹
        -- - Monotone L¹-convergent sequences converge a.e.
        have h_CE_right_cont_q : ∀ᵐ ω ∂μ,
            ⨅ r : Set.Ioi q, alphaIicCE X hX_contract hX_meas hX_L2 (r : ℝ) ω =
            alphaIicCE X hX_contract hX_meas hX_L2 (q : ℝ) ω := by
          -- SETUP: Tail σ-algebra infrastructure
          have hm_le : TailSigma.tailSigma X ≤ (inferInstance : MeasurableSpace Ω) :=
            TailSigma.tailSigma_le X hX_meas
          haveI : Fact (TailSigma.tailSigma X ≤ (inferInstance : MeasurableSpace Ω)) := ⟨hm_le⟩
          -- SigmaFinite via instances
          haveI : SigmaFinite (μ.trim hm_le) := inferInstance

          -- Define sequence r_n = q + 1/(n+1) → q from above
          let r : ℕ → ℚ := fun n => q + 1 / ((n : ℚ) + 1)
          -- r n > q as rationals
          have hr_pos_rat : ∀ n, q < r n := fun n => by
            simp only [r]
            have h1 : (0 : ℚ) < (n : ℚ) + 1 := by positivity
            linarith [one_div_pos.mpr h1]
          -- r n > q as reals
          have hr_pos : ∀ n, (q : ℝ) < (r n : ℝ) := fun n => by
            exact_mod_cast hr_pos_rat n

          have hr_tendsto : Tendsto (fun n => (r n : ℝ)) atTop (𝓝 (q : ℝ)) := by
            simp only [r, Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_natCast]
            have h1 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
              tendsto_one_div_add_atTop_nhds_zero_nat
            simpa using tendsto_const_nhds.add h1

          -- Define functions f_n = alphaIicCE(r_n) and F = alphaIicCE(q)
          let f : ℕ → Ω → ℝ := fun n => alphaIicCE X hX_contract hX_meas hX_L2 (r n : ℝ)
          let F : Ω → ℝ := alphaIicCE X hX_contract hX_meas hX_L2 (q : ℝ)

          -- Integrability
          have hf_int : ∀ n, Integrable (f n) μ := fun _ => integrable_condExp
          have hF_int : Integrable F μ := integrable_condExp

          -- F ≤ f_n a.e.
          have hf_bound : ∀ᵐ ω ∂μ, ∀ n, F ω ≤ f n ω := by
            have h : ∀ n, ∀ᵐ ω ∂μ, F ω ≤ f n ω := fun n =>
              alphaIicCE_mono X hX_contract hX_meas hX_L2 (q : ℝ) (r n : ℝ) (le_of_lt (hr_pos n))
            rw [ae_all_iff]; exact h

          -- f_n is antitone a.e.
          have hf_antitone : ∀ᵐ ω ∂μ, Antitone (fun n => f n ω) := by
            have h_r_anti : ∀ m n, m ≤ n → (r n : ℝ) ≤ (r m : ℝ) := fun m n hmn => by
              simp only [r, Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_natCast]
              have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
              have hmn' : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by
                have : (m : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hmn
                linarith
              have : 1 / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) := one_div_le_one_div_of_le hm1 hmn'
              linarith
            have h_mono_mn : ∀ m n, m ≤ n → ∀ᵐ ω ∂μ, f n ω ≤ f m ω := fun m n hmn =>
              alphaIicCE_mono X hX_contract hX_meas hX_L2 (r n : ℝ) (r m : ℝ) (h_r_anti m n hmn)
            -- Antitone means: ∀ m ≤ n, f n ≤ f m
            -- Use countable intersection over pairs
            have h_ae_pairs : ∀ᵐ ω ∂μ, ∀ m n : ℕ, m ≤ n → f n ω ≤ f m ω := by
              rw [ae_all_iff]; intro m
              rw [ae_all_iff]; intro n
              by_cases hmn : m ≤ n
              · filter_upwards [h_mono_mn m n hmn] with ω hω _; exact hω
              · filter_upwards with ω h; exact absurd h hmn
            filter_upwards [h_ae_pairs] with ω hω
            exact fun m n hmn => hω m n hmn

          -- Integral convergence via DCT: ∫ f_n → ∫ F
          have hf_int_tendsto : Tendsto (fun n => ∫ ω, f n ω ∂μ) atTop (𝓝 (∫ ω, F ω ∂μ)) := by
            -- Define indicators
            let ind : ℝ → Ω → ℝ := fun t ω => Set.indicator (Set.Iic t) (fun _ => (1 : ℝ)) (X 0 ω)
            -- By integral_condExp: ∫ f_n = ∫ ind (r n)
            have h_eq_n : ∀ n, ∫ ω, f n ω ∂μ = ∫ ω, ind (r n : ℝ) ω ∂μ := fun n => by
              simp only [f, alphaIicCE, ind]
              exact integral_condExp hm_le
            have h_eq_F : ∫ ω, F ω ∂μ = ∫ ω, ind (q : ℝ) ω ∂μ := by
              simp only [F, alphaIicCE, ind]
              exact integral_condExp hm_le
            simp_rw [h_eq_n, h_eq_F]
            -- DCT: indicators bounded by 1, converge pointwise
            apply tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
            · -- AEStronglyMeasurable
              intro n; simp only [ind]
              exact ((measurable_const.indicator measurableSet_Iic).comp (hX_meas 0)).aestronglyMeasurable
            · -- Bound integrable
              exact integrable_const 1
            · -- Bound holds a.e.
              intro n; apply ae_of_all; intro ω
              simp only [ind, Set.indicator]; split_ifs <;> norm_num
            · -- Pointwise convergence
              apply ae_of_all; intro ω
              simp only [ind, Set.indicator]
              by_cases hx : X 0 ω ≤ q
              · -- X 0 ω ≤ q: always in Iic (r n) since q < r n
                have h : ∀ n, X 0 ω ≤ (r n : ℝ) := fun n =>
                  le_of_lt (lt_of_le_of_lt hx (hr_pos n))
                simp only [Set.mem_Iic, hx, h, ite_true]
                exact tendsto_const_nhds
              · -- X 0 ω > q: eventually not in Iic (r n)
                push_neg at hx
                simp only [Set.mem_Iic, not_le.mpr hx, ite_false]
                refine tendsto_const_nhds.congr' ?_
                -- Find N such that for n ≥ N, r n < X 0 ω
                have h_event : ∀ᶠ n in atTop, (r n : ℝ) < X 0 ω :=
                  hr_tendsto.eventually (Iio_mem_nhds hx)
                rw [Filter.eventually_atTop] at h_event
                obtain ⟨N, hN⟩ := h_event
                rw [Filter.EventuallyEq, Filter.eventually_atTop]
                use N; intro n hn
                have hlt : (r n : ℝ) < X 0 ω := hN n hn
                have : ¬(X 0 ω ≤ (r n : ℝ)) := not_le.mpr hlt
                simp [this]

          -- A.E. convergence via tendsto_of_integral_tendsto_of_antitone
          have hf_ae_tendsto : ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop (𝓝 (F ω)) :=
            tendsto_of_integral_tendsto_of_antitone hf_int hF_int hf_int_tendsto hf_antitone hf_bound

          -- ⨅_n f_n = F a.e. (by tendsto_atTop_ciInf + tendsto_nhds_unique)
          have h_ciInf_eq : ∀ᵐ ω ∂μ, ⨅ n, f n ω = F ω := by
            filter_upwards [hf_ae_tendsto, hf_antitone, hf_bound] with ω hω_tend hω_anti hω_bdd
            have h_bdd : BddBelow (Set.range fun n => f n ω) := ⟨F ω, by
              intro x hx; obtain ⟨n, rfl⟩ := hx; exact hω_bdd n⟩
            exact tendsto_nhds_unique (tendsto_atTop_ciInf hω_anti h_bdd) hω_tend

          -- Transfer from sequence {r_n} to all rationals > q
          -- Key: for any s > q in ℚ, there exists n with r_n < s, so ⨅_n ≤ ⨅_{s > q}
          have h_ae_mono_CE : ∀ᵐ ω ∂μ, ∀ s t : ℚ, s ≤ t →
              alphaIicCE X hX_contract hX_meas hX_L2 (s : ℝ) ω ≤
              alphaIicCE X hX_contract hX_meas hX_L2 (t : ℝ) ω := by
            have h : ∀ s t : ℚ, s ≤ t → ∀ᵐ ω ∂μ,
                alphaIicCE X hX_contract hX_meas hX_L2 (s : ℝ) ω ≤
                alphaIicCE X hX_contract hX_meas hX_L2 (t : ℝ) ω := fun s t hst =>
              alphaIicCE_mono X hX_contract hX_meas hX_L2 (s : ℝ) (t : ℝ) (by exact_mod_cast hst)
            rw [ae_all_iff]; intro s
            rw [ae_all_iff]; intro t
            by_cases hst : s ≤ t
            · filter_upwards [h s t hst] with ω hω _; exact hω
            · filter_upwards with ω hmn; exact absurd hmn hst

          -- Combine: show equality for both directions
          filter_upwards [h_ciInf_eq, hf_bound, h_ae_mono_CE] with ω h_eq hω_bdd hω_mono
          apply le_antisymm
          · -- ⨅_{s > q} ≤ ⨅_n f_n = F
            -- The infimum over r_n is ≥ infimum over all s > q since r_n ∈ Ioi q
            calc ⨅ s : Set.Ioi q, alphaIicCE X hX_contract hX_meas hX_L2 (s : ℝ) ω
                ≤ ⨅ n, f n ω := by
                  apply le_ciInf; intro n
                  -- r n is in Ioi q, so we can use it as a witness
                  have h_bdd_below : BddBelow (Set.range fun s : Set.Ioi q =>
                      alphaIicCE X hX_contract hX_meas hX_L2 (s : ℝ) ω) :=
                    ⟨F ω, fun x ⟨⟨s, hs⟩, hx⟩ => hx ▸ hω_mono q s (le_of_lt hs)⟩
                  exact ciInf_le h_bdd_below ⟨r n, hr_pos_rat n⟩
              _ = F ω := h_eq
          · -- F ≤ ⨅_{s > q}
            apply le_ciInf
            intro ⟨s, hs⟩
            -- Since r_n → q and s > q, ∃ N with r_N < s
            have hs_real : (q : ℝ) < (s : ℝ) := by exact_mod_cast hs
            have h_event : ∀ᶠ n in atTop, (r n : ℝ) < (s : ℝ) :=
              hr_tendsto.eventually (Iio_mem_nhds hs_real)
            rw [Filter.eventually_atTop] at h_event
            obtain ⟨N, hN⟩ := h_event
            -- alphaIicCE(s) ω ≥ f_N ω = alphaIicCE(r_N) ω ≥ ⨅_n f_n ω = F ω
            have hN_lt : (r N : ℝ) < (s : ℝ) := hN N le_rfl
            calc alphaIicCE X hX_contract hX_meas hX_L2 (s : ℝ) ω
                ≥ alphaIicCE X hX_contract hX_meas hX_L2 (r N : ℝ) ω :=
                    hω_mono (r N) s (le_of_lt (by exact_mod_cast hN_lt))
              _ = f N ω := rfl
              _ ≥ ⨅ n, f n ω := ciInf_le ⟨F ω, fun x ⟨n, hx⟩ => hx ▸ hω_bdd n⟩ N
              _ = F ω := h_eq
        -- Add right-continuity to filter_upwards
        filter_upwards [h_mono_rat, h_ae_eq_rat, h_CE_right_cont_q] with ω h_mono h_eq h_rc_CE
        -- Lower bound by monotonicity
        have h_le : alphaIicRat X hX_contract hX_meas hX_L2 ω q ≤
            ⨅ r : Set.Ioi q, alphaIicRat X hX_contract hX_meas hX_L2 ω r := by
          apply le_ciInf; intro ⟨r, hr⟩; simp only [alphaIicRat]
          exact h_mono q r (le_of_lt hr)
        -- Upper bound: use h_rc_CE and h_eq to transfer to alphaIicRat
        have h_ge : ⨅ r : Set.Ioi q, alphaIicRat X hX_contract hX_meas hX_L2 ω r ≤
            alphaIicRat X hX_contract hX_meas hX_L2 ω q := by
          -- h_rc_CE: ⨅_{r > q} alphaIicCE(r) = alphaIicCE(q)
          -- h_eq: alphaIic(r) = alphaIicCE(r) for all r ∈ ℚ
          -- alphaIicRat is defined as alphaIic on ℚ
          -- First show the infimums are equal
          have h_inf_eq : ⨅ r : Set.Ioi q, alphaIicRat X hX_contract hX_meas hX_L2 ω r =
              ⨅ r : Set.Ioi q, alphaIicCE X hX_contract hX_meas hX_L2 (r.val : ℝ) ω := by
            apply iInf_congr; intro ⟨r, hr⟩
            simp only [alphaIicRat, Subtype.coe_mk]; exact h_eq r
          rw [h_inf_eq, h_rc_CE]
          simp only [alphaIicRat]; exact (h_eq q).symm.le
        exact le_antisymm h_ge h_le

      -- Step F: Combine to show IsRatStieltjesPoint a.e.
      have h_is_stieltjes : ∀ᵐ ω ∂μ, ProbabilityTheory.IsRatStieltjesPoint
          (alphaIicRat X hX_contract hX_meas hX_L2) ω := by
        filter_upwards [h_mono_rat, h_tendsto_bot, h_tendsto_top, h_right_cont]
          with ω h_mono h_bot h_top h_rc
        -- Constructor order: mono, atTop_one, atBot_zero, iInf_rat_gt_eq
        exact ⟨h_mono, h_top, h_bot, h_rc⟩

      -- Step G: At IsRatStieltjesPoint, stieltjes = infimum = alphaIic
      --
      -- PROOF STRATEGY:
      -- By StieltjesFunction.iInf_rat_gt_eq: F t = ⨅ r > t (r ∈ ℚ), F r
      -- At Stieltjes points, toRatCDF = alphaIicRat, so F r = alphaIic (r:ℝ)
      -- Thus: F t = ⨅ r > t (r ∈ ℚ), alphaIic (r:ℝ)
      -- Need: alphaIic t = ⨅ r > t (r ∈ ℚ), alphaIic (r:ℝ) (right-continuity of alphaIic)
      --
      -- For this to work, we need:
      -- 1. alphaIic is a.e. monotone (from alphaIic_ae_eq_alphaIicCE + alphaIicCE_mono)
      -- 2. alphaIic is right-continuous (infimum over rationals = value)
      --
      -- At IsRatStieltjesPoint ω:
      -- - stieltjesOfMeasurableRat t = ⨅ q > t (q ∈ ℚ), toRatCDF q
      --                              = ⨅ q > t (q ∈ ℚ), alphaIicRat q
      --                              = ⨅ q > t (q ∈ ℚ), alphaIic (q : ℝ)  (by h_eq at rationals)
      -- Need: this equals alphaIic t
      --
      -- The key insight is that alphaIic is defined as the clipped L¹ limit,
      -- and alphaIicCE = E[1_{Iic t} ∘ X_0 | G] is right-continuous in t (for a.e. ω).
      -- Since alphaIic =ᵐ alphaIicCE, the right-continuity transfers.
      -- Step G1: alphaIic t =ᵐ alphaIicCE t at the specific real t
      have h_ae_eq_t : ∀ᵐ ω ∂μ, alphaIic X hX_contract hX_meas hX_L2 t ω =
          alphaIicCE X hX_contract hX_meas hX_L2 t ω :=
        alphaIic_ae_eq_alphaIicCE X hX_contract hX_meas hX_L2 t

      -- Step G2: alphaIicCE is right-continuous at t (same argument as Step E, but for real t)
      -- ⨅_{r > t, r ∈ ℚ} alphaIicCE r = alphaIicCE t a.e.
      --
      -- Key insight: We don't need to construct a specific sequence converging to t.
      -- We can use the fact that for any s > t, there exists a rational q with t < q < s.
      -- Combined with monotonicity, this gives the right-continuity.
      --
      -- For this sorry, we defer to the fact that alphaIicCE is right-continuous
      -- because it's defined via conditional expectation of indicators 1_{Iic t},
      -- and these are right-continuous in t (the function value at t equals the
      -- right-limit at t).
      have h_right_cont_CE_t : ∀ᵐ ω ∂μ,
          ⨅ r : {q : ℚ // (t : ℝ) < q}, alphaIicCE X hX_contract hX_meas hX_L2 (r : ℝ) ω =
          alphaIicCE X hX_contract hX_meas hX_L2 t ω := by
        -- Strategy: use monotonicity of alphaIicCE + density of ℚ in ℝ
        -- Define real sequence s_n = t + 1/(n+1) → t from above
        -- Prove alphaIicCE(s_n) → alphaIicCE(t) a.e. using DCT (same as Step E)
        -- Transfer to rational infimum using density of ℚ

        have hm_le : TailSigma.tailSigma X ≤ (inferInstance : MeasurableSpace Ω) :=
          TailSigma.tailSigma_le X hX_meas
        haveI : Fact (TailSigma.tailSigma X ≤ (inferInstance : MeasurableSpace Ω)) := ⟨hm_le⟩
        haveI : SigmaFinite (μ.trim hm_le) := inferInstance

        -- Define real sequence s_n = t + 1/(n+1) → t from above
        let s : ℕ → ℝ := fun n => t + 1 / ((n : ℝ) + 1)
        have hs_pos : ∀ n, t < s n := fun n => by
          simp only [s]
          have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
          linarith [one_div_pos.mpr h1]

        have hs_tendsto : Tendsto s atTop (𝓝 t) := by
          simp only [s]
          have h1 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
            tendsto_one_div_add_atTop_nhds_zero_nat
          simpa using tendsto_const_nhds.add h1

        -- Define functions f_n = alphaIicCE(s_n) and F = alphaIicCE(t)
        let f : ℕ → Ω → ℝ := fun n => alphaIicCE X hX_contract hX_meas hX_L2 (s n)
        let F : Ω → ℝ := alphaIicCE X hX_contract hX_meas hX_L2 t

        -- Integrability
        have hf_int : ∀ n, Integrable (f n) μ := fun _ => integrable_condExp
        have hF_int : Integrable F μ := integrable_condExp

        -- F ≤ f_n a.e.
        have hf_bound : ∀ᵐ ω ∂μ, ∀ n, F ω ≤ f n ω := by
          have h : ∀ n, ∀ᵐ ω ∂μ, F ω ≤ f n ω := fun n =>
            alphaIicCE_mono X hX_contract hX_meas hX_L2 t (s n) (le_of_lt (hs_pos n))
          rw [ae_all_iff]; exact h

        -- f_n is antitone a.e. (s_n decreasing → alphaIicCE(s_n) decreasing)
        have hf_antitone : ∀ᵐ ω ∂μ, Antitone (fun n => f n ω) := by
          have h_s_anti : ∀ m n, m ≤ n → s n ≤ s m := fun m n hmn => by
            simp only [s]
            have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
            have hmn' : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by
              have : (m : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hmn
              linarith
            have : 1 / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) := one_div_le_one_div_of_le hm1 hmn'
            linarith
          have h_mono_mn : ∀ m n, m ≤ n → ∀ᵐ ω ∂μ, f n ω ≤ f m ω := fun m n hmn =>
            alphaIicCE_mono X hX_contract hX_meas hX_L2 (s n) (s m) (h_s_anti m n hmn)
          have h_ae_pairs : ∀ᵐ ω ∂μ, ∀ m n : ℕ, m ≤ n → f n ω ≤ f m ω := by
            rw [ae_all_iff]; intro m
            rw [ae_all_iff]; intro n
            by_cases hmn : m ≤ n
            · filter_upwards [h_mono_mn m n hmn] with ω hω _; exact hω
            · filter_upwards with ω h; exact absurd h hmn
          filter_upwards [h_ae_pairs] with ω hω
          exact fun m n hmn => hω m n hmn

        -- Integral convergence via DCT: ∫ f_n → ∫ F
        have hf_int_tendsto : Tendsto (fun n => ∫ ω, f n ω ∂μ) atTop (𝓝 (∫ ω, F ω ∂μ)) := by
          let ind : ℝ → Ω → ℝ := fun u ω => Set.indicator (Set.Iic u) (fun _ => (1 : ℝ)) (X 0 ω)
          have h_eq_n : ∀ n, ∫ ω, f n ω ∂μ = ∫ ω, ind (s n) ω ∂μ := fun n => by
            simp only [f, alphaIicCE, ind]
            exact integral_condExp hm_le
          have h_eq_F : ∫ ω, F ω ∂μ = ∫ ω, ind t ω ∂μ := by
            simp only [F, alphaIicCE, ind]
            exact integral_condExp hm_le
          simp_rw [h_eq_n, h_eq_F]
          apply tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
          · intro n; simp only [ind]
            exact ((measurable_const.indicator measurableSet_Iic).comp (hX_meas 0)).aestronglyMeasurable
          · exact integrable_const 1
          · intro n; apply ae_of_all; intro ω
            simp only [ind, Set.indicator]; split_ifs <;> norm_num
          · apply ae_of_all; intro ω
            simp only [ind, Set.indicator]
            by_cases hx : X 0 ω ≤ t
            · have h : ∀ n, X 0 ω ≤ s n := fun n => le_of_lt (lt_of_le_of_lt hx (hs_pos n))
              simp only [Set.mem_Iic, hx, h, ite_true]
              exact tendsto_const_nhds
            · push_neg at hx
              simp only [Set.mem_Iic, not_le.mpr hx, ite_false]
              refine tendsto_const_nhds.congr' ?_
              have h_event : ∀ᶠ n in atTop, s n < X 0 ω := hs_tendsto.eventually (Iio_mem_nhds hx)
              rw [Filter.eventually_atTop] at h_event
              obtain ⟨N, hN⟩ := h_event
              rw [Filter.EventuallyEq, Filter.eventually_atTop]
              use N; intro n hn
              have hlt : s n < X 0 ω := hN n hn
              have : ¬(X 0 ω ≤ s n) := not_le.mpr hlt
              simp [this]

        -- A.E. convergence via tendsto_of_integral_tendsto_of_antitone
        have hf_ae_tendsto : ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop (𝓝 (F ω)) :=
          tendsto_of_integral_tendsto_of_antitone hf_int hF_int hf_int_tendsto hf_antitone hf_bound

        -- ⨅_n f_n = F a.e.
        have h_ciInf_eq : ∀ᵐ ω ∂μ, ⨅ n, f n ω = F ω := by
          filter_upwards [hf_ae_tendsto, hf_antitone, hf_bound] with ω hω_tend hω_anti hω_bdd
          have h_bdd : BddBelow (Set.range fun n => f n ω) := ⟨F ω, by
            intro x hx; obtain ⟨n, rfl⟩ := hx; exact hω_bdd n⟩
          exact tendsto_nhds_unique (tendsto_atTop_ciInf hω_anti h_bdd) hω_tend

        -- Pre-define a sequence of rationals q_n with t < q_n < s_n for each n
        -- This allows us to add the monotonicity conditions to filter_upwards
        have h_exists_q : ∀ n, ∃ q : ℚ, t < q ∧ (q : ℝ) < s n := fun n => exists_rat_btwn (hs_pos n)
        let q : ℕ → ℚ := fun n => (h_exists_q n).choose
        have hq_lower : ∀ n, t < q n := fun n => (h_exists_q n).choose_spec.1
        have hq_upper : ∀ n, (q n : ℝ) < s n := fun n => (h_exists_q n).choose_spec.2

        -- Get a.e. monotonicity of alphaIicCE at t and rationals
        have h_ae_mono_t_rat : ∀ᵐ ω ∂μ, ∀ r : ℚ, t < r →
            F ω ≤ alphaIicCE X hX_contract hX_meas hX_L2 (r : ℝ) ω := by
          have h : ∀ r : ℚ, t < r → ∀ᵐ ω ∂μ,
              F ω ≤ alphaIicCE X hX_contract hX_meas hX_L2 (r : ℝ) ω := fun r hr =>
            alphaIicCE_mono X hX_contract hX_meas hX_L2 t (r : ℝ) (le_of_lt hr)
          rw [ae_all_iff]; intro r
          by_cases hr : t < r
          · filter_upwards [h r hr] with ω hω _; exact hω
          · filter_upwards with ω hfalse; exact absurd hfalse hr

        -- Get a.e. monotonicity at (q_n, s_n) for all n
        have h_ae_mono_q_s : ∀ᵐ ω ∂μ, ∀ n,
            alphaIicCE X hX_contract hX_meas hX_L2 (q n : ℝ) ω ≤ f n ω := by
          have h : ∀ n, ∀ᵐ ω ∂μ,
              alphaIicCE X hX_contract hX_meas hX_L2 (q n : ℝ) ω ≤
              alphaIicCE X hX_contract hX_meas hX_L2 (s n) ω := fun n =>
            alphaIicCE_mono X hX_contract hX_meas hX_L2 (q n : ℝ) (s n) (le_of_lt (hq_upper n))
          rw [ae_all_iff]; exact h

        -- Transfer from real sequence to rational infimum
        filter_upwards [h_ciInf_eq, hf_bound, h_ae_mono_t_rat, h_ae_mono_q_s]
          with ω h_eq hω_bdd hω_mono_t_rat hω_mono_q_s
        apply le_antisymm
        · -- ⨅_{r > t, r ∈ ℚ} ≤ ⨅_n f_n = F
          calc ⨅ r : {r' : ℚ // t < r'}, alphaIicCE X hX_contract hX_meas hX_L2 (r : ℝ) ω
              ≤ ⨅ n, f n ω := by
                apply le_ciInf; intro n
                -- Use the pre-chosen rational q n with t < q n < s n
                have h_bdd_below : BddBelow (Set.range fun r : {r' : ℚ // t < r'} =>
                    alphaIicCE X hX_contract hX_meas hX_L2 (r : ℝ) ω) :=
                  ⟨F ω, fun x ⟨⟨r, hr⟩, hx⟩ => hx ▸ hω_mono_t_rat r hr⟩
                calc ⨅ r : {r' : ℚ // t < r'}, alphaIicCE X hX_contract hX_meas hX_L2 (r : ℝ) ω
                    ≤ alphaIicCE X hX_contract hX_meas hX_L2 (q n : ℝ) ω :=
                        ciInf_le h_bdd_below ⟨q n, hq_lower n⟩
                  _ ≤ f n ω := hω_mono_q_s n
            _ = F ω := h_eq
        · -- F ≤ ⨅_{r > t, r ∈ ℚ}
          -- Need to show nonempty { q : ℚ // t < q }
          haveI : Nonempty { r' : ℚ // t < r' } := by
            obtain ⟨q, hq⟩ := exists_rat_gt t
            exact ⟨⟨q, hq⟩⟩
          apply le_ciInf
          intro ⟨r, hr⟩
          exact hω_mono_t_rat r hr

      -- Combine: add all the a.e. conditions
      filter_upwards [h_is_stieltjes, h_ae_eq_rat, h_ae_eq_t, h_right_cont_CE_t] with ω h_sp h_eq h_eq_t h_rc_CE_t
      have h_toRatCDF := ProbabilityTheory.toRatCDF_of_isRatStieltjesPoint h_sp
      -- stieltjesOfMeasurableRat t = ⨅_{q > t} stieltjesOfMeasurableRat q (by StieltjesFunction.iInf_rat_gt_eq)
      -- At IsRatStieltjesPoint, stieltjesOfMeasurableRat q = toRatCDF q = alphaIicRat q
      -- = ⨅_{q > t} alphaIicRat q = ⨅_{q > t} alphaIicCE q (by h_eq)
      -- = alphaIicCE t (by h_rc_CE_t) = alphaIic t (by h_eq_t)
      let F := ProbabilityTheory.stieltjesOfMeasurableRat
          (alphaIicRat X hX_contract hX_meas hX_L2)
          (measurable_alphaIicRat X hX_contract hX_meas hX_L2) ω
      -- F t = ⨅_{q > t} F q by right-continuity of Stieltjes functions
      have h1 : F t = ⨅ q : {q : ℚ // t < q}, F (q : ℝ) := (StieltjesFunction.iInf_rat_gt_eq F t).symm
      -- At IsRatStieltjesPoint, F q = toRatCDF q = alphaIicRat q
      have h_F_eq_rat : ∀ q : ℚ, F (q : ℝ) = alphaIicRat X hX_contract hX_meas hX_L2 ω q := fun q => by
        rw [ProbabilityTheory.stieltjesOfMeasurableRat_eq, h_toRatCDF]
      have h2 : ⨅ q : {q : ℚ // t < q}, F (q : ℝ) =
          ⨅ q : {q : ℚ // t < q}, alphaIicRat X hX_contract hX_meas hX_L2 ω q := by
        apply iInf_congr; intro ⟨q, _⟩; exact h_F_eq_rat q
      have h3 : ⨅ q : {q : ℚ // t < q}, alphaIicRat X hX_contract hX_meas hX_L2 ω q =
          ⨅ q : {q : ℚ // t < q}, alphaIicCE X hX_contract hX_meas hX_L2 (q : ℝ) ω := by
        apply iInf_congr; intro ⟨q, hq⟩
        simp only [alphaIicRat]; exact h_eq q
      rw [h1, h2, h3, h_rc_CE_t, h_eq_t]

    -- Combine the three steps
    filter_upwards [h_stieltjes_eq] with ω hω
    rw [h_integral_eq ω, h_meas_eq ω, ← hω]

  -- MONOTONE CLASS ARGUMENT
  --
  -- The strategy is to extend from indicators of half-lines (base case) to all bounded
  -- measurable functions f. We use the standard functional monotone class approach:
  --
  -- 1. Show the property holds for indicators of all Borel sets (via π-λ on sets)
  -- 2. Extend to simple functions by linearity
  -- 3. Extend to bounded measurable by approximation + dominated convergence
  --
  -- For this proof, we use the fact that both sides (L¹ limit and integral against ν)
  -- are uniquely determined by their values on indicators of half-lines, since:
  -- - The L¹ limit is linear and continuous under bounded pointwise convergence
  -- - Integration against ν is linear and continuous under bounded pointwise convergence
  -- - Half-lines generate the Borel σ-algebra on ℝ
  --
  -- By uniqueness of extension from a generating π-system, the two must agree.

  -- === CORE INSIGHT ===
  -- Both operations f ↦ α_f (L¹ limit) and f ↦ ∫ f dν are:
  -- 1. Linear in f
  -- 2. Continuous under L¹ convergence (with uniform bound)
  -- 3. Agree on indicators of half-lines (base case)
  --
  -- By the functional monotone class theorem, they must agree on all bounded measurable f.
  --
  -- The key observation is that the integral ∫ f dν is uniquely determined by the
  -- measure ν, which is in turn uniquely determined by its CDF values ν(Iic t).
  -- The base case establishes that the L¹ limit α_{Iic t} agrees with ν(Iic t) a.e.
  -- for all t. This is sufficient to determine α = ∫ f dν for all bounded measurable f.

  -- IMPLEMENTATION: Use measure uniqueness on Borel ℝ
  --
  -- Both the L¹ limit functional and the integral against ν define set functions on
  -- Borel sets (via indicators). The base case shows these agree on the π-system {Iic t}.
  -- Since both are countably additive on disjoint sets (by DCT arguments), they define
  -- the same measure on Borel ℝ. For bounded measurable f, the integral against either
  -- measure is the same.

  -- === FUNCTIONAL MONOTONE CLASS THEOREM ===
  --
  -- We need to extend from the base case (indicators of half-lines) to all bounded
  -- measurable functions. The key insight is that both operations are determined by
  -- their values on a generating π-system:
  --
  -- Operation 1: f ↦ L¹ limit of (1/N) Σ f(X_k)
  -- Operation 2: f ↦ ∫ f dν (integration against directing measure)
  --
  -- Both are:
  -- - Linear in f
  -- - Continuous under bounded pointwise convergence (by DCT)
  -- - Equal on indicators 1_{Iic t} for all t ∈ ℝ (by base case)
  --
  -- Since {Iic t | t ∈ ℝ} generates the Borel σ-algebra on ℝ, and both operations
  -- are countably determined, they must agree on all bounded measurable functions.
  --
  -- FORMAL PROOF STRATEGY (standard functional monotone class):
  --
  -- Step A: Extend to indicators of all Borel sets
  -- Define the class C = {S : Borel set | L¹ limit for 1_S = ν(S) a.e.}
  -- Show C is a Dynkin system (λ-system):
  -- - ∅ ∈ C: Both sides equal 0
  -- - S ∈ C ⟹ Sᶜ ∈ C: 1_{Sᶜ} = 1 - 1_S, use linearity
  -- - Disjoint Sₙ ∈ C ⟹ ⋃ₙ Sₙ ∈ C: 1_{⋃Sₙ} = Σ 1_{Sₙ}, use DCT
  --
  -- Base case shows: C ⊇ {Iic t | t ∈ ℝ} (π-system)
  -- By π-λ theorem: C = all Borel sets
  --
  -- Step B: Extend to simple functions
  -- Simple function g = Σᵢ cᵢ · 1_{Sᵢ} where Sᵢ are disjoint Borel sets
  -- L¹ limit for g = Σᵢ cᵢ · (L¹ limit for 1_{Sᵢ}) by linearity
  --                = Σᵢ cᵢ · ν(Sᵢ) by Step A
  --                = ∫ g dν
  --
  -- Step C: Extend to bounded measurable
  -- For bounded measurable f with |f| ≤ M:
  -- - Use SimpleFunc.approxOn to get simple gₙ → f pointwise with |gₙ| ≤ M
  -- - L¹ limit for f = lim (L¹ limit for gₙ) by DCT
  --                  = lim ∫ gₙ dν by Step B
  --                  = ∫ f dν by DCT for integration
  --
  -- IMPLEMENTATION NOTE:
  -- The base case shows alphaIic t = ∫ 1_{Iic t} dν a.e. via the Stieltjes extension.
  -- This requires careful connection between:
  -- - alphaIic (clipped L¹ limit for indicators)
  -- - The raw L¹ limit from weighted_sums_converge_L1
  -- - The directing_measure (Stieltjes function of alphaIicRat)
  --
  -- For indicators in [0,1], the clipping is trivial since averages are in [0,1].
  -- The L¹ limit is unique (up to a.e. equality), so all formulations agree.

  -- For the complete formal proof, we would need helper lemmas:
  -- 1. weighted_sums_converge_L1_add: linearity of L¹ limits
  -- 2. weighted_sums_converge_L1_smul: scalar multiplication
  -- 3. π-λ induction on Borel sets using MeasurableSpace.induction_on_inter
  -- 4. SimpleFunc.approxOn approximation bounds
  -- 5. DCT for both L¹ limits and integrals

  -- KEY MATHLIB REFERENCE for measure uniqueness:
  -- `Measure.ext_of_generateFrom_of_iUnion` from Mathlib.MeasureTheory.Measure.Restrict:
  --   Two measures are equal if they agree on a π-system generating the σ-algebra
  --   and are finite on a spanning sequence in the π-system.
  --
  -- For Borel ℝ with generating π-system {Iic t | t ∈ ℝ}:
  -- - Spanning sequence: B_n = Iic n for n ∈ ℕ
  -- - Both the L¹ limit "measure" and directing_measure ν(ω) are probability measures
  -- - They agree on Iic t for all t (base case)
  -- - Therefore they agree on all Borel sets

  -- The mathematical content is established; the formal implementation requires
  -- substantial but routine bookkeeping following the functional monotone class pattern.
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
  have h_conv : ∀ n, ∀ ε > 0, ∃ M : ℕ, ∀ m : ℕ, m ≥ M →
      ∫ ω, |(1/(m:ℝ)) * ∑ k : Fin m, ind (X (n + k.val + 1) ω) - limit ω| ∂μ < ε :=
    h_spec.2.2

  -- SIMPLIFIED PROOF: Use the fact that limit is already L¹ from h_spec.2.1
  --
  -- Key insight: h_spec.2.1 gives us MemLp limit 1 μ, so limit is integrable!
  -- alphaIic = clip01(limit) by definition, and clip01(limit) =ᵐ limit since
  -- the Cesàro averages are in [0,1] and converge to limit in L¹.
  -- By L¹ uniqueness, limit ∈ [0,1] a.e., so clip01(limit) =ᵐ limit.

  have h_limit_integrable : Integrable limit μ := h_spec.2.1.integrable le_rfl

  -- alphaIic is integrable (bounded by 1, measurable)
  have h_alphaIic_integrable : Integrable (alphaIic X hX_contract hX_meas hX_L2 t) μ := by
    have h_meas := alphaIic_measurable X hX_contract hX_meas hX_L2 t
    have h_bdd : ∀ ω, ‖alphaIic X hX_contract hX_meas hX_L2 t ω‖ ≤ 1 := by
      intro ω
      rw [Real.norm_eq_abs, abs_le]
      have ⟨h0, h1⟩ := alphaIic_bound X hX_contract hX_meas hX_L2 t ω
      constructor
      · linarith
      · exact h1
    exact Integrable.of_bound h_meas.aestronglyMeasurable 1 (Filter.Eventually.of_forall h_bdd)

  -- alphaIic = clip01(limit) pointwise
  have h_alphaIic_def : ∀ ω, alphaIic X hX_contract hX_meas hX_L2 t ω =
      max 0 (min 1 (limit ω)) := fun ω => rfl

  -- The Cesàro averages are in [0,1] pointwise
  let A : ℕ → Ω → ℝ := fun m ω => (1/(m:ℝ)) * ∑ k : Fin m, ind (X (0 + k.val + 1) ω)
  have h_A_in_01 : ∀ m : ℕ, m > 0 → ∀ ω, 0 ≤ A m ω ∧ A m ω ≤ 1 := by
    intro m hm ω
    have h_sum_nonneg : 0 ≤ ∑ k : Fin m, ind (X (0 + k.val + 1) ω) := by
      apply Finset.sum_nonneg; intro k _; simp [ind, Set.indicator]; split_ifs <;> linarith
    have h_sum_le_m : ∑ k : Fin m, ind (X (0 + k.val + 1) ω) ≤ m := by
      calc ∑ k : Fin m, ind (X (0 + k.val + 1) ω)
          ≤ ∑ _k : Fin m, (1 : ℝ) := by
            apply Finset.sum_le_sum; intro k _; simp [ind, Set.indicator]; split_ifs <;> linarith
        _ = m := by simp
    constructor
    · apply mul_nonneg; positivity; exact h_sum_nonneg
    · calc A m ω = (1/(m:ℝ)) * ∑ k : Fin m, ind (X (0 + k.val + 1) ω) := rfl
          _ ≤ (1/(m:ℝ)) * m := by apply mul_le_mul_of_nonneg_left h_sum_le_m; positivity
          _ = 1 := by field_simp

  -- limit is in [0,1] a.e. since it's the L¹ limit of functions in [0,1]
  -- Proof: L¹ convergence → convergence in measure → a.e. convergent subsequence
  -- → pointwise limit of [0,1]-valued functions is in [0,1]
  have h_limit_in_01 : ∀ᵐ ω ∂μ, 0 ≤ limit ω ∧ limit ω ≤ 1 := by
    -- Step 1: Each A m is measurable
    have hA_meas : ∀ m, Measurable (A m) := fun m => by
      apply Measurable.mul measurable_const
      refine Finset.measurable_sum _ (fun k _ => ind_meas.comp (hX_meas _))

    -- Step 2: L¹ convergence: ∫|A m - limit| → 0
    have h_tendsto_L1 : Filter.Tendsto (fun m => ∫ ω, |A m ω - limit ω| ∂μ) atTop (𝓝 0) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨M, hM⟩ := h_conv 0 ε hε
      refine ⟨M, fun m hm => ?_⟩
      simp only [Real.dist_eq, sub_zero]
      rw [abs_of_nonneg (integral_nonneg (fun ω => abs_nonneg _))]
      exact hM m hm

    have h_limit_meas : Measurable limit := h_spec.1

    -- Step 3: L¹ convergence implies convergence in measure
    -- Use tendstoInMeasure_of_tendsto_eLpNorm_of_ne_top with p = 1
    have h_A_int : ∀ m, Integrable (A m) μ := fun m => by
      refine ⟨(hA_meas m).aestronglyMeasurable, ?_⟩
      apply hasFiniteIntegral_of_bounded (C := 1)
      filter_upwards with ω
      rw [Real.norm_eq_abs]
      by_cases hm : m = 0
      · simp only [A, hm, Nat.cast_zero, div_zero, Finset.univ_eq_empty, Finset.sum_empty,
          mul_zero, abs_zero, zero_le_one]
      · have ⟨h0, h1⟩ := h_A_in_01 m (Nat.pos_of_ne_zero hm) ω
        rw [abs_of_nonneg h0]; exact h1
    have h_diff_int : ∀ m, Integrable (fun ω => A m ω - limit ω) μ :=
      fun m => (h_A_int m).sub h_limit_integrable
    have h_tendstoInMeasure : TendstoInMeasure μ A atTop limit := by
      -- First show eLpNorm (A m - limit) 1 μ → 0
      have h_eLpNorm_tendsto : Tendsto (fun m => eLpNorm (A m - limit) 1 μ) atTop (𝓝 0) := by
        simp_rw [eLpNorm_one_eq_lintegral_enorm]
        rw [ENNReal.tendsto_atTop_zero]
        intro ε hε
        -- Handle ε = ⊤ case (trivially true since lintegral is finite)
        by_cases hε_top : ε = ⊤
        · refine ⟨0, fun m _ => ?_⟩
          rw [hε_top]
          conv_lhs => rw [show (fun ω => ‖(A m - limit) ω‖ₑ) = (fun ω => ‖A m ω - limit ω‖ₑ) by rfl]
          rw [← ofReal_integral_norm_eq_lintegral_enorm (h_diff_int m)]
          exact le_top
        · -- ε ≠ ⊤ case: use L¹ convergence
          obtain ⟨M, hM⟩ := Metric.tendsto_atTop.mp h_tendsto_L1 ε.toReal
            (ENNReal.toReal_pos hε.ne' hε_top)
          refine ⟨M, fun m hm => ?_⟩
          have := hM m hm
          simp only [Real.dist_eq, sub_zero] at this
          conv_lhs => rw [show (fun ω => ‖(A m - limit) ω‖ₑ) = (fun ω => ‖A m ω - limit ω‖ₑ) by rfl]
          rw [← ofReal_integral_norm_eq_lintegral_enorm (h_diff_int m)]
          have h_int_nonneg : 0 ≤ ∫ x, |A m x - limit x| ∂μ := integral_nonneg (fun ω => abs_nonneg _)
          have h_norm_eq_abs : ∫ x, ‖A m x - limit x‖ ∂μ = ∫ x, |A m x - limit x| ∂μ := by
            apply integral_congr_ae; filter_upwards with ω; exact Real.norm_eq_abs _
          rw [h_norm_eq_abs]
          have h_lt : ∫ x, |A m x - limit x| ∂μ < ε.toReal := by
            rwa [abs_of_nonneg h_int_nonneg] at this
          have h_toReal_pos : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hε_top
          have h1 : ENNReal.ofReal (∫ x, |A m x - limit x| ∂μ) < ENNReal.ofReal ε.toReal := by
            rw [ENNReal.ofReal_lt_ofReal_iff h_toReal_pos]
            exact h_lt
          have h2 : ENNReal.ofReal ε.toReal ≤ ε := ENNReal.ofReal_toReal_le
          exact le_of_lt (lt_of_lt_of_le h1 h2)
      exact tendstoInMeasure_of_tendsto_eLpNorm_of_ne_top one_ne_zero ENNReal.one_ne_top
        (fun m => (hA_meas m).aestronglyMeasurable) h_limit_meas.aestronglyMeasurable h_eLpNorm_tendsto

    -- Step 4: Convergence in measure implies a.e. convergent subsequence
    obtain ⟨ns, hns_mono, hns_ae⟩ := h_tendstoInMeasure.exists_seq_tendsto_ae

    -- Step 5: The subsequence A (ns k) → limit a.e., and each A (ns k) ∈ [0,1]
    filter_upwards [hns_ae] with ω hω_conv
    -- Each A (ns k) ω ∈ [0,1] for k > 0
    have h_seq_in_01 : ∀ k, 0 ≤ A (ns k) ω ∧ A (ns k) ω ≤ 1 := fun k => by
      by_cases hnsk : ns k = 0
      · simp [A, hnsk]
      · exact h_A_in_01 (ns k) (Nat.pos_of_ne_zero hnsk) ω
    -- Limits preserve inequalities
    constructor
    · exact ge_of_tendsto hω_conv (Filter.Eventually.of_forall (fun k => (h_seq_in_01 k).1))
    · exact le_of_tendsto hω_conv (Filter.Eventually.of_forall (fun k => (h_seq_in_01 k).2))

  -- Therefore clip01(limit) =ᵐ limit
  have h_clip_eq_limit : ∀ᵐ ω ∂μ, max 0 (min 1 (limit ω)) = limit ω := by
    filter_upwards [h_limit_in_01] with ω ⟨h0, h1⟩
    rw [min_eq_right h1, max_eq_right h0]

  -- So alphaIic =ᵐ limit
  have h_alphaIic_ae_eq : ∀ᵐ ω ∂μ, alphaIic X hX_contract hX_meas hX_L2 t ω = limit ω := by
    filter_upwards [h_clip_eq_limit] with ω hω
    rw [h_alphaIic_def ω, hω]

  -- Step 5: Show ∫ A_m = μ(X_0 ∈ Iic t).toReal for all m > 0
  have h_cesaro_integral : ∀ m : ℕ, m > 0 →
      ∫ ω, A m ω ∂μ = (μ (X 0 ⁻¹' Set.Iic t)).toReal := by
    intro m hm
    -- The integral of the average = average of the integrals
    have h_int_sum : ∫ ω, A m ω ∂μ =
        (1/(m:ℝ)) * ∑ k : Fin m, ∫ ω, ind (X (0 + k.val + 1) ω) ∂μ := by
      simp only [A]
      rw [integral_mul_left]
      congr 1
      rw [integral_finset_sum]
      intro k _
      have h_meas_comp : Measurable (fun ω => ind (X (0 + k.val + 1) ω)) :=
        ind_meas.comp (hX_meas _)
      have h_bdd : ∀ ω, ‖ind (X (0 + k.val + 1) ω)‖ ≤ 1 := by
        intro ω; rw [Real.norm_eq_abs]; exact ind_bdd _
      exact Integrable.of_bound h_meas_comp.aestronglyMeasurable 1 (Filter.Eventually.of_forall h_bdd)
    rw [h_int_sum]
    -- Each integral equals μ(X_j ∈ Iic t)
    have h_each : ∀ k : Fin m, ∫ ω, ind (X (0 + k.val + 1) ω) ∂μ =
        (μ (X (0 + k.val + 1) ⁻¹' Set.Iic t)).toReal := by
      intro k
      have h_ind_eq : ∀ ω, ind (X (0 + k.val + 1) ω) =
          (X (0 + k.val + 1) ⁻¹' Set.Iic t).indicator (fun _ => (1 : ℝ)) ω := by
        intro ω; simp only [ind, Set.indicator, Set.mem_Iic, Set.mem_preimage]
      simp_rw [h_ind_eq]
      rw [integral_indicator (hX_meas (0 + k.val + 1) measurableSet_Iic)]
      rw [setIntegral_const, smul_eq_mul, mul_one]
      rfl  -- μ.real s = (μ s).toReal by definition
    simp_rw [h_each]
    -- By contractability, all marginals are equal
    have h_marginal_eq : ∀ j : ℕ, μ (X j ⁻¹' Set.Iic t) = μ (X 0 ⁻¹' Set.Iic t) := by
      intro j
      have h_map := L2Helpers.contractable_map_single X hX_contract hX_meas (i := j)
      rw [← Measure.map_apply (hX_meas j) measurableSet_Iic]
      rw [h_map]
      rw [Measure.map_apply (hX_meas 0) measurableSet_Iic]
    simp_rw [h_marginal_eq]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp

  -- Step 6: Compute ∫ alphaIic using ∫ alphaIic = ∫ limit and L¹ convergence of A_m → limit
  -- Since alphaIic =ᵐ limit, we have ∫ alphaIic = ∫ limit
  have h_int_eq_limit : ∫ ω, alphaIic X hX_contract hX_meas hX_L2 t ω ∂μ = ∫ ω, limit ω ∂μ :=
    integral_congr_ae h_alphaIic_ae_eq

  -- Show ∫ limit = marginal by L¹ convergence
  have h_limit_integral : ∫ ω, limit ω ∂μ = (μ (X 0 ⁻¹' Set.Iic t)).toReal := by
    by_contra h_ne
    have h_gap : ∃ δ > 0, |∫ ω, limit ω ∂μ - (μ (X 0 ⁻¹' Set.Iic t)).toReal| ≥ δ := by
      use |∫ ω, limit ω ∂μ - (μ (X 0 ⁻¹' Set.Iic t)).toReal|
      exact ⟨abs_pos.mpr (sub_ne_zero.mpr h_ne), le_refl _⟩
    obtain ⟨δ, hδ_pos, hδ⟩ := h_gap
    obtain ⟨M, hM⟩ := h_conv 0 (δ/2) (by linarith)
    let m := max M 2
    have hm_ge_M : m ≥ M := le_max_left M 2
    have hm_pos : m > 0 := Nat.lt_of_lt_of_le (by decide : 0 < 2) (le_max_right M 2)
    have h_bound := hM m hm_ge_M
    have h_int_eq := h_cesaro_integral m hm_pos
    -- |∫ A_m - ∫ limit| ≤ ∫ |A_m - limit| < δ/2
    have h_int_close : |∫ ω, A m ω ∂μ - ∫ ω, limit ω ∂μ| < δ/2 := by
      calc |∫ ω, A m ω ∂μ - ∫ ω, limit ω ∂μ|
          = |∫ ω, (A m ω - limit ω) ∂μ| := by
            congr 1
            rw [integral_sub]
            · -- A_m is integrable
              have h_A_meas : Measurable (A m) := by
                apply Measurable.const_mul
                apply Finset.measurable_sum; intro k _; exact ind_meas.comp (hX_meas _)
              exact Integrable.of_bound h_A_meas.aestronglyMeasurable 1
                (Filter.Eventually.of_forall (fun ω => by
                  rw [Real.norm_eq_abs, abs_le]
                  have ⟨h0, h1⟩ := h_A_in_01 m hm_pos ω
                  constructor <;> linarith))
            · exact h_limit_integrable
        _ ≤ ∫ ω, |A m ω - limit ω| ∂μ := abs_integral_le_integral_abs
        _ < δ/2 := h_bound
    rw [h_int_eq] at h_int_close
    rw [abs_sub_comm] at h_int_close
    linarith

  rw [h_int_eq_limit, h_limit_integral]

/-! ### Injective to StrictMono via Sorting

For the bridge property, we need to convert an injective function `k : Fin m → ℕ`
to a strictly monotone one. This is done by sorting the image of k.
-/

/-- Any injective function `k : Fin m → ℕ` can be composed with a permutation
to become strictly monotone.

**Construction:** Let `s := image k univ` (the image of k as a finset of ℕ).
Since k is injective, `s.card = m`. The `orderIsoOfFin` gives the sorted
enumeration of s. We define σ to map i to the position of k(i) in the sorted order.

**Key property:** `(fun i => k (σ i))` is strictly increasing (sorted order). -/
lemma injective_implies_strictMono_perm {m : ℕ}
    (k : Fin m → ℕ) (hk : Function.Injective k) :
    ∃ (σ : Equiv.Perm (Fin m)), StrictMono (fun i => k (σ i)) := by
  classical
  -- Define the image of k as a finset
  let s : Finset ℕ := Finset.image k Finset.univ
  -- By injectivity, s has cardinality m
  have hs : s.card = m := by
    simp only [s, Finset.card_image_of_injective Finset.univ hk, Finset.card_univ, Fintype.card_fin]
  -- Get the sorted enumeration of s
  let sorted : Fin m ≃o ↑s := Finset.orderIsoOfFin s hs
  -- For each i : Fin m, k(i) is in s, so we can find its sorted position
  have hk_mem : ∀ i : Fin m, k i ∈ s := by
    intro i
    simp only [s, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨i, rfl⟩
  -- Define σ: for each position j in sorted order, find which i : Fin m maps to it
  -- sorted j gives the j-th smallest element of s
  -- We want σ such that k (σ j) = sorted j
  -- Define σ⁻¹ first: σ⁻¹(i) = sorted position of k(i)
  let σ_inv : Fin m → Fin m := fun i =>
    sorted.symm ⟨k i, hk_mem i⟩
  -- σ_inv is injective because sorted.symm and k are both injective
  have hσ_inv_inj : Function.Injective σ_inv := by
    intro i j hij
    simp only [σ_inv] at hij
    have h := sorted.symm.injective hij
    simp only [Subtype.mk.injEq] at h
    exact hk h
  -- Since σ_inv : Fin m → Fin m is injective, it's a bijection (by Fintype.bijective_iff_injective_and_card)
  have hσ_inv_bij : Function.Bijective σ_inv := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨hσ_inv_inj, rfl⟩
  -- Convert to an Equiv.Perm
  let σ : Equiv.Perm (Fin m) := Equiv.ofBijective σ_inv hσ_inv_bij
  -- Now σ.symm is the permutation we want
  use σ.symm
  -- Show k ∘ σ.symm is strictly monotone
  intro i j hij
  -- σ.symm(i) is the unique index such that σ_inv(σ.symm(i)) = i
  -- i.e., sorted position of k(σ.symm(i)) is i
  -- So k(σ.symm(i)) = sorted(i) (the i-th smallest element)
  have h_eq_i : k (σ.symm i) = ↑(sorted i) := by
    have h1 : σ_inv (σ.symm i) = i := by
      simp only [σ, Equiv.ofBijective_apply_symm_apply]
    simp only [σ_inv] at h1
    have h2 : sorted.symm ⟨k (σ.symm i), hk_mem (σ.symm i)⟩ = i := h1
    have h3 := sorted.apply_symm_apply ⟨k (σ.symm i), hk_mem (σ.symm i)⟩
    rw [h2] at h3
    exact Subtype.ext_iff.mp h3.symm
  have h_eq_j : k (σ.symm j) = ↑(sorted j) := by
    have h1 : σ_inv (σ.symm j) = j := by
      simp only [σ, Equiv.ofBijective_apply_symm_apply]
    simp only [σ_inv] at h1
    have h2 : sorted.symm ⟨k (σ.symm j), hk_mem (σ.symm j)⟩ = j := h1
    have h3 := sorted.apply_symm_apply ⟨k (σ.symm j), hk_mem (σ.symm j)⟩
    rw [h2] at h3
    exact Subtype.ext_iff.mp h3.symm
  -- Goal: (fun i => k (σ.symm i)) i < (fun i => k (σ.symm i)) j
  -- This simplifies to: k (σ.symm i) < k (σ.symm j)
  simp only
  rw [h_eq_i, h_eq_j]
  -- sorted is an OrderIso, so it's strictly monotone
  exact sorted.strictMono hij

/-! ### Collision Bound for Route B

The key estimate for Route B: the fraction of non-injective maps φ : Fin m → Fin N
tends to 0 as N → ∞, with rate O(m²/N).
-/

/-- Bijection between constrained functions {φ | φ i = φ j} and functions on Fin n.

The constraint φ i = φ j means φ j is determined by φ i, so effectively we only need to
specify φ on {k | k ≠ j}, which has cardinality n when the domain is Fin (n+1). -/
def constrainedFunctionEquiv {N n : ℕ} (i j : Fin (n+1)) (hij : i ≠ j) :
    {φ : Fin (n+1) → Fin N // φ i = φ j} ≃ (Fin n → Fin N) where
  toFun := fun ⟨φ, _⟩ => fun k => φ ((finSuccAboveEquiv j) k)
  invFun := fun ψ =>
    let i' := (finSuccAboveEquiv j).symm ⟨i, hij⟩
    ⟨fun k => if h : k = j then ψ i' else ψ ((finSuccAboveEquiv j).symm ⟨k, h⟩),
     by simp only [hij, dite_false]; rfl⟩
  left_inv := fun ⟨φ, hφ⟩ => by
    simp only [Subtype.mk.injEq]
    funext k
    by_cases hk : k = j
    · simp only [hk, dite_true]
      conv_rhs => rw [← hφ]
      congr 1
      have h := (finSuccAboveEquiv j).apply_symm_apply ⟨i, hij⟩
      simp only [Subtype.ext_iff] at h
      exact h
    · simp only [hk, dite_false]
      congr 1
      have h := (finSuccAboveEquiv j).apply_symm_apply ⟨k, hk⟩
      simp only [Subtype.ext_iff] at h
      exact h
  right_inv := fun ψ => by
    funext k
    simp only
    have hne : ((finSuccAboveEquiv j) k : Fin (n+1)) ≠ j := ((finSuccAboveEquiv j) k).prop
    simp only [hne, dite_false]
    congr 1
    exact (finSuccAboveEquiv j).symm_apply_apply k

/-- Cardinality of {φ | φ i = φ j} equals N^(m-1).
The constraint φ i = φ j reduces the degrees of freedom by 1. -/
lemma card_collision_set (m N : ℕ) (i j : Fin m) (hij : i ≠ j) :
    Fintype.card {φ : Fin m → Fin N // φ i = φ j} = N^(m - 1) := by
  cases m with
  | zero => exact Fin.elim0 i
  | succ n =>
    rw [Fintype.card_eq.mpr ⟨constrainedFunctionEquiv i j hij⟩]
    simp only [Fintype.card_fun, Fintype.card_fin, Nat.add_sub_cancel]

/-- The set of ordered pairs (i, j) with i ≠ j. -/
def collisionPairs (m : ℕ) : Finset (Fin m × Fin m) :=
  Finset.filter (fun ij => ij.1 ≠ ij.2) Finset.univ

/-- The number of collision pairs is at most m². -/
lemma card_collisionPairs_le (m : ℕ) : (collisionPairs m).card ≤ m * m := by
  simp only [collisionPairs]
  calc (Finset.filter (fun ij : Fin m × Fin m => ij.1 ≠ ij.2) Finset.univ).card
      ≤ (Finset.univ : Finset (Fin m × Fin m)).card := Finset.card_filter_le _ _
    _ = Fintype.card (Fin m × Fin m) := by rw [Finset.card_univ]
    _ = Fintype.card (Fin m) * Fintype.card (Fin m) := Fintype.card_prod _ _
    _ = m * m := by simp [Fintype.card_fin]

/-- For each pair (i, j), the set of maps with collision φ i = φ j. -/
def mapsWithCollision (m N : ℕ) (ij : Fin m × Fin m) : Finset (Fin m → Fin N) :=
  Finset.filter (fun φ => φ ij.1 = φ ij.2) Finset.univ

/-- The number of non-injective maps φ : Fin m → Fin N is at most m² * N^(m-1).

**Proof:** A non-injective map has some pair (i, j) with i ≠ j and φ(i) = φ(j).
By union bound over the m² pairs, and for each pair there are at most N^(m-1) maps.
-/
lemma card_nonInjective_le (m N : ℕ) (_hN : 0 < N) :
    Fintype.card {φ : Fin m → Fin N // ¬Function.Injective φ} ≤ m * m * N^(m - 1) := by
  classical
  -- For m = 0 or m = 1, there are no non-injective maps
  cases m with
  | zero =>
    have : IsEmpty {φ : Fin 0 → Fin N // ¬Function.Injective φ} := by
      constructor
      intro ⟨φ, hφ⟩
      simp only [Function.Injective] at hφ
      push_neg at hφ
      obtain ⟨i, _, _, _⟩ := hφ
      exact Fin.elim0 i
    simp [Fintype.card_eq_zero]
  | succ n =>
    cases n with
    | zero =>
      have : IsEmpty {φ : Fin 1 → Fin N // ¬Function.Injective φ} := by
        constructor
        intro ⟨φ, hφ⟩
        simp only [Function.Injective] at hφ
        push_neg at hφ
        obtain ⟨i, j, _, hij⟩ := hφ
        exact absurd (Subsingleton.elim i j) hij
      simp [Fintype.card_eq_zero]
    | succ k =>
      -- m = k + 2 ≥ 2
      -- Key: non-injective ↔ has collision at some pair (i,j)
      have h_subset : (Finset.univ.filter (fun φ : Fin (k+2) → Fin N => ¬Function.Injective φ))
          ⊆ (collisionPairs (k+2)).biUnion (mapsWithCollision (k+2) N) := by
        intro φ hφ
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hφ
        simp only [Finset.mem_biUnion, mapsWithCollision, Finset.mem_filter, Finset.mem_univ,
                   true_and, collisionPairs]
        -- φ is not injective, so ∃ i ≠ j with φ i = φ j
        simp only [Function.Injective] at hφ
        push_neg at hφ
        obtain ⟨i, j, heq, hne⟩ := hφ
        refine ⟨(i, j), ?_, heq⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact hne

      -- Each collision set has cardinality ≤ N^(m-1)
      have h_each : ∀ ij ∈ collisionPairs (k+2), (mapsWithCollision (k+2) N ij).card ≤ N^(k + 1) := by
        intro ij hij_mem
        obtain ⟨i, j⟩ := ij
        simp only [collisionPairs, Finset.mem_filter, Finset.mem_univ, true_and] at hij_mem
        simp only [mapsWithCollision]
        have h_eq : (Finset.filter (fun φ : Fin (k+2) → Fin N => φ i = φ j) Finset.univ).card
            = Fintype.card {φ : Fin (k+2) → Fin N // φ i = φ j} := by
          rw [Fintype.card_subtype]
        rw [h_eq, card_collision_set (k+2) N i j hij_mem]
        -- k + 2 - 1 = k + 1 in ℕ
        have harith : k + 2 - 1 = k + 1 := by omega
        rw [harith]

      -- Combine using biUnion bound
      calc Fintype.card {φ : Fin (k+2) → Fin N // ¬Function.Injective φ}
          = (Finset.univ.filter (fun φ : Fin (k+2) → Fin N => ¬Function.Injective φ)).card := by
            rw [Fintype.card_subtype]
        _ ≤ ((collisionPairs (k+2)).biUnion (mapsWithCollision (k+2) N)).card :=
            Finset.card_le_card h_subset
        _ ≤ ∑ ij ∈ collisionPairs (k+2), (mapsWithCollision (k+2) N ij).card :=
            Finset.card_biUnion_le
        _ ≤ ∑ _ij ∈ collisionPairs (k+2), N^(k + 1) := Finset.sum_le_sum h_each
        _ = (collisionPairs (k+2)).card * N^(k + 1) := by rw [Finset.sum_const, smul_eq_mul]
        _ ≤ (k + 2) * (k + 2) * N^(k + 1) := by
            apply Nat.mul_le_mul_right
            exact card_collisionPairs_le (k + 2)

/-- The fraction of non-injective maps tends to 0 as N → ∞.

For fixed m, the fraction (# non-injective) / N^m ≤ m²/N → 0.
-/
lemma nonInjective_fraction_tendsto_zero (m : ℕ) :
    Tendsto (fun N => (Fintype.card {φ : Fin m → Fin N // ¬Function.Injective φ} : ℝ) / (N : ℝ)^m)
            atTop (𝓝 0) := by
  -- Handle m = 0 specially
  cases m with
  | zero =>
    simp only [pow_zero, div_one]
    -- For m = 0, the set is empty (all functions are vacuously injective)
    have h : ∀ N, Fintype.card {φ : Fin 0 → Fin N // ¬Function.Injective φ} = 0 := by
      intro N
      rw [Fintype.card_eq_zero_iff]
      constructor
      intro ⟨φ, hφ⟩
      simp only [Function.Injective] at hφ
      push_neg at hφ
      obtain ⟨i, _, _, _⟩ := hφ
      exact Fin.elim0 i
    simp only [h, Nat.cast_zero]
    exact tendsto_const_nhds
  | succ n =>
    -- For m = n+1 ≥ 1, use the bound and squeeze theorem
    -- Upper bound: fraction ≤ (n+1)² * N^n / N^(n+1) = (n+1)² / N → 0
    have h_bound : ∀ᶠ N in atTop, (Fintype.card {φ : Fin (n+1) → Fin N // ¬Function.Injective φ} : ℝ)
        / (N : ℝ)^(n+1) ≤ ((n+1)^2 : ℕ) / (N : ℝ) := by
      filter_upwards [eventually_gt_atTop 0] with N hN
      have hN_pos : (0 : ℕ) < N := hN
      have hN_real : (0 : ℝ) < N := Nat.cast_pos.mpr hN
      -- Apply card_nonInjective_le
      have h_card : Fintype.card {φ : Fin (n+1) → Fin N // ¬Function.Injective φ}
          ≤ (n+1) * (n+1) * N^n := card_nonInjective_le (n+1) N hN_pos
      -- Convert to reals and divide
      calc (Fintype.card {φ : Fin (n+1) → Fin N // ¬Function.Injective φ} : ℝ) / (N : ℝ)^(n+1)
          ≤ ((n+1) * (n+1) * N^n : ℕ) / (N : ℝ)^(n+1) := by
            apply div_le_div_of_nonneg_right
            · exact Nat.cast_le.mpr h_card
            · exact le_of_lt (pow_pos hN_real (n+1))
        _ = ((n+1)^2 : ℕ) * (N : ℝ)^n / (N : ℝ)^(n+1) := by
            congr 1
            push_cast
            ring
        _ = ((n+1)^2 : ℕ) / (N : ℝ) := by
            have hN_ne : (N : ℝ) ≠ 0 := ne_of_gt hN_real
            have hN_pow_ne : (N : ℝ)^n ≠ 0 := pow_ne_zero n hN_ne
            rw [pow_succ]
            field_simp
            ring
    -- Lower bound
    have h_nonneg : ∀ᶠ N in atTop, 0 ≤ (Fintype.card {φ : Fin (n+1) → Fin N // ¬Function.Injective φ} : ℝ)
        / (N : ℝ)^(n+1) := by
      filter_upwards [eventually_gt_atTop 0] with N hN
      apply div_nonneg
      · exact Nat.cast_nonneg _
      · exact pow_nonneg (Nat.cast_nonneg N) (n+1)
    -- Upper bound limit
    have h_lim : Tendsto (fun N : ℕ => ((n+1)^2 : ℕ) / (N : ℝ)) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat _
    -- Apply squeeze
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_lim h_nonneg h_bound

/-! ### Product L¹ Convergence

For Route B, we need: if each factor converges in L¹, then the product converges in L¹
(under boundedness assumptions).
-/

/-- Helper: |∏ f| ≤ 1 when all |f i| ≤ 1. -/
lemma abs_prod_le_one {n : ℕ} (f : Fin n → ℝ) (hf : ∀ i, |f i| ≤ 1) : |∏ i, f i| ≤ 1 := by
  rw [Finset.abs_prod]
  have h1 : ∏ i, |f i| ≤ ∏ _i : Fin n, (1 : ℝ) := by
    apply Finset.prod_le_prod
    · intro i _; exact abs_nonneg _
    · intro i _; exact hf i
  simp at h1
  exact h1

/-- Telescoping bound: |∏ f - ∏ g| ≤ ∑ |f_j - g_j| when factors are bounded by 1.

This is proved by induction using the identity:
  a*b - c*d = a*(b-d) + (a-c)*d
-/
lemma abs_prod_sub_prod_le {m : ℕ} (f g : Fin m → ℝ)
    (hf : ∀ i, |f i| ≤ 1) (hg : ∀ i, |g i| ≤ 1) :
    |∏ i, f i - ∏ i, g i| ≤ ∑ i, |f i - g i| := by
  induction m with
  | zero => simp
  | succ n ih =>
    rw [Fin.prod_univ_succ, Fin.prod_univ_succ, Fin.sum_univ_succ]
    let P_f := ∏ i : Fin n, f i.succ
    let P_g := ∏ i : Fin n, g i.succ
    -- Use identity: a*b - c*d = a*(b-d) + (a-c)*d
    have h1 : f 0 * P_f - g 0 * P_g = f 0 * (P_f - P_g) + (f 0 - g 0) * P_g := by ring
    have hPg : |P_g| ≤ 1 := abs_prod_le_one (fun i => g i.succ) (fun i => hg i.succ)
    calc |f 0 * P_f - g 0 * P_g|
        = |f 0 * (P_f - P_g) + (f 0 - g 0) * P_g| := by rw [h1]
      _ ≤ |f 0 * (P_f - P_g)| + |(f 0 - g 0) * P_g| := abs_add_le _ _
      _ = |f 0| * |P_f - P_g| + |f 0 - g 0| * |P_g| := by rw [abs_mul, abs_mul]
      _ ≤ 1 * |P_f - P_g| + |f 0 - g 0| * 1 := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_right (hf 0) (abs_nonneg _)
          · exact mul_le_mul_of_nonneg_left hPg (abs_nonneg _)
      _ = |P_f - P_g| + |f 0 - g 0| := by ring
      _ ≤ (∑ i : Fin n, |f i.succ - g i.succ|) + |f 0 - g 0| := by
          apply add_le_add_right
          exact ih (fun i => f i.succ) (fun i => g i.succ)
                   (fun i => hf i.succ) (fun i => hg i.succ)
      _ = |f 0 - g 0| + ∑ i : Fin n, |f i.succ - g i.succ| := by ring

/-- Helper: |a - b| ≤ |a| + |b|. -/
lemma abs_sub_le_abs_add (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  calc |a - b| = |a + (-b)| := by ring_nf
    _ ≤ |a| + |-b| := abs_add_le a (-b)
    _ = |a| + |b| := by rw [abs_neg]

/-- Product of L¹-convergent bounded sequences converges in L¹.

If f_n(i) → g(i) in L¹ for each i, and all functions are bounded by 1,
then ∏_i f_n(i) → ∏_i g(i) in L¹.

**Proof:** By `abs_prod_sub_prod_le`, we have pointwise:
  |∏_i f_n(i) - ∏_i g(i)| ≤ ∑_j |f_n(j) - g(j)|

Integrating and using Fubini:
  ∫ |∏ f - ∏ g| ≤ ∫ ∑_j |f_j - g_j| = ∑_j ∫ |f_j - g_j|

The RHS tends to 0 by h_conv and `tendsto_finset_sum`.
-/
lemma prod_tendsto_L1_of_L1_tendsto
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {m : ℕ} (f : ℕ → Fin m → Ω → ℝ) (g : Fin m → Ω → ℝ)
    (hf_bdd : ∀ n i ω, |f n i ω| ≤ 1)
    (hg_bdd : ∀ i ω, |g i ω| ≤ 1)
    (hf_meas : ∀ n i, AEStronglyMeasurable (f n i) μ)
    (hg_meas : ∀ i, AEStronglyMeasurable (g i) μ)
    (h_conv : ∀ i, Tendsto (fun n => ∫ ω, |f n i ω - g i ω| ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, |∏ i : Fin m, f n i ω - ∏ i : Fin m, g i ω| ∂μ) atTop (𝓝 0) := by
  -- Step 1: Pointwise bound from abs_prod_sub_prod_le
  have h_pointwise : ∀ n ω, |∏ i : Fin m, f n i ω - ∏ i : Fin m, g i ω|
      ≤ ∑ i : Fin m, |f n i ω - g i ω| := fun n ω =>
    abs_prod_sub_prod_le (fun i => f n i ω) (fun i => g i ω)
      (fun i => hf_bdd n i ω) (fun i => hg_bdd i ω)

  -- Step 2: Sum of L¹ norms tends to 0
  have h_sum_tendsto : Tendsto (fun n => ∑ i : Fin m, ∫ ω, |f n i ω - g i ω| ∂μ) atTop (𝓝 0) := by
    rw [show (0 : ℝ) = ∑ _i : Fin m, (0 : ℝ) by simp]
    apply tendsto_finset_sum
    intro i _
    exact h_conv i

  -- Helper: |f n i - g i| is integrable
  have h_diff_int : ∀ n i, Integrable (fun ω => |f n i ω - g i ω|) μ := by
    intro n i
    apply Integrable.abs
    apply Integrable.of_bound (C := 2)
    · exact (hf_meas n i).sub (hg_meas i)
    · apply ae_of_all μ
      intro ω
      calc ‖f n i ω - g i ω‖ = |f n i ω - g i ω| := Real.norm_eq_abs _
        _ ≤ |f n i ω| + |g i ω| := abs_sub_le_abs_add _ _
        _ ≤ 1 + 1 := add_le_add (hf_bdd n i ω) (hg_bdd i ω)
        _ = 2 := by ring

  -- Step 3: Apply squeeze_zero
  apply squeeze_zero
  · -- Lower bound: ∫|...| ≥ 0
    intro n
    exact integral_nonneg (fun ω => abs_nonneg _)
  · -- Upper bound: ∫|∏f-∏g| ≤ ∑∫|f-g|
    intro n
    have h_int_bound : ∫ ω, |∏ i : Fin m, f n i ω - ∏ i : Fin m, g i ω| ∂μ
        ≤ ∫ ω, ∑ i : Fin m, |f n i ω - g i ω| ∂μ := by
      apply integral_mono_of_nonneg
      · exact ae_of_all μ (fun ω => abs_nonneg _)
      · apply integrable_finset_sum
        intro i _
        exact h_diff_int n i
      · exact ae_of_all μ (h_pointwise n)
    calc ∫ ω, |∏ i : Fin m, f n i ω - ∏ i : Fin m, g i ω| ∂μ
        ≤ ∫ ω, ∑ i : Fin m, |f n i ω - g i ω| ∂μ := h_int_bound
      _ = ∑ i : Fin m, ∫ ω, |f n i ω - g i ω| ∂μ := by
          rw [integral_finset_sum]
          intro i _
          exact h_diff_int n i
  · exact h_sum_tendsto

/-- The bridge property: E[∏ᵢ 𝟙_{Bᵢ}(X_{k(i)})] = E[∏ᵢ ν(·)(Bᵢ)].

This is the key property needed for complete_from_directing_measure.
It follows from contractability and the fact that α_{𝟙_B} = ν(·)(B).
-/
lemma directing_measure_bridge
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ)
    {m : ℕ} (k : Fin m → ℕ) (hk : Function.Injective k)
    (B : Fin m → Set ℝ) (hB : ∀ i, MeasurableSet (B i)) :
    ∫⁻ ω, ∏ i : Fin m,
        ENNReal.ofReal ((B i).indicator (fun _ => (1 : ℝ)) (X (k i) ω)) ∂μ
      = ∫⁻ ω, ∏ i : Fin m,
        directing_measure X hX_contract hX_meas hX_L2 ω (B i) ∂μ := by
  classical
  -- PROOF STRATEGY (using injective_implies_strictMono_perm + contractability):
  --
  -- STEP 1: Reduce to the strictly monotone case
  -- By injective_implies_strictMono_perm, ∃ σ : Perm (Fin m) with k ∘ σ strictly monotone.
  -- Reindexing: ∏_i 1_{B_i}(X_{k_i}) = ∏_j 1_{B_{σ j}}(X_{(k∘σ) j})
  -- (Same product, different enumeration of factors)
  --
  -- STEP 2: Apply contractability
  -- Since k ∘ σ is strictly monotone, by Contractable.allStrictMono_eq:
  --   E[f(X_{(k∘σ) 0}, ..., X_{(k∘σ)(m-1)})] = E[f(X_0, ..., X_{m-1})]
  -- Applied to f = ∏_j 1_{B_{σ j}}:
  --   E[∏_j 1_{B_{σ j}}(X_{(k∘σ) j})] = E[∏_j 1_{B_{σ j}}(X_j)]
  --
  -- STEP 3: Similarly for RHS
  -- ∏_i ν(·)(B_i) = ∏_j ν(·)(B_{σ j}) (same product, reindexed)
  --
  -- STEP 4: Prove the identity case (k = id)
  -- Need: E[∏_j 1_{B_j}(X_j)] = E[∏_j ν(·)(B_j)]
  -- This is the core reconstruction theorem requiring:
  -- - Route B: U-statistic expansion with collision bound
  -- - Or: Tower property with conditional independence
  --
  -- For now, we implement the reduction and leave the identity case as sorry.

  -- Handle trivial case m = 0
  cases m with
  | zero => simp
  | succ n =>
    -- Step 1: Get the sorting permutation
    obtain ⟨σ, hσ_mono⟩ := injective_implies_strictMono_perm k hk

    -- Step 2: Reindex LHS
    -- The product ∏_i f(i) equals ∏_j f(σ j) for any permutation σ
    -- Since σ is a bijection, this is just (Equiv.prod_comp σ _).symm
    have h_lhs_reindex : ∀ ω,
        ∏ i : Fin (n + 1), ENNReal.ofReal ((B i).indicator (fun _ => (1 : ℝ)) (X (k i) ω))
      = ∏ j : Fin (n + 1), ENNReal.ofReal ((B (σ j)).indicator (fun _ => (1 : ℝ)) (X (k (σ j)) ω)) := by
      intro ω
      exact (Equiv.prod_comp σ _).symm
    simp_rw [h_lhs_reindex]

    -- Step 3: Reindex RHS similarly
    have h_rhs_reindex : ∀ ω,
        ∏ i : Fin (n + 1), directing_measure X hX_contract hX_meas hX_L2 ω (B i)
      = ∏ j : Fin (n + 1), directing_measure X hX_contract hX_meas hX_L2 ω (B (σ j)) := by
      intro ω
      exact (Equiv.prod_comp σ _).symm
    simp_rw [h_rhs_reindex]

    -- Now k ∘ σ is strictly monotone. Let k' = k ∘ σ and B' = B ∘ σ.
    -- We need to prove:
    --   E[∏_j 1_{B'_j}(X_{k'_j})] = E[∏_j ν(·)(B'_j)]
    -- where k' is strictly monotone.
    --
    -- By contractability (Contractable.allStrictMono_eq):
    --   Distribution of (X_{k'_0}, ..., X_{k'_{n}}) = Distribution of (X_0, ..., X_n)
    -- This means: E[∏_j 1_{B'_j}(X_{k'_j})] = E[∏_j 1_{B'_j}(X_j)]
    --
    -- So we reduce to proving the IDENTITY CASE:
    --   E[∏_j 1_{B_j}(X_j)] = E[∏_j ν(·)(B_j)]
    --
    -- This requires proving that the finite-dimensional marginals of X
    -- match those of the product measure ν(ω)^⊗m.
    --
    -- ROUTE B (U-statistic/collision bound) proves this directly.
    -- See plan file for detailed steps.

    -- Step 1: Define indicator and empirical frequencies
    -- I i j ω = 1 if X j ω ∈ B (σ i), else 0
    let B' := fun i => B (σ i)  -- reindexed sets
    let I : Fin (n + 1) → ℕ → Ω → ℝ := fun i j ω =>
      (B' i).indicator (fun _ => (1 : ℝ)) (X j ω)

    -- Empirical frequency: p N i ω = (1/(N+1)) ∑_{j < N+1} I i (j+1) ω
    -- Uses indices 1, 2, ..., N+1 to match directing_measure_integral (n=0, m=N+1)
    let p : ℕ → Fin (n + 1) → Ω → ℝ := fun N i ω =>
      (1 / ((N + 1 : ℕ) : ℝ)) * ∑ j : Fin (N + 1), I i (j.val + 1) ω

    -- Product of empirical frequencies
    let q : ℕ → Ω → ℝ := fun N ω => ∏ i : Fin (n + 1), p N i ω

    -- Limit: product of directing measure values
    let r : Ω → ℝ := fun ω =>
      ∏ i : Fin (n + 1), (directing_measure X hX_contract hX_meas hX_L2 ω (B' i)).toReal

    -- Basic bounds on I
    have I_nonneg : ∀ i j ω, 0 ≤ I i j ω := fun i j ω => by
      simp only [I]
      exact Set.indicator_nonneg (fun _ _ => zero_le_one) _

    have I_le_one : ∀ i j ω, I i j ω ≤ 1 := fun i j ω => by
      simp only [I]
      by_cases h : X j ω ∈ B' i <;> simp [Set.indicator, h]

    have I_abs_le_one : ∀ i j ω, |I i j ω| ≤ 1 := fun i j ω => by
      rw [abs_of_nonneg (I_nonneg i j ω)]
      exact I_le_one i j ω

    -- Step 2: L¹ convergence of each coordinate p N i → directing_measure ω (B' i)
    -- Use directing_measure_integral for the indicator function

    -- Helper: indicator functions are measurable and bounded
    have I_meas : ∀ i, Measurable ((B' i).indicator (fun _ => (1 : ℝ))) := fun i =>
      measurable_const.indicator (hB (σ i))
    have I_bdd : ∀ i, ∃ M, ∀ x, |(B' i).indicator (fun _ => (1 : ℝ)) x| ≤ M := fun i =>
      ⟨1, fun x => by by_cases h : x ∈ B' i <;> simp [Set.indicator, h]⟩

    -- For each i, get L¹ limit and identification with directing measure
    -- The limit α_i satisfies: p N i → α_i in L¹, and α_i = ν(·)(B' i) a.e.
    -- Note: We use indices (k.val + 1) to match our definition of p which uses indices 1, 2, ..., m
    have h_coord_conv : ∀ i : Fin (n + 1),
        ∃ α_i : Ω → ℝ, Measurable α_i ∧ MemLp α_i 1 μ ∧
          (∀ ε > 0, ∃ M : ℕ, ∀ m ≥ M,
            ∫ ω, |(1/(m:ℝ)) * ∑ k : Fin m, I i (k.val + 1) ω - α_i ω| ∂μ < ε) ∧
          (∀ᵐ ω ∂μ, α_i ω = (directing_measure X hX_contract hX_meas hX_L2 ω (B' i)).toReal) := by
      intro i
      -- Use directing_measure_integral for the indicator function
      obtain ⟨α_i, hα_meas, hα_L1, hα_conv, hα_eq⟩ :=
        directing_measure_integral X hX_contract hX_meas hX_L2
          ((B' i).indicator (fun _ => 1)) (I_meas i) (I_bdd i)
      refine ⟨α_i, hα_meas, hα_L1, ?_, ?_⟩
      · -- Convergence: directing_measure_integral with n=0 gives exactly what we need
        -- It provides: ∫ |(1/m) ∑_{k<m} f(X_{0+k+1}) - α| dμ < ε for m ≥ M
        -- which is: ∫ |(1/m) ∑_{k<m} f(X_{k+1}) - α| dμ < ε for m ≥ M
        -- This matches our indexing I i (k.val + 1) exactly!
        intro ε hε
        obtain ⟨M, hM⟩ := hα_conv 0 ε hε
        refine ⟨M, fun m hm => ?_⟩
        -- Convert: 0 + k + 1 = k + 1, and the indicator matches I's definition
        simp only [zero_add, I] at hM
        exact hM m hm
      · -- Identification: ∫ 1_B dν = ν(B)
        filter_upwards [hα_eq] with ω hω
        rw [hω]
        -- ∫ 1_{B'_i}(x) d(ν ω) = ν ω (B' i)
        -- Note: (fun _ => 1) = 1 definitionally for Pi types
        -- and μ.real s = (μ s).toReal definitionally
        convert MeasureTheory.integral_indicator_one (hB (σ i)) using 1

    -- Step 3: Use contractability to reduce LHS to identity case
    -- Since k ∘ σ is strictly monotone, by Contractable.allStrictMono_eq:
    -- Distribution of (X_{(k∘σ)(0)}, ..., X_{(k∘σ)(n)}) = Distribution of (X_0, ..., X_n)

    -- Define the strictly monotone k' = k ∘ σ
    let k' : Fin (n + 1) → ℕ := k ∘ σ

    -- k' is strictly monotone
    have hk'_mono : StrictMono k' := hσ_mono

    -- The identity function on Fin (n+1) is strictly monotone
    have hid_mono : StrictMono (fun i : Fin (n + 1) => (i : ℕ)) := fun i j hij => hij

    -- By contractability, the measures are equal
    have h_map_eq := hX_contract.allStrictMono_eq (n + 1) k' (fun i => i.val) hk'_mono hid_mono

    -- This gives us that for any measurable function f:
    -- ∫ f(X_{k'(0)}, ..., X_{k'(n)}) dμ = ∫ f(X_0, ..., X_n) dμ

    -- Apply this to reduce LHS to identity case
    -- Goal becomes: ∫⁻ ∏_i 1_{B(σi)}(X_i) dμ = ∫⁻ ∏_i ν(·)(B(σi)) dμ
    -- which is the identity case with B' i = B (σ i)

    -- Step 4: Obtain limiting functions from h_coord_conv
    -- For each i, we have α_i → ν(·)(B' i) a.e.
    -- We need to apply prod_tendsto_L1_of_L1_tendsto

    -- Choose the limiting functions
    choose α_funcs hα_funcs using h_coord_conv
    -- Each hα_funcs i provides:
    -- - (hα_funcs i).1 : Measurable (α_funcs i)
    -- - (hα_funcs i).2.1 : MemLp (α_funcs i) 1 μ
    -- - (hα_funcs i).2.2.1 : L¹ convergence ε-δ form
    -- - (hα_funcs i).2.2.2 : α_funcs i = ν(·)(B' i).toReal a.e.

    -- Step 4: The identity case target
    -- LHS: ∫⁻ ∏_i 1_{B'_i}(X_i) dμ
    -- RHS: ∫⁻ ∏_i ν(·)(B' i) dμ

    -- Key: Since hk : k ∘ σ = id, we have k (σ i) = i for all i
    -- So the LHS of the main goal is exactly ∫⁻ ∏_i 1_{B(σi)}(X_i) dμ = ∫⁻ ∏_i 1_{B'_i}(X_i) dμ

    -- Step 5: Use the a.e. equality of α_i and r_i := ν(·)(B' i).toReal
    -- By h_coord_conv, α_funcs i = ν(·)(B' i).toReal a.e.
    -- Therefore ∏_i α_funcs i = ∏_i ν(·)(B' i).toReal a.e.

    -- Step 6: The collision bound argument (detailed in plan)
    -- Shows E[q N] → E[∏_i I i i] as N → ∞
    -- Together with E[q N] → E[∏_i α_funcs i], we get equality

    -- Step 7: Use h_map_eq to rewrite LHS as identity case
    -- Define the measurable function on (Fin (n+1) → ℝ)
    let f : (Fin (n + 1) → ℝ) → ENNReal := fun x =>
      ∏ j : Fin (n + 1), ENNReal.ofReal ((B (σ j)).indicator (fun _ => (1 : ℝ)) (x j))

    -- LHS = ∫ f ∘ (fun ω j => X (k' j) ω) dμ
    --     = ∫ f d(Measure.map (fun ω j => X (k' j) ω) μ)  by change of variables
    -- Identity case = ∫ f ∘ (fun ω j => X j ω) dμ
    --               = ∫ f d(Measure.map (fun ω j => X j ω) μ)  by change of variables
    -- Since h_map_eq says these measures are equal, LHS = Identity case

    -- The key theorem: by h_map_eq and lintegral_map_equiv or similar,
    -- ∫⁻ ∏_j 1_{B(σj)}(X_{k'(j)}) dμ = ∫⁻ ∏_j 1_{B(σj)}(X_j) dμ

    -- So our goal reduces to proving the IDENTITY CASE:
    -- ∫⁻ ∏_j 1_{B(σj)}(X_j) dμ = ∫⁻ ∏_j ν(·)(B(σj)) dμ

    -- Step 8: The identity case (U-statistic expansion)
    --
    -- **Goal:** Prove E[∏_j 1_{B(σj)}(X_j)] = E[∏_j ν(·)(B(σj))]
    --
    -- **Available Infrastructure:**
    -- - `nonInjective_fraction_tendsto_zero` (line 942): collision bound
    -- - `prod_tendsto_L1_of_L1_tendsto` (line 1068): product L¹ convergence
    -- - `Finset.prod_univ_sum`: ∏ i, ∑ j, f i j = ∑ φ, ∏ i, f i (φ i)
    -- - `Contractable.allStrictMono_eq`: contractability reduction (line 1333)
    --
    -- **Proof outline:**
    --
    -- 1. EXPAND q_N: The empirical product q N ω = ∏_i p N i ω where
    --    p N i ω = (1/N) ∑_{j<N} I i j ω
    --    By Finset.prod_univ_sum: q N = (1/N^m) ∑_{φ : Fin m → Fin N} ∏_i I i (φ i)
    --
    -- 2. SPLIT by injectivity of φ:
    --    ∑_φ = ∑_{φ injective} + ∑_{φ non-injective}
    --
    -- 3. INJECTIVE CASE: For injective φ, by contractability (allStrictMono_eq),
    --    E[∏_i I i (φ i)] = E[∏_i I i i] (the identity case)
    --    So injective sum contributes: (# injective) × E[∏_i I i i]
    --
    -- 4. NON-INJECTIVE CASE: Each |∏_i I i (φ i)| ≤ 1, so
    --    |∑_{φ non-inj}| ≤ (# non-injective)
    --    After division by N^m: → 0 by nonInjective_fraction_tendsto_zero
    --
    -- 5. LIMIT: As N → ∞,
    --    - E[q N] → E[∏_i I i i] (from steps 3-4 + falling factorial limit)
    --    - E[q N] → E[∏_i α_funcs i] (by prod_tendsto_L1_of_L1_tendsto)
    --    - By uniqueness of limits: E[∏_i I i i] = E[∏_i α_funcs i]
    --
    -- 6. A.E. EQUALITY: α_funcs i = ν(·)(B' i).toReal a.e. (from h_coord_conv)
    --    So E[∏_i α_funcs i] = E[∏_i ν(·)(B' i).toReal]
    --
    -- 7. ENNREAL: Convert real integrals to ENNReal using lintegral_ofReal
    --    (products of [0,1] values are in [0,1])
    --
    -- Each step is standard but involves significant bookkeeping.
    -- The mathematical content is validated by the infrastructure lemmas above.

    -- ═══════════════════════════════════════════════════════════════════════════════
    -- IDENTITY CASE: U-statistic expansion proof
    -- ═══════════════════════════════════════════════════════════════════════════════
    --
    -- PROOF OUTLINE:
    --
    -- STEP A: Reduce LHS from k' indices to identity indices using contractability
    --   By h_map_eq, the pushforward measures are equal:
    --     Measure.map (fun ω i => X (k' i) ω) μ = Measure.map (fun ω i => X i.val ω) μ
    --   By lintegral_map (change of variables), integrals of any f are equal.
    --
    -- STEP B: Identity case via U-statistic expansion
    --   E[q N] → E[∏_i I i i] as N → ∞ (using injective/non-injective split)
    --   E[q N] → E[∏_i α_funcs i] (by prod_tendsto_L1_of_L1_tendsto)
    --   By uniqueness: E[∏_i I i i] = E[∏_i α_funcs i]
    --
    -- STEP C: A.e. equality
    --   α_funcs i = ν(·)(B' i).toReal a.e. (from h_coord_conv)
    --   So E[∏_i α_funcs i] = E[∏_i ν(·)(B' i).toReal]
    --
    -- STEP D: Real ↔ ENNReal conversion
    --   Convert between ∫ and ∫⁻ using ofReal_integral_eq_lintegral_ofReal
    --
    -- INFRASTRUCTURE USED:
    -- - h_map_eq: contractability (Measure.map equality)
    -- - h_coord_conv: L¹ convergence and a.e. identification
    -- - nonInjective_fraction_tendsto_zero: collision bound
    -- - prod_tendsto_L1_of_L1_tendsto: product of L¹ limits
    -- - lintegral_map: change of variables
    -- - ofReal_integral_eq_lintegral_ofReal: Real ↔ ENNReal
    --
    -- The full implementation requires careful bookkeeping of these conversions.
    -- The mathematical content is validated by the infrastructure above.

    -- ═══════════════════════════════════════════════════════════════════════════════
    -- IMPLEMENTATION OUTLINE (detailed in comments above, lines 2048-2087)
    -- ═══════════════════════════════════════════════════════════════════════════════
    --
    -- STEP A: Use contractability (h_map_eq) to reduce LHS to identity case
    --   Since k' is strictly monotone, by Contractable.allStrictMono_eq:
    --   Measure.map (fun ω j => X (k' j) ω) μ = Measure.map (fun ω j => X j ω) μ
    --   By lintegral_map: ∫⁻ f(X_{k'(0)}, ...) dμ = ∫⁻ f(X_0, ...) dμ
    --
    -- Measurability of f : (Fin (n+1) → ℝ) → ENNReal
    have hf_meas : Measurable f := by
      apply Finset.measurable_prod
      intro i _
      apply Measurable.ennreal_ofReal
      -- Need: (fun x => (B (σ i)).indicator (fun _ => 1) (x i)) is measurable
      -- This is (indicator ∘ projection), where indicator : ℝ → ℝ and projection : (Fin → ℝ) → ℝ
      exact (measurable_const.indicator (hB (σ i))).comp (measurable_pi_apply i)

    -- Projection to finite prefix
    let proj_k' : Ω → (Fin (n + 1) → ℝ) := fun ω j => X (k' j) ω
    let proj_id : Ω → (Fin (n + 1) → ℝ) := fun ω j => X j.val ω

    have hproj_k'_meas : Measurable proj_k' := by
      apply measurable_pi_lambda
      intro j
      exact hX_meas (k' j)

    have hproj_id_meas : Measurable proj_id := by
      apply measurable_pi_lambda
      intro j
      exact hX_meas j.val

    -- By h_map_eq: the pushforward measures are equal
    have h_lhs_eq_id : ∫⁻ ω, f (proj_k' ω) ∂μ = ∫⁻ ω, f (proj_id ω) ∂μ := by
      -- h_map_eq says: Measure.map proj_k' μ = Measure.map proj_id μ
      -- Use ← lintegral_map to rewrite ∫⁻ ω, f (g ω) ∂μ to ∫⁻ x, f x ∂(μ.map g)
      rw [← lintegral_map hf_meas hproj_k'_meas, ← lintegral_map hf_meas hproj_id_meas,
          h_map_eq]

    -- Rewrite LHS using h_lhs_eq_id
    -- LHS = ∫⁻ f ∘ proj_k' dμ = ∫⁻ f ∘ proj_id dμ (identity case)
    -- Note: k (σ j) = (k ∘ σ) j = k' j, so X (k (σ j)) = X (k' j) = proj_k' ω j
    have h_lhs_eq_fk : (fun ω => ∏ j : Fin (n + 1),
        ENNReal.ofReal ((B (σ j)).indicator (fun _ => (1 : ℝ)) (X (k (σ j)) ω)))
      = fun ω => f (proj_k' ω) := by
      ext ω
      simp only [f, proj_k']
      rfl

    have h_rhs_eq_fid : (fun ω => ∏ j : Fin (n + 1),
        ENNReal.ofReal ((B (σ j)).indicator (fun _ => (1 : ℝ)) (X j.val ω)))
      = fun ω => f (proj_id ω) := by
      ext ω
      simp only [f, proj_id]

    rw [h_lhs_eq_fk, h_lhs_eq_id, ← h_rhs_eq_fid]

    -- STEP B: Now prove the identity case
    -- Goal: ∫⁻ ∏_j 1_{B'_j}(X_j) dμ = ∫⁻ ∏_j ν(·)(B'_j) dμ
    --
    -- This uses U-statistic expansion (detailed proof in comments lines 2058-2087).
    --
    -- Key facts:
    -- 1. E[q N] → E[∏_i I i i] via U-stat expansion (collision bound + falling factorial)
    -- 2. E[q N] → E[∏_i α_funcs i] via prod_tendsto_L1_of_L1_tendsto
    -- 3. By uniqueness: E[∏_i I i i] = E[∏_i α_funcs i]
    -- 4. By a.e. equality: E[∏_i α_funcs i] = E[∏_i ν(·)(B'_i).toReal]
    -- 5. Convert to ENNReal

    -- U-STATISTIC EXPANSION ARGUMENT
    --
    -- The mathematical content is validated by the infrastructure lemmas:
    -- - nonInjective_fraction_tendsto_zero (line 1641)
    -- - prod_tendsto_L1_of_L1_tendsto (line 1767)
    -- - h_coord_conv (provides L¹ convergence and a.e. identification)
    --
    -- PROOF SKETCH (steps 1-10 detailed above)

    -- Step B.1: Convert LHS from ENNReal to real integral
    -- LHS = ∫⁻ ∏_j ofReal(I j j ω) dμ
    -- For indicator functions with values in {0,1}, ∏ ofReal = ofReal ∏
    have h_lhs_prod : ∀ ω, ∏ j : Fin (n + 1),
        ENNReal.ofReal ((B (σ j)).indicator (fun _ => (1 : ℝ)) (X j.val ω))
      = ENNReal.ofReal (∏ j : Fin (n + 1), (B (σ j)).indicator (fun _ => (1 : ℝ)) (X j.val ω)) := by
      intro ω
      -- Product of ofReal equals ofReal of product when all terms are nonneg
      rw [ENNReal.ofReal_prod_of_nonneg]
      intro j _
      exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
    simp_rw [h_lhs_prod]

    -- Step B.2: The LHS is now ∫⁻ ofReal (∏_j 1_{B'_j}(X_j)) dμ
    -- This equals ∫ ∏_j 1_{B'_j}(X_j) dμ when integrable and nonneg

    -- Step B.3: Convert RHS
    -- RHS = ∫⁻ ∏_j ν ω (B'_j) dμ
    -- Need to relate ν ω (B'_j) to (ν ω (B'_j)).toReal

    -- The products on both sides are in [0,1], so both integrands are nonneg.
    -- The key is that their expectations are equal via the U-stat argument.

    -- Step B.4: Apply prod_tendsto_L1_of_L1_tendsto
    -- We have p N i → α_funcs i in L¹ for each i (from h_coord_conv)
    -- Therefore ∏_i p N i → ∏_i α_funcs i in L¹

    -- Bounds on p N i: since I ∈ [0,1], averages are in [0,1]
    have p_nonneg : ∀ N i ω, 0 ≤ p N i ω := fun N i ω => by
      simp only [p]
      apply mul_nonneg
      · positivity
      · apply Finset.sum_nonneg; intro j _; exact I_nonneg i (j.val + 1) ω

    have p_le_one : ∀ N i ω, p N i ω ≤ 1 := fun N i ω => by
      simp only [p]
      calc (1 / ((N + 1 : ℕ) : ℝ)) * ∑ j : Fin (N + 1), I i (j.val + 1) ω
          ≤ (1 / ((N + 1 : ℕ) : ℝ)) * ∑ _j : Fin (N + 1), (1 : ℝ) := by
            apply mul_le_mul_of_nonneg_left
            · apply Finset.sum_le_sum; intro j _; exact I_le_one i (j.val + 1) ω
            · positivity
        _ = (1 / ((N + 1 : ℕ) : ℝ)) * (N + 1 : ℕ) := by simp
        _ = 1 := by field_simp

    have p_abs_le_one : ∀ N i ω, |p N i ω| ≤ 1 := fun N i ω => by
      rw [abs_of_nonneg (p_nonneg N i ω)]
      exact p_le_one N i ω

    -- Define r_funcs to be the direct probability measure values (pointwise bounded)
    -- This equals α_funcs a.e. but has pointwise bounds in [0,1]
    let r_funcs : Fin (n + 1) → Ω → ℝ := fun i ω =>
      (directing_measure X hX_contract hX_meas hX_L2 ω (B' i)).toReal

    -- r_funcs is pointwise bounded since ν is a probability measure
    have r_nonneg : ∀ i ω, 0 ≤ r_funcs i ω := fun i ω => ENNReal.toReal_nonneg

    have r_le_one : ∀ i ω, r_funcs i ω ≤ 1 := fun i ω => by
      simp only [r_funcs]
      have h_prob : IsProbabilityMeasure (directing_measure X hX_contract hX_meas hX_L2 ω) :=
        directing_measure_isProbabilityMeasure X hX_contract hX_meas hX_L2 ω
      have h1 : (directing_measure X hX_contract hX_meas hX_L2 ω (B' i)).toReal
          ≤ (directing_measure X hX_contract hX_meas hX_L2 ω Set.univ).toReal := by
        apply ENNReal.toReal_mono (measure_ne_top _ _)
        exact measure_mono (Set.subset_univ _)
      have h2 : (directing_measure X hX_contract hX_meas hX_L2 ω Set.univ).toReal = 1 := by
        simp [measure_univ]
      linarith

    have r_abs_le_one : ∀ i ω, |r_funcs i ω| ≤ 1 := fun i ω => by
      rw [abs_of_nonneg (r_nonneg i ω)]
      exact r_le_one i ω

    -- r_funcs = α_funcs a.e.
    have r_eq_α_ae : ∀ i, r_funcs i =ᵐ[μ] α_funcs i := fun i => by
      filter_upwards [(hα_funcs i).2.2.2] with ω hω
      simp only [r_funcs]
      exact hω.symm

    -- Measurability of p N i
    have p_meas : ∀ N i, AEStronglyMeasurable (p N i) μ := fun N i => by
      apply Measurable.aestronglyMeasurable
      simp only [p]
      apply Measurable.const_mul
      apply Finset.measurable_sum
      intro j _
      simp only [I]
      exact (measurable_const.indicator (hB (σ i))).comp (hX_meas (j.val + 1))

    -- Measurability of α_funcs
    have α_meas : ∀ i, AEStronglyMeasurable (α_funcs i) μ := fun i =>
      (hα_funcs i).1.aestronglyMeasurable

    -- Measurability of r_funcs
    have r_meas : ∀ i, AEStronglyMeasurable (r_funcs i) μ := fun i =>
      (α_meas i).congr (r_eq_α_ae i).symm

    -- L¹ convergence to α_funcs: convert ε-δ to Tendsto form
    have h_L1_conv : ∀ i, Tendsto (fun N => ∫ ω, |p N i ω - α_funcs i ω| ∂μ) atTop (𝓝 0) := by
      intro i
      rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨M, hM⟩ := (hα_funcs i).2.2.1 ε hε
      refine ⟨M, fun N hN => ?_⟩
      simp only [Real.dist_eq, sub_zero]
      -- |∫|·|| - 0| = ∫|·| since integral of abs is nonneg
      rw [abs_of_nonneg (integral_nonneg (fun ω => abs_nonneg _))]
      -- p N uses (N+1) in denominator and sums over Fin (N+1)
      -- hM m says: for m ≥ M, ∫ |1/m * ∑_{k : Fin m} I i (k+1) - α| < ε
      -- So we apply hM with m = N+1
      have hN1 : N + 1 ≥ M := Nat.le_add_right_of_le hN
      specialize hM (N + 1) hN1
      -- Now hM : ∫ |1/(N+1) * ∑_{k : Fin (N+1)} I i (k+1) - α_funcs i| < ε
      -- This matches p N i exactly (definitionally equal up to coercion)
      simp only [p]
      exact hM

    -- L¹ convergence to r_funcs (follows from α_funcs since they're a.e. equal)
    have h_L1_conv_r : ∀ i, Tendsto (fun N => ∫ ω, |p N i ω - r_funcs i ω| ∂μ) atTop (𝓝 0) := by
      intro i
      have h_ae_eq : ∀ N, (fun ω => |p N i ω - r_funcs i ω|) =ᵐ[μ]
          (fun ω => |p N i ω - α_funcs i ω|) := fun N => by
        filter_upwards [r_eq_α_ae i] with ω hω
        simp only [hω]
      simp only [fun N => integral_congr_ae (h_ae_eq N)]
      exact h_L1_conv i

    -- Apply prod_tendsto_L1_of_L1_tendsto with r_funcs (which has pointwise bounds)
    have h_prod_L1 : Tendsto (fun N => ∫ ω, |q N ω - ∏ i : Fin (n + 1), r_funcs i ω| ∂μ)
        atTop (𝓝 0) := by
      -- q N ω = ∏_i p N i ω, so this follows from prod_tendsto_L1_of_L1_tendsto
      have h := prod_tendsto_L1_of_L1_tendsto (fun N i => p N i) r_funcs
        p_abs_le_one r_abs_le_one p_meas r_meas h_L1_conv_r
      -- The goal matches h exactly since q N ω = ∏_i p N i ω by definition
      exact h

    -- Step B.5: The a.e. equality α_funcs i = ν(·)(B' i).toReal
    have h_ae_eq : ∀ᵐ ω ∂μ, ∏ i : Fin (n + 1), α_funcs i ω =
        ∏ i : Fin (n + 1), (directing_measure X hX_contract hX_meas hX_L2 ω (B' i)).toReal := by
      -- Combine the a.e. equalities for each coordinate
      have h_all : ∀ᵐ ω ∂μ, ∀ i : Fin (n + 1),
          α_funcs i ω = (directing_measure X hX_contract hX_meas hX_L2 ω (B' i)).toReal := by
        apply ae_all_iff.mpr
        intro i
        exact (hα_funcs i).2.2.2
      filter_upwards [h_all] with ω hω
      congr 1
      ext i
      exact hω i

    -- Step B.6: Convert RHS to use toReal
    -- ν ω (B' j) = ofReal ((ν ω (B' j)).toReal) when ν ω (B' j) ≠ ⊤
    -- Since ν is a probability measure, ν ω (B' j) ≤ 1 < ⊤
    have h_rhs_convert : ∀ ω, ∏ j : Fin (n + 1),
        directing_measure X hX_contract hX_meas hX_L2 ω (B (σ j))
      = ENNReal.ofReal (∏ j : Fin (n + 1),
        (directing_measure X hX_contract hX_meas hX_L2 ω (B (σ j))).toReal) := by
      intro ω
      have h_ne_top : ∀ j, directing_measure X hX_contract hX_meas hX_L2 ω (B (σ j)) ≠ ⊤ := by
        intro j
        have h_prob : IsProbabilityMeasure (directing_measure X hX_contract hX_meas hX_L2 ω) :=
          directing_measure_isProbabilityMeasure X hX_contract hX_meas hX_L2 ω
        exact measure_ne_top _ _
      rw [ENNReal.ofReal_prod_of_nonneg]
      · congr 1
        ext j
        exact (ENNReal.ofReal_toReal (h_ne_top j)).symm
      · intro j _
        exact ENNReal.toReal_nonneg

    simp_rw [h_rhs_convert]

    -- Step B.7: Now goal is:
    -- ∫⁻ ofReal (∏_j 1_{B'_j}(X_j)) dμ = ∫⁻ ofReal (∏_j ν(·)(B'_j).toReal) dμ
    --
    -- Since both products are in [0,1] and the integrands are equal a.e.
    -- (via the L¹ limit argument), the integrals are equal.
    --
    -- The remaining step is to show the pointwise a.e. equality:
    -- ∏_j 1_{B'_j}(X_j) = ∏_j ν(·)(B'_j).toReal a.e.
    --
    -- This is NOT true pointwise! The LHS is 0 or 1, the RHS is a product of probabilities.
    -- The equality is only at the level of EXPECTATIONS.
    --
    -- So we need a different approach: show the INTEGRALS are equal.
    --
    -- Key insight: By the U-stat expansion,
    --   ∫ ∏_j 1_{B'_j}(X_j) dμ = lim_N ∫ q N dμ = ∫ ∏_j α_funcs j dμ = ∫ ∏_j ν(·)(B'_j).toReal dμ
    --
    -- Then convert real integrals to ENNReal lintegrals.

    -- FINAL STEP: The integral equality via L¹ limit
    --
    -- Strategy:
    -- 1. From h_prod_L1: ∫ q N → ∫ ∏ r_funcs (L¹ convergence gives integral convergence)
    -- 2. Need: ∫ q N → ∫ ∏ I j j via U-stat expansion
    -- 3. By uniqueness: ∫ ∏ I j j = ∫ ∏ r_funcs
    -- 4. Convert to ENNReal lintegrals

    -- Step 1: L¹ convergence implies integral convergence
    -- From h_prod_L1: |∫ q N - ∫ ∏ r_funcs| ≤ ∫ |q N - ∏ r_funcs| → 0
    --
    -- First, establish integrability (products of bounded functions on probability space)
    -- Product of bounded AEStronglyMeasurable functions is integrable on probability space
    -- Uses: Integrable.of_bound + Finset.aestronglyMeasurable_prod + bound by 1
    -- TODO: eta-expansion issue with Finset.aestronglyMeasurable_prod needs fixing
    -- p N i is AEStronglyMeasurable (product of bounded measurable functions)
    have p_meas : ∀ N i, AEStronglyMeasurable (p N i) μ := fun N i => by
      simp only [p]
      -- (1/(N+1)) * ∑ I i (j+1) is measurable
      have h_sum_meas : Measurable (fun ω => ∑ j : Fin (N + 1), I i (j.val + 1) ω) := by
        apply Finset.measurable_sum
        intro j _
        exact (measurable_const.indicator (hB (σ i))).comp (hX_meas (j.val + 1))
      exact (h_sum_meas.const_mul _).aestronglyMeasurable

    -- p N i ω is in [0, 1] for all N, i, ω
    have p_nonneg : ∀ N i ω, 0 ≤ p N i ω := fun N i ω => by
      simp only [p]
      apply mul_nonneg
      · apply div_nonneg zero_le_one
        exact Nat.cast_nonneg _
      · apply Finset.sum_nonneg
        intro j _
        exact I_nonneg i (j.val + 1) ω

    have p_le_one : ∀ N i ω, p N i ω ≤ 1 := fun N i ω => by
      simp only [p]
      rw [div_mul_eq_mul_div, one_mul]
      apply div_le_one_of_le₀
      · -- ∑ j, I i (j+1) ω ≤ N+1
        calc ∑ j : Fin (N + 1), I i (j.val + 1) ω
            ≤ ∑ _j : Fin (N + 1), (1 : ℝ) := by
                apply Finset.sum_le_sum
                intro j _
                exact I_le_one i (j.val + 1) ω
          _ = (N + 1 : ℕ) := by simp
      · exact Nat.cast_nonneg _

    have q_int : ∀ N, Integrable (q N) μ := fun N => by
      apply Integrable.of_bound (C := 1)
      · -- AEStronglyMeasurable
        simp only [q]
        apply Finset.aestronglyMeasurable_fun_prod
        intro i _
        exact p_meas N i
      · -- Bounded by 1
        filter_upwards with ω
        simp only [q]
        rw [Real.norm_eq_abs, abs_of_nonneg]
        · apply Finset.prod_le_one
          · intro i _; exact p_nonneg N i ω
          · intro i _; exact p_le_one N i ω
        · apply Finset.prod_nonneg
          intro i _; exact p_nonneg N i ω

    have r_prod_int : Integrable (fun ω => ∏ i : Fin (n + 1), r_funcs i ω) μ := by
      apply Integrable.of_bound (C := 1)
      · -- AEStronglyMeasurable: use Finset.aestronglyMeasurable_fun_prod
        apply Finset.aestronglyMeasurable_fun_prod
        intro i _
        exact r_meas i
      · -- Bounded by 1
        filter_upwards with ω
        rw [Real.norm_eq_abs, abs_of_nonneg]
        · apply Finset.prod_le_one
          · intro i _; exact r_nonneg i ω
          · intro i _; exact r_le_one i ω
        · apply Finset.prod_nonneg
          intro i _; exact r_nonneg i ω

    -- L¹ convergence implies integral convergence
    -- Use that |∫ q N - ∫ ∏ r| ≤ ∫ |q N - ∏ r| → 0
    have h_int_prod_r : Tendsto (fun N => ∫ ω, q N ω ∂μ) atTop
        (𝓝 (∫ ω, ∏ i : Fin (n + 1), r_funcs i ω ∂μ)) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      rw [Metric.tendsto_atTop] at h_prod_L1
      obtain ⟨M, hM⟩ := h_prod_L1 ε hε
      refine ⟨M, fun N hN => ?_⟩
      rw [Real.dist_eq]
      calc |∫ ω, q N ω ∂μ - ∫ ω, ∏ i, r_funcs i ω ∂μ|
          = |∫ ω, (q N ω - ∏ i, r_funcs i ω) ∂μ| := by
              rw [integral_sub (q_int N) r_prod_int]
        _ = ‖∫ ω, (q N ω - ∏ i, r_funcs i ω) ∂μ‖ := (Real.norm_eq_abs _).symm
        _ ≤ ∫ ω, ‖q N ω - ∏ i, r_funcs i ω‖ ∂μ := norm_integral_le_integral_norm _
        _ = ∫ ω, |q N ω - ∏ i, r_funcs i ω| ∂μ := by
              apply integral_congr_ae
              filter_upwards with ω
              exact Real.norm_eq_abs _
        _ < ε := by
              specialize hM N hN
              rw [Real.dist_eq, sub_zero, abs_of_nonneg] at hM
              · exact hM
              · exact integral_nonneg (fun ω => abs_nonneg _)

    -- Step 2: The LHS product equals ∏_j I j j.val
    -- LHS: ∏_j (B (σ j)).indicator 1 (X j.val) = ∏_j I j j.val
    have h_lhs_eq_I : ∀ ω, ∏ j : Fin (n + 1), (B (σ j)).indicator (fun _ => (1 : ℝ)) (X j.val ω)
        = ∏ j : Fin (n + 1), I j j.val ω := by
      intro ω
      apply Finset.prod_congr rfl
      intro j _
      simp only [I, B']

    -- Step 3: The identity shift
    -- ∫ ∏_j I j (j+1) = ∫ ∏_j I j j by contractability
    -- (Both use n+1 distinct indices: 1,2,...,n+1 vs 0,1,...,n)
    have h_shift : ∫ ω, ∏ j : Fin (n + 1), I j (j.val + 1) ω ∂μ =
        ∫ ω, ∏ j : Fin (n + 1), I j j.val ω ∂μ := by
      -- Define the two projections
      let proj_shift : Ω → (Fin (n + 1) → ℝ) := fun ω j => X (j.val + 1) ω
      let proj_id : Ω → (Fin (n + 1) → ℝ) := fun ω j => X j.val ω
      -- Both are strictly monotone index sequences
      have h_shift_mono : StrictMono (fun j : Fin (n + 1) => j.val + 1) := by
        intro a b hab; exact Nat.add_lt_add_right hab 1
      have h_id_mono : StrictMono (fun j : Fin (n + 1) => j.val) := fun a b hab => hab
      -- By contractability
      have h_map := hX_contract.allStrictMono_eq (n + 1)
        (fun j => j.val + 1) (fun j => j.val) h_shift_mono h_id_mono
      -- The function to integrate
      let g : (Fin (n + 1) → ℝ) → ℝ := fun x =>
        ∏ j : Fin (n + 1), (B (σ j)).indicator (fun _ => (1 : ℝ)) (x j)
      have hg_meas : Measurable g := by
        apply Finset.measurable_prod
        intro j _
        exact (measurable_const.indicator (hB (σ j))).comp (measurable_pi_apply j)
      -- Measurability of projections
      have h_proj_shift_meas : Measurable proj_shift := by
        apply measurable_pi_lambda; intro j; exact hX_meas (j.val + 1)
      have h_proj_id_meas : Measurable proj_id := by
        apply measurable_pi_lambda; intro j; exact hX_meas j.val
      -- Apply integral_map
      have h_eq_shift : (fun ω => ∏ j, I j (j.val + 1) ω) = (fun ω => g (proj_shift ω)) := by
        ext ω
        simp only [g, proj_shift, I, B']
      have h_eq_id : (fun ω => g (proj_id ω)) = (fun ω => ∏ j, I j j.val ω) := by
        ext ω
        simp only [g, proj_id, I, B']
      calc ∫ ω, ∏ j, I j (j.val + 1) ω ∂μ
          = ∫ ω, g (proj_shift ω) ∂μ := by rw [← h_eq_shift]
        _ = ∫ x, g x ∂(Measure.map proj_shift μ) := by
              rw [integral_map h_proj_shift_meas.aemeasurable hg_meas.aestronglyMeasurable]
        _ = ∫ x, g x ∂(Measure.map proj_id μ) := by rw [h_map]
        _ = ∫ ω, g (proj_id ω) ∂μ := by
              rw [← integral_map h_proj_id_meas.aemeasurable hg_meas.aestronglyMeasurable]
        _ = ∫ ω, ∏ j, I j j.val ω ∂μ := by rw [h_eq_id]

    -- Step 4: U-stat expansion argument
    -- Show ∫ q N → ∫ ∏ I j (j+1) as N → ∞
    -- This uses the collision bound and the fact that injective maps dominate
    --
    -- KEY INSIGHT: Instead of full expansion, use squeeze theorem:
    -- q N ω ≈ ∏_i (1/(N+1)) ∑_j I i (j+1)
    -- The cross terms from different j values are bounded, and the "diagonal"
    -- (identity) term dominates as N → ∞.
    --
    -- For now, we use that both limits equal lim ∫ q N by h_prod_L1,
    -- and the shift gives us the identity case.

    -- By the squeeze/limit argument, ∫ q N → ∫ ∏ I j (j+1) = ∫ ∏ I j j
    -- Combined with h_int_prod_r, we get the desired equality.

    -- The key fact: r_funcs = ν(·)(B' i).toReal = ν(·)(B(σ i)).toReal
    have h_r_eq_rhs : ∀ ω, ∏ j : Fin (n + 1), r_funcs j ω =
        ∏ j : Fin (n + 1), (directing_measure X hX_contract hX_meas hX_L2 ω (B (σ j))).toReal := by
      intro ω
      apply Finset.prod_congr rfl
      intro j _
      simp only [r_funcs, B']

    -- Step 5: Convert real integrals to ENNReal lintegrals
    -- Goal: ∫⁻ (∏ j, ofReal (I j j)) = ∫⁻ (∏ j, ν(B(σj)))

    -- Both products are in [0,1]
    have h_lhs_nonneg : ∀ ω, 0 ≤ ∏ j : Fin (n + 1), I j j.val ω := fun ω => by
      apply Finset.prod_nonneg; intro j _; exact I_nonneg j j.val ω
    have h_rhs_nonneg : ∀ ω,
        0 ≤ ∏ j : Fin (n + 1), (directing_measure X hX_contract hX_meas hX_L2 ω (B (σ j))).toReal :=
      fun ω => by apply Finset.prod_nonneg; intro j _; exact ENNReal.toReal_nonneg

    -- Integrability of indicator product (bounded by 1)
    have h_lhs_int : Integrable (fun ω => ∏ j : Fin (n + 1), I j j.val ω) μ := by
      apply Integrable.of_bound (C := 1)
      · -- AEStronglyMeasurable
        apply Finset.aestronglyMeasurable_fun_prod
        intro j _
        exact ((measurable_const.indicator (hB (σ j))).comp
          (hX_meas j.val)).aestronglyMeasurable
      · -- Bounded by 1
        filter_upwards with ω
        rw [Real.norm_eq_abs, abs_of_nonneg (h_lhs_nonneg ω)]
        apply Finset.prod_le_one
        · intro j _; exact I_nonneg j j.val ω
        · intro j _; exact I_le_one j j.val ω

    -- Integrability of RHS product (bounded by 1)
    have h_rhs_int : Integrable
        (fun ω => ∏ j : Fin (n + 1),
          (directing_measure X hX_contract hX_meas hX_L2 ω (B (σ j))).toReal) μ := by
      apply Integrable.of_bound (C := 1)
      · -- AEStronglyMeasurable
        apply Finset.aestronglyMeasurable_fun_prod
        intro j _
        have h_dm_meas := directing_measure_measurable X hX_contract hX_meas hX_L2 (B (σ j)) (hB (σ j))
        exact ENNReal.measurable_toReal.comp h_dm_meas |>.aestronglyMeasurable
      · -- Bounded by 1
        filter_upwards with ω
        rw [Real.norm_eq_abs, abs_of_nonneg (h_rhs_nonneg ω)]
        apply Finset.prod_le_one
        · intro j _; exact ENNReal.toReal_nonneg
        · intro j _
          have h_prob := directing_measure_isProbabilityMeasure X hX_contract hX_meas hX_L2 ω
          -- ν s ≤ ν univ = 1 for probability measure
          have h_le : directing_measure X hX_contract hX_meas hX_L2 ω (B (σ j)) ≤ 1 :=
            (measure_mono (Set.subset_univ _)).trans_eq h_prob.measure_univ
          exact (ENNReal.toReal_mono ENNReal.one_ne_top h_le).trans_eq ENNReal.one_toReal

    -- Use h_lhs_prod and h_rhs_convert to rewrite both sides as ofReal of products
    -- Then use ofReal_integral_eq_lintegral_ofReal

    -- LHS rewrite: ∫⁻ (∏ j, ofReal (I j j)) = ∫⁻ ofReal (∏ j, I j j)
    have h_lhs_rewrite : ∫⁻ ω, ∏ j, ENNReal.ofReal (I j j.val ω) ∂μ
        = ∫⁻ ω, ENNReal.ofReal (∏ j, I j j.val ω) ∂μ := by
      apply lintegral_congr
      intro ω
      rw [← ENNReal.ofReal_prod_of_nonneg (fun j _ => I_nonneg j j.val ω)]

    -- RHS rewrite: ∫⁻ (∏ j, ν(B(σj))) = ∫⁻ ofReal (∏ j, ν(B(σj)).toReal)
    have h_rhs_rewrite : ∫⁻ ω, ∏ j, directing_measure X hX_contract hX_meas hX_L2 ω (B (σ j)) ∂μ
        = ∫⁻ ω, ENNReal.ofReal (∏ j,
            (directing_measure X hX_contract hX_meas hX_L2 ω (B (σ j))).toReal) ∂μ := by
      apply lintegral_congr
      intro ω
      exact h_rhs_convert ω

    -- Convert lintegrals to real integrals using ofReal_integral_eq_lintegral_ofReal
    -- Need: ∫⁻ ofReal f = ofReal (∫ f) for nonneg f (rearranged)
    have h_lhs_to_real : ∫⁻ ω, ENNReal.ofReal (∏ j, I j j.val ω) ∂μ
        = ENNReal.ofReal (∫ ω, ∏ j, I j j.val ω ∂μ) := by
      rw [← ofReal_integral_eq_lintegral_ofReal h_lhs_int (ae_of_all μ h_lhs_nonneg)]

    have h_rhs_to_real : ∫⁻ ω, ENNReal.ofReal (∏ j,
          (directing_measure X hX_contract hX_meas hX_L2 ω (B (σ j))).toReal) ∂μ
        = ENNReal.ofReal (∫ ω, ∏ j,
            (directing_measure X hX_contract hX_meas hX_L2 ω (B (σ j))).toReal ∂μ) := by
      rw [← ofReal_integral_eq_lintegral_ofReal h_rhs_int (ae_of_all μ h_rhs_nonneg)]

    -- Rewrite LHS and RHS using these lemmas
    -- Goal after simp_rw h_rhs_convert: ∫⁻ ofReal (∏ I) = ∫⁻ ofReal (∏ ν.toReal)
    -- LHS was already rewritten by simp_rw h_lhs_prod, so skip h_lhs_rewrite
    -- Using h_lhs_to_real and h_rhs_to_real, becomes:
    -- ofReal (∫ ∏ I) = ofReal (∫ ∏ ν.toReal)
    rw [h_lhs_to_real, h_rhs_to_real]

    -- Now we need: ∫ (∏ I j j) = ∫ (∏ ν(B(σj)).toReal)
    -- This follows from the calc chain
    congr 1
    calc ∫ ω, ∏ j, I j j.val ω ∂μ
        = ∫ ω, ∏ j, I j (j.val + 1) ω ∂μ := h_shift.symm
      _ = ∫ ω, ∏ j, r_funcs j ω ∂μ := by
          -- U-STAT EXPANSION ARGUMENT
          -- Strategy:
          -- 1. h_int_prod_r: ∫ q N → ∫ ∏ r_funcs
          -- 2. Show: ∫ q N → ∫ ∏ I j (j+1) via expansion
          -- 3. By tendsto_nhds_unique, ∫ ∏ I j (j+1) = ∫ ∏ r_funcs

          -- Step A: Show ∫ q N → ∫ ∏ I j (j+1)
          -- q N = ∏_i (1/(N+1)) ∑_k I i (k+1)
          --     = (1/(N+1))^{n+1} ∑_φ ∏_i I i (φ(i)+1)
          --
          -- For injective φ, by contractability:
          --   E[∏ I i (φ(i)+1)] = E[∏ I i (i+1)]
          --
          -- So: ∫ q N = (# inj/(N+1)^m) * ∫ ∏ I + O(# non-inj/(N+1)^m)
          --          → 1 * ∫ ∏ I + 0 as N → ∞

          -- The expected value of the product indicator
          let E_prod := ∫ ω, ∏ j : Fin (n + 1), I j (j.val + 1) ω ∂μ

          -- Integrability of ∏ I j (j+1) - bounded measurable on probability space
          have h_I_prod_int : Integrable (fun ω => ∏ j : Fin (n + 1), I j (j.val + 1) ω) μ := by
            apply Integrable.of_bound (C := 1)
            · -- AEStronglyMeasurable
              apply Finset.aestronglyMeasurable_fun_prod
              intro j _
              exact ((measurable_const.indicator (hB (σ j))).comp
                (hX_meas (j.val + 1))).aestronglyMeasurable
            · -- Bounded by 1
              filter_upwards with ω
              rw [Real.norm_eq_abs, abs_of_nonneg]
              · apply Finset.prod_le_one
                · intro j _; exact I_nonneg j (j.val + 1) ω
                · intro j _; exact I_le_one j (j.val + 1) ω
              · apply Finset.prod_nonneg
                intro j _; exact I_nonneg j (j.val + 1) ω

          -- Bound on each product of indicators (for any index function)
          -- Each factor I j k ω is in [0,1], so product is in [0,1] as well.
          have h_prod_bound : ∀ (N : ℕ) (φ : Fin (n + 1) → Fin (N + 1)) (ω : Ω),
              |∏ j : Fin (n + 1), I j (φ j).val ω| ≤ 1 := fun N φ ω => by
            rw [abs_of_nonneg]
            · -- ∏ I j k ω ≤ 1 since each I j k ω ≤ 1
              apply Finset.prod_le_one
              · intro j _; exact I_nonneg j (φ j).val ω
              · intro j _; exact I_le_one j (φ j).val ω
            · -- 0 ≤ ∏ I j k ω since each I j k ω ≥ 0
              apply Finset.prod_nonneg
              intro j _; exact I_nonneg j (φ j).val ω

          -- TECHNICAL NOTE: The claim "∫ ∏ I i (φ(i)) = E_prod for all injective φ" requires
          -- EXCHANGEABILITY, not just contractability. Contractability only gives equality
          -- for strictly monotone selections via allStrictMono_eq.
          --
          -- For a general injective φ = k' ∘ τ (where k' is strictly monotone and τ is a permutation):
          -- ∫ ∏_j I j (φ j) dμ = ∫ ∏_j I j (k' (τ j)) dμ
          --                    = ∫ ∏_i I (τ⁻¹ i) (k' i) dμ  [substituting i = τ j]
          --                    = ∫ g(X (k' 0), ..., X (k' n)) dμ  where g depends on τ
          --                    = ∫ g(X 0, ..., X n) dμ  [by allStrictMono_eq]
          --
          -- This equals E_prod only if the distribution of (X_0, ..., X_n) is symmetric
          -- under permutation, i.e., EXCHANGEABILITY.
          --
          -- The resolution is that contractable sequences ARE exchangeable (de Finetti),
          -- so this equality holds. But we're in the middle of proving de Finetti!
          --
          -- ALTERNATIVE APPROACH: Use the fact that the strictly monotone selections
          -- (which are 1/m! of all injective selections) give the correct value, and
          -- show the average over all injective selections also converges to E_prod
          -- by a symmetry argument.
          --
          -- For now, we assume this claim and defer the full proof.
          have h_inj_eq : ∀ N ≥ n, ∀ (φ : Fin (n + 1) → Fin (N + 1)),
              Function.Injective φ →
                ∫ ω, ∏ j : Fin (n + 1), I j (φ j).val ω ∂μ = E_prod := by
            intro N hN φ hφ
            -- Deferred: requires exchangeability (consequence of de Finetti)
            -- or a sophisticated symmetry argument using the specific structure of B and σ.
            sorry

          -- U-stat expansion: ∫ q N → E_prod
          have h_qN_tends : Tendsto (fun N => ∫ ω, q N ω ∂μ) atTop (𝓝 E_prod) := by
            rw [Metric.tendsto_atTop]
            intro ε hε
            -- For large N, the non-injective fraction is < ε/2
            have h_frac := nonInjective_fraction_tendsto_zero (n + 1)
            rw [Metric.tendsto_atTop] at h_frac
            obtain ⟨M1, hM1⟩ := h_frac (ε / 2) (half_pos hε)
            -- Also need N ≥ n so injective maps exist
            let M := max M1 n
            refine ⟨M, fun N hN => ?_⟩
            -- q N ω = (1/(N+1))^{n+1} * ∑_φ ∏_j I j (φ(j)+1)
            -- where the sum is over φ : Fin (n+1) → Fin (N+1)
            -- Actually, q N = ∏_i p N i = ∏_i (1/(N+1)) ∑_k I i (k+1)
            -- For clarity, let's compute ∫ q N directly using the definition

            -- Due to technical complexity with Fintype.prod_sum in Lean 4,
            -- we use a squeeze argument instead.
            -- |∫ q N - E_prod| ≤ |∫ q N - ∫ ∏ r_funcs| + |∫ ∏ r_funcs - E_prod|
            -- The first term → 0 by h_int_prod_r.
            -- The second term will be shown small via the same limit.

            -- Since both h_int_prod_r and what we're proving give the same limit,
            -- we use that ∫ ∏ r_funcs is the limit of ∫ q N.
            -- Then E_prod also equals this limit by the expansion argument.

            -- For a cleaner proof, note that we already have h_int_prod_r showing
            -- ∫ q N → ∫ ∏ r_funcs. If we can show E_prod = ∫ ∏ r_funcs (the goal!),
            -- then h_int_prod_r gives us this tendsto.

            -- This is circular! We need a direct argument.
            -- The direct argument uses the expansion formula.

            -- DIRECT COMPUTATION:
            -- ∫ q N ω dμ(ω) is linear in the product expansion.
            -- However, the formal expansion is complex.
            -- Instead, use that q N is uniformly bounded in [0,1] and
            -- converges pointwise to a limit (which by DCT equals the integral limit).

            -- Actually, the L¹ bound directly gives convergence to the limit.
            -- Since h_prod_L1 shows ‖q N - ∏ r_funcs‖₁ → 0,
            -- the integrals must converge: ∫ q N → ∫ ∏ r_funcs.

            -- We claim E_prod = ∫ ∏ r_funcs, which is what we're trying to prove!
            -- This seems circular. The resolution is that we need the U-stat expansion
            -- to establish the equality, not assume it.

            -- RESOLUTION: The U-stat expansion shows that for each N,
            -- |∫ q N - E_prod| ≤ (non-injective fraction) * 2 → 0.
            -- This is because:
            -- ∫ q N = (1/(N+1))^m * ∑_φ ∫ ∏ I j (φ j)
            -- For injective φ: ∫ ∏ I = E_prod
            -- For non-injective φ: |∫ ∏ I| ≤ 1
            -- So |∫ q N - E_prod| ≤ |∫ q N - (# inj/(N+1)^m) * E_prod|
            --                       + |(# inj/(N+1)^m) * E_prod - E_prod|
            -- = (# non-inj/(N+1)^m) * (bound) + (1 - # inj/(N+1)^m) * |E_prod|
            -- = O(non-inj fraction) → 0

            -- For now, use a simplified bound that directly leverages measurability
            -- and the L¹ framework we've built.

            -- Since this is getting complex, let's use the existing infrastructure:
            -- We showed h_int_prod_r: ∫ q N → ∫ ∏ r_funcs
            -- We need: E_prod = ∫ ∏ r_funcs

            -- The key insight is that BOTH limits are determined by the sequence ∫ q N.
            -- Since limits are unique, if we can show ∫ q N → E_prod, then E_prod = ∫ ∏ r_funcs.

            -- For a complete formal proof, we'd need to expand q N using Fintype.prod_sum.
            -- This is technically involved, so we mark this step as admitting the
            -- U-stat expansion formula and focus on the limit argument.

            -- The bound follows from the U-stat expansion (which uses h_inj_eq).
            -- Let m = n + 1. By Fintype.prod_sum:
            --   ∫ q N = (1/(N+1))^m ∑_φ ∫ ∏_j I j (φ(j)+1)
            -- Split by injectivity:
            --   = (1/(N+1))^m [∑_{φ inj} ∫ ∏ I + ∑_{φ non-inj} ∫ ∏ I]
            -- By h_inj_eq: ∑_{φ inj} ∫ ∏ I = (# inj) * E_prod
            -- Each non-inj term is bounded by 1: ∑_{φ non-inj} ∫ ∏ I ≤ # non-inj
            -- So: |∫ q N - E_prod| ≤ |# inj / (N+1)^m - 1| * |E_prod| + # non-inj / (N+1)^m
            --                      = (# non-inj / (N+1)^m) * |E_prod| + # non-inj / (N+1)^m
            --                      ≤ 2 * # non-inj / (N+1)^m
            --                      → 0 by nonInjective_fraction_tendsto_zero
            have hN_ge_n : N ≥ n := le_of_max_le_right hN
            have hN_ge_M1 : N ≥ M1 := le_of_max_le_left hN
            specialize hM1 N hN_ge_M1
            rw [Real.dist_eq, abs_of_nonneg] at hM1
            · simp only [Real.dist_eq]
              -- DEFERRED: Full U-stat expansion proof.
              -- The argument above shows the bound, assuming h_inj_eq.
              -- Both h_inj_eq and this step are logically equivalent to
              -- establishing exchangeability from contractability (de Finetti).
              sorry
            · rw [sub_zero]
              apply div_nonneg (Nat.cast_nonneg _)
              exact pow_nonneg (Nat.cast_nonneg (α := ℝ) N) _

          -- By uniqueness of limits
          exact tendsto_nhds_unique h_qN_tends h_int_prod_r
      _ = ∫ ω, ∏ j, (directing_measure X hX_contract hX_meas hX_L2 ω (B (σ j))).toReal ∂μ := by
          apply integral_congr_ae
          filter_upwards with ω
          exact h_r_eq_rhs ω

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
    exact directing_measure_measurable X hX_contract hX_meas hX_L2 s hs
  -- Property 3: Bridge property (requires injectivity of k)
  · intro m k hk_inj B hB
    exact directing_measure_bridge X hX_contract hX_meas hX_L2 k hk_inj B hB

end Exchangeability.DeFinetti.ViaL2

