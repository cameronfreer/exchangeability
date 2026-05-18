/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Exchangeability.DeFinetti.ViaL2.Clip01
import Exchangeability.DeFinetti.ViaL2.BlockAverages
import Exchangeability.DeFinetti.ViaL2.CesaroConvergence
import Exchangeability.DeFinetti.ViaL2.MainConvergence
import Exchangeability.DeFinetti.ViaL2.DirectingMeasureIntegral
import Exchangeability.DeFinetti.L2Helpers
import Exchangeability.DeFinetti.BridgeProperty
import Exchangeability.Contractability
import Exchangeability.Tail.CondExpShiftInvariance
import Exchangeability.Util.StrictMono
import Exchangeability.Util.ProductBounds
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Analysis.SpecialFunctions.Choose

/-!
# Additional L² helpers

Technical lemmas supporting the L² proof of de Finetti's theorem.

## Contents

* Elementary helpers (clip01, Lipschitz properties)
* L¹ convergence helpers
* Boundedness helpers
* AE strong measurability helpers
* CDF/Stieltjes constructions used by `MainConvergence.lean`
-/

noncomputable section

namespace Exchangeability.DeFinetti.ViaL2

open MeasureTheory ProbabilityTheory BigOperators Filter Topology
open Exchangeability
open Exchangeability.Util.StrictMono (injective_implies_strictMono_perm)

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-! ## CDF construction via `stieltjesOfMeasurableRat`

Wraps mathlib's measurable-rational-CDF infrastructure to give CDFs with the right
boundary behavior at ±∞ for every ω (not just a.e.).
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
  · exact .of_forall fun _ => zero_le _
  · exact .of_forall fun n => hmono n

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
@[nolint unusedArguments]
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
          congr 1
          · -- First term: use _h_avg_eq' to rewrite c * (average) to average of c*f
            rw [← _h_avg_eq']
          · -- Second term: swap order in absolute value
            rw [abs_sub_comm]

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
          have h_int1 : Integrable (fun ω => |(1 / (m : ℝ)) * ∑ k : Fin m, (c * f (X (k.val + 1) ω)) - alpha_c ω|) μ :=
            (h_avg_cf_int.sub h_alpha_c_int).abs
          have h_int2 : Integrable (fun ω => |c| * |(1 / (m : ℝ)) * ∑ k : Fin m, f (X (k.val + 1) ω) - alpha ω|) μ :=
            (h_avg_f_int.sub h_alpha_int).abs.const_mul _
          rw [integral_add h_int1 h_int2, integral_const_mul]

    -- Derive |c| * ∫|avg_f - alpha| ≤ |c| * (ε/(|c|+1))
    have h_scaled : |c| * ∫ ω, |(1 / (m : ℝ)) * ∑ k : Fin m, f (X (k.val + 1) ω) - alpha ω| ∂μ ≤ |c| * (ε / (|c| + 1)) := by
      exact mul_le_mul_of_nonneg_left (le_of_lt hM₂) (abs_nonneg _)

    -- Final bound: < ε + |c| * (ε / (|c| + 1)) < 2ε < 4ε = ∫|...|
    -- This gives ∫|...| < ∫|...|, a contradiction
    have h_strict_ineq : ∫ ω, |alpha_c ω - c * alpha ω| ∂μ < 4 * ε :=
      calc ∫ ω, |alpha_c ω - c * alpha ω| ∂μ
          ≤ ∫ ω, |(1 / (m : ℝ)) * ∑ k : Fin m, (c * f (X (k.val + 1) ω)) - alpha_c ω| ∂μ +
            |c| * ∫ ω, |(1 / (m : ℝ)) * ∑ k : Fin m, f (X (k.val + 1) ω) - alpha ω| ∂μ := h_int_bound
        _ < ε + |c| * (ε / (|c| + 1)) := by linarith [hM₁, h_scaled]
        _ < ε + ε := by linarith [_h_bound]
        _ = 2 * ε := by ring
        _ < 4 * ε := by linarith
    -- But 4 * ε = ∫|...|, so we have ∫|...| < ∫|...|
    have h_eq_4eps : ∫ ω, |alpha_c ω - c * alpha ω| ∂μ = 4 * ε := by linarith [hε_def]
    linarith

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
             (1 / (m : ℝ)) * ∑ k : Fin m, g (X (k.val + 1) ω) - alpha_g ω| := by
          -- Apply abs_add_le with correct associativity
          have h := abs_add_le (-((1 / (m : ℝ)) * ∑ k : Fin m, (f + g) (X (k.val + 1) ω) - alpha_fg ω))
              ((1 / (m : ℝ)) * ∑ k : Fin m, f (X (k.val + 1) ω) - alpha_f ω +
               (1 / (m : ℝ)) * ∑ k : Fin m, g (X (k.val + 1) ω) - alpha_g ω)
          convert h using 1
          ring
        _ ≤ |-((1 / (m : ℝ)) * ∑ k : Fin m, (f + g) (X (k.val + 1) ω) - alpha_fg ω)| +
            (|(1 / (m : ℝ)) * ∑ k : Fin m, f (X (k.val + 1) ω) - alpha_f ω| +
            |(1 / (m : ℝ)) * ∑ k : Fin m, g (X (k.val + 1) ω) - alpha_g ω|) := by
          -- First, fix the parenthesization inside the absolute value from the previous step
          -- The previous RHS has |A - α_f + B - α_g| which parses as |((A - α_f) + B) - α_g|
          -- We need |(A - α_f) + (B - α_g)| to apply abs_add_le
          have h_paren : |(1 / (m : ℝ)) * ∑ k : Fin m, f (X (k.val + 1) ω) - alpha_f ω +
                          (1 / (m : ℝ)) * ∑ k : Fin m, g (X (k.val + 1) ω) - alpha_g ω| =
                         |((1 / (m : ℝ)) * ∑ k : Fin m, f (X (k.val + 1) ω) - alpha_f ω) +
                          ((1 / (m : ℝ)) * ∑ k : Fin m, g (X (k.val + 1) ω) - alpha_g ω)| := by
            congr 1; ring
          rw [h_paren]
          have h_tri := abs_add_le ((1 / (m : ℝ)) * ∑ k : Fin m, f (X (k.val + 1) ω) - alpha_f ω)
              ((1 / (m : ℝ)) * ∑ k : Fin m, g (X (k.val + 1) ω) - alpha_g ω)
          gcongr
        _ = |-((1 / (m : ℝ)) * ∑ k : Fin m, (f + g) (X (k.val + 1) ω) - alpha_fg ω)| +
            |(1 / (m : ℝ)) * ∑ k : Fin m, f (X (k.val + 1) ω) - alpha_f ω| +
            |(1 / (m : ℝ)) * ∑ k : Fin m, g (X (k.val + 1) ω) - alpha_g ω| := by ring
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

    -- Final bound: < ε + ε + ε = 3ε < 4ε = ∫|...|
    -- This gives ∫|...| < ∫|...|, a contradiction
    have h_strict_ineq : ∫ ω, |alpha_fg ω - (alpha_f ω + alpha_g ω)| ∂μ < 4 * ε :=
      calc ∫ ω, |alpha_fg ω - (alpha_f ω + alpha_g ω)| ∂μ
          ≤ ∫ ω, |(1 / (m : ℝ)) * ∑ k : Fin m, (f + g) (X (k.val + 1) ω) - alpha_fg ω| ∂μ +
            ∫ ω, |(1 / (m : ℝ)) * ∑ k : Fin m, f (X (k.val + 1) ω) - alpha_f ω| ∂μ +
            ∫ ω, |(1 / (m : ℝ)) * ∑ k : Fin m, g (X (k.val + 1) ω) - alpha_g ω| ∂μ := h_int_bound
        _ < ε + ε + ε := by
          have h1 := add_lt_add hM_fg hM_f
          have h2 := add_lt_add h1 hM_g
          convert h2 using 1 <;> ring
        _ = 3 * ε := by ring
        _ < 4 * ε := by linarith
    -- But 4 * ε = ∫|...|, so we have ∫|...| < ∫|...|
    have h_eq_4eps : ∫ ω, |alpha_fg ω - (alpha_f ω + alpha_g ω)| ∂μ = 4 * ε := by linarith [hε_def]
    linarith

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
               (((1 / (m : ℝ)) * ∑ k : Fin m, f (X (k.val + 1) ω)) - alpha ω)| := by
            -- Fix parenthesization: |-A + B - C| parses as |(-A + B) - C|, need |(-A) + (B - C)|
            have h_paren : |-(((1 / (m : ℝ)) * ∑ k : Fin m, (1 - f (X (k.val + 1) ω))) - alpha_sub ω) +
                            (((1 / (m : ℝ)) * ∑ _k : Fin m, (1 : ℝ)) - alpha_1 ω) -
                            (((1 / (m : ℝ)) * ∑ k : Fin m, f (X (k.val + 1) ω)) - alpha ω)| =
                           |(-(((1 / (m : ℝ)) * ∑ k : Fin m, (1 - f (X (k.val + 1) ω))) - alpha_sub ω)) +
                            ((((1 / (m : ℝ)) * ∑ _k : Fin m, (1 : ℝ)) - alpha_1 ω) -
                             (((1 / (m : ℝ)) * ∑ k : Fin m, f (X (k.val + 1) ω)) - alpha ω))| := by
              congr 1; ring
            rw [h_paren]
            exact abs_add_le _ _
          _ ≤ |-(((1 / (m : ℝ)) * ∑ k : Fin m, (1 - f (X (k.val + 1) ω))) - alpha_sub ω)| +
              (|(((1 / (m : ℝ)) * ∑ _k : Fin m, (1 : ℝ)) - alpha_1 ω)| +
              |(((1 / (m : ℝ)) * ∑ k : Fin m, f (X (k.val + 1) ω)) - alpha ω)|) := by
            -- Apply triangle inequality: |B - C| ≤ |B| + |C|. Use abs_sub_le B 0 C.
            have h_bound := abs_sub_le
                (((1 / (m : ℝ)) * ∑ _k : Fin m, (1 : ℝ)) - alpha_1 ω) 0
                (((1 / (m : ℝ)) * ∑ k : Fin m, f (X (k.val + 1) ω)) - alpha ω)
            simp only [sub_zero, zero_sub, abs_neg] at h_bound
            gcongr
          -- Convert right-associative to left-associative
          _ = |-(((1 / (m : ℝ)) * ∑ k : Fin m, (1 - f (X (k.val + 1) ω))) - alpha_sub ω)| +
              |(((1 / (m : ℝ)) * ∑ _k : Fin m, (1 : ℝ)) - alpha_1 ω)| +
              |(((1 / (m : ℝ)) * ∑ k : Fin m, f (X (k.val + 1) ω)) - alpha ω)| := by ring
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
      (∀ᵐ ω ∂μ, alpha ω = ∫ x, f x ∂(directing_measure X hX_contract hX_meas hX_L2 ω)) :=
  -- Use the simplified identification chain approach (Kallenberg-aligned)
  directing_measure_integral_via_chain X hX_contract hX_meas hX_L2 f hf_meas hf_bdd

/-- **Packaged directing measure theorem:** Existence of a directing kernel with all
key properties bundled together.

For a contractable sequence X on ℝ, there exists:
1. A limit function α ∈ L¹ that is the L¹ limit of Cesàro averages
2. A random probability measure ν(·) on ℝ (the directing measure)
3. The identification α = ∫ f dν a.e.

This packages the outputs of `directing_measure` and `directing_measure_integral`
into a single existential statement that is convenient for applications.

**Proof:** Follows directly from `directing_measure_integral` which provides
the limit α and its identification with ∫ f dν, combined with
`directing_measure_isProbabilityMeasure` and `directing_measure_measurable`.
-/
lemma alpha_is_conditional_expectation_packaged
  {Ω : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
  (hX_meas : ∀ i, Measurable (X i))
  (hX_L2 : ∀ i, MemLp (X i) 2 μ)
  (f : ℝ → ℝ) (hf_meas : Measurable f)
  (hf_bdd : ∃ C, ∀ x, |f x| ≤ C) :
  ∃ (alpha : Ω → ℝ) (nu : Ω → Measure ℝ),
    Measurable alpha ∧
    MemLp alpha 1 μ ∧
    (∀ ω, IsProbabilityMeasure (nu ω)) ∧
    (∀ s, MeasurableSet s → Measurable (fun ω => nu ω s)) ∧
    -- L¹ convergence: Cesàro averages converge to alpha
    (∀ n, ∀ ε > 0, ∃ M : ℕ, ∀ m : ℕ, m ≥ M →
      ∫ ω, |(1/(m:ℝ)) * ∑ k : Fin m, f (X (n + k.val + 1) ω) - alpha ω| ∂μ < ε) ∧
    -- Identification: alpha equals the integral against nu
    (∀ᵐ ω ∂μ, alpha ω = ∫ x, f x ∂(nu ω)) := by
  -- Use directing_measure for nu and directing_measure_integral for alpha
  obtain ⟨alpha, hα_meas, hα_L1, hα_conv, hα_eq⟩ :=
    directing_measure_integral X hX_contract hX_meas hX_L2 f hf_meas hf_bdd
  refine ⟨alpha, directing_measure X hX_contract hX_meas hX_L2, hα_meas, hα_L1, ?_, ?_, hα_conv, hα_eq⟩
  · exact directing_measure_isProbabilityMeasure X hX_contract hX_meas hX_L2
  · exact fun s hs => directing_measure_measurable X hX_contract hX_meas hX_L2 s hs

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
      apply HasFiniteIntegral.of_bounded (C := 1)
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
          conv_lhs => rw [show (fun ω => ‖(A m - limit) ω‖ₑ) = (fun ω => ‖A m ω - limit ω‖ₑ) from rfl]
          rw [← ofReal_integral_norm_eq_lintegral_enorm (h_diff_int m)]
          exact le_top
        · -- ε ≠ ⊤ case: use L¹ convergence
          obtain ⟨M, hM⟩ := Metric.tendsto_atTop.mp h_tendsto_L1 ε.toReal
            (ENNReal.toReal_pos hε.ne' hε_top)
          refine ⟨M, fun m hm => ?_⟩
          have := hM m hm
          simp only [Real.dist_eq, sub_zero] at this
          conv_lhs => rw [show (fun ω => ‖(A m - limit) ω‖ₑ) = (fun ω => ‖A m ω - limit ω‖ₑ) from rfl]
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
      rw [integral_const_mul]
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

**Note:** The lemma `injective_implies_strictMono_perm` is now in
`Exchangeability.Util.StrictMono` and imported via `open` at the top of this file.
-/

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
@[nolint unusedArguments]
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
      push Not at hφ
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
        push Not at hφ
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
        push Not at hφ
        obtain ⟨i, j, heq, hne⟩ := hφ
        refine ⟨(i, j), ?_, heq⟩
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
      push Not at hφ
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
    Exchangeability.Util.abs_prod_sub_prod_le (fun i => f n i ω) (fun i => g i ω)
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
        _ ≤ |f n i ω| + |g i ω| := Exchangeability.Util.abs_sub_le_abs_add _ _
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

/-- Block index function is strictly monotone.

For the block-separated approach, we define indices using disjoint ordered blocks:
  k_φ(i) := i * N + φ(i)  for φ : Fin m → Fin N

This is STRICTLY MONOTONE for any φ because:
  k_φ(i) = i * N + φ(i) ≤ i * N + (N-1) < (i+1) * N ≤ k_φ(i+1)

This is the key insight that makes the block-separated approach work:
every selection is StrictMono, so contractability applies to EVERY term
(no exchangeability required).
-/
@[nolint unusedArguments]
lemma block_index_strictMono {m N : ℕ} (_hN : 0 < N) (φ : Fin m → Fin N) :
    StrictMono (fun i : Fin m => i.val * N + (φ i).val) := by
  intro i j hij
  -- Need: i * N + φ(i) < j * N + φ(j)
  -- Since i < j, we have i + 1 ≤ j, so (i+1) * N ≤ j * N
  -- Also, i * N + φ(i) ≤ i * N + (N-1) = (i+1) * N - 1 < (i+1) * N
  have hφ_bound : (φ i).val < N := (φ i).isLt
  have hi_bound : i.val * N + (φ i).val < (i.val + 1) * N := by
    rw [Nat.add_mul, Nat.one_mul]
    exact Nat.add_lt_add_left hφ_bound _
  have hj_lower : (i.val + 1) * N ≤ j.val * N := by
    have h : i.val + 1 ≤ j.val := hij
    exact Nat.mul_le_mul_right N h
  calc i.val * N + (φ i).val
      < (i.val + 1) * N := hi_bound
    _ ≤ j.val * N := hj_lower
    _ ≤ j.val * N + (φ j).val := Nat.le_add_right _ _

/-- The bridge property: E[∏ᵢ 𝟙_{Bᵢ}(X_{k(i)})] = E[∏ᵢ ν(·)(Bᵢ)].

This is the key property needed for `complete_from_directing_measure`.
Uses `indicator_product_bridge` from `BridgeProperty.lean`, establishing that
the directing measure satisfies `hν_law` via shift invariance of conditional expectations.
-/
lemma directing_measure_bridge
    [StandardBorelSpace Ω]
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
  -- Apply indicator_product_bridge after showing directing_measure satisfies hν_law
  let ν := directing_measure X hX_contract hX_meas hX_L2
  have hν_prob : ∀ ω, IsProbabilityMeasure (ν ω) :=
    directing_measure_isProbabilityMeasure X hX_contract hX_meas hX_L2
  have hν_meas : ∀ B : Set ℝ, MeasurableSet B → Measurable (fun ω => ν ω B) :=
    directing_measure_measurable X hX_contract hX_meas hX_L2
  -- Establish hν_law: (ν ω B).toReal =ᵐ E[1_B ∘ X n | tail] for all n
  have hν_law : ∀ n B, MeasurableSet B →
      (fun ω => (ν ω B).toReal) =ᵐ[μ]
        μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ (X n) | ViaMartingale.tailSigma X] := by
    intro n B hB
    have h_tail_eq : ViaMartingale.tailSigma X = TailSigma.tailSigma X :=
      ViaMartingale.tailSigma_eq_canonical X
    have hf_meas : Measurable (Set.indicator B (fun _ => (1 : ℝ))) :=
      measurable_const.indicator hB
    -- Base case n=0: directing_measure_integral_eq_condExp gives ∫ 1_B dν =ᵐ E[1_B ∘ X 0 | tail]
    have h_n0 : (fun ω => (ν ω B).toReal) =ᵐ[μ]
        μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ (X 0) | TailSigma.tailSigma X] := by
      have h_eq := directing_measure_integral_eq_condExp X hX_contract hX_meas hX_L2
        (Set.indicator B (fun _ => (1 : ℝ))) hf_meas
        ⟨1, fun x => by simp only [Set.indicator]; split_ifs <;> norm_num⟩
      have h_integral : ∀ ω, ∫ x, Set.indicator B (fun _ => (1 : ℝ)) x ∂(ν ω) = (ν ω B).toReal := by
        intro ω
        have h1 : Set.indicator B (fun _ => (1 : ℝ)) = B.indicator 1 := by
          ext x; simp only [Set.indicator, Pi.one_apply]
        rw [h1, integral_indicator_one hB]; rfl
      filter_upwards [h_eq] with ω hω; rw [← h_integral ω, hω]; rfl
    -- Shift invariance: E[1_B ∘ X n | tail] =ᵐ E[1_B ∘ X 0 | tail]
    have h_shift : μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ (X n) | TailSigma.tailSigma X] =ᵐ[μ]
        μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ (X 0) | TailSigma.tailSigma X] :=
      Exchangeability.Tail.ShiftInvariance.condExp_shift_eq_condExp X hX_contract hX_meas
        (Set.indicator B (fun _ => (1 : ℝ))) hf_meas
        ((integrable_const 1).indicator (hX_meas 0 hB)) n
    calc (fun ω => (ν ω B).toReal) =ᵐ[μ]
        μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ (X 0) | TailSigma.tailSigma X] := h_n0
      _ =ᵐ[μ] μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ (X n) | TailSigma.tailSigma X] := h_shift.symm
      _ =ᵐ[μ] μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ (X n) | ViaMartingale.tailSigma X] := by
          rw [h_tail_eq]
  exact indicator_product_bridge X hX_contract hX_meas ν hν_prob hν_meas hν_law k hk B hB

/-! ### Original proof structure (commented out due to incomplete lemmas)

The original proof attempted to show:
1. Reduce injective k to strictly monotone via permutation
2. Use contractability for distributional equality
3. Apply U-statistic expansion for product expectations
4. Conclude via L¹ convergence of block averages

Key intermediate lemmas that need completion:
- h_pblock_vs_shifted: Bound on shifted averages
- h_L1_shifted_ref: L¹ bound from L² via Cauchy-Schwarz
- h_block_L1: Product L¹ convergence
-/

/-- **Main packaging theorem for L² proof.**

This theorem packages all the directing measure properties needed by
`CommonEnding.complete_from_directing_measure`:

1. `ν` is a probability measure for all ω
2. `ω ↦ ν(ω)(s)` is measurable for all measurable sets s
3. The bridge property: E[∏ᵢ 1_{Bᵢ}(X_{k(i)})] = E[∏ᵢ ν(·)(Bᵢ)]

This enables the final step of the L² proof of de Finetti's theorem.
-/
theorem directing_measure_satisfies_requirements
    [StandardBorelSpace Ω]
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

