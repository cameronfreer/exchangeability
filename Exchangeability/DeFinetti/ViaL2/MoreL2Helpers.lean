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

