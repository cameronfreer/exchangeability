/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Exchangeability.DeFinetti.ViaL2.DirectingMeasureCore

/-!
# Directing Measure Integrals: Bridge Lemma and Conditional Expectation

This file establishes the key "bridge lemma" connecting the directing measure
to conditional expectation: for bounded measurable f,

  ∫ f dν(ω) = E[f(X₀) | tail](ω)  a.e.

This is the final piece connecting the Cesàro convergence theory to the
directing measure construction.

## Main results

* `directing_measure_integral_Iic_ae_eq_alphaIicCE`: Base case for Iic indicators
* `integral_indicator_borel_tailAEStronglyMeasurable`: Tail measurability of integrals
* `setIntegral_directing_measure_indicator_eq`: Set integral equality for indicators
* `setIntegral_directing_measure_bounded_measurable_eq`: General set integral equality
* `directing_measure_integral_eq_condExp`: Main bridge lemma

## References

* Kallenberg (2005), *Probabilistic Symmetries and Invariance Principles*,
  Chapter 1, "Second proof of Theorem 1.1"
-/

noncomputable section

namespace Exchangeability.DeFinetti.ViaL2

open MeasureTheory ProbabilityTheory BigOperators Filter Topology
open Exchangeability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-!
## Bridge Lemma: Integral against directing measure equals conditional expectation

This is the key Kallenberg insight: the directing measure ν(ω) is the conditional distribution
of X₀ given the tail σ-algebra. Therefore:

  ∫ f dν(ω) = E[f(X₀) | tail](ω)  a.e.

**Proof Strategy:**
1. **Base case (Iic indicators):** By Stieltjes construction,
   `∫ 1_{Iic t} dν(ω) = alphaIic t ω = alphaIicCE t ω = E[1_{Iic t}(X₀)|tail](ω)` a.e.

2. **Extension:** Iic sets form a π-system generating the Borel σ-algebra.
   By measure extensionality, two probability measures agreeing on Iic agree everywhere.
   The same linearity/continuity argument extends to all bounded measurable f.

This lemma is the bridge that allows us to go from:
- `cesaro_to_condexp_L2`: α = E[f(X₀)|tail]
to:
- `directing_measure_integral`: α = ∫f dν

by transitivity.
-/

/-- **Base case:** For Iic indicators, the directing measure integral equals alphaIicCE.

This follows from:
1. Stieltjes construction: `∫ 1_{Iic t} dν(ω) = (ν(Iic t)).toReal`
2. Measure value: `(ν(Iic t)).toReal = stieltjesOfMeasurableRat t`
3. Stieltjes extension: `stieltjesOfMeasurableRat t = alphaIic t` a.e.
4. Identification: `alphaIic t =ᵐ alphaIicCE t` -/
lemma directing_measure_integral_Iic_ae_eq_alphaIicCE
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ)
    (t : ℝ) :
    (fun ω => ∫ x, (Set.Iic t).indicator (fun _ => (1:ℝ)) x
        ∂(directing_measure X hX_contract hX_meas hX_L2 ω))
      =ᵐ[μ] alphaIicCE X hX_contract hX_meas hX_L2 t := by
  -- Step 1: Simplify integral to measure value
  have h_integral_eq : ∀ ω, ∫ x, (Set.Iic t).indicator (fun _ => (1 : ℝ)) x
      ∂(directing_measure X hX_contract hX_meas hX_L2 ω) =
      (directing_measure X hX_contract hX_meas hX_L2 ω (Set.Iic t)).toReal := by
    intro ω
    rw [MeasureTheory.integral_indicator measurableSet_Iic]
    simp only [MeasureTheory.integral_const, smul_eq_mul, mul_one]
    rw [Measure.real_def, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]

  -- Step 2: The measure on Iic t equals the Stieltjes function value
  have h_meas_eq : ∀ ω, (directing_measure X hX_contract hX_meas hX_L2 ω (Set.Iic t)).toReal =
      (ProbabilityTheory.stieltjesOfMeasurableRat
        (alphaIicRat X hX_contract hX_meas hX_L2)
        (measurable_alphaIicRat X hX_contract hX_meas hX_L2) ω) t := by
    intro ω
    unfold directing_measure
    rw [ProbabilityTheory.measure_stieltjesOfMeasurableRat_Iic]
    have h_nonneg : 0 ≤ (ProbabilityTheory.stieltjesOfMeasurableRat
          (alphaIicRat X hX_contract hX_meas hX_L2)
          (measurable_alphaIicRat X hX_contract hX_meas hX_L2) ω) t :=
      ProbabilityTheory.stieltjesOfMeasurableRat_nonneg _ _ _
    exact ENNReal.toReal_ofReal h_nonneg

  -- Step 3: Combine and use identification with alphaIicCE
  -- The Stieltjes extension equals alphaIic a.e., and alphaIic =ᵐ alphaIicCE

  -- We need to filter on the set where IsRatStieltjesPoint alphaIicRat ω holds.
  -- This requires: monotonicity, limits at ±∞, and right-continuity at all rationals.

  -- Get monotonicity of alphaIic at all rational pairs
  have h_mono_ae : ∀ᵐ ω ∂μ, ∀ q r : ℚ, q ≤ r →
      alphaIic X hX_contract hX_meas hX_L2 (q : ℝ) ω ≤
      alphaIic X hX_contract hX_meas hX_L2 (r : ℝ) ω := by
    rw [ae_all_iff]; intro q
    rw [ae_all_iff]; intro r
    by_cases hqr : q ≤ r
    · have h_le : (q : ℝ) ≤ (r : ℝ) := Rat.cast_le.mpr hqr
      filter_upwards [alphaIic_ae_eq_alphaIicCE X hX_contract hX_meas hX_L2 (q : ℝ),
                      alphaIic_ae_eq_alphaIicCE X hX_contract hX_meas hX_L2 (r : ℝ),
                      alphaIicCE_mono X hX_contract hX_meas hX_L2 (q : ℝ) (r : ℝ) h_le]
        with ω hq hr hCE_mono
      intro _
      rw [hq, hr]
      exact hCE_mono
    · exact ae_of_all μ (fun ω h_contra => absurd h_contra hqr)

  -- Get limits at ±∞ (along integers, which implies along rationals by monotonicity)
  have h_bot_ae : ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ =>
      alphaIic X hX_contract hX_meas hX_L2 (-(n : ℝ)) ω) atTop (𝓝 0) :=
    alphaIic_ae_tendsto_zero_at_bot X hX_contract hX_meas hX_L2

  have h_top_ae : ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ =>
      alphaIic X hX_contract hX_meas hX_L2 (n : ℝ) ω) atTop (𝓝 1) :=
    alphaIic_ae_tendsto_one_at_top X hX_contract hX_meas hX_L2

  -- Also filter on alphaIic = alphaIicCE at all rationals (countable ae union)
  have h_ae_all_rationals : ∀ᵐ ω ∂μ, ∀ q : ℚ,
      alphaIic X hX_contract hX_meas hX_L2 (q : ℝ) ω =
      alphaIicCE X hX_contract hX_meas hX_L2 (q : ℝ) ω := by
    rw [ae_all_iff]
    intro q
    exact alphaIic_ae_eq_alphaIicCE X hX_contract hX_meas hX_L2 (q : ℝ)

  -- Filter on alphaIicCE_mono at (t, q) for all rationals q > t
  have h_mono_t_rational : ∀ᵐ ω ∂μ, ∀ q : ℚ, t < q →
      alphaIicCE X hX_contract hX_meas hX_L2 t ω ≤
      alphaIicCE X hX_contract hX_meas hX_L2 (q : ℝ) ω := by
    rw [ae_all_iff]
    intro q
    by_cases htq : t < q
    · have h_le : t ≤ (q : ℝ) := le_of_lt htq
      filter_upwards [alphaIicCE_mono X hX_contract hX_meas hX_L2 t (q : ℝ) h_le] with ω hω
      intro _
      exact hω
    · exact ae_of_all μ (fun ω h_contra => absurd h_contra htq)

  -- Filter on all necessary conditions (including right-continuity at t and all rationals)
  filter_upwards [alphaIic_ae_eq_alphaIicCE X hX_contract hX_meas hX_L2 t,
                  h_mono_ae, h_bot_ae, h_top_ae, h_ae_all_rationals, h_mono_t_rational,
                  alphaIicCE_right_continuous_at X hX_contract hX_meas hX_L2 t,
                  alphaIicCE_iInf_rat_gt_eq X hX_contract hX_meas hX_L2]
    with ω h_ae h_mono h_bot h_top h_ae_rat h_mono_t_rat h_right_cont h_iInf_rat_gt_CE
  rw [h_integral_eq, h_meas_eq]
  -- Need: stieltjesOfMeasurableRat alphaIicRat ω t = alphaIicCE t ω
  -- By h_ae: alphaIic t ω = alphaIicCE t ω
  rw [← h_ae]

  -- The Stieltjes function is defined via toRatCDF.
  -- At rational points, stieltjesOfMeasurableRat equals toRatCDF.
  -- toRatCDF uses alphaIicRat when IsRatStieltjesPoint holds, else defaultRatCDF.

  -- Show that IsRatStieltjesPoint alphaIicRat ω holds for this ω.
  -- We verify the conditions using h_mono, h_bot, h_top.
  have h_alphaIicRat_mono : Monotone (alphaIicRat X hX_contract hX_meas hX_L2 ω) := by
    intro q r hqr
    unfold alphaIicRat
    exact h_mono q r hqr

  -- For limits at ±∞ along rationals, use monotonicity + integer limits
  have h_alphaIicRat_tendsto_top : Tendsto (alphaIicRat X hX_contract hX_meas hX_L2 ω)
      atTop (𝓝 1) := by
    -- alphaIicRat is monotone and bounded above by 1
    -- The integer subsequence converges to 1, so the whole sequence does
    -- Use tendsto_atTop_isLUB with the fact that 1 is the supremum
    apply tendsto_atTop_isLUB h_alphaIicRat_mono
    -- Need to show 1 is the LUB of the range
    -- Since alphaIicRat is monotone, bounded by 1, and the integer sequence → 1,
    -- the sup is 1.
    constructor
    · -- 1 is an upper bound
      rintro _ ⟨q, rfl⟩
      unfold alphaIicRat alphaIic
      -- max 0 (min 1 x) ≤ 1 always holds
      exact max_le zero_le_one (min_le_left _ _)
    · -- 1 is the least upper bound
      intro b hb
      -- b ≥ alphaIicRat n for all n, so b ≥ lim alphaIicRat n = 1
      by_contra h_not
      push_neg at h_not
      have hε : 1 - b > 0 := by linarith
      -- Since alphaIicRat n → 1, for large n we have alphaIicRat n > b
      have h_nat : Tendsto (fun n : ℕ => alphaIicRat X hX_contract hX_meas hX_L2 ω (n : ℚ))
          atTop (𝓝 1) := by
        unfold alphaIicRat
        simp only [Rat.cast_natCast]
        exact h_top
      rw [Metric.tendsto_atTop] at h_nat
      obtain ⟨N, hN⟩ := h_nat (1 - b) hε
      have h_contra := hb (Set.mem_range.mpr ⟨N, rfl⟩)
      specialize hN N le_rfl
      rw [Real.dist_eq] at hN
      have h_abs : |alphaIicRat X hX_contract hX_meas hX_L2 ω N - 1| < 1 - b := hN
      have h_lower : alphaIicRat X hX_contract hX_meas hX_L2 ω N ≥ 0 := by
        unfold alphaIicRat alphaIic
        -- 0 ≤ max 0 (min 1 x) always holds
        exact le_max_left 0 _
      have h_upper : alphaIicRat X hX_contract hX_meas hX_L2 ω N ≤ 1 := by
        unfold alphaIicRat alphaIic
        exact max_le zero_le_one (min_le_left _ _)
      rw [abs_sub_lt_iff] at h_abs
      linarith

  have h_alphaIicRat_tendsto_bot : Tendsto (alphaIicRat X hX_contract hX_meas hX_L2 ω)
      atBot (𝓝 0) := by
    -- Similar argument using monotonicity and GLB at -∞
    apply tendsto_atBot_isGLB h_alphaIicRat_mono
    -- Need to show 0 is the GLB of the range
    constructor
    · -- 0 is a lower bound
      rintro _ ⟨q, rfl⟩
      unfold alphaIicRat alphaIic
      -- 0 ≤ max 0 (min 1 x) always holds
      exact le_max_left 0 _
    · -- 0 is the greatest lower bound
      intro b hb
      by_contra h_not
      push_neg at h_not
      have hε : b > 0 := h_not
      -- Since alphaIicRat (-n) → 0, for large n we have alphaIicRat (-n) < b
      have h_nat : Tendsto (fun n : ℕ => alphaIicRat X hX_contract hX_meas hX_L2 ω (-(n : ℚ)))
          atTop (𝓝 0) := by
        unfold alphaIicRat
        simp only [Rat.cast_neg, Rat.cast_natCast]
        exact h_bot
      rw [Metric.tendsto_atTop] at h_nat
      obtain ⟨N, hN⟩ := h_nat b hε
      have h_contra := hb (Set.mem_range.mpr ⟨-(N : ℚ), rfl⟩)
      specialize hN N le_rfl
      rw [Real.dist_eq, abs_sub_comm] at hN
      have h_lower : alphaIicRat X hX_contract hX_meas hX_L2 ω (-(N : ℚ)) ≥ 0 := by
        unfold alphaIicRat alphaIic
        -- 0 ≤ max 0 (min 1 x) always holds
        exact le_max_left 0 _
      have h_abs : |alphaIicRat X hX_contract hX_meas hX_L2 ω (-(N : ℚ)) - 0| < b := by
        rwa [abs_sub_comm] at hN
      simp only [sub_zero, abs_of_nonneg h_lower] at h_abs
      linarith

  -- Right-continuity at rationals for alphaIicRat.
  -- This is a key property that follows from alphaIicCE being right-continuous
  -- (as a conditional expectation of right-continuous indicators).
  have h_iInf_rat_gt : ∀ q : ℚ, ⨅ r : Set.Ioi q,
      alphaIicRat X hX_contract hX_meas hX_L2 ω r = alphaIicRat X hX_contract hX_meas hX_L2 ω q := by
    intro q
    -- By monotonicity, the infimum is a limit from the right.
    -- For CDFs, right-continuity says this limit equals the value.
    apply le_antisymm
    · -- iInf ≤ value: Use h_iInf_rat_gt_CE and the identification h_ae_rat.
      -- alphaIicRat ω r = alphaIic (r : ℝ) ω = alphaIicCE (r : ℝ) ω for rational r.
      -- h_iInf_rat_gt_CE q says: ⨅ r > q, alphaIicCE r ω = alphaIicCE q ω
      -- Convert between alphaIicRat and alphaIicCE using h_ae_rat.
      unfold alphaIicRat
      -- Now goal is: ⨅ r : Set.Ioi q, alphaIic (r : ℝ) ω ≤ alphaIic (q : ℝ) ω
      rw [h_ae_rat q]
      -- Goal: ⨅ r : Set.Ioi q, alphaIic (r : ℝ) ω ≤ alphaIicCE (q : ℝ) ω
      have h_eq : ⨅ r : Set.Ioi q, alphaIic X hX_contract hX_meas hX_L2 (r : ℝ) ω =
          ⨅ r : Set.Ioi q, alphaIicCE X hX_contract hX_meas hX_L2 (r : ℝ) ω := by
        congr 1
        ext ⟨r, hr⟩
        exact h_ae_rat r
      rw [h_eq, h_iInf_rat_gt_CE q]
    · -- value ≤ iInf: use monotonicity
      apply le_ciInf
      intro ⟨r, hr⟩
      exact h_alphaIicRat_mono (le_of_lt hr)

  -- Now we know IsRatStieltjesPoint holds, so toRatCDF = alphaIicRat
  have h_isRSP : ProbabilityTheory.IsRatStieltjesPoint
      (alphaIicRat X hX_contract hX_meas hX_L2) ω :=
    ⟨h_alphaIicRat_mono, h_alphaIicRat_tendsto_top, h_alphaIicRat_tendsto_bot, h_iInf_rat_gt⟩

  -- Use toRatCDF_of_isRatStieltjesPoint: when IsRatStieltjesPoint holds, toRatCDF = f
  -- Then stieltjesOfMeasurableRat at t equals the infimum over rationals > t
  -- which by h_iInf_rat_gt equals alphaIicRat restricted to t
  -- But we need the value at real t, not rational t.

  -- The Stieltjes function at real t is defined as inf over rationals > t.
  -- stieltjesOfMeasurableRat f hf ω t = ⨅ q > t, toRatCDF f ω q
  -- Since IsRatStieltjesPoint holds: = ⨅ q > t, f ω q = ⨅ q > t, alphaIicRat ω q

  -- By right-continuity of alphaIic (which follows from being a CDF):
  -- ⨅ q > t, alphaIic q ω = alphaIic t ω

  -- The Stieltjes function equals its value via the iInf_rat_gt characterization
  have h_stieltjes_eq : (ProbabilityTheory.stieltjesOfMeasurableRat
        (alphaIicRat X hX_contract hX_meas hX_L2)
        (measurable_alphaIicRat X hX_contract hX_meas hX_L2) ω) t =
      ⨅ q : {q : ℚ // t < q}, alphaIicRat X hX_contract hX_meas hX_L2 ω q := by
    rw [← StieltjesFunction.iInf_rat_gt_eq]
    congr 1
    funext q
    rw [ProbabilityTheory.stieltjesOfMeasurableRat_eq]
    rw [ProbabilityTheory.toRatCDF_of_isRatStieltjesPoint h_isRSP]

  rw [h_stieltjes_eq]
  unfold alphaIicRat
  -- Now we need: ⨅ q > t, alphaIic q ω = alphaIic t ω

  -- Strategy: Use h_ae_rat to transfer to alphaIicCE, then use right-continuity.
  -- ⨅ q > t, alphaIic q ω = ⨅ q > t, alphaIicCE q ω  (by h_ae_rat)
  -- = alphaIicCE t ω  (by right-continuity of alphaIicCE)
  -- = alphaIic t ω   (by h_ae)

  -- Step 1: Rewrite the infimum using h_ae_rat
  have h_infimum_eq : (⨅ q : {q : ℚ // t < q}, alphaIic X hX_contract hX_meas hX_L2 (q : ℝ) ω) =
      ⨅ q : {q : ℚ // t < q}, alphaIicCE X hX_contract hX_meas hX_L2 (q : ℝ) ω := by
    congr 1
    ext ⟨q, _⟩
    exact h_ae_rat q

  rw [h_infimum_eq]

  -- Step 2: Show ⨅ q > t, alphaIicCE q ω = alphaIicCE t ω (right-continuity of alphaIicCE)
  -- alphaIicCE is the conditional expectation of the indicator 1_{Iic t}(X₀).
  -- As t → t₀⁺, the indicator 1_{Iic t} ↓ 1_{Iic t₀} pointwise (since Iic t ↓ Iic t₀).
  -- By monotone convergence for conditional expectations:
  -- E[1_{Iic t}(X₀) | tail] → E[1_{Iic t₀}(X₀) | tail] a.e.

  -- For this specific ω, we need: ⨅ q > t, alphaIicCE q ω = alphaIicCE t ω.
  -- This is the pointwise right-continuity of alphaIicCE.

  -- Actually, we filtered on conditions for alphaIicCE at rationals and at t,
  -- but not directly on right-continuity. Let's prove it using monotonicity.

  -- alphaIicCE is monotone a.e. We use the rational monotonicity we have.
  -- For q > t (rational), alphaIicCE t ω ≤ alphaIicCE q ω (by monotonicity).
  -- So alphaIicCE t ω ≤ ⨅ q > t, alphaIicCE q ω.
  -- The other direction (⨅ ≤ value) requires right-continuity.

  have h_nonempty : Nonempty {q : ℚ // t < q} := by
    -- Find a rational greater than t
    obtain ⟨q, hq⟩ := exists_rat_gt t
    exact ⟨⟨q, hq⟩⟩

  apply le_antisymm
  · -- ⨅ q > t, alphaIicCE q ω ≤ alphaIicCE t ω
    -- This is the "hard" direction requiring right-continuity.
    -- Use that the infimum of a monotone decreasing sequence converging to t
    -- equals the limit, which is the value at t for right-continuous functions.

    -- The set {q : ℚ // t < q} has infimum t.
    -- For monotone alphaIicCE, ⨅ q > t, alphaIicCE q = lim_{q → t⁺} alphaIicCE q.
    -- Right-continuity would give lim_{q → t⁺} alphaIicCE q = alphaIicCE t.

    -- For now, we use the key fact that alphaIicCE is bounded in [0,1] and monotone,
    -- so the infimum exists. The infimum equals the value at t by right-continuity
    -- of CDFs built from L¹ limits.

    -- Use the right-continuity lemma (filtered on via h_right_cont)
    calc ⨅ q : {q : ℚ // t < q}, alphaIicCE X hX_contract hX_meas hX_L2 (q : ℝ) ω
        ≤ alphaIicCE X hX_contract hX_meas hX_L2 t ω := h_right_cont
      _ = alphaIic X hX_contract hX_meas hX_L2 t ω := h_ae.symm

  · -- alphaIic t ω ≤ ⨅ q > t, alphaIicCE q ω
    -- By monotonicity: for q > t, alphaIicCE t ω ≤ alphaIicCE q ω.
    -- And alphaIic t ω = alphaIicCE t ω by h_ae.
    -- So alphaIic t ω ≤ ⨅ q > t, alphaIicCE q ω.
    rw [h_ae]
    apply le_ciInf
    intro ⟨q, hq⟩
    -- Need: alphaIicCE t ω ≤ alphaIicCE q ω where t < q
    -- This follows from h_mono_t_rat!
    exact h_mono_t_rat q hq

/-! ### Helper Lemmas for Monotone Class Extension

The following lemmas build up the π-λ argument needed for `directing_measure_integral_eq_condExp`.
Each phase is factored out as a separate lemma with its own sorry to be filled.

**Phase A**: Indicators of Borel sets → tail-AEStronglyMeasurable
**Phase B**: Simple functions → tail-AEStronglyMeasurable (via linearity)
**Phase C**: Bounded measurable functions → tail-AEStronglyMeasurable (via DCT + limits)
-/

/-- **Phase A:** For all Borel sets s, ω ↦ ∫ 1_s dν(ω) is tail-AEStronglyMeasurable.

The π-λ argument:
1. Base case: `{Iic t | t ∈ ℝ}` is a π-system generating Borel ℝ
2. For Iic t: uses `directing_measure_integral_Iic_ae_eq_alphaIicCE` + `stronglyMeasurable_condExp`
3. For ∅: integral is 0 (constant)
4. For complement: ∫ 1_{sᶜ} dν = 1 - ∫ 1_s dν (probability measure)
5. For disjoint unions: ∫ 1_{⋃ fn} dν = ∑' ∫ 1_{fn n} dν (σ-additivity)
6. Apply `MeasurableSpace.induction_on_inter` with `borel_eq_generateFrom_Iic`
-/
lemma integral_indicator_borel_tailAEStronglyMeasurable
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ)
    (s : Set ℝ) (hs : MeasurableSet s) :
    @AEStronglyMeasurable Ω ℝ _ (TailSigma.tailSigma X) _
      (fun ω => ∫ x, s.indicator (fun _ => (1:ℝ)) x
        ∂(directing_measure X hX_contract hX_meas hX_L2 ω)) μ := by
  classical
  -- Define the class of "good" sets G
  let G : Set (Set ℝ) := {t | MeasurableSet t ∧
    @AEStronglyMeasurable Ω ℝ _ (TailSigma.tailSigma X) _
      (fun ω => ∫ x, t.indicator (fun _ => (1:ℝ)) x
        ∂(directing_measure X hX_contract hX_meas hX_L2 ω)) μ}

  -- Step 1: G contains the π-system of half-lines {Iic t}
  have h_pi : ∀ t : ℝ, Set.Iic t ∈ G := by
    intro t
    constructor
    · exact measurableSet_Iic
    · -- By directing_measure_integral_Iic_ae_eq_alphaIicCE:
      -- ∫ 1_{Iic t} dν(ω) =ᵐ alphaIicCE t ω
      -- alphaIicCE t is tail-StronglyMeasurable (it's a condExp)
      have h_ae := directing_measure_integral_Iic_ae_eq_alphaIicCE X hX_contract hX_meas hX_L2 t
      have h_tail_sm : @StronglyMeasurable Ω ℝ _ (TailSigma.tailSigma X)
          (alphaIicCE X hX_contract hX_meas hX_L2 t) := by
        unfold alphaIicCE
        exact stronglyMeasurable_condExp
      exact AEStronglyMeasurable.congr h_tail_sm.aestronglyMeasurable h_ae.symm

  -- Step 2: G is a Dynkin system (λ-system)
  have h_empty : ∅ ∈ G := by
    constructor
    · exact MeasurableSet.empty
    · simp only [Set.indicator_empty, integral_zero]
      exact aestronglyMeasurable_const

  have h_compl : ∀ t ∈ G, tᶜ ∈ G := by
    intro t ⟨ht_meas, ht_aesm⟩
    constructor
    · exact ht_meas.compl
    · -- ∫ 1_{tᶜ} dν = ∫ (1 - 1_t) dν = 1 - ∫ 1_t dν (since ν is probability measure)
      have h_eq : ∀ ω, ∫ x, tᶜ.indicator (fun _ => (1:ℝ)) x
          ∂(directing_measure X hX_contract hX_meas hX_L2 ω) =
          1 - ∫ x, t.indicator (fun _ => (1:ℝ)) x
            ∂(directing_measure X hX_contract hX_meas hX_L2 ω) := by
        intro ω
        haveI hprob := directing_measure_isProbabilityMeasure X hX_contract hX_meas hX_L2 ω
        -- 1_{tᶜ} = 1 - 1_t
        have h_ind_compl : ∀ x, tᶜ.indicator (fun _ => (1:ℝ)) x =
            1 - t.indicator (fun _ => (1:ℝ)) x := by
          intro x
          by_cases hx : x ∈ t
          · simp [Set.indicator_of_mem hx, Set.indicator_of_not_mem (Set.not_mem_compl_iff.mpr hx)]
          · simp [Set.indicator_of_not_mem hx, Set.indicator_of_mem (Set.mem_compl hx)]
        simp_rw [h_ind_compl]
        rw [integral_sub (integrable_const 1), integral_const, measureReal_univ_eq_one, one_smul]
        exact (integrable_const 1).indicator ht_meas
      simp_rw [h_eq]
      exact aestronglyMeasurable_const.sub ht_aesm

  have h_iUnion : ∀ (f : ℕ → Set ℝ), (∀ i j, i ≠ j → Disjoint (f i) (f j)) →
      (∀ n, f n ∈ G) → (⋃ n, f n) ∈ G := by
    intro f hdisj hf
    constructor
    · exact MeasurableSet.iUnion (fun n => (hf n).1)
    · -- ∫ 1_{⋃ fn} dν = ∑' n, ∫ 1_{fn n} dν
      -- Partial sums are tail-AEStronglyMeasurable, converge pointwise to tsum
      -- Use aestronglyMeasurable_of_tendsto_ae
      have h_eq : ∀ ω, ∫ x, (⋃ n, f n).indicator (fun _ => (1:ℝ)) x
          ∂(directing_measure X hX_contract hX_meas hX_L2 ω) =
          ∑' n, ∫ x, (f n).indicator (fun _ => (1:ℝ)) x
            ∂(directing_measure X hX_contract hX_meas hX_L2 ω) := by
        intro ω
        haveI hprob := directing_measure_isProbabilityMeasure X hX_contract hX_meas hX_L2 ω
        -- indicator of union = sum of indicators for disjoint sets
        have h_ind_union : ∀ x, (⋃ n, f n).indicator (fun _ => (1:ℝ)) x =
            ∑' n, (f n).indicator (fun _ => (1:ℝ)) x := by
          intro x
          by_cases hx : x ∈ ⋃ n, f n
          · obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
            rw [Set.indicator_of_mem hx]
            -- x is in exactly one f n due to disjointness
            have h_unique : ∀ m, m ≠ n → x ∉ f m := by
              intro m hm hxm
              exact (hdisj n m (Ne.symm hm)).ne_of_mem hn hxm rfl
            rw [tsum_eq_single n]
            · simp [Set.indicator_of_mem hn]
            · intro m hm; simp [Set.indicator_of_not_mem (h_unique m hm)]
          · simp only [Set.indicator_of_not_mem hx]
            have : ∀ n, x ∉ f n := fun n hn => hx (Set.mem_iUnion.mpr ⟨n, hn⟩)
            simp [Set.indicator_of_not_mem (this _)]
        simp_rw [h_ind_union]
        -- integral of tsum = tsum of integrals (for nonneg functions)
        rw [integral_tsum]
        · exact fun n => (measurable_const.indicator (hf n).1).aestronglyMeasurable
        · -- Show ∑' i, ∫⁻ ‖1_{fi}‖ dν ≠ ⊤
          -- Each indicator has norm at most 1, and disjoint sets sum to at most 1
          have h_le_one : ∑' i, ∫⁻ a, ‖(f i).indicator (fun _ => (1:ℝ)) a‖ₑ
              ∂(directing_measure X hX_contract hX_meas hX_L2 ω) ≤ 1 := by
            have h_eq_meas : ∀ i, ∫⁻ a, ‖(f i).indicator (fun _ => (1:ℝ)) a‖ₑ
                ∂(directing_measure X hX_contract hX_meas hX_L2 ω)
                = directing_measure X hX_contract hX_meas hX_L2 ω (f i) := by
              intro i
              have h1 : ∫⁻ a, ‖(f i).indicator (fun _ => (1:ℝ)) a‖ₑ
                    ∂(directing_measure X hX_contract hX_meas hX_L2 ω)
                  = ∫⁻ a, (f i).indicator 1 a
                    ∂(directing_measure X hX_contract hX_meas hX_L2 ω) := by
                apply lintegral_congr; intro a
                simp only [Set.indicator, Real.enorm_eq_ofReal_abs, Pi.one_apply]
                split_ifs <;> simp
              rw [h1, lintegral_indicator_one (hf i).1]
            simp_rw [h_eq_meas]
            -- For disjoint measurable sets, sum = measure of union
            have hdisj' : Pairwise (Function.onFun Disjoint f) := fun i j hij => hdisj i j hij
            have hmeas : ∀ i, MeasurableSet (f i) := fun i => (hf i).1
            calc ∑' i, directing_measure X hX_contract hX_meas hX_L2 ω (f i)
                = directing_measure X hX_contract hX_meas hX_L2 ω (⋃ i, f i) :=
                  (measure_iUnion hdisj' hmeas).symm
              _ ≤ 1 := prob_le_one
          exact ne_top_of_le_ne_top ENNReal.one_ne_top h_le_one
      -- Now show the AEStronglyMeasurable property
      -- Key: partial sums ∑_{i<N} ∫ 1_{fi} dν are tail-AESM, converge to tsum
      let partialSum (N : ℕ) (ω : Ω) : ℝ := ∑ n ∈ Finset.range N,
        ∫ x, (f n).indicator (fun _ => (1:ℝ)) x
          ∂(directing_measure X hX_contract hX_meas hX_L2 ω)
      have h_partial_aesm : ∀ N, @AEStronglyMeasurable Ω ℝ _ (TailSigma.tailSigma X) _
          (partialSum N) μ := by
        intro N
        -- Use induction on N to build up the sum
        induction N with
        | zero =>
          -- partialSum 0 = 0, which is a constant
          have h_zero : partialSum 0 = fun _ => 0 := by
            funext ω
            show ∑ n ∈ Finset.range 0, _ = 0
            simp only [Finset.range_zero, Finset.sum_empty]
          rw [h_zero]
          exact aestronglyMeasurable_const
        | succ n ih =>
          -- partialSum (n+1) = partialSum n + (term at n)
          have h_succ : partialSum (n + 1) = fun ω => partialSum n ω +
              ∫ x, (f n).indicator (fun _ => (1:ℝ)) x
                ∂(directing_measure X hX_contract hX_meas hX_L2 ω) := by
            funext ω
            show ∑ k ∈ Finset.range (n + 1), _ = ∑ k ∈ Finset.range n, _ + _
            simp only [Finset.sum_range_succ]
          rw [h_succ]
          exact ih.add (hf n).2
      -- Partial sums converge pointwise to the full sum
      have h_tendsto : ∀ ω, Filter.Tendsto (fun N => partialSum N ω) Filter.atTop
          (nhds (∑' n, ∫ x, (f n).indicator (fun _ => (1:ℝ)) x
            ∂(directing_measure X hX_contract hX_meas hX_L2 ω))) := by
        intro ω
        haveI hprob := directing_measure_isProbabilityMeasure X hX_contract hX_meas hX_L2 ω
        -- Each term is nonnegative and bounded by 1
        have h_nonneg : ∀ n, 0 ≤ ∫ x, (f n).indicator (fun _ => (1:ℝ)) x
            ∂(directing_measure X hX_contract hX_meas hX_L2 ω) := by
          intro n
          apply integral_nonneg
          intro x; exact Set.indicator_nonneg (fun _ _ => zero_le_one) x
        -- For disjoint sets, partial sums ≤ 1 (probability measure)
        have h_partial_le : ∀ N, ∑ n ∈ Finset.range N, ∫ x, (f n).indicator (fun _ => (1:ℝ)) x
            ∂(directing_measure X hX_contract hX_meas hX_L2 ω) ≤ 1 := by
          intro N
          calc ∑ n ∈ Finset.range N, ∫ x, (f n).indicator (fun _ => (1:ℝ)) x
                ∂(directing_measure X hX_contract hX_meas hX_L2 ω)
            = ∫ x, ∑ n ∈ Finset.range N, (f n).indicator (fun _ => (1:ℝ)) x
                ∂(directing_measure X hX_contract hX_meas hX_L2 ω) := by
                rw [integral_finset_sum]
                intro i _
                exact (integrable_const 1).indicator (hf i).1
            _ ≤ ∫ _, 1 ∂(directing_measure X hX_contract hX_meas hX_L2 ω) := by
                apply integral_mono
                · apply integrable_finset_sum
                  intro i _
                  exact (integrable_const 1).indicator (hf i).1
                · exact integrable_const 1
                · intro x
                  -- Sum of disjoint indicators ≤ 1
                  have : ∑ n ∈ Finset.range N, (f n).indicator (fun _ => (1:ℝ)) x ≤ 1 := by
                    by_cases hx : ∃ n ∈ Finset.range N, x ∈ f n
                    · obtain ⟨m, hm_mem, hxm⟩ := hx
                      rw [Finset.sum_eq_single m]
                      · simp [Set.indicator_of_mem hxm]
                      · intro n hn hn_ne
                        have hne : m ≠ n := Ne.symm hn_ne
                        have hdisj_mn := hdisj m n hne
                        rw [Set.indicator_of_notMem]
                        exact Set.disjoint_left.mp hdisj_mn hxm
                      · intro hm_not; exact absurd hm_mem hm_not
                    · push_neg at hx
                      have h_zero : ∀ n ∈ Finset.range N, (f n).indicator (fun _ => (1:ℝ)) x = 0 :=
                        fun n hn => Set.indicator_of_notMem (hx n hn) _
                      rw [Finset.sum_eq_zero h_zero]
                      exact zero_le_one
                  exact this
            _ = 1 := by simp [measureReal_univ_eq_one]
        have h_summable : Summable (fun n => ∫ x, (f n).indicator (fun _ => (1:ℝ)) x
            ∂(directing_measure X hX_contract hX_meas hX_L2 ω)) :=
          summable_of_sum_range_le h_nonneg h_partial_le
        exact h_summable.hasSum.tendsto_sum_nat
      -- Apply aestronglyMeasurable_of_tendsto_ae
      have h_ae_tendsto : ∀ᵐ ω ∂μ, Filter.Tendsto (fun N => partialSum N ω) Filter.atTop
          (nhds (∑' n, ∫ x, (f n).indicator (fun _ => (1:ℝ)) x
            ∂(directing_measure X hX_contract hX_meas hX_L2 ω))) :=
        ae_of_all _ h_tendsto
      -- Construct AEStronglyMeasurable directly
      -- Key insight: partialSum n → tsum pointwise, and each partialSum n is tail-AESM
      -- Use ambient aestronglyMeasurable_of_tendsto_ae to get ambient AESM for the limit
      -- Then use the tail-AESM property of partialSum to extract a tail-SM witness
      have h_partial_ambient : ∀ n, AEStronglyMeasurable (partialSum n) μ := by
        intro n
        -- Each h_partial_aesm n is tail-AESM, which implies ambient-AESM
        -- tail-AESM has a tail-SM witness, and tail-SM implies ambient-SM
        exact (h_partial_aesm n).mono (TailSigma.tailSigma_le X hX_meas)
      have h_tsum_ambient : AEStronglyMeasurable
          (fun ω => ∑' n, ∫ x, (f n).indicator (fun _ => (1:ℝ)) x
            ∂(directing_measure X hX_contract hX_meas hX_L2 ω)) μ :=
        aestronglyMeasurable_of_tendsto_ae Filter.atTop h_partial_ambient h_ae_tendsto
      -- Now we need to show tail-AESM, not just ambient-AESM
      -- Key: the limit function equals ∑' n, ∫ ... which we can show is tail-AESM
      -- by using that each term is tail-AESM and taking the tsum
      have h_tsum_aesm : @AEStronglyMeasurable Ω ℝ _ (TailSigma.tailSigma X) _
            (fun ω => ∑' n, ∫ x, (f n).indicator (fun _ => (1:ℝ)) x
              ∂(directing_measure X hX_contract hX_meas hX_L2 ω)) μ := by
        -- Use that partial sums are tail-AESM and converge ae to get tail-AESM limit
        -- Get the tail-SM ae-representatives for each partial sum
        let g_n (n : ℕ) : Ω → ℝ := (h_partial_aesm n).mk (partialSum n)
        have hg_n_sm : ∀ n, @StronglyMeasurable Ω ℝ _ (TailSigma.tailSigma X) (g_n n) :=
          fun n => (h_partial_aesm n).stronglyMeasurable_mk
        have hg_n_ae : ∀ n, partialSum n =ᶠ[ae μ] g_n n := fun n => (h_partial_aesm n).ae_eq_mk
        -- Define the limit using the ae-representatives
        -- g_n converge ae to the tsum (since partialSum n → tsum and partialSum n =ᵐ g_n)
        have h_g_tendsto : ∀ᵐ ω ∂μ, Filter.Tendsto (fun n => g_n n ω) Filter.atTop
            (nhds (∑' k, ∫ x, (f k).indicator (fun _ => (1:ℝ)) x
              ∂(directing_measure X hX_contract hX_meas hX_L2 ω))) := by
          have h_ae_eq_all : ∀ᵐ ω ∂μ, ∀ n, g_n n ω = partialSum n ω := by
            rw [ae_all_iff]
            intro n
            exact (hg_n_ae n).symm
          filter_upwards [h_ae_eq_all] with ω h_eq
          simp_rw [h_eq]
          exact h_tendsto ω
        -- Use exists_stronglyMeasurable_limit_of_tendsto_ae on the g_n sequence
        have h_ae_exists : ∀ᵐ ω ∂μ, ∃ l, Filter.Tendsto (fun n => g_n n ω) Filter.atTop (nhds l) := by
          filter_upwards [h_g_tendsto] with ω hω
          exact ⟨_, hω⟩
        -- The g_n are ambient-AESM (since tail-SM implies ambient-AESM)
        have hg_n_ambient : ∀ n, AEStronglyMeasurable (g_n n) μ := by
          intro n
          exact (hg_n_sm n).aestronglyMeasurable.mono (TailSigma.tailSigma_le X hX_meas)
        -- Get the strongly measurable limit
        obtain ⟨g_lim, hg_lim_sm, hg_lim_tendsto⟩ :=
          exists_stronglyMeasurable_limit_of_tendsto_ae hg_n_ambient h_ae_exists
        -- g_lim is ambient-SM. We need to show it equals the tsum ae and is tail-AESM
        -- The limit of g_n equals tsum ae
        have h_lim_eq_tsum : g_lim =ᶠ[ae μ]
            (fun ω => ∑' k, ∫ x, (f k).indicator (fun _ => (1:ℝ)) x
              ∂(directing_measure X hX_contract hX_meas hX_L2 ω)) := by
          filter_upwards [hg_lim_tendsto, h_g_tendsto] with ω hω1 hω2
          exact tendsto_nhds_unique hω1 hω2
        -- We need ∃ h, tail-SM h ∧ tsum =ᵐ h
        -- Use limUnder which is the pointwise limit - StronglyMeasurable.limUnder shows
        -- that the pointwise limit of tail-SM functions is tail-SM
        let g_tail : Ω → ℝ := fun ω => limUnder atTop (fun n => g_n n ω)
        have hg_tail_sm : @StronglyMeasurable Ω ℝ _ (TailSigma.tailSigma X) g_tail :=
          @StronglyMeasurable.limUnder ℕ Ω ℝ (TailSigma.tailSigma X) _ _ _ atTop _
            (fun n => g_n n) _ hg_n_sm
        -- g_tail equals tsum ae (since g_n → tsum ae, and limUnder captures this limit)
        have hg_tail_eq_tsum : g_tail =ᶠ[ae μ]
            (fun ω => ∑' k, ∫ x, (f k).indicator (fun _ => (1:ℝ)) x
              ∂(directing_measure X hX_contract hX_meas hX_L2 ω)) := by
          filter_upwards [h_g_tendsto] with ω hω
          exact hω.limUnder_eq
        refine ⟨g_tail, hg_tail_sm, hg_tail_eq_tsum.symm⟩
      exact AEStronglyMeasurable.congr h_tsum_aesm (ae_of_all _ (fun ω => (h_eq ω).symm))

  -- Step 3: Apply π-λ theorem
  let S : Set (Set ℝ) := Set.range (Set.Iic : ℝ → Set ℝ)
  have h_gen : (inferInstance : MeasurableSpace ℝ) = MeasurableSpace.generateFrom S :=
    @borel_eq_generateFrom_Iic ℝ _ _ _ _
  have h_pi_S : IsPiSystem S := by
    intro u hu v hv _
    obtain ⟨s, rfl⟩ := hu
    obtain ⟨t, rfl⟩ := hv
    use min s t
    exact Set.Iic_inter_Iic.symm

  have h_induction : ∀ t (htm : MeasurableSet t), t ∈ G := fun t htm =>
    MeasurableSpace.induction_on_inter h_gen h_pi_S
      h_empty
      (fun u ⟨r, hr⟩ => hr ▸ h_pi r)
      (fun u hum hu => h_compl u hu)
      (fun f hdisj hfm hf => h_iUnion f hdisj hf)
      t htm

  exact (h_induction s hs).2

/-- **Phase B:** For simple functions, the integral is tail-AEStronglyMeasurable.

Simple functions are finite linear combinations of indicator functions.
Uses `Finset.aestronglyMeasurable_sum` and scalar multiplication. -/
lemma integral_simpleFunc_tailAEStronglyMeasurable
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ)
    (φ : SimpleFunc ℝ ℝ) :
    @AEStronglyMeasurable Ω ℝ _ (TailSigma.tailSigma X) _
      (fun ω => ∫ x, φ x ∂(directing_measure X hX_contract hX_meas hX_L2 ω)) μ := by
  -- SimpleFunc integral: ∫ φ dν = ∑ c ∈ φ.range, ν.real(φ⁻¹'{c}) • c
  -- For each c: ν.real(φ⁻¹'{c}) = ∫ 1_{φ⁻¹'{c}} dν, which is tail-AESM by A1
  -- c • (tail-AESM) is tail-AESM
  -- Finite sum of tail-AESM is tail-AESM

  -- The integral equals a finite sum over the range
  have h_eq : ∀ ω, ∫ x, φ x ∂(directing_measure X hX_contract hX_meas hX_L2 ω) =
      ∑ c ∈ φ.range, (directing_measure X hX_contract hX_meas hX_L2 ω).real (φ ⁻¹' {c}) • c := by
    intro ω
    haveI hprob := directing_measure_isProbabilityMeasure X hX_contract hX_meas hX_L2 ω
    -- φ is integrable on any probability measure (simple functions are bounded)
    have h_int : Integrable (⇑φ) (directing_measure X hX_contract hX_meas hX_L2 ω) :=
      SimpleFunc.integrable_of_isFiniteMeasure φ
    exact SimpleFunc.integral_eq_sum φ h_int

  -- Rewrite using h_eq
  have h_aesm : @AEStronglyMeasurable Ω ℝ _ (TailSigma.tailSigma X) _
      (fun ω => ∑ c ∈ φ.range,
        (directing_measure X hX_contract hX_meas hX_L2 ω).real (φ ⁻¹' {c}) • c) μ := by
    -- Need to help Lean see the eta-expanded form for Finset.aestronglyMeasurable_sum
    -- Convert fun ω => ∑ c ∈ s, f c ω  to  ∑ c ∈ s, (fun ω => f c ω)
    have h_eq_form : (fun ω => ∑ c ∈ φ.range,
        (directing_measure X hX_contract hX_meas hX_L2 ω).real (φ ⁻¹' {c}) • c) =
        ∑ c ∈ φ.range, fun ω =>
          (directing_measure X hX_contract hX_meas hX_L2 ω).real (φ ⁻¹' {c}) • c := by
      ext ω
      simp only [Finset.sum_apply]
    rw [h_eq_form]
    -- Convert smul to mul for ℝ-valued functions
    simp_rw [smul_eq_mul]
    -- Prove AEStronglyMeasurable for each term, then use finite sum
    have h_terms_aesm : ∀ c ∈ φ.range, @AEStronglyMeasurable Ω ℝ _ (TailSigma.tailSigma X) _
        (fun ω => (directing_measure X hX_contract hX_meas hX_L2 ω).real (φ ⁻¹' {c}) * c) μ := by
      intro c _
      -- Need to show: ω ↦ ν(ω).real(φ⁻¹'{c}) * c is tail-AESM
      have h_preimage_meas : MeasurableSet (φ ⁻¹' {c}) := SimpleFunc.measurableSet_preimage φ {c}
      -- ω ↦ ν(ω).real(φ⁻¹'{c}) = ∫ 1_{φ⁻¹'{c}} dν(ω) is tail-AESM by A1
      have h_real_eq : ∀ ω, (directing_measure X hX_contract hX_meas hX_L2 ω).real (φ ⁻¹' {c}) =
          ∫ x, (φ ⁻¹' {c}).indicator 1 x
            ∂(directing_measure X hX_contract hX_meas hX_L2 ω) := by
        intro ω
        haveI hprob := directing_measure_isProbabilityMeasure X hX_contract hX_meas hX_L2 ω
        exact (integral_indicator_one h_preimage_meas).symm
      have h_term_aesm : @AEStronglyMeasurable Ω ℝ _ (TailSigma.tailSigma X) _
          (fun ω => (directing_measure X hX_contract hX_meas hX_L2 ω).real (φ ⁻¹' {c})) μ := by
        have := integral_indicator_borel_tailAEStronglyMeasurable X hX_contract hX_meas hX_L2
          (φ ⁻¹' {c}) h_preimage_meas
        exact AEStronglyMeasurable.congr this (ae_of_all _ (fun ω => (h_real_eq ω).symm))
      -- (tail-AESM) * c is tail-AESM (smul_const gives f(x) • c = f(x) * c for ℝ)
      exact h_term_aesm.smul_const c
    -- Sum of tail-AESM functions is tail-AESM (finite induction)
    have h_zero : @AEStronglyMeasurable Ω ℝ _ (TailSigma.tailSigma X) _ (fun _ => 0) μ :=
      aestronglyMeasurable_const
    have h_add : ∀ f g : Ω → ℝ,
        @AEStronglyMeasurable Ω ℝ _ (TailSigma.tailSigma X) _ f μ →
        @AEStronglyMeasurable Ω ℝ _ (TailSigma.tailSigma X) _ g μ →
        @AEStronglyMeasurable Ω ℝ _ (TailSigma.tailSigma X) _ (f + g) μ :=
      fun _ _ hf hg => hf.add hg
    exact Finset.sum_induction _ _ h_add h_zero h_terms_aesm

  exact AEStronglyMeasurable.congr h_aesm (ae_of_all _ (fun ω => (h_eq ω).symm))

/-- **Phase C:** For bounded measurable f, the integral is tail-AEStronglyMeasurable.

Uses `SimpleFunc.approxOn` to approximate f by simple functions.
Takes limit via `aestronglyMeasurable_of_tendsto_ae` + DCT. -/
lemma integral_bounded_measurable_tailAEStronglyMeasurable
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ)
    (f : ℝ → ℝ) (hf_meas : Measurable f) (hf_bdd : ∃ M, ∀ x, |f x| ≤ M) :
    @AEStronglyMeasurable Ω ℝ _ (TailSigma.tailSigma X) _
      (fun ω => ∫ x, f x ∂(directing_measure X hX_contract hX_meas hX_L2 ω)) μ := by
  -- Get the bound M (ensure M ≥ 0)
  obtain ⟨M, hM⟩ := hf_bdd
  obtain ⟨M', hM'_nonneg, hM'⟩ : ∃ M' : ℝ, 0 ≤ M' ∧ ∀ x, |f x| ≤ M' := by
    use max M 0
    exact ⟨le_max_right M 0, fun x => (hM x).trans (le_max_left M 0)⟩

  -- The range of f is in Set.Icc (-M') M'
  have hf_range : ∀ x, f x ∈ Set.Icc (-M') M' := by
    intro x
    rw [Set.mem_Icc]
    exact abs_le.mp (hM' x)

  -- Set.Icc (-M') M' is nonempty (contains 0 when M' ≥ 0)
  have h0_mem : (0 : ℝ) ∈ Set.Icc (-M') M' := by
    rw [Set.mem_Icc]
    exact ⟨by linarith, hM'_nonneg⟩

  -- Approximate f by simple functions using approxOn
  let φ : ℕ → SimpleFunc ℝ ℝ := SimpleFunc.approxOn f hf_meas (Set.Icc (-M') M') 0 h0_mem

  -- Each φ n has values in Set.Icc (-M') M'
  have hφ_range : ∀ n x, φ n x ∈ Set.Icc (-M') M' := by
    intro n x
    exact SimpleFunc.approxOn_mem hf_meas h0_mem n x

  -- φ n → f pointwise (since f x ∈ closure (Icc (-M') M') = Icc (-M') M')
  have hφ_tendsto : ∀ x, Filter.Tendsto (fun n => φ n x) Filter.atTop (nhds (f x)) := by
    intro x
    apply SimpleFunc.tendsto_approxOn hf_meas h0_mem
    -- f x ∈ closure (Icc (-M') M') = Icc (-M') M' (closed set)
    rw [IsClosed.closure_eq (isClosed_Icc)]
    exact hf_range x

  -- Each ∫ φ_n dν(ω) is tail-AESM by Phase B
  have hφ_aesm : ∀ n, @AEStronglyMeasurable Ω ℝ _ (TailSigma.tailSigma X) _
      (fun ω => ∫ x, φ n x ∂(directing_measure X hX_contract hX_meas hX_L2 ω)) μ := by
    intro n
    exact integral_simpleFunc_tailAEStronglyMeasurable X hX_contract hX_meas hX_L2 (φ n)

  -- ∫ φ_n dν(ω) → ∫ f dν(ω) for each ω (by DCT on ν(ω))
  have h_int_tendsto : ∀ ω, Filter.Tendsto
      (fun n => ∫ x, φ n x ∂(directing_measure X hX_contract hX_meas hX_L2 ω))
      Filter.atTop
      (nhds (∫ x, f x ∂(directing_measure X hX_contract hX_meas hX_L2 ω))) := by
    intro ω
    haveI hprob := directing_measure_isProbabilityMeasure X hX_contract hX_meas hX_L2 ω
    -- Apply DCT with bound M' (constant, hence integrable)
    apply tendsto_integral_of_dominated_convergence (fun _ => M')
    · intro n
      exact (SimpleFunc.measurable (φ n)).aestronglyMeasurable
    · exact integrable_const M'
    · intro n
      filter_upwards with x
      rw [Real.norm_eq_abs]
      have := hφ_range n x
      rw [Set.mem_Icc] at this
      exact abs_le.mpr this
    · filter_upwards with x
      exact hφ_tendsto x

  -- Strategy: Each ∫ φ_n dν(·) is tail-Measurable (not just AESM). Pointwise limits of
  -- tail-measurable functions are tail-measurable. Then tail-Measurable → tail-AESM.
  -- Technical issue: aestronglyMeasurable_of_tendsto_ae requires same σ-algebra for SM and measure.
  -- TODO: Prove using measurable_of_tendsto_metrizable on the underlying measurable functions.
  -- For now, we use that the limit is ambient-AESM (which is strictly weaker but compiles).
  have hφ_aesm_ambient : ∀ n, AEStronglyMeasurable
      (fun ω => ∫ x, φ n x ∂(directing_measure X hX_contract hX_meas hX_L2 ω)) μ := by
    intro n
    exact (hφ_aesm n).mono (TailSigma.tailSigma_le X hX_meas)
  -- The limit is ambient-AESM
  have h_limit_aesm : AEStronglyMeasurable
      (fun ω => ∫ x, f x ∂(directing_measure X hX_contract hX_meas hX_L2 ω)) μ :=
    aestronglyMeasurable_of_tendsto_ae Filter.atTop hφ_aesm_ambient (ae_of_all μ h_int_tendsto)
  -- Strategy: Use StronglyMeasurable.limUnder on tail-SM representatives.
  -- Get the tail-SM ae-representatives for each ∫ φ_n dν(·)
  let g_n (n : ℕ) : Ω → ℝ := (hφ_aesm n).mk (fun ω => ∫ x, φ n x
      ∂(directing_measure X hX_contract hX_meas hX_L2 ω))
  have hg_n_sm : ∀ n, @StronglyMeasurable Ω ℝ _ (TailSigma.tailSigma X) (g_n n) :=
    fun n => (hφ_aesm n).stronglyMeasurable_mk
  have hg_n_ae : ∀ n, (fun ω => ∫ x, φ n x ∂(directing_measure X hX_contract hX_meas hX_L2 ω))
      =ᶠ[ae μ] g_n n := fun n => (hφ_aesm n).ae_eq_mk
  -- g_n converge ae to ∫ f dν(·) (since ∫ φ_n dν(·) → ∫ f dν(·) pointwise and ∫ φ_n dν(·) =ᵐ g_n)
  have h_g_tendsto : ∀ᵐ ω ∂μ, Filter.Tendsto (fun n => g_n n ω) Filter.atTop
      (nhds (∫ x, f x ∂(directing_measure X hX_contract hX_meas hX_L2 ω))) := by
    have h_ae_eq_all : ∀ᵐ ω ∂μ, ∀ n, g_n n ω = ∫ x, φ n x
        ∂(directing_measure X hX_contract hX_meas hX_L2 ω) := by
      rw [ae_all_iff]
      intro n
      exact (hg_n_ae n).symm
    filter_upwards [h_ae_eq_all] with ω h_eq
    simp_rw [h_eq]
    exact h_int_tendsto ω
  -- Use limUnder which is the pointwise limit - StronglyMeasurable.limUnder shows
  -- that the pointwise limit of tail-SM functions is tail-SM
  let g_tail : Ω → ℝ := fun ω => limUnder atTop (fun n => g_n n ω)
  have hg_tail_sm : @StronglyMeasurable Ω ℝ _ (TailSigma.tailSigma X) g_tail :=
    @StronglyMeasurable.limUnder ℕ Ω ℝ (TailSigma.tailSigma X) _ _ _ atTop _
      (fun n => g_n n) _ hg_n_sm
  -- g_tail equals ∫ f dν(·) ae (since g_n → ∫ f dν(·) ae, and limUnder captures this limit)
  have hg_tail_eq : g_tail =ᶠ[ae μ]
      (fun ω => ∫ x, f x ∂(directing_measure X hX_contract hX_meas hX_L2 ω)) := by
    filter_upwards [h_g_tendsto] with ω hω
    exact hω.limUnder_eq
  exact ⟨g_tail, hg_tail_sm, hg_tail_eq.symm⟩

/-- **Set integral equality for Iic indicators.**

Base case: For Iic indicators, set integral equality follows from
`directing_measure_integral_Iic_ae_eq_alphaIicCE` + `setIntegral_condExp`. -/
lemma setIntegral_directing_measure_indicator_Iic_eq
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ)
    (t : ℝ) (A : Set Ω)
    (hA : @MeasurableSet Ω (TailSigma.tailSigma X) A)
    (hμA : μ A < ⊤) :
    ∫ ω in A, (∫ x, (Set.Iic t).indicator (fun _ => (1:ℝ)) x
        ∂(directing_measure X hX_contract hX_meas hX_L2 ω)) ∂μ
      = ∫ ω in A, (Set.Iic t).indicator (fun _ => (1:ℝ)) (X 0 ω) ∂μ := by
  -- Set up σ-algebra facts
  have hm_le : TailSigma.tailSigma X ≤ (inferInstance : MeasurableSpace Ω) :=
    TailSigma.tailSigma_le X hX_meas
  haveI : SigmaFinite (μ.trim hm_le) := inferInstance

  -- Step 1: ∫ 1_{Iic t} dν(ω) =ᵐ alphaIicCE t ω
  have h_ae := directing_measure_integral_Iic_ae_eq_alphaIicCE X hX_contract hX_meas hX_L2 t

  -- Step 2: ∫_A (∫ 1_{Iic t} dν) dμ = ∫_A alphaIicCE t dμ
  -- Use setIntegral_congr_ae
  have hA_ambient : MeasurableSet A := hm_le A hA
  have h_step2 : ∫ ω in A, (∫ x, (Set.Iic t).indicator (fun _ => (1:ℝ)) x
      ∂(directing_measure X hX_contract hX_meas hX_L2 ω)) ∂μ =
      ∫ ω in A, alphaIicCE X hX_contract hX_meas hX_L2 t ω ∂μ := by
    apply setIntegral_congr_ae hA_ambient
    filter_upwards [h_ae] with ω hω _
    exact hω

  -- Step 3: ∫_A alphaIicCE t dμ = ∫_A 1_{Iic t}(X₀) dμ
  -- alphaIicCE t = μ[1_{Iic t} ∘ X 0 | tail], so by setIntegral_condExp
  have h_step3 : ∫ ω in A, alphaIicCE X hX_contract hX_meas hX_L2 t ω ∂μ =
      ∫ ω in A, (Set.Iic t).indicator (fun _ => (1:ℝ)) (X 0 ω) ∂μ := by
    unfold alphaIicCE
    -- Convert composition form to lambda form
    simp only [indIic, Function.comp_def]
    -- Need to show the indicator function is integrable
    have h_int : Integrable (fun ω => (Set.Iic t).indicator (fun _ => (1:ℝ)) (X 0 ω)) μ := by
      apply Integrable.indicator
      · exact integrable_const 1
      · exact measurableSet_Iic.preimage (hX_meas 0)
    rw [setIntegral_condExp hm_le h_int hA]

  rw [h_step2, h_step3]

/-- **Set integral equality for Borel indicator functions.**

Extended from Iic indicators via π-λ argument. -/
lemma setIntegral_directing_measure_indicator_eq
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ)
    (s : Set ℝ) (hs : MeasurableSet s)
    (A : Set Ω) (hA : @MeasurableSet Ω (TailSigma.tailSigma X) A) (hμA : μ A < ⊤) :
    ∫ ω in A, (∫ x, s.indicator (fun _ => (1:ℝ)) x
        ∂(directing_measure X hX_contract hX_meas hX_L2 ω)) ∂μ
      = ∫ ω in A, s.indicator (fun _ => (1:ℝ)) (X 0 ω) ∂μ := by
  classical
  have hm_le : TailSigma.tailSigma X ≤ (inferInstance : MeasurableSpace Ω) :=
    TailSigma.tailSigma_le X hX_meas
  have hA_ambient : MeasurableSet A := hm_le A hA

  -- Define G = {t | MeasurableSet t ∧ set integral equality holds}
  let G : Set (Set ℝ) := {t | MeasurableSet t ∧
    ∫ ω in A, (∫ x, t.indicator (fun _ => (1:ℝ)) x
        ∂(directing_measure X hX_contract hX_meas hX_L2 ω)) ∂μ
      = ∫ ω in A, t.indicator (fun _ => (1:ℝ)) (X 0 ω) ∂μ}

  -- Step 1: G contains {Iic t}
  have h_pi : ∀ t : ℝ, Set.Iic t ∈ G := fun t => ⟨measurableSet_Iic,
    setIntegral_directing_measure_indicator_Iic_eq X hX_contract hX_meas hX_L2 t A hA hμA⟩

  -- Step 2: G is a Dynkin system
  have h_empty : ∅ ∈ G := by
    constructor
    · exact MeasurableSet.empty
    · simp only [Set.indicator_empty, integral_zero]

  have h_compl : ∀ t ∈ G, tᶜ ∈ G := by
    intro t ⟨ht_meas, ht_eq⟩
    constructor
    · exact ht_meas.compl
    · -- LHS: ∫_A (∫ 1_{tᶜ} dν) dμ = ∫_A (1 - ∫ 1_t dν) dμ = ∫_A 1 dμ - ∫_A (∫ 1_t dν) dμ
      -- RHS: ∫_A 1_{tᶜ}(X₀) dμ = ∫_A (1 - 1_t(X₀)) dμ = ∫_A 1 dμ - ∫_A 1_t(X₀) dμ
      -- By ht_eq, LHS = RHS
      have h_lhs_eq : ∫ ω in A, (∫ x, tᶜ.indicator (fun _ => (1:ℝ)) x
          ∂(directing_measure X hX_contract hX_meas hX_L2 ω)) ∂μ =
          ∫ ω in A, (1 : ℝ) ∂μ - ∫ ω in A, (∫ x, t.indicator (fun _ => (1:ℝ)) x
            ∂(directing_measure X hX_contract hX_meas hX_L2 ω)) ∂μ := by
        -- ∫ 1_{tᶜ} dν = 1 - ∫ 1_t dν (since ν is probability measure)
        have h_compl_eq : ∀ ω, ∫ x, tᶜ.indicator (fun _ => (1:ℝ)) x
            ∂(directing_measure X hX_contract hX_meas hX_L2 ω) =
            1 - ∫ x, t.indicator (fun _ => (1:ℝ)) x
              ∂(directing_measure X hX_contract hX_meas hX_L2 ω) := by
          intro ω
          haveI hprob := directing_measure_isProbabilityMeasure X hX_contract hX_meas hX_L2 ω
          have h_ind_compl : ∀ x, tᶜ.indicator (fun _ => (1:ℝ)) x =
              1 - t.indicator (fun _ => (1:ℝ)) x := by
            intro x
            by_cases hx : x ∈ t
            · simp [Set.indicator_of_mem hx, Set.indicator_of_not_mem (Set.not_mem_compl_iff.mpr hx)]
            · simp [Set.indicator_of_not_mem hx, Set.indicator_of_mem (Set.mem_compl hx)]
          simp_rw [h_ind_compl]
          rw [integral_sub (integrable_const 1), integral_const, measureReal_univ_eq_one, one_smul]
          exact (integrable_const 1).indicator ht_meas
        simp_rw [h_compl_eq]
        rw [integral_sub, integral_const]
        · exact (integrable_const 1).integrableOn
        · -- Need integrability of ω ↦ ∫ 1_t dν(ω) on A
          apply Integrable.integrableOn
          apply Integrable.mono' (integrable_const 1)
          · exact integral_indicator_borel_tailAEStronglyMeasurable X hX_contract hX_meas hX_L2 t ht_meas
              |>.mono hm_le
          · filter_upwards with ω
            rw [Real.norm_eq_abs]
            haveI hprob := directing_measure_isProbabilityMeasure X hX_contract hX_meas hX_L2 ω
            calc |∫ x, t.indicator (fun _ => (1:ℝ)) x
                ∂(directing_measure X hX_contract hX_meas hX_L2 ω)|
              ≤ ∫ x, |t.indicator (fun _ => (1:ℝ)) x|
                  ∂(directing_measure X hX_contract hX_meas hX_L2 ω) := abs_integral_le_integral_abs
              _ ≤ ∫ _, 1 ∂(directing_measure X hX_contract hX_meas hX_L2 ω) := by
                  apply integral_mono_of_nonneg
                  · exact ae_of_all _ (fun _ => abs_nonneg _)
                  · exact integrable_const 1
                  · exact ae_of_all _ (fun x => by
                      simp only [Set.indicator_apply]
                      split_ifs <;> simp)
              _ = 1 := by simp [measureReal_univ_eq_one]
      have h_rhs_eq : ∫ ω in A, tᶜ.indicator (fun _ => (1:ℝ)) (X 0 ω) ∂μ =
          ∫ ω in A, (1 : ℝ) ∂μ - ∫ ω in A, t.indicator (fun _ => (1:ℝ)) (X 0 ω) ∂μ := by
        have h_ind_compl : ∀ ω, tᶜ.indicator (fun _ => (1:ℝ)) (X 0 ω) =
            1 - t.indicator (fun _ => (1:ℝ)) (X 0 ω) := by
          intro ω
          by_cases hx : X 0 ω ∈ t
          · simp [Set.indicator_of_mem hx, Set.indicator_of_not_mem (Set.not_mem_compl_iff.mpr hx)]
          · simp [Set.indicator_of_not_mem hx, Set.indicator_of_mem (Set.mem_compl hx)]
        simp_rw [h_ind_compl]
        rw [integral_sub, integral_const]
        · exact (integrable_const 1).integrableOn
        · apply Integrable.integrableOn
          exact (integrable_const 1).indicator (ht_meas.preimage (hX_meas 0))
      rw [h_lhs_eq, h_rhs_eq, ht_eq]

  have h_iUnion : ∀ (f : ℕ → Set ℝ), (∀ i j, i ≠ j → Disjoint (f i) (f j)) →
      (∀ n, f n ∈ G) → (⋃ n, f n) ∈ G := by
    intro f hdisj hf
    constructor
    · exact MeasurableSet.iUnion (fun n => (hf n).1)
    · -- LHS: ∫_A (∫ 1_{⋃ fn} dν) dμ = ∫_A (∑' ∫ 1_{fn} dν) dμ = ∑' ∫_A (∫ 1_{fn} dν) dμ
      -- RHS: ∫_A 1_{⋃ fn}(X₀) dμ = ∫_A (∑' 1_{fn}(X₀)) dμ = ∑' ∫_A 1_{fn}(X₀) dμ
      -- By (hf n).2, each term is equal, hence sums are equal
      have h_lhs_eq : ∫ ω in A, (∫ x, (⋃ n, f n).indicator (fun _ => (1:ℝ)) x
          ∂(directing_measure X hX_contract hX_meas hX_L2 ω)) ∂μ =
          ∑' n, ∫ ω in A, (∫ x, (f n).indicator (fun _ => (1:ℝ)) x
            ∂(directing_measure X hX_contract hX_meas hX_L2 ω)) ∂μ := by
        -- First rewrite the inner integral as a tsum
        have h_inner_eq : ∀ ω, ∫ x, (⋃ n, f n).indicator (fun _ => (1:ℝ)) x
            ∂(directing_measure X hX_contract hX_meas hX_L2 ω) =
            ∑' n, ∫ x, (f n).indicator (fun _ => (1:ℝ)) x
              ∂(directing_measure X hX_contract hX_meas hX_L2 ω) := by
          intro ω
          haveI hprob := directing_measure_isProbabilityMeasure X hX_contract hX_meas hX_L2 ω
          have h_ind_union : ∀ x, (⋃ n, f n).indicator (fun _ => (1:ℝ)) x =
              ∑' n, (f n).indicator (fun _ => (1:ℝ)) x := by
            intro x
            by_cases hx : x ∈ ⋃ n, f n
            · obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
              rw [Set.indicator_of_mem hx]
              have h_unique : ∀ m, m ≠ n → x ∉ f m := by
                intro m hm hxm; exact (hdisj n m (Ne.symm hm)).ne_of_mem hn hxm rfl
              rw [tsum_eq_single n]
              · simp [Set.indicator_of_mem hn]
              · intro m hm; simp [Set.indicator_of_not_mem (h_unique m hm)]
            · simp only [Set.indicator_of_not_mem hx]
              have : ∀ n, x ∉ f n := fun n hn => hx (Set.mem_iUnion.mpr ⟨n, hn⟩)
              simp [Set.indicator_of_not_mem (this _)]
          simp_rw [h_ind_union]
          rw [integral_tsum]
          · exact fun n => (measurable_const.indicator (hf n).1).aestronglyMeasurable
          · -- ∑' i, ∫⁻ a, ‖(f i).indicator 1 a‖ₑ ∂ν ≠ ⊤
            -- For disjoint sets on prob measure: ∑' i, ν(f i) = ν(⋃ f i) ≤ 1
            apply ne_top_of_le_ne_top (ENNReal.one_ne_top)
            have h_sum_eq : ∑' i, ∫⁻ a, ‖(f i).indicator (fun _ => (1:ℝ)) a‖ₑ
                ∂(directing_measure X hX_contract hX_meas hX_L2 ω) =
                ∑' i, (directing_measure X hX_contract hX_meas hX_L2 ω) (f i) := by
              refine tsum_congr (fun i => ?_)
              have h_eq : ∀ a, ‖(f i).indicator (fun _ => (1:ℝ)) a‖ₑ =
                  (f i).indicator (fun _ => (1:ENNReal)) a := by
                intro a
                rw [enorm_indicator_eq_indicator_enorm]
                simp only [Real.enorm_eq_ofReal_abs, abs_one, ENNReal.ofReal_one]
              simp_rw [h_eq]
              have h_ind_eq : (fun a => (f i).indicator (fun _ => (1:ENNReal)) a) =
                  (f i).indicator 1 := by ext; simp [Set.indicator]
              rw [h_ind_eq, lintegral_indicator_one (hf i).1]
            calc ∑' i, ∫⁻ a, ‖(f i).indicator (fun _ => (1:ℝ)) a‖ₑ
                ∂(directing_measure X hX_contract hX_meas hX_L2 ω)
              = ∑' i, (directing_measure X hX_contract hX_meas hX_L2 ω) (f i) := h_sum_eq
              _ = (directing_measure X hX_contract hX_meas hX_L2 ω) (⋃ i, f i) := by
                rw [measure_iUnion hdisj (fun i => (hf i).1)]
              _ ≤ 1 := prob_le_one
        simp_rw [h_inner_eq]
        -- Now we need: ∫_A (∑' fn) dμ = ∑' ∫_A fn dμ
        rw [integral_tsum]
        · -- case hf: AEStronglyMeasurable
          intro i
          exact integral_indicator_borel_tailAEStronglyMeasurable X hX_contract hX_meas hX_L2
            (f i) (hf i).1 |>.mono hm_le |>.restrict
        · -- case hf': ∑' ... ≠ ⊤ (prove sum is finite)
          -- Use interchange: ∑' ∫⁻ = ∫⁻ ∑', then bound by ∫⁻ 1 = μ(A)
          apply ne_top_of_le_ne_top (measure_ne_top (μ.restrict A) Set.univ)
          -- For each ω, the inner integral equals ν(ω)(f i) which is nonneg
          have h_eq_meas : ∀ ω i, ‖∫ x, (f i).indicator (fun _ => (1:ℝ)) x
              ∂(directing_measure X hX_contract hX_meas hX_L2 ω)‖ₑ =
              (directing_measure X hX_contract hX_meas hX_L2 ω) (f i) := by
            intro ω i
            haveI hprob := directing_measure_isProbabilityMeasure X hX_contract hX_meas hX_L2 ω
            have h_ind_eq : (fun x => (f i).indicator (fun _ => (1:ℝ)) x) =
                (f i).indicator 1 := by ext; simp [Set.indicator]
            rw [h_ind_eq, integral_indicator_one (hf i).1, Measure.real]
            simp only [Real.enorm_eq_ofReal_abs]
            rw [abs_of_nonneg (ENNReal.toReal_nonneg), ENNReal.ofReal_toReal]
            exact measure_ne_top _ _
          simp_rw [h_eq_meas]
          -- Interchange sum and integral using lintegral_tsum
          have h_ae_meas : ∀ i, AEMeasurable (fun ω => (directing_measure X hX_contract hX_meas hX_L2 ω) (f i))
              (μ.restrict A) := by
            intro i
            have h_meas_dm : Measurable (directing_measure X hX_contract hX_meas hX_L2) :=
              ProbabilityTheory.measurable_measure_stieltjesOfMeasurableRat
                (measurable_alphaIicRat X hX_contract hX_meas hX_L2)
            exact Measurable.aemeasurable (MeasureTheory.Measure.measurable_measure.mp h_meas_dm (f i) (hf i).1)
          rw [← lintegral_tsum h_ae_meas]
          -- Now bound: ∫⁻ (∑' ν(f i)) ≤ ∫⁻ 1 = μ(A)
          have h_bound : ∫⁻ ω in A, ∑' i, (directing_measure X hX_contract hX_meas hX_L2 ω) (f i) ∂μ
              ≤ ∫⁻ ω in A, 1 ∂μ := by
            apply lintegral_mono
            intro ω
            haveI hprob := directing_measure_isProbabilityMeasure X hX_contract hX_meas hX_L2 ω
            calc ∑' i, (directing_measure X hX_contract hX_meas hX_L2 ω) (f i)
              = (directing_measure X hX_contract hX_meas hX_L2 ω) (⋃ i, f i) :=
                (measure_iUnion hdisj (fun i => (hf i).1)).symm
              _ ≤ 1 := prob_le_one
          calc ∫⁻ ω in A, ∑' i, (directing_measure X hX_contract hX_meas hX_L2 ω) (f i) ∂μ
            ≤ ∫⁻ ω in A, 1 ∂μ := h_bound
            _ = (μ.restrict A) Set.univ := lintegral_one

      have h_rhs_eq : ∫ ω in A, (⋃ n, f n).indicator (fun _ => (1:ℝ)) (X 0 ω) ∂μ =
          ∑' n, ∫ ω in A, (f n).indicator (fun _ => (1:ℝ)) (X 0 ω) ∂μ := by
        have h_ind_union : ∀ ω, (⋃ n, f n).indicator (fun _ => (1:ℝ)) (X 0 ω) =
            ∑' n, (f n).indicator (fun _ => (1:ℝ)) (X 0 ω) := by
          intro ω
          by_cases hx : X 0 ω ∈ ⋃ n, f n
          · obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
            rw [Set.indicator_of_mem hx]
            have h_unique : ∀ m, m ≠ n → X 0 ω ∉ f m := by
              intro m hm hxm; exact (hdisj n m (Ne.symm hm)).ne_of_mem hn hxm rfl
            rw [tsum_eq_single n]
            · simp [Set.indicator_of_mem hn]
            · intro m hm; simp [Set.indicator_of_not_mem (h_unique m hm)]
          · simp only [Set.indicator_of_not_mem hx]
            have : ∀ n, X 0 ω ∉ f n := fun n hn => hx (Set.mem_iUnion.mpr ⟨n, hn⟩)
            simp [Set.indicator_of_not_mem (this _)]
        simp_rw [h_ind_union]
        rw [integral_tsum]
        · intro n
          exact ((measurable_const.indicator (hf n).1).comp (hX_meas 0)).aestronglyMeasurable.restrict
        · -- ∑' n, ∫⁻ ω in A, ‖1_{fn}(X₀ ω)‖ₑ ∂μ ≠ ⊤
          -- Each term equals μ({ω ∈ A | X₀ ω ∈ f n}), sum bounded by μ(A)
          apply ne_top_of_le_ne_top (measure_ne_top (μ.restrict A) Set.univ)
          have h_eq : ∀ n, ∫⁻ ω in A, ‖(f n).indicator (fun _ => (1:ℝ)) (X 0 ω)‖ₑ ∂μ =
              (μ.restrict A) (X 0 ⁻¹' (f n)) := by
            intro n
            have h_simp : ∀ ω, ‖(f n).indicator (fun _ => (1:ℝ)) (X 0 ω)‖ₑ =
                (X 0 ⁻¹' (f n)).indicator (fun _ => (1:ENNReal)) ω := by
              intro ω
              by_cases hω : X 0 ω ∈ f n
              · simp [Set.indicator_of_mem hω, Set.mem_preimage, hω]
              · simp [Set.indicator_of_notMem hω, Set.mem_preimage, hω]
            simp_rw [h_simp]
            have h_ind_eq : (fun ω => (X 0 ⁻¹' (f n)).indicator (fun _ => (1:ENNReal)) ω) =
                (X 0 ⁻¹' (f n)).indicator 1 := by ext; simp [Set.indicator]
            rw [h_ind_eq, lintegral_indicator_one ((hf n).1.preimage (hX_meas 0))]
          simp_rw [h_eq]
          have h_disj : Pairwise (Function.onFun Disjoint fun n => X 0 ⁻¹' (f n)) := by
            intro i j hij
            simp only [Function.onFun]
            exact (hdisj i j hij).preimage (X 0)
          calc ∑' n, (μ.restrict A) (X 0 ⁻¹' (f n))
            = (μ.restrict A) (⋃ n, X 0 ⁻¹' (f n)) :=
              (measure_iUnion h_disj (fun n => (hf n).1.preimage (hX_meas 0))).symm
            _ ≤ (μ.restrict A) Set.univ := measure_mono (Set.subset_univ _)

      rw [h_lhs_eq, h_rhs_eq]
      congr 1
      ext n
      exact (hf n).2

  -- Step 3: Apply π-λ theorem
  let S : Set (Set ℝ) := Set.range (Set.Iic : ℝ → Set ℝ)
  have h_gen : (inferInstance : MeasurableSpace ℝ) = MeasurableSpace.generateFrom S :=
    @borel_eq_generateFrom_Iic ℝ _ _ _ _
  have h_pi_S : IsPiSystem S := by
    intro u hu v hv _
    obtain ⟨r, rfl⟩ := hu
    obtain ⟨t, rfl⟩ := hv
    use min r t
    exact Set.Iic_inter_Iic.symm

  have h_induction : ∀ t (htm : MeasurableSet t), t ∈ G := fun t htm =>
    MeasurableSpace.induction_on_inter h_gen h_pi_S
      h_empty
      (fun u ⟨r, hr⟩ => hr ▸ h_pi r)
      (fun u hum hu => h_compl u hu)
      (fun f hdisj hfm hf => h_iUnion f hdisj hf)
      t htm

  exact (h_induction s hs).2

/-- **Set integral equality for bounded measurable functions.**

This is the key equality needed for `ae_eq_condExp_of_forall_setIntegral_eq`. -/
lemma setIntegral_directing_measure_bounded_measurable_eq
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ)
    (f : ℝ → ℝ) (hf_meas : Measurable f) (hf_bdd : ∃ M, ∀ x, |f x| ≤ M)
    (A : Set Ω) (hA : @MeasurableSet Ω (TailSigma.tailSigma X) A) (hμA : μ A < ⊤) :
    ∫ ω in A, (∫ x, f x ∂(directing_measure X hX_contract hX_meas hX_L2 ω)) ∂μ
      = ∫ ω in A, f (X 0 ω) ∂μ := by
  -- Get the bound M (ensure M ≥ 0)
  obtain ⟨M, hM⟩ := hf_bdd
  obtain ⟨M', hM'_nonneg, hM'⟩ : ∃ M' : ℝ, 0 ≤ M' ∧ ∀ x, |f x| ≤ M' := by
    use max M 0
    exact ⟨le_max_right M 0, fun x => (hM x).trans (le_max_left M 0)⟩

  have hm_le : TailSigma.tailSigma X ≤ (inferInstance : MeasurableSpace Ω) :=
    TailSigma.tailSigma_le X hX_meas
  have hA_ambient : MeasurableSet A := hm_le A hA

  -- The range of f is in Set.Icc (-M') M'
  have hf_range : ∀ x, f x ∈ Set.Icc (-M') M' := by
    intro x
    rw [Set.mem_Icc]
    exact abs_le.mp (hM' x)

  have h0_mem : (0 : ℝ) ∈ Set.Icc (-M') M' := by
    rw [Set.mem_Icc]; exact ⟨by linarith, hM'_nonneg⟩

  -- Approximate f by simple functions
  let φ : ℕ → SimpleFunc ℝ ℝ := SimpleFunc.approxOn f hf_meas (Set.Icc (-M') M') 0 h0_mem

  have hφ_range : ∀ n x, φ n x ∈ Set.Icc (-M') M' := fun n x =>
    SimpleFunc.approxOn_mem hf_meas h0_mem n x

  have hφ_tendsto : ∀ x, Filter.Tendsto (fun n => φ n x) Filter.atTop (nhds (f x)) := by
    intro x
    apply SimpleFunc.tendsto_approxOn hf_meas h0_mem
    rw [IsClosed.closure_eq (isClosed_Icc)]
    exact hf_range x

  -- LHS: ∫_A (∫ φ_n dν) dμ → ∫_A (∫ f dν) dμ
  have h_lhs_tendsto : Filter.Tendsto
      (fun n => ∫ ω in A, (∫ x, φ n x ∂(directing_measure X hX_contract hX_meas hX_L2 ω)) ∂μ)
      Filter.atTop
      (nhds (∫ ω in A, (∫ x, f x ∂(directing_measure X hX_contract hX_meas hX_L2 ω)) ∂μ)) := by
    -- Apply DCT with bound M' (set integrals are definitionally restricted integrals)
    apply tendsto_integral_of_dominated_convergence (fun _ => M')
    · intro n
      exact integral_simpleFunc_tailAEStronglyMeasurable X hX_contract hX_meas hX_L2 (φ n)
        |>.mono hm_le |>.restrict
    · exact (integrable_const M').integrableOn
    · intro n
      filter_upwards with ω
      rw [Real.norm_eq_abs]
      haveI hprob := directing_measure_isProbabilityMeasure X hX_contract hX_meas hX_L2 ω
      -- |∫ φ_n dν| ≤ M' (since |φ_n| ≤ M' and ν is prob measure)
      calc |∫ x, φ n x ∂(directing_measure X hX_contract hX_meas hX_L2 ω)|
        ≤ ∫ x, |φ n x| ∂(directing_measure X hX_contract hX_meas hX_L2 ω) := abs_integral_le_integral_abs
        _ ≤ ∫ _, M' ∂(directing_measure X hX_contract hX_meas hX_L2 ω) := by
            apply integral_mono_of_nonneg
            · exact ae_of_all _ (fun _ => abs_nonneg _)
            · exact integrable_const M'
            · filter_upwards with x
              have := hφ_range n x
              rw [Set.mem_Icc] at this
              exact abs_le.mpr this
        _ = M' := by simp [measureReal_univ_eq_one]
    · filter_upwards with ω
      -- ∫ φ_n dν(ω) → ∫ f dν(ω) by DCT on ν(ω)
      haveI hprob := directing_measure_isProbabilityMeasure X hX_contract hX_meas hX_L2 ω
      apply tendsto_integral_of_dominated_convergence (fun _ => M')
      · intro n; exact (SimpleFunc.measurable (φ n)).aestronglyMeasurable
      · exact integrable_const M'
      · intro n; filter_upwards with x
        rw [Real.norm_eq_abs]
        have := hφ_range n x
        rw [Set.mem_Icc] at this
        exact abs_le.mpr this
      · filter_upwards with x; exact hφ_tendsto x

  -- RHS: ∫_A φ_n(X₀) dμ → ∫_A f(X₀) dμ
  have h_rhs_tendsto : Filter.Tendsto
      (fun n => ∫ ω in A, (φ n) (X 0 ω) ∂μ)
      Filter.atTop
      (nhds (∫ ω in A, f (X 0 ω) ∂μ)) := by
    -- Apply DCT with bound M' (set integrals are definitionally restricted integrals)
    apply tendsto_integral_of_dominated_convergence (fun _ => M')
    · intro n
      exact ((SimpleFunc.measurable (φ n)).comp (hX_meas 0)).aestronglyMeasurable.restrict
    · exact (integrable_const M').integrableOn
    · intro n
      filter_upwards with ω
      rw [Real.norm_eq_abs]
      have := hφ_range n (X 0 ω)
      rw [Set.mem_Icc] at this
      exact abs_le.mpr this
    · filter_upwards with ω
      exact hφ_tendsto (X 0 ω)

  -- For each n, LHS_n = RHS_n
  have h_eq_n : ∀ n, ∫ ω in A, (∫ x, φ n x ∂(directing_measure X hX_contract hX_meas hX_L2 ω)) ∂μ
      = ∫ ω in A, (φ n) (X 0 ω) ∂μ := by
    intro n
    -- SimpleFunc integral is finite sum of indicator integrals
    -- Use setIntegral_directing_measure_indicator_eq + linearity
    have h_sf_eq : ∀ ω, ∫ x, φ n x ∂(directing_measure X hX_contract hX_meas hX_L2 ω) =
        ∑ c ∈ (φ n).range, (directing_measure X hX_contract hX_meas hX_L2 ω).real ((φ n) ⁻¹' {c}) • c := by
      intro ω
      haveI hprob := directing_measure_isProbabilityMeasure X hX_contract hX_meas hX_L2 ω
      have h_int : Integrable (⇑(φ n)) (directing_measure X hX_contract hX_meas hX_L2 ω) :=
        SimpleFunc.integrable_of_isFiniteMeasure (φ n)
      exact SimpleFunc.integral_eq_sum (φ n) h_int
    have h_rhs_sf_eq : ∀ ω, (φ n) (X 0 ω) =
        ∑ c ∈ (φ n).range, ((φ n) ⁻¹' {c}).indicator (fun _ => c) (X 0 ω) := by
      intro ω
      let c₀ := (φ n) (X 0 ω)
      have hc₀_mem : c₀ ∈ (φ n).range := SimpleFunc.mem_range_self (φ n) (X 0 ω)
      have hX_in_preimage : X 0 ω ∈ (φ n) ⁻¹' {c₀} := Set.mem_preimage.mpr rfl
      rw [Finset.sum_eq_single c₀]
      · simp only [Set.indicator_of_mem hX_in_preimage]
        -- Now goal is (φ n) (X 0 ω) = c₀, which is rfl since c₀ := (φ n) (X 0 ω)
        rfl
      · intro c _ hc_ne
        have hX_not_in : X 0 ω ∉ (φ n) ⁻¹' {c} := by
          simp only [Set.mem_preimage, Set.mem_singleton_iff]
          intro heq
          exact hc_ne heq.symm
        simp only [Set.indicator_of_notMem hX_not_in]
      · intro hc₀_not
        exact (hc₀_not hc₀_mem).elim
    -- Both sides are sums; equality term by term
    simp_rw [h_sf_eq, h_rhs_sf_eq]
    rw [integral_finset_sum, integral_finset_sum]
    · congr 1
      ext c
      -- Need: ∫_A ν(ω).real((φ n)⁻¹'{c}) • c dμ = ∫_A 1_{(φ n)⁻¹'{c}}(X₀) • c dμ
      have h_preimage_meas : MeasurableSet ((φ n) ⁻¹' {c}) := SimpleFunc.measurableSet_preimage (φ n) {c}
      -- Transform LHS: ν(ω).real(S) • c = (∫ 1_S dν) • c
      have h_real_eq_ind : ∀ ω, (directing_measure X hX_contract hX_meas hX_L2 ω).real ((φ n) ⁻¹' {c}) =
          ∫ x, ((φ n) ⁻¹' {c}).indicator (fun _ => (1:ℝ)) x
            ∂(directing_measure X hX_contract hX_meas hX_L2 ω) := by
        intro ω
        haveI hprob := directing_measure_isProbabilityMeasure X hX_contract hX_meas hX_L2 ω
        have h_ind_eq : ((φ n) ⁻¹' {c}).indicator (fun _ => (1:ℝ)) = ((φ n) ⁻¹' {c}).indicator 1 := by
          ext; simp [Set.indicator]
        rw [h_ind_eq, integral_indicator_one h_preimage_meas]
      -- Transform RHS indicator: 1_S(fun _ => c)(x) = 1_S(fun _ => 1)(x) * c
      have h_ind_X0 : ∀ ω, ((φ n) ⁻¹' {c}).indicator (fun _ => c) (X 0 ω) =
          ((φ n) ⁻¹' {c}).indicator (fun _ => (1:ℝ)) (X 0 ω) * c := by
        intro ω
        by_cases hω : X 0 ω ∈ (φ n) ⁻¹' {c}
        · simp [Set.indicator_of_mem hω]
        · simp [Set.indicator_of_notMem hω]
      simp only [smul_eq_mul, h_real_eq_ind, h_ind_X0]
      -- LHS: ∫ ((∫ indicator 1 ∂ν) * c) dμ,  RHS: ∫ (indicator 1 (X₀) * c) dμ
      -- Factor out * c from both sides using integral_mul_const
      simp only [integral_mul_const]
      -- Now LHS: (∫ (∫ ind dν) dμ) * c,  RHS: (∫ ind(X₀) dμ) * c
      congr 1
      exact setIntegral_directing_measure_indicator_eq X hX_contract hX_meas hX_L2
        ((φ n) ⁻¹' {c}) h_preimage_meas A hA hμA
    · intro c _
      apply Integrable.integrableOn
      have h_pm : MeasurableSet ((φ n) ⁻¹' {c}) := SimpleFunc.measurableSet_preimage (φ n) {c}
      exact (integrable_const c).indicator (h_pm.preimage (hX_meas 0))
    · intro c _
      apply Integrable.integrableOn
      -- Goal: Integrable (fun ω => ν(ω).real(S) • c) μ
      -- Convert to: Integrable (fun ω => ν(ω).real(S) * c) μ
      simp only [smul_eq_mul]
      -- Use Integrable.mul_const for f * c
      apply Integrable.mul_const
      -- Now prove: Integrable (fun ω => ν(ω).real(S)) μ
      have h_pm : MeasurableSet ((φ n) ⁻¹' {c}) := SimpleFunc.measurableSet_preimage (φ n) {c}
      -- ν(ω).real(S) = ∫ 1_S dν(ω), so use Integrable.mono' with indicator AESM
      have h_eq_intind : (fun ω => (directing_measure X hX_contract hX_meas hX_L2 ω).real ((φ n) ⁻¹' {c})) =
          (fun ω => ∫ x, ((φ n) ⁻¹' {c}).indicator 1 x ∂(directing_measure X hX_contract hX_meas hX_L2 ω)) := by
        ext ω
        haveI hprob := directing_measure_isProbabilityMeasure X hX_contract hX_meas hX_L2 ω
        exact (integral_indicator_one h_pm).symm
      rw [h_eq_intind]
      apply Integrable.mono' (integrable_const 1)
      · exact integral_indicator_borel_tailAEStronglyMeasurable X hX_contract hX_meas hX_L2
          ((φ n) ⁻¹' {c}) h_pm |>.mono hm_le
      · filter_upwards with ω
        rw [Real.norm_eq_abs]
        haveI hprob := directing_measure_isProbabilityMeasure X hX_contract hX_meas hX_L2 ω
        rw [abs_le]
        constructor
        · have h := integral_indicator_one h_pm (μ := directing_measure X hX_contract hX_meas hX_L2 ω)
          rw [h]
          -- Goal: -1 ≤ μ.real S
          calc (-1 : ℝ) ≤ 0 := by linarith
            _ ≤ (directing_measure X hX_contract hX_meas hX_L2 ω).real ((φ n) ⁻¹' {c}) := measureReal_nonneg
        · have h := integral_indicator_one h_pm (μ := directing_measure X hX_contract hX_meas hX_L2 ω)
          rw [h]; exact measureReal_le_one

  -- Since limits are unique and h_eq_n holds for all n, the limits are equal
  exact tendsto_nhds_unique h_lhs_tendsto (h_rhs_tendsto.congr (fun n => (h_eq_n n).symm))

/-- **Main bridge lemma:** For any bounded measurable f, the integral against directing_measure
equals the conditional expectation E[f(X₀)|tail].

This is the Kallenberg identification: ν(ω) is the conditional distribution of X₀ given tail. -/
lemma directing_measure_integral_eq_condExp
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ)
    (f : ℝ → ℝ) (hf_meas : Measurable f) (hf_bdd : ∃ M, ∀ x, |f x| ≤ M) :
    (fun ω => ∫ x, f x ∂(directing_measure X hX_contract hX_meas hX_L2 ω))
      =ᵐ[μ] μ[fun ω => f (X 0 ω) | TailSigma.tailSigma X] := by
  -- PROOF STRATEGY: Monotone class extension from Iic to bounded measurable
  --
  -- === STEP 1: Base case for Iic indicators ===
  -- For f = 1_{Iic t}, we need: ∫ 1_{Iic t} dν(ω) =ᵐ E[1_{Iic t}(X₀)|tail](ω)
  --
  -- - LHS: By directing_measure_integral_Iic_ae_eq_alphaIicCE, ∫ 1_{Iic t} dν(ω) =ᵐ αIicCE t ω
  -- - RHS: By definition of αIicCE, αIicCE t ω = μ[1_{Iic t} ∘ X 0 | TailSigma.tailSigma X](ω)
  -- - Result: LHS =ᵐ αIicCE t =ᵐ RHS ✓
  --
  -- === STEP 2: Extend to Ioc indicators ===
  -- For f = 1_{Ioc a b} = 1_{Iic b} - 1_{Iic a} (when a < b):
  -- - ∫ 1_{Ioc a b} dν(ω) = ∫ 1_{Iic b} dν - ∫ 1_{Iic a} dν  (linearity of integral)
  -- - E[1_{Ioc a b}(X₀)|tail] = E[1_{Iic b}(X₀)|tail] - E[1_{Iic a}(X₀)|tail]  (condExp_sub)
  -- - By Step 1, both pairs are a.e. equal → 1_{Ioc a b} works ✓
  --
  -- === STEP 3: Extend to simple functions ===
  -- Simple functions are finite linear combinations of Ioc indicators.
  -- By linearity of both operations (integral_add, integral_smul, condExp_add, condExp_smul),
  -- the result holds for all simple functions ✓
  --
  -- === STEP 4: Extend to bounded measurable ===
  -- For bounded measurable f with |f| ≤ M:
  -- - Use SimpleFunc.approxOn (or MeasureTheory.Lp.simpleFunc_approximation) to get
  --   simple functions s_n → f pointwise with |s_n| ≤ M
  -- - For LHS: Apply MeasureTheory.tendsto_integral_of_dominated_convergence
  --   (dominating function is M, bound by boundedness)
  -- - For RHS: Apply MeasureTheory.tendsto_condExpL1_of_dominated_convergence
  --   (same dominating function)
  -- - Both sides converge in L¹, and by Step 3 they're a.e. equal for each s_n
  -- - By L¹ limit uniqueness, the limits are a.e. equal ✓
  --
  -- Key mathlib lemmas:
  -- - directing_measure_integral_Iic_ae_eq_alphaIicCE (base case, exists above)
  -- - MeasureTheory.condExp_sub, MeasureTheory.condExp_smul (linearity)
  -- - MeasureTheory.SimpleFunc.approxOn (approximation by simple functions)
  -- - MeasureTheory.tendsto_integral_of_dominated_convergence (DCT for integrals)
  -- - MeasureTheory.tendsto_condExpL1_of_dominated_convergence (DCT for condExp)
  --
  -- ═══════════════════════════════════════════════════════════════════════════════
  -- PROOF STRATEGY: Conditional distribution uniqueness
  --
  -- The directing measure ν(ω) is constructed so that its CDF equals αIicCE:
  --   (ν(ω))(Iic t) = αIicCE t ω = E[1_{Iic t}(X₀)|tail](ω) a.e.
  --
  -- Since measures on ℝ are uniquely determined by their CDFs, and the conditional
  -- distribution of X₀ given tail is uniquely characterized by the same CDF values,
  -- we have ν(ω) = P_{X₀|tail}(ω) as measures for a.e. ω.
  --
  -- Therefore, for any bounded measurable f:
  --   ∫ f dν(ω) = E[f(X₀)|tail](ω) a.e.
  --
  -- The proof involves:
  -- 1. Base case: For Iic indicators, directing_measure_integral_Iic_ae_eq_alphaIicCE
  --    gives ∫ 1_{Iic t} dν(ω) =ᵐ αIicCE t ω = E[1_{Iic t}(X₀)|tail](ω)
  --
  -- 2. Extension: For general bounded measurable f, use:
  --    - Step functions approximation (via Ioc indicators)
  --    - Linearity of both ∫ · dν and E[·|tail]
  --    - Dominated convergence to pass to limit
  --
  -- OR use the uniqueness of conditional expectation:
  -- If h is m-measurable and ∫_A h dμ = ∫_A f(X₀) dμ for all m-measurable A,
  -- then h =ᵐ E[f(X₀)|m].
  --
  -- The key is showing ∫_A (∫ f dν) dμ = ∫_A f(X₀) dμ via Fubini and the
  -- conditional distribution property.
  -- ═══════════════════════════════════════════════════════════════════════════════
  --
  -- MATHEMATICAL CONTENT (to be formalized):
  --
  -- The proof requires showing that ν(ω) is the regular conditional distribution
  -- of X₀ given the tail σ-algebra. This follows from:
  -- 1. CDF agreement: For all t, (ν(ω))(Iic t) = E[1_{Iic t}(X₀)|tail](ω) a.e.
  -- 2. Measures are determined by CDFs (uniqueness)
  -- 3. Integration against measures determined by CDFs
  --
  -- The formalization uses ae_eq_condExp_of_forall_setIntegral_eq and requires:
  -- 1. Measurability of ω ↦ ∫ f dν(ω) w.r.t. tail σ-algebra
  -- 2. Set integral equality: ∫_A (∫ f dν) dμ = ∫_A f(X₀) dμ for tail-measurable A
  -- 3. Monotone class extension from Iic indicators to bounded measurable functions

  -- Set up the sub-σ-algebra and sigma-finiteness
  have hm_le : TailSigma.tailSigma X ≤ (inferInstance : MeasurableSpace Ω) :=
    TailSigma.tailSigma_le X hX_meas
  haveI hm_fact : Fact (TailSigma.tailSigma X ≤ (inferInstance : MeasurableSpace Ω)) := ⟨hm_le⟩
  haveI hσ : SigmaFinite (μ.trim hm_le) := inferInstance

  -- Get the bound M (ensure M ≥ 0)
  obtain ⟨M, hM⟩ := hf_bdd
  obtain ⟨M', hM'_nonneg, hM'⟩ : ∃ M' : ℝ, 0 ≤ M' ∧ ∀ x, |f x| ≤ M' := by
    use max M 0
    exact ⟨le_max_right M 0, fun x => (hM x).trans (le_max_left M 0)⟩

  -- Define g = fun ω => ∫ x, f x ∂ν(ω)
  let g : Ω → ℝ := fun ω => ∫ x, f x ∂(directing_measure X hX_contract hX_meas hX_L2 ω)

  -- f ∘ X 0 is integrable (bounded function composed with measurable map)
  have hfX0_int : Integrable (fun ω => f (X 0 ω)) μ := by
    refine Integrable.mono' (integrable_const M') ?_ ?_
    · exact (hf_meas.comp (hX_meas 0)).aestronglyMeasurable
    · filter_upwards with ω; rw [Real.norm_eq_abs]; exact hM' (X 0 ω)

  -- g is bounded by M' (since ν(ω) is a probability measure)
  have hg_bdd : ∀ ω, |g ω| ≤ M' := by
    intro ω
    haveI : IsProbabilityMeasure (directing_measure X hX_contract hX_meas hX_L2 ω) :=
      directing_measure_isProbabilityMeasure X hX_contract hX_meas hX_L2 ω
    calc |g ω| = |∫ x, f x ∂(directing_measure X hX_contract hX_meas hX_L2 ω)| := rfl
      _ ≤ ∫ x, |f x| ∂(directing_measure X hX_contract hX_meas hX_L2 ω) :=
          abs_integral_le_integral_abs
      _ ≤ ∫ x, M' ∂(directing_measure X hX_contract hX_meas hX_L2 ω) := by
          apply integral_mono_of_nonneg
          · exact ae_of_all _ (fun _ => abs_nonneg _)
          · exact integrable_const M'
          · exact ae_of_all _ hM'
      _ = M' := by simp only [integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul]

  -- g is AEStronglyMeasurable w.r.t. ambient σ-algebra
  -- Uses monotone class theorem: measurability extends from Iic indicators to bounded measurable f.
  -- First prove tail-AEStronglyMeasurable (hgm), then get ambient from it
  -- Key insight: alphaIicCE t is strongly measurable w.r.t. tail σ-algebra (it's a condExp)
  -- So ∫ 1_{Iic t} dν(ω) =ᵐ alphaIicCE t ω is tail-AEStronglyMeasurable
  -- Extend to bounded measurable f via step function approximation + limits

  have hgm_early : @AEStronglyMeasurable Ω ℝ _ (TailSigma.tailSigma X) _ g μ :=
    -- Use the factored-out helper lemma for Phase C (which builds on Phases A and B)
    integral_bounded_measurable_tailAEStronglyMeasurable X hX_contract hX_meas hX_L2 f hf_meas ⟨M, hM⟩

  -- Ambient AEStronglyMeasurable follows from tail via .mono
  have hg_asm : AEStronglyMeasurable g μ := AEStronglyMeasurable.mono hm_le hgm_early

  -- g is integrable (bounded and measurable on probability space)
  have hg_int : Integrable g μ := by
    refine Integrable.mono' (integrable_const M') hg_asm ?_
    filter_upwards with ω; rw [Real.norm_eq_abs]; exact hg_bdd ω

  -- Apply ae_eq_condExp_of_forall_setIntegral_eq
  -- The theorem says: if g is tail-AEStronglyMeasurable and has the same set integrals as f ∘ X 0
  -- on all tail-measurable sets, then g =ᵐ μ[f ∘ X 0 | tail].
  -- Our goal is g =ᵐ μ[f ∘ X 0 | tail] where g = fun ω => ∫ f dν(ω).
  refine ae_eq_condExp_of_forall_setIntegral_eq hm_le hfX0_int ?hg_int_finite ?hg_eq ?hgm

  case hg_int_finite =>
    intro s _ _; exact hg_int.integrableOn

  case hgm =>
    -- ae_eq_condExp_of_forall_setIntegral_eq needs tail-AEStronglyMeasurable
    -- This is exactly what hgm_early provides.
    exact hgm_early

  case hg_eq =>
    -- The key: ∫_A g dμ = ∫_A f(X₀) dμ for tail-measurable A with μ A < ∞
    intro A hA hμA
    -- Use the factored-out helper lemma for set integral equality
    exact setIntegral_directing_measure_bounded_measurable_eq
      X hX_contract hX_meas hX_L2 f hf_meas ⟨M, hM⟩ A hA hμA

/-- **Simplified directing measure integral via identification chain.**

This lemma proves that the L¹ limit α equals ∫f dν a.e. using the Kallenberg identification chain:
1. α = E[f(X₀)|tail]  (from `cesaro_to_condexp_L2`)
2. E[f(X₀)|tail] = ∫f dν  (from `directing_measure_integral_eq_condExp`)
3. Therefore α = ∫f dν by transitivity

This approach bypasses the Ioc/step function decomposition entirely, giving a much simpler proof.

**Key insight:** By uniqueness of L¹ limits, the L¹ limit from `weighted_sums_converge_L1`
equals the L² limit from `cesaro_to_condexp_L2` (since L² convergence implies L¹ on prob spaces).
-/
lemma directing_measure_integral_via_chain
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
  -- Get α from weighted_sums_converge_L1
  obtain ⟨alpha, hα_meas, hα_L1, hα_conv⟩ :=
    weighted_sums_converge_L1 X hX_contract hX_meas hX_L2 f hf_meas hf_bdd
  refine ⟨alpha, hα_meas, hα_L1, hα_conv, ?_⟩

  -- ═══════════════════════════════════════════════════════════════════════════════
  -- IDENTIFICATION CHAIN: α = E[f(X₀)|tail] = ∫f dν
  -- ═══════════════════════════════════════════════════════════════════════════════

  -- Step 1: Get α_f from cesaro_to_condexp_L2 with identification
  -- α_f =ᵐ E[f(X₀)|tail]
  -- Note: cesaro_to_condexp_L2 requires |f x| ≤ 1, so we need to rescale if M > 1
  obtain ⟨M, hM⟩ := hf_bdd
  by_cases hM_zero : M = 0
  · -- If M = 0, then f = 0, so both α and ∫f dν are 0 a.e.
    have hf_zero : ∀ x, f x = 0 := fun x => by
      have := hM x
      rw [hM_zero] at this
      exact abs_nonpos_iff.mp this

    -- Show ∫f dν = 0 for all ω (deterministic, not just a.e.)
    have h_integral_zero : ∀ ω, ∫ x, f x ∂(directing_measure X hX_contract hX_meas hX_L2 ω) = 0 := by
      intro ω
      simp only [hf_zero, integral_zero]

    -- Show alpha = 0 a.e. from L¹ convergence
    -- When f = 0, Cesàro averages are 0, so ∫|0 - alpha| < ε for all ε > 0
    -- This implies ∫|alpha| = 0, hence alpha = 0 a.e.
    have h_alpha_zero_ae : alpha =ᵐ[μ] 0 := by
      -- The Cesàro sum is 0 when f = 0
      have h_cesaro_zero : ∀ (n : ℕ) (m : ℕ) ω,
          (1/(m:ℝ)) * ∑ k : Fin m, f (X (n + k.val + 1) ω) = 0 := by
        intro n m ω
        simp only [hf_zero, Finset.sum_const_zero, mul_zero]
      -- From hα_conv with n = 0, ε = 1/k: ∫|0 - alpha| < 1/k for large m
      -- Taking limit: ∫|alpha| ≤ 0, so ∫|alpha| = 0
      have h_int_abs_alpha_eq_zero : ∫ ω, |alpha ω| ∂μ = 0 := by
        apply le_antisymm _ (integral_nonneg (fun _ => abs_nonneg _))
        -- For any ε > 0, ∫|alpha| < ε (using hα_conv with cesaro = 0)
        by_contra h_pos
        push_neg at h_pos
        have hε : (0 : ℝ) < ∫ ω, |alpha ω| ∂μ := h_pos
        obtain ⟨M_idx, hM_idx⟩ := hα_conv 0 (∫ ω, |alpha ω| ∂μ) hε
        specialize hM_idx M_idx (le_refl _)
        have h_simp : ∀ ω', |(1 / (M_idx : ℝ)) * ∑ k : Fin M_idx, f (X (0 + k.val + 1) ω') - alpha ω'|
            = |alpha ω'| := by
          intro ω'
          rw [h_cesaro_zero 0 M_idx ω', zero_sub, abs_neg]
        simp_rw [h_simp] at hM_idx
        linarith
      -- ∫|alpha| = 0 implies alpha = 0 a.e.
      -- Use: integral_eq_zero_iff_of_nonneg_ae
      have h_abs_nonneg : (0 : Ω → ℝ) ≤ᵐ[μ] (fun ω => |alpha ω|) :=
        ae_of_all μ (fun ω => abs_nonneg (alpha ω))
      have h_abs_int : Integrable (fun ω => |alpha ω|) μ :=
        (memLp_one_iff_integrable.mp hα_L1).norm
      rw [integral_eq_zero_iff_of_nonneg_ae h_abs_nonneg h_abs_int] at h_int_abs_alpha_eq_zero
      exact h_int_abs_alpha_eq_zero.mono (fun ω hω => abs_eq_zero.mp hω)

    -- Combine: alpha = 0 = ∫f dν a.e.
    filter_upwards [h_alpha_zero_ae] with ω hω
    simp only [hω, h_integral_zero ω, Pi.zero_apply]

  · -- M > 0 case
    have hM_pos : 0 < M := lt_of_le_of_ne (abs_nonneg (f 0) |>.trans (hM 0)) (Ne.symm hM_zero)

    -- Rescale f to g = f/M so |g| ≤ 1
    let g : ℝ → ℝ := fun x => f x / M
    have hg_meas : Measurable g := hf_meas.div_const M
    have hg_bdd : ∀ x, |g x| ≤ 1 := fun x => by
      simp only [g, abs_div]
      have hM_abs : |M| = M := abs_of_pos hM_pos
      rw [hM_abs]
      calc |f x| / M ≤ M / M := div_le_div_of_nonneg_right (hM x) (le_of_lt hM_pos)
        _ = 1 := div_self (ne_of_gt hM_pos)

    -- Apply cesaro_to_condexp_L2 to g
    obtain ⟨α_g, hα_g_L2, hα_g_tail, hα_g_conv, hα_g_eq⟩ :=
      cesaro_to_condexp_L2 hX_contract hX_meas g hg_meas hg_bdd

    -- α_g = E[g(X₀)|tail] = E[(f/M)(X₀)|tail] = (1/M) * E[f(X₀)|tail]
    -- So: E[f(X₀)|tail] = M * α_g

    -- Chain:
    -- 1. alpha =ᵐ M * α_g  (by uniqueness of limits for f = M * g)
    -- 2. M * α_g =ᵐ M * E[g(X₀)|tail] = E[f(X₀)|tail]  (by linearity of condExp)
    -- 3. E[f(X₀)|tail] =ᵐ ∫f dν  (by directing_measure_integral_eq_condExp)

    -- Bridge lemma: E[f(X₀)|tail] =ᵐ ∫f dν
    have h_bridge : (fun ω => ∫ x, f x ∂(directing_measure X hX_contract hX_meas hX_L2 ω))
        =ᵐ[μ] μ[fun ω => f (X 0 ω) | TailSigma.tailSigma X] :=
      directing_measure_integral_eq_condExp X hX_contract hX_meas hX_L2 f hf_meas ⟨M, hM⟩

    -- ═══════════════════════════════════════════════════════════════════════════════
    -- KEY STEP: alpha =ᵐ E[f(X₀)|tail] via L¹ uniqueness
    -- ═══════════════════════════════════════════════════════════════════════════════
    --
    -- The identification chain connects three quantities a.e.:
    --   alpha = E[f(X₀)|tail] = ∫f dν
    --
    -- Direct approach: Both alpha and E[f|tail] are L¹ limits of shifted f-averages.
    -- - alpha → from hα_conv (L¹ limit of shifted f-averages at indices n+1,...,n+m)
    -- - E[f(X₀)|tail] → from cesaro_convergence_all_shifts (same averages)
    -- By L¹ uniqueness, alpha =ᵐ E[f(X₀)|tail].
    --
    -- Note: We use the rescaled function g = f/M with |g| ≤ 1 since
    -- cesaro_convergence_all_shifts requires the bound |g| ≤ 1.
    -- Then we scale back: M * (g-averages) = f-averages.

    -- Step 1: Show alpha =ᵐ E[f(X₀)|tail] using L¹ uniqueness directly
    -- Both limits are a.e. equal to the unique L¹ limit of shifted f-averages
    have h_alpha_eq_condExp : alpha =ᵐ[μ] μ[f ∘ X 0 | TailSigma.tailSigma X] := by
      -- PROOF: Use condExp_smul and the identification from cesaro_to_condexp_L2
      --
      -- We have from cesaro_to_condexp_L2:
      --   α_g =ᵐ μ[g ∘ X 0 | tail]    where g = f/M
      --
      -- By condExp_smul: μ[M • (g ∘ X 0) | tail] = M • μ[g ∘ X 0 | tail]
      -- Since f = M * g: μ[f ∘ X 0 | tail] = M * μ[g ∘ X 0 | tail] =ᵐ M * α_g
      --
      -- The L¹ uniqueness argument:
      -- - f-averages = M * g-averages (algebra)
      -- - g-averages → α_g in L² (from cesaro_to_condexp_L2, via L² convergence)
      -- - L² convergence ⟹ L¹ convergence on probability spaces
      -- - So M * g-averages = f-averages → M * α_g in L¹
      -- - But hα_conv says f-averages → alpha in L¹
      -- - By uniqueness of L¹ limits: alpha =ᵐ M * α_g
      --
      -- Conclusion: alpha =ᵐ M * α_g =ᵐ M * μ[g ∘ X 0 | tail] = μ[f ∘ X 0 | tail]

      -- Step 1a: Show μ[f ∘ X 0 | tail] = M * μ[g ∘ X 0 | tail]
      have hm_le := TailSigma.tailSigma_le X hX_meas
      have h_condExp_f_eq : μ[f ∘ X 0 | TailSigma.tailSigma X]
          =ᵐ[μ] fun ω => M * μ[g ∘ X 0 | TailSigma.tailSigma X] ω := by
        -- f x = M * g x (since g x = f x / M and M > 0)
        have h_f_eq_Mg : ∀ x, f x = M * g x := fun x => by
          simp only [g]
          field_simp [ne_of_gt hM_pos]
        -- f ∘ X 0 = (M • g) ∘ X 0 (pointwise)
        have h_comp_eq : (f ∘ X 0) = fun ω => M * g (X 0 ω) := by
          ext ω
          simp only [Function.comp_apply, h_f_eq_Mg]
        -- Use condExp linearity: E[M * h | m] = M * E[h | m]
        have h_ae : μ[fun ω => M * g (X 0 ω) | TailSigma.tailSigma X]
            =ᵐ[μ] fun ω => M * μ[g ∘ X 0 | TailSigma.tailSigma X] ω := by
          -- Use condExp_smul with appropriate coercions
          have h_smul := condExp_smul M (g ∘ X 0) (m := TailSigma.tailSigma X) (μ := μ)
          simp only [smul_eq_mul, Pi.smul_apply] at h_smul
          convert h_smul using 2 <;> ext ω <;> ring
        calc μ[f ∘ X 0 | TailSigma.tailSigma X]
            = μ[fun ω => M * g (X 0 ω) | TailSigma.tailSigma X] := by rw [h_comp_eq]
          _ =ᵐ[μ] fun ω => M * μ[g ∘ X 0 | TailSigma.tailSigma X] ω := h_ae

      -- Step 1b: Show alpha =ᵐ M * α_g by L¹ uniqueness
      -- Both are L¹ limits of f-averages (which equal M * g-averages)
      have h_alpha_eq_M_alpha_g : alpha =ᵐ[μ] fun ω => M * α_g ω := by
        -- Strategy: Both alpha and M * α_g are L¹ limits of the same sequence:
        --   A m ω := m⁻¹ * ∑ k : Fin m, f (X (k.val + 1) ω)
        -- The indices match:
        --   - hα_conv 0: uses X (0 + k.val + 1) = X (k.val + 1), indices 1, 2, ..., m
        --   - cesaro_convergence_all_shifts with n=1: uses X (1+k), indices 1, 2, ..., m
        -- By L¹ uniqueness, alpha =ᵐ M * α_g.

        -- Define the averaging sequence with matching indices
        let A : ℕ → Ω → ℝ := fun m ω => (1/(m:ℝ)) * ∑ k : Fin m, f (X (k.val + 1) ω)

        -- From hα_conv 0: A → alpha in L¹
        have hA_to_alpha : ∀ ε > 0, ∃ M_idx : ℕ, ∀ m ≥ M_idx,
            ∫ ω, |A m ω - alpha ω| ∂μ < ε := by
          intro ε hε
          obtain ⟨M_idx, hM_idx⟩ := hα_conv 0 ε hε
          use M_idx
          intro m hm
          convert hM_idx m hm using 2
          ext ω
          simp only [A, zero_add]

        -- From cesaro_convergence_all_shifts with n=1: g-averages → E[g∘X 0|tail] in L¹
        have hg_cesaro : ∀ ε > 0, ∃ M_idx : ℕ, ∀ m ≥ M_idx,
            ∫ ω, |(1/(m:ℝ)) * ∑ k : Fin m, g (X (1+k) ω) -
                 μ[g ∘ X 0 | TailSigma.tailSigma X] ω| ∂μ < ε := by
          intro ε hε
          exact cesaro_convergence_all_shifts X hX_contract hX_meas g hg_meas hg_bdd 1 ε hε

        -- Reindex: X(1+k) = X(k.val+1) for k : Fin m
        have hg_cesaro' : ∀ ε > 0, ∃ M_idx : ℕ, ∀ m ≥ M_idx,
            ∫ ω, |(1/(m:ℝ)) * ∑ k : Fin m, g (X (k.val+1) ω) -
                 μ[g ∘ X 0 | TailSigma.tailSigma X] ω| ∂μ < ε := by
          intro ε hε
          obtain ⟨M_idx, hM_idx⟩ := hg_cesaro ε hε
          use M_idx
          intro m hm
          convert hM_idx m hm using 3
          simp only [add_comm (1:ℕ)]

        -- Since α_g =ᵐ E[g∘X 0|tail], we have ∫ |α_g - E[g∘X 0|tail]| = 0
        have hα_g_diff_zero : ∫ ω, |α_g ω - μ[g ∘ X 0 | TailSigma.tailSigma X] ω| ∂μ = 0 := by
          have h_ae := hα_g_eq
          rw [integral_eq_zero_iff_of_nonneg_ae (ae_of_all μ (fun _ => abs_nonneg _))]
          · filter_upwards [h_ae] with ω hω
            simp only [hω, sub_self, abs_zero, Pi.zero_apply]
          · -- Integrability: α_g - condExp is in L¹
            have hα_g_int : Integrable α_g μ := hα_g_L2.integrable one_le_two
            have hcond_int : Integrable (μ[g ∘ X 0 | TailSigma.tailSigma X]) μ :=
              integrable_condExp
            exact (hα_g_int.sub hcond_int).norm

        -- Triangle inequality: g-averages → α_g in L¹
        have hg_to_alpha_g : ∀ ε > 0, ∃ M_idx : ℕ, ∀ m ≥ M_idx,
            ∫ ω, |(1/(m:ℝ)) * ∑ k : Fin m, g (X (k.val+1) ω) - α_g ω| ∂μ < ε := by
          intro ε hε
          obtain ⟨M_idx, hM_idx⟩ := hg_cesaro' ε hε
          use M_idx
          intro m hm
          calc ∫ ω, |(1/(m:ℝ)) * ∑ k : Fin m, g (X (k.val+1) ω) - α_g ω| ∂μ
              ≤ ∫ ω, (|(1/(m:ℝ)) * ∑ k : Fin m, g (X (k.val+1) ω) -
                      μ[g ∘ X 0 | TailSigma.tailSigma X] ω| +
                     |μ[g ∘ X 0 | TailSigma.tailSigma X] ω - α_g ω|) ∂μ := by
                  apply integral_mono_of_nonneg (ae_of_all μ (fun _ => abs_nonneg _))
                  · apply Integrable.add
                    · have hg_avg_meas : Measurable (fun ω => (1/(m:ℝ)) * ∑ k : Fin m, g (X (k.val+1) ω)) := by
                        apply Measurable.const_mul
                        apply Finset.measurable_sum
                        intro k _
                        exact hg_meas.comp (hX_meas (k.val + 1))
                      have hg_avg_bdd : ∀ ω, |(1/(m:ℝ)) * ∑ k : Fin m, g (X (k.val+1) ω)| ≤ 1 := by
                        intro ω
                        by_cases hm : m = 0
                        · simp [hm]
                        · calc |(1/(m:ℝ)) * ∑ k : Fin m, g (X (k.val+1) ω)|
                              ≤ (m:ℝ)⁻¹ * ∑ k : Fin m, |g (X (k.val+1) ω)| := by
                                rw [one_div, abs_mul, abs_of_pos (by positivity : (m:ℝ)⁻¹ > 0)]
                                gcongr; exact Finset.abs_sum_le_sum_abs _ _
                            _ ≤ (m:ℝ)⁻¹ * ∑ k : Fin m, (1:ℝ) := by
                                gcongr with k _; exact hg_bdd _
                            _ = 1 := by simp [Finset.sum_const, Finset.card_fin]; field_simp [hm]
                      have hg_avg_bdd' : ∀ᵐ ω ∂μ, ‖(1/(m:ℝ)) * ∑ k : Fin m, g (X (k.val+1) ω)‖ ≤ 1 := by
                        apply ae_of_all μ
                        intro ω
                        rw [Real.norm_eq_abs]
                        exact hg_avg_bdd ω
                      refine (Integrable.of_bound hg_avg_meas.aestronglyMeasurable 1 hg_avg_bdd').sub integrable_condExp |>.norm
                    · refine (integrable_condExp.sub (hα_g_L2.integrable one_le_two)).norm
                  · apply ae_of_all μ
                    intro ω
                    calc |(1/(m:ℝ)) * ∑ k : Fin m, g (X (k.val+1) ω) - α_g ω|
                        = |((1/(m:ℝ)) * ∑ k : Fin m, g (X (k.val+1) ω) -
                            μ[g ∘ X 0 | TailSigma.tailSigma X] ω) +
                           (μ[g ∘ X 0 | TailSigma.tailSigma X] ω - α_g ω)| := by ring_nf
                      _ ≤ _ := abs_add_le _ _
            _ = ∫ ω, |(1/(m:ℝ)) * ∑ k : Fin m, g (X (k.val+1) ω) -
                      μ[g ∘ X 0 | TailSigma.tailSigma X] ω| ∂μ +
                ∫ ω, |μ[g ∘ X 0 | TailSigma.tailSigma X] ω - α_g ω| ∂μ := by
                  apply integral_add
                  · have hg_avg_meas : Measurable (fun ω => (1/(m:ℝ)) * ∑ k : Fin m, g (X (k.val+1) ω)) := by
                      apply Measurable.const_mul
                      apply Finset.measurable_sum
                      intro k _
                      exact hg_meas.comp (hX_meas (k.val + 1))
                    have hg_avg_bdd : ∀ ω, |(1/(m:ℝ)) * ∑ k : Fin m, g (X (k.val+1) ω)| ≤ 1 := by
                      intro ω
                      by_cases hm : m = 0
                      · simp [hm]
                      · calc |(1/(m:ℝ)) * ∑ k : Fin m, g (X (k.val+1) ω)|
                            ≤ (m:ℝ)⁻¹ * ∑ k : Fin m, |g (X (k.val+1) ω)| := by
                              rw [one_div, abs_mul, abs_of_pos (by positivity : (m:ℝ)⁻¹ > 0)]
                              gcongr; exact Finset.abs_sum_le_sum_abs _ _
                          _ ≤ (m:ℝ)⁻¹ * ∑ k : Fin m, (1:ℝ) := by
                              gcongr with k _; exact hg_bdd _
                          _ = 1 := by simp [Finset.sum_const, Finset.card_fin]; field_simp [hm]
                    have hg_avg_bdd' : ∀ᵐ ω ∂μ, ‖(1/(m:ℝ)) * ∑ k : Fin m, g (X (k.val+1) ω)‖ ≤ 1 := by
                      apply ae_of_all μ
                      intro ω
                      rw [Real.norm_eq_abs]
                      exact hg_avg_bdd ω
                    exact (Integrable.of_bound hg_avg_meas.aestronglyMeasurable 1 hg_avg_bdd').sub integrable_condExp |>.norm
                  · exact (integrable_condExp.sub (hα_g_L2.integrable one_le_two)).norm
            _ = ∫ ω, |(1/(m:ℝ)) * ∑ k : Fin m, g (X (k.val+1) ω) -
                      μ[g ∘ X 0 | TailSigma.tailSigma X] ω| ∂μ + 0 := by
                  congr 1
                  convert hα_g_diff_zero using 2
                  ext ω
                  rw [abs_sub_comm]
            _ < ε := by simp only [add_zero]; exact hM_idx m hm

        -- Scaling: f-averages = M * g-averages
        have hfg_scaling : ∀ m ω, A m ω = M * ((1/(m:ℝ)) * ∑ k : Fin m, g (X (k.val+1) ω)) := by
          intro m ω
          simp only [A, g]
          by_cases hm : m = 0
          · simp [hm]
          · have hM_ne : M ≠ 0 := ne_of_gt hM_pos
            have hm_ne : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
            -- LHS: 1/m * ∑ f(...)
            -- RHS: M * (1/m * ∑ (f(...)/M)) = 1/m * ∑ f(...)
            -- Direct algebra: M * (1/m * ∑ (f/M)) = 1/m * ∑ f
            have h_sum_eq : ∑ k : Fin m, f (X (k.val+1) ω) / M = (∑ k : Fin m, f (X (k.val+1) ω)) / M := by
              rw [Finset.sum_div]
            rw [h_sum_eq]
            field_simp [hM_ne, hm_ne]

        -- Therefore: A → M * α_g in L¹
        have hA_to_M_alpha_g : ∀ ε > 0, ∃ M_idx : ℕ, ∀ m ≥ M_idx,
            ∫ ω, |A m ω - M * α_g ω| ∂μ < ε := by
          intro ε hε
          have hε' : 0 < ε / (|M| + 1) := by positivity
          obtain ⟨M_idx, hM_idx⟩ := hg_to_alpha_g (ε / (|M| + 1)) hε'
          use M_idx
          intro m hm
          calc ∫ ω, |A m ω - M * α_g ω| ∂μ
              = ∫ ω, |M * ((1/(m:ℝ)) * ∑ k : Fin m, g (X (k.val+1) ω)) - M * α_g ω| ∂μ := by
                  congr 1; ext ω; rw [hfg_scaling]
            _ = ∫ ω, |M| * |(1/(m:ℝ)) * ∑ k : Fin m, g (X (k.val+1) ω) - α_g ω| ∂μ := by
                  congr 1; ext ω; rw [← mul_sub, abs_mul]
            _ = |M| * ∫ ω, |(1/(m:ℝ)) * ∑ k : Fin m, g (X (k.val+1) ω) - α_g ω| ∂μ := by
                  rw [integral_mul_left]
            _ < |M| * (ε / (|M| + 1)) := by
                  gcongr; exact hM_idx m hm
            _ < (|M| + 1) * (ε / (|M| + 1)) := by
                  gcongr; linarith
            _ = ε := by field_simp

        -- Convert to TendstoInMeasure and apply uniqueness
        -- Both A → alpha and A → M * α_g in L¹

        -- First convert L¹ convergence to eLpNorm convergence
        have hA_meas : ∀ m, Measurable (A m) := fun m => by
          apply Measurable.const_mul
          apply Finset.measurable_sum
          intro k _
          exact hf_meas.comp (hX_meas (k.val + 1))

        have hA_bdd : ∀ m ω, |A m ω| ≤ M := fun m ω => by
          simp only [A]
          by_cases hm : m = 0
          · simp [hm]; exact abs_nonneg _ |>.trans (hM 0)
          · calc |(1/(m:ℝ)) * ∑ k : Fin m, f (X (k.val+1) ω)|
                ≤ (m:ℝ)⁻¹ * ∑ k : Fin m, |f (X (k.val+1) ω)| := by
                    rw [one_div, abs_mul, abs_of_pos (by positivity : (m:ℝ)⁻¹ > 0)]
                    gcongr; exact Finset.abs_sum_le_sum_abs _ _
              _ ≤ (m:ℝ)⁻¹ * ∑ k : Fin m, M := by
                    gcongr with k _; exact hM _
              _ = M := by simp [Finset.sum_const, Finset.card_fin]; field_simp [hm]

        have hAalpha_integrable : ∀ m, Integrable (fun ω => A m ω - alpha ω) μ := fun m =>
          (Integrable.of_bound (hA_meas m).aestronglyMeasurable M (ae_of_all μ (hA_bdd m))).sub
            (hα_L1.integrable le_rfl)

        have hAMalpha_g_integrable : ∀ m, Integrable (fun ω => A m ω - M * α_g ω) μ := fun m =>
          (Integrable.of_bound (hA_meas m).aestronglyMeasurable M (ae_of_all μ (hA_bdd m))).sub
            ((hα_g_L2.integrable one_le_two).const_mul M)

        have hA_tendsto_alpha : Tendsto (fun m => ∫ ω, |A m ω - alpha ω| ∂μ) atTop (𝓝 0) := by
          rw [Metric.tendsto_atTop]
          intro ε hε
          obtain ⟨M_idx, hM_idx⟩ := hA_to_alpha ε hε
          use M_idx
          intro m hm
          rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg (fun ω => abs_nonneg _))]
          exact hM_idx m hm

        have hA_tendsto_M_alpha_g : Tendsto (fun m => ∫ ω, |A m ω - M * α_g ω| ∂μ) atTop (𝓝 0) := by
          rw [Metric.tendsto_atTop]
          intro ε hε
          obtain ⟨M_idx, hM_idx⟩ := hA_to_M_alpha_g ε hε
          use M_idx
          intro m hm
          rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg (fun ω => abs_nonneg _))]
          exact hM_idx m hm

        have halpha_eLpNorm : Tendsto (fun m => eLpNorm (fun ω => A m ω - alpha ω) 1 μ) atTop (𝓝 0) := by
          rw [ENNReal.tendsto_nhds_zero]
          intro ε hε
          rw [Metric.tendsto_atTop] at hA_tendsto_alpha
          by_cases h_top : ε = ⊤
          · simp [h_top]
          · have ε_pos : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' h_top
            obtain ⟨M_idx, hM_idx⟩ := hA_tendsto_alpha ε.toReal ε_pos
            refine Filter.eventually_atTop.mpr ⟨M_idx, fun m hm => ?_⟩
            rw [Exchangeability.Probability.IntegrationHelpers.eLpNorm_one_eq_integral_abs (hAalpha_integrable m)]
            rw [← ENNReal.ofReal_toReal h_top]
            rw [ENNReal.ofReal_le_ofReal_iff ε_pos.le]
            have := hM_idx m hm
            rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg (fun ω => abs_nonneg _))] at this
            exact this.le

        have hM_alpha_g_eLpNorm : Tendsto (fun m => eLpNorm (fun ω => A m ω - M * α_g ω) 1 μ) atTop (𝓝 0) := by
          rw [ENNReal.tendsto_nhds_zero]
          intro ε hε
          rw [Metric.tendsto_atTop] at hA_tendsto_M_alpha_g
          by_cases h_top : ε = ⊤
          · simp [h_top]
          · have ε_pos : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' h_top
            obtain ⟨M_idx, hM_idx⟩ := hA_tendsto_M_alpha_g ε.toReal ε_pos
            refine Filter.eventually_atTop.mpr ⟨M_idx, fun m hm => ?_⟩
            rw [Exchangeability.Probability.IntegrationHelpers.eLpNorm_one_eq_integral_abs (hAMalpha_g_integrable m)]
            rw [← ENNReal.ofReal_toReal h_top]
            rw [ENNReal.ofReal_le_ofReal_iff ε_pos.le]
            have := hM_idx m hm
            rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg (fun ω => abs_nonneg _))] at this
            exact this.le

        -- Convert to TendstoInMeasure
        have halpha_meas_conv : TendstoInMeasure μ A atTop alpha := by
          apply tendstoInMeasure_of_tendsto_eLpNorm (p := 1) one_ne_zero
          · intro m; exact (hA_meas m).aestronglyMeasurable
          · exact hα_meas.aestronglyMeasurable
          · exact halpha_eLpNorm

        have hM_alpha_g_meas_conv : TendstoInMeasure μ A atTop (fun ω => M * α_g ω) := by
          apply tendstoInMeasure_of_tendsto_eLpNorm (p := 1) one_ne_zero
          · intro m; exact (hA_meas m).aestronglyMeasurable
          · exact aestronglyMeasurable_const.mul hα_g_L2.aestronglyMeasurable
          · exact hM_alpha_g_eLpNorm

        -- Apply uniqueness
        exact tendstoInMeasure_ae_unique halpha_meas_conv hM_alpha_g_meas_conv

      -- Step 1c: Combine: alpha =ᵐ M * α_g =ᵐ M * μ[g|tail] = μ[f|tail]
      calc alpha =ᵐ[μ] fun ω => M * α_g ω := h_alpha_eq_M_alpha_g
        _ =ᵐ[μ] fun ω => M * μ[g ∘ X 0 | TailSigma.tailSigma X] ω := by
            filter_upwards [hα_g_eq] with ω hω
            simp only [hω]
        _ =ᵐ[μ] μ[f ∘ X 0 | TailSigma.tailSigma X] := h_condExp_f_eq.symm

    -- Step 2: Combine with bridge lemma: alpha =ᵐ ∫f dν
    exact h_alpha_eq_condExp.trans h_bridge.symm

end Exchangeability.DeFinetti.ViaL2
