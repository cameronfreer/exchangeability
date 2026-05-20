/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Exchangeability.DeFinetti.ViaL2.DirectingMeasureCore

/-!
# Directing measure: Iic base case

For each `t : ℝ`, the integral of the indicator of `Iic t` against the directing measure
agrees, almost everywhere in `ω`, with `alphaIicCE X t ω`. This is the Stieltjes-level
identification that the kernel bridge and the bounded-measurable extension both consume.

## Main result

* `directing_measure_integral_Iic_ae_eq_alphaIicCE`: base case for `Iic` indicators.

## References

* Kallenberg (2005), *Probabilistic Symmetries and Invariance Principles*,
  Chapter 1, "Second proof of Theorem 1.1"
-/

noncomputable section

namespace Exchangeability.DeFinetti.ViaL2

open MeasureTheory ProbabilityTheory BigOperators Filter Topology
open Exchangeability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- **Base case:** For Iic indicators, the directing measure integral equals `alphaIicCE`.

Proof outline:
1. Stieltjes construction: `∫ 1_{Iic t} dν(ω) = (ν(Iic t)).toReal`
2. Measure value: `(ν(Iic t)).toReal = stieltjesOfMeasurableRat t`
3. Stieltjes extension: `stieltjesOfMeasurableRat t = alphaIic t` a.e.
4. Identification: `alphaIic t =ᵐ alphaIicCE t`

Both the kernel bridge (`directing_measure_ae_eq_condExpKernel_map`) and the bounded-
measurable extension in `DirectingMeasureIntegral` consume this Iic identification. -/
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
      push Not at h_not
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
      push Not at h_not
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

end Exchangeability.DeFinetti.ViaL2

end
