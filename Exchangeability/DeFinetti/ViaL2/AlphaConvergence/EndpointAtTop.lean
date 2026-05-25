/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Exchangeability.DeFinetti.ViaL2.AlphaIicCE
import Exchangeability.DeFinetti.ViaL2.CesaroConvergence.L1
import Exchangeability.DeFinetti.ViaL2.AlphaConvergence.EndpointCommon

/-!
# Endpoint limit at +∞ for `alphaIicCE`

L¹ and almost-everywhere pointwise convergence of `alphaIicCE` to 1 as `t → +∞`.

## Main result

* `alphaIicCE_ae_tendsto_one_atTop`: For a.e. ω, `alphaIicCE X _ t ω → 1` as `t → +∞`.

The L¹ stepping stone `alphaIicCE_L1_tendsto_one_atTop` is private to this file.

## References

* Kallenberg (2005), *Probabilistic Symmetries and Invariance Principles*,
  Chapter 1, "Second proof of Theorem 1.1"
-/

noncomputable section

namespace Exchangeability.DeFinetti.ViaL2

open MeasureTheory ProbabilityTheory BigOperators Filter Topology
open Exchangeability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- **L¹ endpoint limit at +∞**: As t → +∞, alphaIicCE → 1 in L¹.

**Proof strategy:**
Similar to the -∞ case, but `1_{(-∞,t]}(X_0 ω)` → 1 as t → +∞. -/
private lemma alphaIicCE_L1_tendsto_one_atTop
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ) :
    Tendsto (fun n : ℕ =>
      ∫ ω, |alphaIicCE X hX_contract hX_meas hX_L2 (n : ℝ) ω - 1| ∂μ)
      atTop (𝓝 0) := by
  -- Strategy: Similar to atBot case, but now (indIic (n:ℝ)) → 1 pointwise
  -- So ∫ |(indIic (n:ℝ)) ∘ X 0 - 1| → 0

  -- Set up the tail σ-algebra Fact instance (needed for condExp)
  have hm_le : Exchangeability.Tail.tailProcess X ≤ (inferInstance : MeasurableSpace Ω) :=
    Exchangeability.Tail.tailProcess_le_ambient X hX_meas
  haveI : Fact (Exchangeability.Tail.tailProcess X ≤ (inferInstance : MeasurableSpace Ω)) := ⟨hm_le⟩

  -- Step 1: Show ∫ |(indIic (n:ℝ)) ∘ X 0 - 1| → 0
  -- Integral of |indicator - 1| = μ(X 0 > n) → 0 by continuity
  have h_indicator_tendsto : Tendsto (fun n : ℕ =>
      ∫ ω, |(indIic (n : ℝ)) (X 0 ω) - 1| ∂μ) atTop (𝓝 0) := by
    -- |indIic n - 1| = indicator of (n, ∞) since indIic n = indicator of (-∞, n]
    have h_eq : ∀ n : ℕ, ∫ ω, |(indIic (n : ℝ)) (X 0 ω) - 1| ∂μ
        = (μ (X 0 ⁻¹' Set.Ioi (n : ℝ))).toReal := by
      intro n
      have : (fun ω => |(indIic (n : ℝ)) (X 0 ω) - 1|)
          = (Set.Ioi (n : ℝ)).indicator (fun _ => (1 : ℝ)) ∘ (X 0) := by
        ext ω
        simp only [indIic, Set.indicator, Function.comp_apply, Set.mem_Ioi, Set.mem_Iic]
        split_ifs with h1 h2
        · -- X 0 ω ≤ n and X 0 ω > n: contradiction
          linarith
        · -- X 0 ω ≤ n and ¬(X 0 ω > n): both give 0
          norm_num
        · -- ¬(X 0 ω ≤ n) and X 0 ω > n: both give 1
          norm_num
        · -- ¬(X 0 ω ≤ n) and ¬(X 0 ω > n): contradiction
          linarith
      rw [this]
      -- Rewrite composition as indicator on preimage
      have h_comp : (Set.Ioi (n : ℝ)).indicator (fun _ => (1 : ℝ)) ∘ (X 0)
          = (X 0 ⁻¹' Set.Ioi (n : ℝ)).indicator (fun _ => (1 : ℝ)) := by
        ext ω
        simp only [Function.comp_apply, Set.indicator_apply]
        rfl
      rw [h_comp, integral_indicator (measurableSet_preimage (hX_meas 0) measurableSet_Ioi),
          setIntegral_one_eq_measureReal]
      rfl
    simp only [h_eq]
    -- The sets {X 0 > n} decrease to empty
    have h_antitone : Antitone (fun n : ℕ => X 0 ⁻¹' Set.Ioi (n : ℝ)) := by
      intro n m hnm
      apply Set.preimage_mono
      intro x hx
      simp only [Set.mem_Ioi] at hx ⊢
      calc x > (m : ℝ) := hx
           _ ≥ (n : ℝ) := by simp [Nat.cast_le, hnm]
    have h_empty : (⋂ (n : ℕ), X 0 ⁻¹' Set.Ioi (n : ℝ)) = ∅ := by
      ext ω
      simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_Ioi, Set.mem_empty_iff_false, iff_false]
      intro h
      -- For all n, X 0 ω > n, impossible by Archimedean property
      obtain ⟨n, hn⟩ := exists_nat_gt (X 0 ω)
      have h1 : X 0 ω > (n : ℝ) := h n
      linarith
    have h_meas : ∀ (n : ℕ), NullMeasurableSet (X 0 ⁻¹' Set.Ioi (n : ℝ)) μ := fun n =>
      (measurableSet_preimage (hX_meas 0) measurableSet_Ioi).nullMeasurableSet
    have h_fin : ∃ (n : ℕ), μ (X 0 ⁻¹' Set.Ioi (n : ℝ)) ≠ ⊤ := by
      use 0
      exact measure_ne_top μ _
    have h_tendsto_ennreal : Tendsto (fun (n : ℕ) => μ (X 0 ⁻¹' Set.Ioi (n : ℝ))) atTop (𝓝 0) := by
      simpa [h_empty, Function.comp] using
        tendsto_measure_iInter_atTop (μ := μ) h_meas h_antitone h_fin
    -- Convert from ENNReal to Real using continuity of toReal at 0
    simpa using
      (ENNReal.continuousAt_toReal (by norm_num : (0 : ENNReal) ≠ ⊤)).tendsto.comp h_tendsto_ennreal

  -- Step 2: L¹ contraction — apply the central `condExp_L1_lipschitz` with
  -- `f = indIic n ∘ X 0`, `g = (fun _ => 1)`. The constant on the RHS lands inside
  -- `condExp` and is rewritten back to `1` via `condExp_const`.
  have h_contraction : ∀ n : ℕ,
      ∫ ω, |alphaIicCE X hX_contract hX_meas hX_L2 (n : ℝ) ω - 1| ∂μ
      ≤ ∫ ω, |(indIic (n : ℝ)) (X 0 ω) - 1| ∂μ := by
    intro n
    have h_int : Integrable ((indIic (n : ℝ)) ∘ (X 0)) μ :=
      Exchangeability.Probability.integrable_indicator_comp (hX_meas 0) measurableSet_Iic
    have h_const : μ[(fun _ : Ω => (1 : ℝ)) | Exchangeability.Tail.tailProcess X] =ᵐ[μ] (fun _ : Ω => (1 : ℝ)) :=
      (condExp_const (μ := μ) (m := Exchangeability.Tail.tailProcess X) hm_le (1 : ℝ)).eventuallyEq
    have h_ae_abs : (fun ω => |alphaIicCE X hX_contract hX_meas hX_L2 (n : ℝ) ω - 1|)
        =ᵐ[μ] (fun ω => |μ[((indIic (n : ℝ)) ∘ (X 0)) | Exchangeability.Tail.tailProcess X] ω
                         - μ[(fun _ : Ω => (1 : ℝ)) | Exchangeability.Tail.tailProcess X] ω|) := by
      filter_upwards [h_const] with ω hω
      show |alphaIicCE X hX_contract hX_meas hX_L2 (n : ℝ) ω - 1| =
        |μ[((indIic (n : ℝ)) ∘ (X 0)) | Exchangeability.Tail.tailProcess X] ω
         - μ[(fun _ : Ω => (1 : ℝ)) | Exchangeability.Tail.tailProcess X] ω|
      rw [hω]; rfl
    rw [integral_congr_ae h_ae_abs]
    exact Exchangeability.Probability.condExp_L1_lipschitz
      (μ := μ) (m := Exchangeability.Tail.tailProcess X) h_int (integrable_const 1)

  -- Apply squeeze theorem: 0 ≤ ‖alphaIicCE - 1‖₁ ≤ ‖indicator - 1‖₁ → 0
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h_indicator_tendsto
    (fun _ => integral_nonneg (fun _ => abs_nonneg _)) h_contraction

/-- **A.e. pointwise endpoint limit at +∞**.

**Proof strategy:**
Similar to the -∞ case, using monotonicity + boundedness + L¹ → 1. -/
lemma alphaIicCE_ae_tendsto_one_atTop
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ =>
      alphaIicCE X hX_contract hX_meas hX_L2 (n : ℝ) ω)
      atTop (𝓝 1) := by
  -- Strategy: the sequence is monotone increasing and bounded in [0,1], so it
  -- converges pointwise a.e. to its supremum `U ω`. The L¹ limit (from
  -- `alphaIicCE_L1_tendsto_one_atTop`) is `1`, so the shared helper
  -- `ae_tendsto_const_of_ae_convergent_of_L1_const` identifies `U ω = 1` a.e.
  set f : ℕ → Ω → ℝ := fun n ω => alphaIicCE X hX_contract hX_meas hX_L2 (n : ℝ) ω
    with hf_def
  set U : Ω → ℝ := fun ω => ⨆ (n : ℕ), f n ω with hU_def
  have hm_le : Exchangeability.Tail.tailProcess X ≤ (inferInstance : MeasurableSpace Ω) :=
    Exchangeability.Tail.tailProcess_le_ambient X hX_meas
  -- (1) Each f n is AEStronglyMeasurable (conditional expectation).
  have hf_meas : ∀ n, AEStronglyMeasurable (f n) μ := fun n => by
    show AEStronglyMeasurable (alphaIicCE X hX_contract hX_meas hX_L2 (n : ℝ)) μ
    unfold alphaIicCE
    exact stronglyMeasurable_condExp.aestronglyMeasurable.mono hm_le
  -- (2) Uniform bound ‖f n ω‖ ≤ 1.
  have hf_bound : ∀ n, ∀ᵐ ω ∂μ, ‖f n ω‖ ≤ (1 : ℝ) := fun n => by
    filter_upwards [alphaIicCE_nonneg_le_one X hX_contract hX_meas hX_L2 (n : ℝ)] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg hω.1]; exact hω.2
  -- (3) Pointwise a.e. convergence to U = ⨆ n, f n ·.
  have hf_ae : ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop (𝓝 (U ω)) := by
    have h_monotone : ∀ᵐ ω ∂μ, ∀ n m : ℕ, n ≤ m → f n ω ≤ f m ω := by
      rw [ae_all_iff]; intro n; rw [ae_all_iff]; intro m
      by_cases hnm : n ≤ m
      · have h_le : (n : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hnm
        filter_upwards [alphaIicCE_mono X hX_contract hX_meas hX_L2
          (n : ℝ) (m : ℝ) h_le] with ω hω
        intro _; exact hω
      · exact ae_of_all μ (fun _ h_contra => absurd h_contra hnm)
    have h_bound_pt : ∀ᵐ ω ∂μ, ∀ n : ℕ, 0 ≤ f n ω ∧ f n ω ≤ 1 := by
      rw [ae_all_iff]; intro n
      exact alphaIicCE_nonneg_le_one X hX_contract hX_meas hX_L2 (n : ℝ)
    filter_upwards [h_monotone, h_bound_pt] with ω h_mono h_bd
    refine tendsto_atTop_ciSup h_mono ⟨1, ?_⟩
    rintro _ ⟨k, rfl⟩; exact (h_bd k).2
  -- (4) L¹ convergence to 1.
  have hf_L1 : Tendsto (fun n => ∫ ω, |f n ω - 1| ∂μ) atTop (𝓝 0) :=
    alphaIicCE_L1_tendsto_one_atTop X hX_contract hX_meas hX_L2
  -- Apply the shared helper.
  exact ae_tendsto_const_of_ae_convergent_of_L1_const hf_meas hf_bound hf_ae hf_L1


end Exchangeability.DeFinetti.ViaL2
