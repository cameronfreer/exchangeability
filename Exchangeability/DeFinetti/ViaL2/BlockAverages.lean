/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Exchangeability.DeFinetti.L2Helpers
import Exchangeability.Contractability
import Exchangeability.ConditionallyIID
import Exchangeability.Probability.CondExp
import Exchangeability.Probability.IntegrationHelpers
import Exchangeability.Probability.LpNormHelpers
import Exchangeability.Util.FinsetHelpers
-- import Exchangeability.Probability.CesaroHelpers  -- TODO: Fix compilation errors
import Exchangeability.Tail.TailSigma
import Exchangeability.Tail.ShiftInvariance
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.AEEqFun
import Mathlib.MeasureTheory.MeasurableSpace.MeasurablyGenerated
import Mathlib.MeasureTheory.PiSystem
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.Analysis.InnerProductSpace.MeanErgodic
import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.Kernel.Disintegration.CondCDF
import Mathlib.Probability.CDF
import Mathlib.Algebra.Order.Group.MinMax
import Canonical

/-!
# de Finetti's Theorem via L² Contractability

**Kallenberg's "second proof"** of de Finetti's theorem using the elementary
L² contractability bound (Lemma 1.2). This is the **lightest-dependency proof**.

## Proof approach

Starting from a **contractable** sequence ξ:

1. Fix a bounded measurable function f ∈ L¹
2. Use Lemma 1.2 (L² contractability bound) and completeness of L¹:
   - Show ‖E_m ∑_{k=n+1}^{n+m} (f(ξ_{n+k}) - α_{k-1})‖₁² → 0
3. Extract limit α_∞ = lim_n α_n in L¹
4. Show α_n is a reverse martingale (subsequence convergence a.s.)
5. Use contractability + dominated convergence:
   - E[f(ξ_i); ∩I_k] = E[α_{k-1}; ∩I_k] → E[α_∞; ∩I_k]
6. Conclude α_n = E_n f(ξ_{n+1}) = ν^f a.s.
7. Complete using the common ending (monotone class argument)

## Main results

* `deFinetti_viaL2`: **Main theorem** - contractable implies conditionally i.i.d.
* `deFinetti`: **Canonical name** (alias for `deFinetti_viaL2`)

Supporting lemmas:
* `weighted_sums_converge_L1`: L² bound implies L¹ convergence
* `reverse_martingale_limit`: Tail-measurable limit via reverse martingale

## Why this proof is default

✅ **Elementary** - Only uses basic L² space theory and Cauchy-Schwarz
✅ **Direct** - Proves convergence via explicit bounds
✅ **Quantitative** - Gives explicit rates of convergence
✅ **Lightest dependencies** - No ergodic theory required

## References

* Kallenberg (2005), *Probabilistic Symmetries and Invariance Principles*,
  Chapter 1, pages 26-27: "Second proof of Theorem 1.1"

-/

noncomputable section

namespace Exchangeability.DeFinetti.ViaL2

open MeasureTheory ProbabilityTheory BigOperators Filter Topology
open Exchangeability
open Exchangeability.DeFinetti.L2Helpers

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

open scoped BigOperators

/-!
## Step 1: L² bound is the key tool

Covariance and Lp utility lemmas are now in L2Helpers.lean.
-/

/-!
## Step 2: L² bound implies L¹ convergence of weighted sums (Kallenberg's key step)
-/

/-- **Finite window of consecutive indices.**

The window `{n+1, n+2, ..., n+k}` represented as a `Finset ℕ`.
Used to express Cesàro averages: `(1/k) * ∑_{i ∈ window n k} f(X_i)`. -/
def window (n k : ℕ) : Finset ℕ :=
  (Finset.range k).image fun i => n + i + 1

/-- The window contains exactly k elements. -/
lemma window_card (n k : ℕ) : (window n k).card = k := by
  classical
  unfold window
  refine (Finset.card_image_iff.mpr ?_).trans ?_
  · intro a ha b hb h
    have h' : n + a = n + b := by
      apply Nat.succ.inj
      simp only [Nat.succ_eq_add_one] at h ⊢
      omega
    exact Nat.add_left_cancel h'
  · simp only [Finset.card_range]

/-- Characterization of window membership. -/
lemma mem_window_iff {n k t : ℕ} :
    t ∈ window n k ↔ ∃ i : ℕ, i < k ∧ t = n + i + 1 := by
  classical
  unfold window
  constructor
  · intro ht
    rcases Finset.mem_image.mp ht with ⟨i, hi, rfl⟩
    refine ⟨i, ?_, rfl⟩
    simpa using hi
  · intro h
    rcases h with ⟨i, hi, rfl⟩
    refine Finset.mem_image.mpr ?_
    refine ⟨i, ?_, rfl⟩
    simpa using hi

/-- Sum over a window of length `k` can be reindexed as a sum over `Fin k`. -/
lemma sum_window_eq_sum_fin {β : Type*} [AddCommMonoid β]
    (n k : ℕ) (g : ℕ → β) :
    ∑ t ∈ window n k, g t = ∑ i : Fin k, g (n + i.val + 1) := by
  classical
  unfold window
  -- Show the image map used to define the window is injective
  have h_inj :
      ∀ a ∈ Finset.range k, ∀ b ∈ Finset.range k,
        (n + a + 1 = n + b + 1 → a = b) := by
    intro a ha b hb h
    have h' : a + 1 = b + 1 := by
      have : n + (a + 1) = n + (b + 1) := by
        omega
      exact Nat.add_left_cancel this
    exact Nat.succ.inj h'
  -- Convert the window sum to a range sum via the image definition
  have h_sum_range :
      ∑ t ∈ Finset.image (fun i => n + i + 1) (Finset.range k), g t
        = ∑ i ∈ Finset.range k, g (n + i + 1) :=
    Finset.sum_image <| by
      intro a ha b hb h
      exact h_inj a ha b hb h
  -- Replace the range sum with a sum over `Fin k`
  have h_range_to_fin :
      ∑ i ∈ Finset.range k, g (n + i + 1)
        = ∑ i : Fin k, g (n + i.val + 1) := by
    classical
    refine (Finset.sum_bij (fun (i : Fin k) _ => i.val)
        (fun i _ => by
          simp [Finset.mem_range, i.is_lt])
        (fun i hi j hj h => by
          exact Fin.ext h)
        (fun b hb => ?_)
        (fun i _ => rfl)).symm
    · rcases Finset.mem_range.mp hb with hb_lt
      refine ⟨⟨b, hb_lt⟩, ?_, rfl⟩
      simp
  simpa using h_sum_range.trans h_range_to_fin


/-!
### Covariance structure lemma

This auxiliary result characterizes the complete second-moment structure of contractable sequences.
It's included here for use in applying l2_contractability_bound.
-/

/-- **Uniform covariance structure for contractable L² sequences.**

A contractable sequence X in L²(μ) has uniform second-moment structure:
- All X_i have the same mean m
- All X_i have the same variance σ²
- All distinct pairs (X_i, X_j) have the same covariance σ²·ρ
- The correlation coefficient satisfies |ρ| ≤ 1

This is proved using the Cauchy-Schwarz inequality and the fact that contractability
forces all marginals of the same dimension to have identical distributions. -/
lemma contractable_covariance_structure
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ) :
    ∃ (m σSq ρ : ℝ),
      (∀ k, ∫ ω, X k ω ∂μ = m) ∧
      (∀ k, ∫ ω, (X k ω - m)^2 ∂μ = σSq) ∧
      (∀ i j, i ≠ j → ∫ ω, (X i ω - m) * (X j ω - m) ∂μ = σSq * ρ) ∧
      0 ≤ σSq ∧ -1 ≤ ρ ∧ ρ ≤ 1 := by
  -- Strategy: Use contractability to show all marginals of same size have same distribution
  -- This implies all X_i have the same mean and variance, and all pairs have same covariance

  -- Define m as the mean of X_0 (all X_i have the same distribution by contractability)
  let m := ∫ ω, X 0 ω ∂μ

  -- All X_i have the same mean by contractability (single-variable marginal)
  have hmean : ∀ k, ∫ ω, X k ω ∂μ = m := by
    intro k
    -- Use contractable_single_marginal_eq to show X_k has same distribution as X_0
    have h_eq_dist := contractable_single_marginal_eq (X := X) hX_contract hX_meas k
    -- Transfer integral via equal distributions
    have h_int_k : ∫ ω, X k ω ∂μ = ∫ x, x ∂(Measure.map (X k) μ) := by
      have h_ae : AEStronglyMeasurable (id : ℝ → ℝ) (Measure.map (X k) μ) :=
        aestronglyMeasurable_id
      exact (integral_map (hX_meas k).aemeasurable h_ae).symm
    have h_int_0 : ∫ ω, X 0 ω ∂μ = ∫ x, x ∂(Measure.map (X 0) μ) := by
      have h_ae : AEStronglyMeasurable (id : ℝ → ℝ) (Measure.map (X 0) μ) :=
        aestronglyMeasurable_id
      exact (integral_map (hX_meas 0).aemeasurable h_ae).symm
    rw [h_int_k, h_eq_dist, ← h_int_0]

  -- Define σSq as the variance of X_0
  let σSq := ∫ ω, (X 0 ω - m)^2 ∂μ

  -- All X_i have the same variance
  have hvar : ∀ k, ∫ ω, (X k ω - m)^2 ∂μ = σSq := by
    intro k
    -- Use equal distribution to transfer the variance integral
    have h_eq_dist := contractable_single_marginal_eq (X := X) hX_contract hX_meas k
    have hmean_k := hmean k
    -- The variance with k's mean equals variance with m (since they're equal)
    show ∫ ω, (X k ω - m)^2 ∂μ = σSq
    -- Transform X_k integral to X_0 integral via measure map
    have h_int_k : ∫ ω, (X k ω - m)^2 ∂μ = ∫ x, (x - m)^2 ∂(Measure.map (X k) μ) := by
      have h_ae : AEStronglyMeasurable (fun x : ℝ => (x - m)^2) (Measure.map (X k) μ) := by
        exact (continuous_id.sub continuous_const).pow 2 |>.aestronglyMeasurable
      exact (integral_map (hX_meas k).aemeasurable h_ae).symm
    have h_int_0 : ∫ ω, (X 0 ω - m)^2 ∂μ = ∫ x, (x - m)^2 ∂(Measure.map (X 0) μ) := by
      have h_ae : AEStronglyMeasurable (fun x : ℝ => (x - m)^2) (Measure.map (X 0) μ) := by
        exact (continuous_id.sub continuous_const).pow 2 |>.aestronglyMeasurable
      exact (integral_map (hX_meas 0).aemeasurable h_ae).symm
    rw [h_int_k, h_eq_dist, ← h_int_0]

  -- Define ρ from the covariance of (X_0, X_1)
  have hσSq_nonneg : 0 ≤ σSq := by
    apply integral_nonneg
    intro ω
    exact sq_nonneg _

  by_cases hσSq_pos : 0 < σSq
  · -- Case: positive variance
    let ρ := (∫ ω, (X 0 ω - m) * (X 1 ω - m) ∂μ) / σSq

    -- All pairs have the same covariance
    have hcov : ∀ i j, i ≠ j → ∫ ω, (X i ω - m) * (X j ω - m) ∂μ = σSq * ρ := by
      intro i j hij
      -- Apply contractability to get equal distributions for pairs
      by_cases h_ord : i < j
      · -- Case i < j: use contractable_map_pair directly
        have h_eq_dist := contractable_map_pair (X := X) hX_contract hX_meas h_ord
        -- Transfer the covariance integral via measure map
        have h_int_ij : ∫ ω, (X i ω - m) * (X j ω - m) ∂μ
            = ∫ p : ℝ × ℝ, (p.1 - m) * (p.2 - m) ∂(Measure.map (fun ω => (X i ω, X j ω)) μ) := by
          have h_ae : AEStronglyMeasurable (fun p : ℝ × ℝ => (p.1 - m) * (p.2 - m))
              (Measure.map (fun ω => (X i ω, X j ω)) μ) := by
            exact ((continuous_fst.sub continuous_const).mul
              (continuous_snd.sub continuous_const)).aestronglyMeasurable
          have h_comp : (fun ω => (X i ω - m) * (X j ω - m))
              = (fun p : ℝ × ℝ => (p.1 - m) * (p.2 - m)) ∘ (fun ω => (X i ω, X j ω)) := rfl
          rw [h_comp]
          exact (integral_map ((hX_meas i).prodMk (hX_meas j)).aemeasurable h_ae).symm
        have h_int_01 : ∫ ω, (X 0 ω - m) * (X 1 ω - m) ∂μ
            = ∫ p : ℝ × ℝ, (p.1 - m) * (p.2 - m) ∂(Measure.map (fun ω => (X 0 ω, X 1 ω)) μ) := by
          have h_ae : AEStronglyMeasurable (fun p : ℝ × ℝ => (p.1 - m) * (p.2 - m))
              (Measure.map (fun ω => (X 0 ω, X 1 ω)) μ) := by
            exact ((continuous_fst.sub continuous_const).mul
              (continuous_snd.sub continuous_const)).aestronglyMeasurable
          have h_comp : (fun ω => (X 0 ω - m) * (X 1 ω - m))
              = (fun p : ℝ × ℝ => (p.1 - m) * (p.2 - m)) ∘ (fun ω => (X 0 ω, X 1 ω)) := rfl
          rw [h_comp]
          exact (integral_map ((hX_meas 0).prodMk (hX_meas 1)).aemeasurable h_ae).symm
        rw [h_int_ij, h_eq_dist, ← h_int_01]
        -- Now need to show: ∫ (X 0 ω - m) * (X 1 ω - m) ∂μ = σSq * ρ
        -- This follows from the definition of ρ
        have hρ_def : ρ = (∫ ω, (X 0 ω - m) * (X 1 ω - m) ∂μ) / σSq := rfl
        rw [hρ_def]
        field_simp [ne_of_gt hσSq_pos]
      · -- Case j < i: use symmetry
        push_neg at h_ord
        have h_ji : j < i := Nat.lt_of_le_of_ne h_ord (Ne.symm hij)
        have h_eq_dist := contractable_map_pair (X := X) hX_contract hX_meas h_ji
        have h_int_ji : ∫ ω, (X j ω - m) * (X i ω - m) ∂μ
            = ∫ p : ℝ × ℝ, (p.1 - m) * (p.2 - m) ∂(Measure.map (fun ω => (X j ω, X i ω)) μ) := by
          have h_ae : AEStronglyMeasurable (fun p : ℝ × ℝ => (p.1 - m) * (p.2 - m))
              (Measure.map (fun ω => (X j ω, X i ω)) μ) := by
            exact ((continuous_fst.sub continuous_const).mul
              (continuous_snd.sub continuous_const)).aestronglyMeasurable
          have h_comp : (fun ω => (X j ω - m) * (X i ω - m))
              = (fun p : ℝ × ℝ => (p.1 - m) * (p.2 - m)) ∘ (fun ω => (X j ω, X i ω)) := rfl
          rw [h_comp]
          exact (integral_map ((hX_meas j).prodMk (hX_meas i)).aemeasurable h_ae).symm
        have h_int_01 : ∫ ω, (X 0 ω - m) * (X 1 ω - m) ∂μ
            = ∫ p : ℝ × ℝ, (p.1 - m) * (p.2 - m) ∂(Measure.map (fun ω => (X 0 ω, X 1 ω)) μ) := by
          have h_ae : AEStronglyMeasurable (fun p : ℝ × ℝ => (p.1 - m) * (p.2 - m))
              (Measure.map (fun ω => (X 0 ω, X 1 ω)) μ) := by
            exact ((continuous_fst.sub continuous_const).mul
              (continuous_snd.sub continuous_const)).aestronglyMeasurable
          have h_comp : (fun ω => (X 0 ω - m) * (X 1 ω - m))
              = (fun p : ℝ × ℝ => (p.1 - m) * (p.2 - m)) ∘ (fun ω => (X 0 ω, X 1 ω)) := rfl
          rw [h_comp]
          exact (integral_map ((hX_meas 0).prodMk (hX_meas 1)).aemeasurable h_ae).symm
        have h_symm : ∫ ω, (X i ω - m) * (X j ω - m) ∂μ = ∫ ω, (X j ω - m) * (X i ω - m) ∂μ := by
          congr 1; ext ω; ring
        rw [h_symm, h_int_ji, h_eq_dist, ← h_int_01]
        -- Now need to show: ∫ (X 0 ω - m) * (X 1 ω - m) ∂μ = σSq * ρ
        -- This follows from the definition of ρ
        have hρ_def : ρ = (∫ ω, (X 0 ω - m) * (X 1 ω - m) ∂μ) / σSq := rfl
        rw [hρ_def]
        field_simp [ne_of_gt hσSq_pos]

    -- Bound on ρ from Cauchy-Schwarz
    have hρ_bd : -1 ≤ ρ ∧ ρ ≤ 1 := by
      -- By Cauchy-Schwarz: |E[(X-m)(Y-m)]|² ≤ E[(X-m)²] · E[(Y-m)²]
      -- For X_0, X_1: |Cov|² ≤ σ² · σ² = σ⁴
      -- So |Cov| ≤ σ², and thus |ρ| = |Cov/σ²| ≤ 1

      -- The centered variables are in L²
      have hf₀ : MemLp (fun ω => X 0 ω - m) 2 μ := (hX_L2 0).sub (memLp_const m)
      have hf₁ : MemLp (fun ω => X 1 ω - m) 2 μ := (hX_L2 1).sub (memLp_const m)

      -- Their product is integrable
      have h_int : Integrable (fun ω => (X 0 ω - m) * (X 1 ω - m)) μ := hf₀.integrable_mul hf₁

      -- Apply Cauchy-Schwarz: |∫ f·g| ≤ √(∫ f²) · √(∫ g²)
      have h_cs : |∫ ω, (X 0 ω - m) * (X 1 ω - m) ∂μ|
          ≤ Real.sqrt (∫ ω, (X 0 ω - m)^2 ∂μ) * Real.sqrt (∫ ω, (X 1 ω - m)^2 ∂μ) := by
        -- Apply Hölder's inequality directly to the integrand
        have h_tri : |∫ ω, (X 0 ω - m) * (X 1 ω - m) ∂μ| ≤ ∫ ω, |(X 0 ω - m) * (X 1 ω - m)| ∂μ :=
          MeasureTheory.norm_integral_le_integral_norm (fun ω => (X 0 ω - m) * (X 1 ω - m))
        have h_abs_mul : ∫ ω, |(X 0 ω - m) * (X 1 ω - m)| ∂μ = ∫ ω, |X 0 ω - m| * |X 1 ω - m| ∂μ := by
          congr 1
          funext ω
          exact abs_mul (X 0 ω - m) (X 1 ω - m)
        have h_holder : ∫ ω, |X 0 ω - m| * |X 1 ω - m| ∂μ
            ≤ (∫ ω, |X 0 ω - m| ^ 2 ∂μ) ^ (1/2 : ℝ) * (∫ ω, |X 1 ω - m| ^ 2 ∂μ) ^ (1/2 : ℝ) := by
          have h_nonneg₀ : ∀ᵐ ω ∂μ, 0 ≤ |X 0 ω - m| := ae_of_all μ (fun ω => abs_nonneg _)
          have h_nonneg₁ : ∀ᵐ ω ∂μ, 0 ≤ |X 1 ω - m| := ae_of_all μ (fun ω => abs_nonneg _)
          have h_key : ∫ ω, |X 0 ω - m| * |X 1 ω - m| ∂μ
              ≤ (∫ ω, |X 0 ω - m| ^ (2:ℝ) ∂μ) ^ ((2:ℝ)⁻¹) * (∫ ω, |X 1 ω - m| ^ (2:ℝ) ∂μ) ^ ((2:ℝ)⁻¹) := by
            have hpq : (2:ℝ).HolderConjugate 2 := by
              constructor
              · norm_num
              · norm_num
              · norm_num
            have hf₀' : MemLp (fun ω => |X 0 ω - m|) (ENNReal.ofReal 2) μ := by
              have h2 : (ENNReal.ofReal 2 : ENNReal) = (2 : ENNReal) := by norm_num
              rw [h2]
              have : MemLp (fun ω => ‖X 0 ω - m‖) 2 μ := hf₀.norm
              have h_eq : (fun ω => ‖X 0 ω - m‖) =ᵐ[μ] (fun ω => |X 0 ω - m|) := by
                filter_upwards with ω
                exact Real.norm_eq_abs _
              exact MemLp.ae_eq h_eq this
            have hf₁' : MemLp (fun ω => |X 1 ω - m|) (ENNReal.ofReal 2) μ := by
              have h2 : (ENNReal.ofReal 2 : ENNReal) = (2 : ENNReal) := by norm_num
              rw [h2]
              have : MemLp (fun ω => ‖X 1 ω - m‖) 2 μ := hf₁.norm
              have h_eq : (fun ω => ‖X 1 ω - m‖) =ᵐ[μ] (fun ω => |X 1 ω - m|) := by
                filter_upwards with ω
                exact Real.norm_eq_abs _
              exact MemLp.ae_eq h_eq this
            have := MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg hpq h_nonneg₀ h_nonneg₁ hf₀' hf₁'
            convert this using 2 <;> norm_num
          convert h_key using 2
          · norm_num
          · norm_num
        have h_sqrt_conv : (∫ ω, |X 0 ω - m| ^ 2 ∂μ) ^ (1/2 : ℝ) * (∫ ω, |X 1 ω - m| ^ 2 ∂μ) ^ (1/2 : ℝ)
            = Real.sqrt (∫ ω, (X 0 ω - m)^2 ∂μ) * Real.sqrt (∫ ω, (X 1 ω - m)^2 ∂μ) := by
          have h4 : (∫ ω, |X 0 ω - m| ^ 2 ∂μ) ^ (1/2 : ℝ) = Real.sqrt (∫ ω, (X 0 ω - m)^2 ∂μ) := by
            rw [Real.sqrt_eq_rpow]
            congr 1
            congr 1
            funext ω
            rw [sq_abs]
          have h5 : (∫ ω, |X 1 ω - m| ^ 2 ∂μ) ^ (1/2 : ℝ) = Real.sqrt (∫ ω, (X 1 ω - m)^2 ∂μ) := by
            rw [Real.sqrt_eq_rpow]
            congr 1
            congr 1
            funext ω
            rw [sq_abs]
          rw [h4, h5]
        calc |∫ ω, (X 0 ω - m) * (X 1 ω - m) ∂μ|
            ≤ ∫ ω, |(X 0 ω - m) * (X 1 ω - m)| ∂μ := h_tri
          _ = ∫ ω, |X 0 ω - m| * |X 1 ω - m| ∂μ := h_abs_mul
          _ ≤ (∫ ω, |X 0 ω - m| ^ 2 ∂μ) ^ (1/2 : ℝ) * (∫ ω, |X 1 ω - m| ^ 2 ∂μ) ^ (1/2 : ℝ) := h_holder
          _ = Real.sqrt (∫ ω, (X 0 ω - m)^2 ∂μ) * Real.sqrt (∫ ω, (X 1 ω - m)^2 ∂μ) := h_sqrt_conv

      -- Substitute the variances
      rw [hvar 0, hvar 1] at h_cs
      have h_sqrt_sq : Real.sqrt σSq * Real.sqrt σSq = σSq := by
        have : σSq * σSq = σSq ^ 2 := (sq σSq).symm
        rw [← Real.sqrt_mul hσSq_nonneg, this, Real.sqrt_sq hσSq_nonneg]
      rw [h_sqrt_sq] at h_cs

      -- The covariance equals σSq * ρ by definition
      have h_cov_eq : ∫ ω, (X 0 ω - m) * (X 1 ω - m) ∂μ = σSq * ρ := by
        have : ρ = (∫ ω, (X 0 ω - m) * (X 1 ω - m) ∂μ) / σSq := rfl
        rw [this]; field_simp [ne_of_gt hσSq_pos]
      rw [h_cov_eq] at h_cs

      -- Now |σSq * ρ| ≤ σSq
      rw [abs_mul, abs_of_pos hσSq_pos, mul_comm] at h_cs
      have h_ρ_bd : |ρ| * σSq ≤ σSq := h_cs
      have : |ρ| ≤ 1 := (mul_le_iff_le_one_left hσSq_pos).mp h_ρ_bd
      exact abs_le.mp this

    exact ⟨m, σSq, ρ, hmean, hvar, hcov, hσSq_nonneg, hρ_bd⟩

  · -- Case: zero variance (all X_i are constant a.s.)
    push_neg at hσSq_pos
    have hσSq_zero : σSq = 0 := le_antisymm hσSq_pos hσSq_nonneg

    -- When variance is 0, all X_i = m almost surely
    have hX_const : ∀ i, ∀ᵐ ω ∂μ, X i ω = m := by
      intro i
      -- Use the fact that variance of X_i is 0
      have h_var_i : ∫ ω, (X i ω - m)^2 ∂μ = 0 := by
        rw [hvar i, hσSq_zero]
      -- When ∫ f² = 0 for a nonnegative function, f = 0 a.e.
      have h_ae_zero : ∀ᵐ ω ∂μ, (X i ω - m)^2 = 0 := by
        have h_nonneg : ∀ ω, 0 ≤ (X i ω - m)^2 := fun ω => sq_nonneg _
        have h_integrable : Integrable (fun ω => (X i ω - m)^2) μ := by
          have : MemLp (fun ω => X i ω - m) 2 μ := (hX_L2 i).sub (memLp_const m)
          exact this.integrable_sq
        exact integral_eq_zero_iff_of_nonneg_ae (ae_of_all _ h_nonneg) h_integrable |>.mp h_var_i
      -- Square equals zero iff the value equals zero
      filter_upwards [h_ae_zero] with ω h
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp h)

    -- Covariance is 0
    have hcov : ∀ i j, i ≠ j → ∫ ω, (X i ω - m) * (X j ω - m) ∂μ = 0 := by
      intro i j _
      -- Use the fact that X_i = m and X_j = m almost everywhere
      have h_ae_prod : ∀ᵐ ω ∂μ, (X i ω - m) * (X j ω - m) = 0 := by
        filter_upwards [hX_const i, hX_const j] with ω hi hj
        rw [hi, hj]
        ring
      -- Integral of a.e. zero function is zero
      have h_integrable : Integrable (fun ω => (X i ω - m) * (X j ω - m)) μ := by
        have h_i : MemLp (fun ω => X i ω - m) 2 μ := (hX_L2 i).sub (memLp_const m)
        have h_j : MemLp (fun ω => X j ω - m) 2 μ := (hX_L2 j).sub (memLp_const m)
        exact h_i.integrable_mul h_j
      exact integral_eq_zero_of_ae h_ae_prod

    -- ρ = 0 works
    use m, σSq, 0
    refine ⟨hmean, hvar, ?_, hσSq_nonneg, ?_⟩
    · intro i j hij
      rw [hcov i j hij, hσSq_zero]
      ring
    · norm_num


/-- **Supremum of weight differences for two non-overlapping windows.**

For two weight vectors representing uniform averages over disjoint windows of size k,
the supremum of their pointwise differences is exactly 1/k. This is the key parameter
in the L² contractability bound.

Uses `ciSup_const` since ℝ is only a `ConditionallyCompleteLattice`. -/
private lemma sup_two_window_weights {k : ℕ} (hk : 0 < k)
    (p q : Fin (2 * k) → ℝ)
    (hp : p = fun i => if i.val < k then 1 / (k : ℝ) else 0)
    (hq : q = fun i => if i.val < k then 0 else 1 / (k : ℝ)) :
    ⨆ i, |p i - q i| = 1 / (k : ℝ) := by
  have h_eq : ∀ i : Fin (2 * k), |p i - q i| = 1 / (k : ℝ) := by
    intro i
    rw [hp, hq]
    simp only
    split_ifs <;> simp [abs_neg]
  haveI : Nonempty (Fin (2 * k)) := ⟨⟨0, Nat.mul_pos (by decide : 0 < 2) hk⟩⟩
  simp_rw [h_eq]
  exact ciSup_const


-- Uniform version of l2_bound_two_windows: The constant Cf is the same for all
-- window positions. This follows because Cf = 2σ²(1-ρ) depends only on the covariance
-- structure of f∘X, which is uniform by contractability.
--
-- We use `l2_contractability_bound` from L2Approach directly by positing that f∘X has
-- a uniform covariance structure (which it must, by contractability).

/-- **Helper: Reindexed weights preserve probability properties.**

When reindexing weights from a finset S to Fin n via an equivalence,
the total sum and nonnegativity are preserved.
-/
private lemma reindexed_weights_prob
    {S : Finset ℕ} {wS : ℕ → ℝ}
    (h_sum_one : ∑ t ∈ S, wS t = 1)
    (h_nonneg : ∀ t, 0 ≤ wS t)
    {nS : ℕ} (eβ : Fin nS ≃ {t // t ∈ S})
    (w : Fin nS → ℝ)
    (h_w_def : ∀ i, w i = wS ((eβ i).1)) :
    (∑ i : Fin nS, w i) = 1 ∧ ∀ i, 0 ≤ w i := by
  constructor
  · have h_equiv : ∑ i : Fin nS, w i = ∑ t ∈ S, wS t := by
      classical
      have h_sum_equiv :
          ∑ i : Fin nS, wS ((eβ i).1) =
            ∑ b : {t // t ∈ S}, wS b.1 :=
        Fintype.sum_equiv eβ
          (fun i : Fin nS => wS ((eβ i).1))
          (fun b => wS b.1) (by intro i; rfl)
      have h_sum_attach :
          ∑ b : {t // t ∈ S}, wS b.1 = ∑ t ∈ S, wS t := by
        exact Finset.sum_attach (s := S) (f := fun t => wS t)
      have h_sum_w :
          ∑ i : Fin nS, w i = ∑ i : Fin nS, wS ((eβ i).1) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        exact h_w_def i
      simp [h_sum_w]
      exact h_sum_equiv.trans h_sum_attach
    simp [h_equiv, h_sum_one]
  · intro i
    rw [h_w_def]
    exact h_nonneg _

lemma l2_bound_two_windows_uniform
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (_hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (_hX_L2 : ∀ i, MemLp (X i) 2 μ)
    (f : ℝ → ℝ) (hf_meas : Measurable f)
    (hf_bdd : ∃ M, ∀ x, |f x| ≤ M)
    -- Accept Cf and covariance structure as arguments
    (Cf mf σSqf ρf : ℝ)
    (hCf_def : Cf = 2 * σSqf * (1 - ρf))
    (_hCf_nonneg : 0 ≤ Cf)
    (hmean : ∀ n, ∫ ω, f (X n ω) ∂μ = mf)
    (hvar : ∀ n, ∫ ω, (f (X n ω) - mf)^2 ∂μ = σSqf)
    (hcov : ∀ n m, n ≠ m → ∫ ω, (f (X n ω) - mf) * (f (X m ω) - mf) ∂μ = σSqf * ρf)
    (hσSq_nonneg : 0 ≤ σSqf)
    (hρ_bd : -1 ≤ ρf ∧ ρf ≤ 1) :
    ∀ (n m k : ℕ), 0 < k →
      ∫ ω, ((1/(k:ℝ)) * ∑ i : Fin k, f (X (n + i.val + 1) ω) -
            (1/(k:ℝ)) * ∑ i : Fin k, f (X (m + i.val + 1) ω))^2 ∂μ
        ≤ Cf / k := by
  -- Use the provided covariance structure to bound window differences
  -- The bound Cf/k comes from l2_contractability_bound applied to weight vectors
  intro n m k hk
  classical

  have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hk_ne : (k : ℝ) ≠ 0 := ne_of_gt hk_pos

  -- Index set: union of the two windows
  set S := window n k ∪ window m k with hS_def
  have h_subset_n : window n k ⊆ S := by
    intro t ht
    exact Finset.mem_union.mpr (Or.inl ht)
  have h_subset_m : window m k ⊆ S := by
    intro t ht
    exact Finset.mem_union.mpr (Or.inr ht)

  -- Random family indexed by natural numbers
  set Y : ℕ → Ω → ℝ := fun t ω => f (X t ω) with hY_def

  -- Weight vectors on the natural numbers (restricted to S)
  set pS : ℕ → ℝ := fun t => if t ∈ window n k then (1 / (k : ℝ)) else 0 with hpS_def
  set qS : ℕ → ℝ := fun t => if t ∈ window m k then (1 / (k : ℝ)) else 0 with hqS_def
  set δ : ℕ → ℝ := fun t => pS t - qS t with hδ_def

  -- Helper lemma: restrict the uniform weight to any subset of S
  have h_weight_restrict :
      ∀ (A : Finset ℕ) (hA : A ⊆ S) ω,
        ∑ t ∈ S, (if t ∈ A then (1 / (k : ℝ)) else 0) * Y t ω
          = (1 / (k : ℝ)) * ∑ t ∈ A, Y t ω := by
    intro A hA ω
    classical
    have h_filter :
        S.filter (fun t => t ∈ A) = A := by
      ext t
      by_cases htA : t ∈ A
      · have : t ∈ S := hA htA
        simp [Finset.mem_filter, htA, this]
      · simp [Finset.mem_filter, htA]
    have h_lhs :
        ∑ t ∈ S, (if t ∈ A then (1 / (k : ℝ)) else 0) * Y t ω
          = ∑ t ∈ S, (if t ∈ A then (1 / (k : ℝ)) * Y t ω else 0) := by
      refine Finset.sum_congr rfl ?_
      intro t ht
      by_cases htA : t ∈ A
      · simp [htA]
      · simp [htA]
    have h_sum :
        ∑ t ∈ S, (if t ∈ A then (1 / (k : ℝ)) else 0) * Y t ω =
          ∑ t ∈ A, (1 / (k : ℝ)) * Y t ω := by
      have h_indicator :=
        (Finset.sum_filter (s := S) (p := fun t => t ∈ A)
            (f := fun t => (1 / (k : ℝ)) * Y t ω)).symm
      simpa [h_lhs, h_filter] using h_indicator
    calc
      ∑ t ∈ S, (if t ∈ A then (1 / (k : ℝ)) else 0) * Y t ω
          = ∑ t ∈ A, (1 / (k : ℝ)) * Y t ω := h_sum
      _ = (1 / (k : ℝ)) * ∑ t ∈ A, Y t ω := by
            simp [Finset.mul_sum]

  -- Difference of window averages written as a single sum over S with weights δ
  have h_sum_delta :
      ∀ ω,
        ∑ t ∈ S, δ t * Y t ω =
          (1 / (k : ℝ)) * ∑ t ∈ window n k, Y t ω -
          (1 / (k : ℝ)) * ∑ t ∈ window m k, Y t ω := by
    intro ω
    have h_sum_p :
        ∑ t ∈ S, pS t * Y t ω =
          (1 / (k : ℝ)) * ∑ t ∈ window n k, Y t ω := by
      simpa [pS] using h_weight_restrict (window n k) h_subset_n ω
    have h_sum_q :
        ∑ t ∈ S, qS t * Y t ω =
          (1 / (k : ℝ)) * ∑ t ∈ window m k, Y t ω := by
      simpa [qS] using h_weight_restrict (window m k) h_subset_m ω
    have h_expand :
        ∑ t ∈ S, δ t * Y t ω =
          ∑ t ∈ S, (pS t * Y t ω - qS t * Y t ω) := by
      refine Finset.sum_congr rfl ?_
      intro t ht
      have : (pS t - qS t) * Y t ω = pS t * Y t ω - qS t * Y t ω := by
        ring
      simpa [δ] using this
    have h_split :
        ∑ t ∈ S, δ t * Y t ω =
          ∑ t ∈ S, pS t * Y t ω - ∑ t ∈ S, qS t * Y t ω := by
      simpa using
        (h_expand.trans
          (Finset.sum_sub_distrib (s := S)
            (f := fun t => pS t * Y t ω)
            (g := fun t => qS t * Y t ω)))
    simpa [h_sum_p, h_sum_q] using h_split

  have h_goal :
      ∀ ω,
        (1 / (k : ℝ)) * ∑ i : Fin k, f (X (n + i.val + 1) ω) -
        (1 / (k : ℝ)) * ∑ i : Fin k, f (X (m + i.val + 1) ω)
          = ∑ t ∈ S, δ t * Y t ω := by
    intro ω
    have := h_sum_delta ω
    simp only [Y, sum_window_eq_sum_fin] at this ⊢
    linarith

  -- Total weights
  have h_sum_pS :
      ∑ t ∈ S, pS t = 1 := by
    classical
    have h_filter :
        S.filter (fun t => t ∈ window n k) = window n k := by
      ext t
      by_cases ht : t ∈ window n k
      · have : t ∈ S := h_subset_n ht
        simp [Finset.mem_filter, ht, this]
      · simp [Finset.mem_filter, ht]
    have h_sum :
        ∑ t ∈ S, pS t = ∑ t ∈ window n k, (1 / (k : ℝ)) := by
      have h_indicator :=
        (Finset.sum_filter (s := S) (p := fun t => t ∈ window n k)
            (f := fun _ : ℕ => (1 / (k : ℝ)))).symm
      simpa [pS, h_filter]
        using h_indicator
    have h_card : (window n k).card = k := window_card n k
    have hk_ne' : (k : ℝ) ≠ 0 := ne_of_gt hk_pos
    have h_one : (window n k).card * (1 / (k : ℝ)) = 1 := by
      simp [h_card, one_div, hk_ne']
    have h_const :
        ∑ t ∈ window n k, (1 / (k : ℝ))
          = (window n k).card * (1 / (k : ℝ)) := by
      simp [Finset.sum_const]
    calc
      ∑ t ∈ S, pS t = (window n k).card * (1 / (k : ℝ)) := by
        simp only [h_sum, h_const]
      _ = 1 := h_one

  have h_sum_qS :
      ∑ t ∈ S, qS t = 1 := by
    classical
    have h_filter :
        S.filter (fun t => t ∈ window m k) = window m k := by
      ext t
      by_cases ht : t ∈ window m k
      · have : t ∈ S := h_subset_m ht
        simp [Finset.mem_filter, ht, this]
      · simp [Finset.mem_filter, ht]
    have h_sum :
        ∑ t ∈ S, qS t = ∑ t ∈ window m k, (1 / (k : ℝ)) := by
      have h_indicator :=
        (Finset.sum_filter (s := S) (p := fun t => t ∈ window m k)
            (f := fun _ : ℕ => (1 / (k : ℝ)))).symm
      simp only at h_indicator
      rw [h_filter] at h_indicator
      exact h_indicator
    have h_card : (window m k).card = k := window_card m k
    have hk_ne' : (k : ℝ) ≠ 0 := ne_of_gt hk_pos
    have h_one : (window m k).card * (1 / (k : ℝ)) = 1 := by
      simp [h_card, one_div, hk_ne']
    have h_const :
        ∑ t ∈ window m k, (1 / (k : ℝ))
          = (window m k).card * (1 / (k : ℝ)) := by
      simp [Finset.sum_const]
    calc
      ∑ t ∈ S, qS t = (window m k).card * (1 / (k : ℝ)) := by
        simp only [h_sum, h_const]
      _ = 1 := h_one

  -- Positivity of the weights
  have hpS_nonneg : ∀ t, 0 ≤ pS t := by
    intro t
    by_cases ht : t ∈ window n k
    · have hk_nonneg : 0 ≤ 1 / (k : ℝ) := div_nonneg zero_le_one (le_of_lt hk_pos)
      simp only [pS, ht, ite_true, hk_nonneg]
    · simp [pS, ht]

  have hqS_nonneg : ∀ t, 0 ≤ qS t := by
    intro t
    by_cases ht : t ∈ window m k
    · have hk_nonneg : 0 ≤ 1 / (k : ℝ) := div_nonneg zero_le_one (le_of_lt hk_pos)
      simp only [qS, ht, ite_true, hk_nonneg]
    · simp [qS, ht]

  -- Absolute bound on δ on S
  have hδ_abs_le :
      ∀ t ∈ S, |δ t| ≤ 1 / (k : ℝ) := by
    intro t htS
    by_cases ht_n : t ∈ window n k
    · by_cases ht_m : t ∈ window m k
      · have : δ t = 0 := by simp [δ, pS, qS, ht_n, ht_m]
        simp [this]
      · have : δ t = 1 / (k : ℝ) := by simp [δ, pS, qS, ht_n, ht_m]
        simp [this]
    · by_cases ht_m : t ∈ window m k
      · have : δ t = - (1 / (k : ℝ)) := by simp [δ, pS, qS, ht_n, ht_m]
        have : |δ t| = 1 / (k : ℝ) := by simp [this, abs_neg]
        simp [this]
      · have : δ t = 0 := by simp [δ, pS, qS, ht_n, ht_m]
        simp [this]

  -- Reindex the union set `S` as a finite type
  let β := {t : ℕ // t ∈ S}
  let nS : ℕ := Fintype.card β
  let eβ : Fin nS ≃ β := (Fintype.equivFin β).symm
  let idx : Fin nS → ℕ := fun i => (eβ i).1
  have h_idx_mem : ∀ i : Fin nS, idx i ∈ S := fun i => (eβ i).2

  -- Random family indexed by `Fin nS`
  let ξ : Fin nS → Ω → ℝ := fun i ω => Y (idx i) ω

  -- Weights transferred to `Fin nS`
  let p : Fin nS → ℝ := fun i => pS (idx i)
  let q : Fin nS → ℝ := fun i => qS (idx i)

  -- Probability properties for the reindexed weights
  have hp_prob : (∑ i : Fin nS, p i) = 1 ∧ ∀ i, 0 ≤ p i :=
    reindexed_weights_prob h_sum_pS hpS_nonneg eβ p (by intro i; rfl)

  have hq_prob : (∑ i : Fin nS, q i) = 1 ∧ ∀ i, 0 ≤ q i :=
    reindexed_weights_prob h_sum_qS hqS_nonneg eβ q (by intro i; rfl)

  -- Supremum bound on the weight difference
  have h_window_nonempty : (window n k).Nonempty := by
    classical
    have hk_pos_nat : 0 < k := hk
    have hcard_pos : 0 < (window n k).card := by simpa [window_card] using hk_pos_nat
    exact Finset.card_pos.mp hcard_pos
  have hβ_nonempty : Nonempty β := by
    classical
    obtain ⟨t, ht⟩ := h_window_nonempty
    exact ⟨⟨t, h_subset_n ht⟩⟩
  have h_nS_pos : 0 < nS := Fintype.card_pos_iff.mpr hβ_nonempty
  have h_sup_le :
      (⨆ i : Fin nS, |p i - q i|) ≤ 1 / (k : ℝ) := by
    classical
    haveI : Nonempty (Fin nS) := Fin.pos_iff_nonempty.mp h_nS_pos
    refine ciSup_le ?_
    intro i
    have hmem : idx i ∈ S := h_idx_mem i
    have hδ_bound := hδ_abs_le (idx i) hmem
    have hδ_eq : δ (idx i) = p i - q i := by simp [δ, p, q, idx]
    simpa [hδ_eq] using hδ_bound

  -- Injectivity of the indexing map
  have h_idx_ne : ∀ {i j : Fin nS}, i ≠ j → idx i ≠ idx j := by
    intro i j hij hval
    have : eβ i = eβ j := by
      apply Subtype.ext
      exact hval
    exact hij (eβ.injective this)

  -- Mean and L² structure for ξ
  have hξ_mean : ∀ i : Fin nS, ∫ ω, ξ i ω ∂μ = mf := by
    intro i
    simpa [ξ, Y, idx, hY_def] using hmean (idx i)

  have hξ_L2 : ∀ i : Fin nS, MemLp (fun ω => ξ i ω - mf) 2 μ := by
    intro i
    -- Reconstruct MemLp from boundedness
    obtain ⟨M, hM⟩ := hf_bdd
    have : MemLp (fun ω => f (X (idx i) ω)) 2 μ := by
      apply MemLp.of_bound (hf_meas.comp (hX_meas (idx i))).aestronglyMeasurable M
      filter_upwards with ω
      simp [Real.norm_eq_abs]
      exact hM (X (idx i) ω)
    simpa [ξ, Y, idx, hY_def] using this.sub (memLp_const mf)

  have hξ_var : ∀ i : Fin nS, ∫ ω, (ξ i ω - mf)^2 ∂μ = (Real.sqrt σSqf) ^ 2 := by
    intro i
    simpa [ξ, Y, idx, hY_def, Real.sq_sqrt hσSq_nonneg] using hvar (idx i)

  have hξ_cov :
      ∀ i j : Fin nS, i ≠ j →
        ∫ ω, (ξ i ω - mf) * (ξ j ω - mf) ∂μ = (Real.sqrt σSqf) ^ 2 * ρf := by
    intro i j hij
    have hneq : idx i ≠ idx j := h_idx_ne hij
    simpa [ξ, Y, idx, hY_def, hneq, Real.sq_sqrt hσSq_nonneg] using
      hcov (idx i) (idx j) hneq

  -- Express the δ-weighted sum in terms of the Fin-indexed weights
  have h_sum_p_fin :
      ∀ ω,
        ∑ i : Fin nS, p i * ξ i ω =
          ∑ t ∈ S, pS t * Y t ω := by
    intro ω
    classical
    have h_sum_equiv :
        ∑ i : Fin nS, p i * ξ i ω =
          ∑ b : β, pS b.1 * Y b.1 ω :=
      Fintype.sum_equiv eβ
        (fun i : Fin nS => p i * ξ i ω)
        (fun b : β => pS b.1 * Y b.1 ω)
        (by intro i; simp [p, ξ, idx, Y])
    have h_sum_attach :
        ∑ b : β, pS b.1 * Y b.1 ω =
          ∑ t ∈ S, pS t * Y t ω := by
      simpa [β] using
        Finset.sum_attach (s := S) (f := fun t => pS t * Y t ω)
    simpa using h_sum_equiv.trans h_sum_attach

  have h_sum_q_fin :
      ∀ ω,
        ∑ i : Fin nS, q i * ξ i ω =
          ∑ t ∈ S, qS t * Y t ω := by
    intro ω
    classical
    have h_sum_equiv :
        ∑ i : Fin nS, q i * ξ i ω =
          ∑ b : β, qS b.1 * Y b.1 ω :=
      Fintype.sum_equiv eβ
        (fun i : Fin nS => q i * ξ i ω)
        (fun b : β => qS b.1 * Y b.1 ω)
        (by intro i; simp [q, ξ, idx, Y])
    have h_sum_attach :
        ∑ b : β, qS b.1 * Y b.1 ω =
          ∑ t ∈ S, qS t * Y t ω := by
      simpa [β] using
        Finset.sum_attach (s := S) (f := fun t => qS t * Y t ω)
    simpa using h_sum_equiv.trans h_sum_attach

  have h_delta_fin :
      ∀ ω,
        ∑ t ∈ S, δ t * Y t ω =
          ∑ i : Fin nS, p i * ξ i ω - ∑ i : Fin nS, q i * ξ i ω := by
    intro ω
    have h_sum_p := h_sum_p_fin ω
    have h_sum_q := h_sum_q_fin ω
    have h_expand :
        ∑ t ∈ S, δ t * Y t ω =
          ∑ t ∈ S, (pS t * Y t ω - qS t * Y t ω) := by
      refine Finset.sum_congr rfl ?_
      intro t ht
      have : (pS t - qS t) * Y t ω = pS t * Y t ω - qS t * Y t ω := by
        ring
      simpa [δ] using this
    have h_split :
        ∑ t ∈ S, δ t * Y t ω =
          ∑ t ∈ S, pS t * Y t ω - ∑ t ∈ S, qS t * Y t ω := by
      simpa using
        (h_expand.trans
          (Finset.sum_sub_distrib (s := S)
            (f := fun t => pS t * Y t ω)
            (g := fun t => qS t * Y t ω)))
    simpa [h_sum_p, h_sum_q] using h_split

  have h_goal_fin :
      ∀ ω,
        (1 / (k : ℝ)) * ∑ i : Fin k, f (X (n + i.val + 1) ω) -
        (1 / (k : ℝ)) * ∑ i : Fin k, f (X (m + i.val + 1) ω)
          = ∑ i : Fin nS, p i * ξ i ω - ∑ i : Fin nS, q i * ξ i ω := by
    intro ω
    have h_goal' := h_goal ω
    have h_delta := h_delta_fin ω
    exact h_goal'.trans h_delta

  -- Apply the L² contractability bound on the reindexed weights
  have h_bound :=
    @L2Approach.l2_contractability_bound Ω _ μ _ nS ξ mf (Real.sqrt σSqf) ρf
      hρ_bd hξ_mean hξ_L2 hξ_var hξ_cov p q hp_prob hq_prob

  have h_factor_nonneg :
      0 ≤ 2 * (Real.sqrt σSqf) ^ 2 * (1 - ρf) := by
    have hσ_nonneg : 0 ≤ (Real.sqrt σSqf) ^ 2 := by exact sq_nonneg _
    have hρ_nonneg : 0 ≤ 1 - ρf := sub_nonneg.mpr hρ_bd.2
    have : 0 ≤ (2 : ℝ) := by norm_num
    exact mul_nonneg (mul_nonneg this hσ_nonneg) hρ_nonneg

  have h_bound_sup :
      2 * (Real.sqrt σSqf) ^ 2 * (1 - ρf) *
        (⨆ i : Fin nS, |p i - q i|) ≤
      2 * (Real.sqrt σSqf) ^ 2 * (1 - ρf) * (1 / (k : ℝ)) := by
    have h :=
      (mul_le_mul_of_nonneg_left h_sup_le h_factor_nonneg :
          (2 * (Real.sqrt σSqf) ^ 2 * (1 - ρf)) *
              (⨆ i : Fin nS, |p i - q i|)
            ≤ (2 * (Real.sqrt σSqf) ^ 2 * (1 - ρf)) * (1 / (k : ℝ)))
    simpa [mul_comm, mul_left_comm, mul_assoc]
      using h

  -- Final bound
  have h_sqrt_sq : (Real.sqrt σSqf) ^ 2 = σSqf := Real.sq_sqrt hσSq_nonneg

  have h_eq_integral :
      ∫ ω,
        ((1 / (k : ℝ)) * ∑ i : Fin k, f (X (n + i.val + 1) ω) -
          (1 / (k : ℝ)) * ∑ i : Fin k, f (X (m + i.val + 1) ω))^2 ∂μ =
        ∫ ω, (∑ i : Fin nS, p i * ξ i ω - ∑ i : Fin nS, q i * ξ i ω)^2 ∂μ := by
    congr 1
    funext ω
    simpa using
      congrArg (fun x : ℝ => x ^ 2) (h_goal_fin ω)

  have h_int_le_sup :
      ∫ ω,
          ((1 / (k : ℝ)) * ∑ i : Fin k, f (X (n + i.val + 1) ω) -
            (1 / (k : ℝ)) * ∑ i : Fin k, f (X (m + i.val + 1) ω))^2 ∂μ ≤
        2 * (Real.sqrt σSqf) ^ 2 * (1 - ρf) *
          (⨆ i : Fin nS, |p i - q i|) := by
    simpa [h_eq_integral.symm] using h_bound

  have h_int_le :
      ∫ ω,
          ((1 / (k : ℝ)) * ∑ i : Fin k, f (X (n + i.val + 1) ω) -
            (1 / (k : ℝ)) * ∑ i : Fin k, f (X (m + i.val + 1) ω))^2 ∂μ ≤
        2 * (Real.sqrt σSqf) ^ 2 * (1 - ρf) * (1 / (k : ℝ)) :=
    h_int_le_sup.trans h_bound_sup

  have h_coef_eq :
      2 * (Real.sqrt σSqf) ^ 2 * (1 - ρf) * ((k : ℝ)⁻¹) = Cf / k := by
    rw [hCf_def, h_sqrt_sq]
    simp [div_eq_mul_inv]

  have h_final :
      ∫ ω,
          ((1 / (k : ℝ)) * ∑ i : Fin k, f (X (n + i.val + 1) ω) -
            (1 / (k : ℝ)) * ∑ i : Fin k, f (X (m + i.val + 1) ω))^2 ∂μ ≤
        Cf / k := by
    simpa [h_coef_eq, one_div] using h_int_le

  exact h_final

/-- **Compute the L² contractability constant for f ∘ X.**

This helper extracts the common covariance structure computation needed by both
`l2_bound_two_windows_uniform` and `l2_bound_long_vs_tail`.

Returns `Cf = 2σ²(1-ρ)` where `(mf, σ², ρ)` is the covariance structure of
`f ∘ X` obtained from `contractable_covariance_structure`.

**Design rationale**: Computing the covariance structure once and passing it to
both bound lemmas ensures they use the same constant, avoiding the need to prove
equality of opaque existential witnesses. -/
lemma get_covariance_constant
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ)
    (f : ℝ → ℝ) (hf_meas : Measurable f)
    (hf_bdd : ∃ M, ∀ x, |f x| ≤ M) :
    ∃ (Cf : ℝ) (mf σSqf ρf : ℝ),
      Cf = 2 * σSqf * (1 - ρf) ∧
      0 ≤ Cf ∧
      -- Covariance structure properties
      (∀ n, ∫ ω, f (X n ω) ∂μ = mf) ∧
      (∀ n, ∫ ω, (f (X n ω) - mf)^2 ∂μ = σSqf) ∧
      (∀ n m, n ≠ m → ∫ ω, (f (X n ω) - mf) * (f (X m ω) - mf) ∂μ = σSqf * ρf) ∧
      0 ≤ σSqf ∧
      -1 ≤ ρf ∧ ρf ≤ 1 := by
  -- Step 1: Show f∘X is contractable
  have hfX_contract : Contractable μ (fun n ω => f (X n ω)) :=
    @contractable_comp Ω _ μ _ X hX_contract hX_meas f hf_meas

  -- Step 2: Get covariance structure (m, σ², ρ) of f∘X
  obtain ⟨M, hM⟩ := hf_bdd
  have hfX_L2 : ∀ i, MemLp (fun ω => f (X i ω)) 2 μ := by
    intro i
    apply MemLp.of_bound (hf_meas.comp (hX_meas i)).aestronglyMeasurable M
    filter_upwards with ω
    simp [Real.norm_eq_abs]
    exact hM (X i ω)

  have hfX_meas : ∀ i, Measurable (fun ω => f (X i ω)) := by
    intro i
    exact hf_meas.comp (hX_meas i)

  obtain ⟨mf, σSqf, ρf, hmean, hvar, hcov, hσSq_nonneg, hρ_bd⟩ :=
    contractable_covariance_structure
      (fun n ω => f (X n ω)) hfX_contract hfX_meas hfX_L2

  -- Step 3: Set Cf = 2σ²(1-ρ)
  let Cf := 2 * σSqf * (1 - ρf)
  have hCf_nonneg : 0 ≤ Cf := by
    apply mul_nonneg
    apply mul_nonneg
    · norm_num
    · exact hσSq_nonneg
    · linarith [hρ_bd.2]

  exact ⟨Cf, mf, σSqf, ρf, rfl, hCf_nonneg, hmean, hvar, hcov, hσSq_nonneg, hρ_bd.1, hρ_bd.2⟩

/-- **L² bound wrapper for two starting windows**.

For contractable sequences, the L² difference between averages starting at different
indices n and m is uniformly small. This gives us the key uniform bound we need.

NOTE: This wrapper is not used in the main proof. The uniform version with disjointness
hypothesis is used instead. This wrapper is left for potential future use.
-/
lemma l2_bound_two_windows
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ)
    (f : ℝ → ℝ) (hf_meas : Measurable f)
    (hf_bdd : ∃ M, ∀ x, |f x| ≤ M)
    (n m : ℕ) {k : ℕ} (hk : 0 < k)
    (_hdisj : Disjoint (window n k) (window m k)) :
    ∃ Cf : ℝ, 0 ≤ Cf ∧
      ∫ ω, ((1/(k:ℝ)) * ∑ i : Fin k, f (X (n + i.val + 1) ω) -
            (1/(k:ℝ)) * ∑ i : Fin k, f (X (m + i.val + 1) ω))^2 ∂μ
        ≤ Cf / k := by
  -- Get covariance constant and structure
  obtain ⟨Cf, mf, σSqf, ρf, hCf_def, hCf_nonneg, hmean, hvar, hcov, hσSq_nn, hρ_bd1, hρ_bd2⟩ :=
    get_covariance_constant X hX_contract hX_meas hX_L2 f hf_meas hf_bdd
  -- Apply uniform bound with the covariance structure
  refine ⟨Cf, hCf_nonneg, ?_⟩
  exact l2_bound_two_windows_uniform X hX_contract hX_meas hX_L2 f hf_meas hf_bdd
    Cf mf σSqf ρf hCf_def hCf_nonneg hmean hvar hcov hσSq_nn ⟨hρ_bd1, hρ_bd2⟩ n m k hk

/-- Reindex the last `k`-block of a length-`m` sum.

For `m,k : ℕ` with `0 < k ≤ m`, and any real constant `c` and function `F : ℕ → ℝ`,
the sum over the last `k` positions of a length-`m` vector can be reindexed to a sum over `Fin k`:
∑_{i<m} (1_{i ≥ m-k} · c) · F(i) = c · ∑_{j<k} F(m - k + j).
-/
private lemma sum_tail_block_reindex
    {m k : ℕ} (hk_pos : 0 < k) (hkm : k ≤ m)
    (c : ℝ) (F : ℕ → ℝ) :
    ∑ i : Fin m, (if i.val < m - k then 0 else c) * F i.val
      = c * ∑ j : Fin k, F (m - k + j.val) := by
  -- Split the sum into indices < m-k (which contribute 0) and indices ≥ m-k
  calc ∑ i : Fin m, (if i.val < m - k then 0 else c) * F i.val
      = ∑ i : Fin m, if i.val < m - k then 0 else c * F i.val := by
          congr 1; ext i; split_ifs <;> ring
    _ = ∑ i ∈ Finset.univ.filter (fun i : Fin m => ¬ i.val < m - k), c * F i.val := by
          have : ∀ i : Fin m, (if i.val < m - k then 0 else c * F i.val) =
                               (if ¬ i.val < m - k then c * F i.val else 0) := by
            intro i; by_cases h : i.val < m - k <;> simp [h]
          simp_rw [this]
          rw [Finset.sum_filter]
    _ = c * ∑ i ∈ Finset.univ.filter (fun i : Fin m => ¬ i.val < m - k), F i.val := by
          rw [← Finset.mul_sum]
    _ = c * ∑ j : Fin k, F (m - k + j.val) := by
          congr 1
          have h_sub : m - (m - k) = k := by omega
          trans (∑ j : Fin (m - (m - k)), F ((m - k) + j.val))
          · exact FinIndexHelpers.sum_filter_fin_val_ge_eq_sum_fin m (m - k) (by omega) F
          · rw [h_sub]

/-- Long average vs tail average bound: Comparing the average of the first m terms
with the average of the last k terms (where k ≤ m) has the same L² contractability bound.

This is the key lemma needed to complete the Cauchy argument in weighted_sums_converge_L1.
-/
lemma l2_bound_long_vs_tail
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (_hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (_hX_L2 : ∀ i, MemLp (X i) 2 μ)
    (f : ℝ → ℝ) (hf_meas : Measurable f)
    (hf_bdd : ∃ M, ∀ x, |f x| ≤ M)
    -- Accept Cf and covariance structure as arguments
    (Cf mf σSqf ρf : ℝ)
    (hCf_def : Cf = 2 * σSqf * (1 - ρf))
    (_hCf_nonneg : 0 ≤ Cf)
    (hmean : ∀ n, ∫ ω, f (X n ω) ∂μ = mf)
    (hvar : ∀ n, ∫ ω, (f (X n ω) - mf)^2 ∂μ = σSqf)
    (hcov : ∀ n m, n ≠ m → ∫ ω, (f (X n ω) - mf) * (f (X m ω) - mf) ∂μ = σSqf * ρf)
    (hσSq_nonneg : 0 ≤ σSqf)
    (hρ_bd : -1 ≤ ρf ∧ ρf ≤ 1)
    (n m k : ℕ) (hk : 0 < k) (hkm : k ≤ m) :
    ∫ ω, ((1 / (m : ℝ)) * ∑ i : Fin m, f (X (n + i.val + 1) ω) -
          (1 / (k : ℝ)) * ∑ i : Fin k, f (X (n + (m - k) + i.val + 1) ω))^2 ∂μ
      ≤ Cf / k := by
  -- Strategy: The key observation is that comparing a long average (1/m) with
  -- a tail average (1/k over last k terms) is the same as comparing two different
  -- weight vectors over the same m terms.

  -- Since Cf is already the uniform bound for equal-weight windows (from hCf_unif),
  -- and this comparison uses weights that differ by at most 1/k at each position,
  -- the bound follows from the general weight lemma.

  -- Specifically:
  -- - Long avg: sum_{i<m} (1/m) f(X_{n+i+1})
  -- - Tail avg: sum_{i<k} (1/k) f(X_{n+(m-k)+i+1}) = sum_{i in [m-k,m)} (1/k) f(X_{n+i+1})
  -- These can be written as:
  --   p_i = 1/m for all i
  --   q_i = 0 for i < m-k, and 1/k for i >= m-k
  -- So sup|p-q| = max(1/m, 1/k) = 1/k (since k ≤ m)

  -- The bound from l2_contractability_bound would be: 2σ²(1-ρ) · (1/k) = Cf/k
  -- which is exactly what we need to prove.

  -- Direct approach using hCf_unif:
  -- The tail average is an equal-weight window of size k starting at n+(m-k):
  --   (1/k) ∑_{j<k} f(X_{n+(m-k)+j+1})
  --
  -- Strategy:
  -- 1. Use triangle inequality: |long_avg - tail_avg| ≤ |long_avg - some_window| + |some_window - tail_avg|
  -- 2. The tail window is exactly window starting at position n+(m-k)
  -- 3. Can compare it with a window of size k starting at n using hCf_unif
  -- 4. The bound Cf/k applies since both are equal-weight windows of size k
  --
  -- Rewrite long average (1/m) * ∑_{i<m} f(X_{n+i+1}) in terms of weights on each position
  -- We can split it as: sum over first (m-k) terms + sum over last k terms
  -- Then compare with the tail average which is just the last k terms weighted by 1/k

  -- Key insight: Write the difference as a weighted combination where we can apply sum_tail_block_reindex
  -- Long avg = (1/m) * [first (m-k) terms + last k terms]
  -- Tail avg = (1/k) * [last k terms]
  -- Difference involves the last k terms with weight (1/m - 1/k) and first terms with weight 1/m

  -- Since |1/m - 1/k| ≤ 1/k and we have at most m terms each bounded,
  -- this reduces to applying the uniform bound hCf_unif

  -- Use that we can rewrite the long average to isolate the tail portion
  -- and apply the uniform bound

  obtain ⟨M, hM⟩ := hf_bdd

  -- The key is to use boundedness to show the difference is controlled
  -- For a more direct proof, we use that:
  -- |long_avg - tail_avg|² ≤ |long_avg - window_avg|² + |window_avg - tail_avg|²
  -- where both terms can be bounded using hCf_unif

  -- However, for simplicity, we can use the fact that both averages involve
  -- bounded functions and the weight difference is small

  -- Direct bound using triangle inequality and boundedness
  have h_bdd_integrand : ∀ ω, ((1 / (m : ℝ)) * ∑ i : Fin m, f (X (n + i.val + 1) ω) -
        (1 / (k : ℝ)) * ∑ i : Fin k, f (X (n + (m - k) + i.val + 1) ω))^2
      ≤ (4 * M)^2 := by
    intro ω
    have h1 : |(1 / (m : ℝ)) * ∑ i : Fin m, f (X (n + i.val + 1) ω)| ≤ M := by
      calc |(1 / (m : ℝ)) * ∑ i : Fin m, f (X (n + i.val + 1) ω)|
          = (1 / (m : ℝ)) * |∑ i : Fin m, f (X (n + i.val + 1) ω)| := by
              rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1 / (m : ℝ))]
        _ ≤ (1 / (m : ℝ)) * (m * M) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            calc |∑ i : Fin m, f (X (n + i.val + 1) ω)|
                ≤ ∑ i : Fin m, |f (X (n + i.val + 1) ω)| := Finset.abs_sum_le_sum_abs _ _
              _ ≤ ∑ i : Fin m, M := by
                  apply Finset.sum_le_sum
                  intro i _; exact hM _
              _ = m * M := by rw [Finset.sum_const, Finset.card_fin]; ring
        _ = M := by
            have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr (Nat.lt_of_lt_of_le hk hkm)
            field_simp [ne_of_gt hm_pos]
    have h2 : |(1 / (k : ℝ)) * ∑ i : Fin k, f (X (n + (m - k) + i.val + 1) ω)| ≤ M := by
      calc |(1 / (k : ℝ)) * ∑ i : Fin k, f (X (n + (m - k) + i.val + 1) ω)|
          = (1 / (k : ℝ)) * |∑ i : Fin k, f (X (n + (m - k) + i.val + 1) ω)| := by
              rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1 / (k : ℝ))]
        _ ≤ (1 / (k : ℝ)) * (k * M) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            calc |∑ i : Fin k, f (X (n + (m - k) + i.val + 1) ω)|
                ≤ ∑ i : Fin k, |f (X (n + (m - k) + i.val + 1) ω)| := Finset.abs_sum_le_sum_abs _ _
              _ ≤ ∑ i : Fin k, M := by
                  apply Finset.sum_le_sum
                  intro i _; exact hM _
              _ = k * M := by rw [Finset.sum_const, Finset.card_fin]; ring
        _ = M := by
          have hk_pos : (0:ℝ) < k := Nat.cast_pos.mpr hk
          field_simp [ne_of_gt hk_pos]
    have ha : |(1 / (m : ℝ)) * ∑ i : Fin m, f (X (n + i.val + 1) ω) -
          (1 / (k : ℝ)) * ∑ i : Fin k, f (X (n + (m - k) + i.val + 1) ω)| ≤
        |(1 / (m : ℝ)) * ∑ i : Fin m, f (X (n + i.val + 1) ω)| +
           |(1 / (k : ℝ)) * ∑ i : Fin k, f (X (n + (m - k) + i.val + 1) ω)| :=
      abs_sub _ _
    calc ((1 / (m : ℝ)) * ∑ i : Fin m, f (X (n + i.val + 1) ω) -
          (1 / (k : ℝ)) * ∑ i : Fin k, f (X (n + (m - k) + i.val + 1) ω))^2
        ≤ (|(1 / (m : ℝ)) * ∑ i : Fin m, f (X (n + i.val + 1) ω)| +
           |(1 / (k : ℝ)) * ∑ i : Fin k, f (X (n + (m - k) + i.val + 1) ω)|)^2 := by
            apply sq_le_sq'
            · have : 0 ≤ |(1 / (m : ℝ)) * ∑ i : Fin m, f (X (n + i.val + 1) ω)| +
                         |(1 / (k : ℝ)) * ∑ i : Fin k, f (X (n + (m - k) + i.val + 1) ω)| := by positivity
              have : -(|(1 / (m : ℝ)) * ∑ i : Fin m, f (X (n + i.val + 1) ω)| +
                      |(1 / (k : ℝ)) * ∑ i : Fin k, f (X (n + (m - k) + i.val + 1) ω)|) ≤
                     (1 / (m : ℝ)) * ∑ i : Fin m, f (X (n + i.val + 1) ω) -
                     (1 / (k : ℝ)) * ∑ i : Fin k, f (X (n + (m - k) + i.val + 1) ω) :=
                neg_le_of_abs_le ha
              linarith
            · exact le_of_abs_le ha
      _ ≤ (M + M)^2 := by
          apply sq_le_sq'
          · have hM_nonneg : 0 ≤ M := by
              have : |f 0| ≤ M := hM 0
              exact le_trans (abs_nonneg _) this
            have : 0 ≤ M + M := by linarith
            have h_sum_bound : |(1 / (m : ℝ)) * ∑ i : Fin m, f (X (n + i.val + 1) ω)| +
                               |(1 / (k : ℝ)) * ∑ i : Fin k, f (X (n + (m - k) + i.val + 1) ω)| ≤ M + M := by
              linarith [h1, h2]
            have : -(M + M) ≤ |(1 / (m : ℝ)) * ∑ i : Fin m, f (X (n + i.val + 1) ω)| +
                               |(1 / (k : ℝ)) * ∑ i : Fin k, f (X (n + (m - k) + i.val + 1) ω)| := by
              have h_nonneg : 0 ≤ |(1 / (m : ℝ)) * ∑ i : Fin m, f (X (n + i.val + 1) ω)| +
                                   |(1 / (k : ℝ)) * ∑ i : Fin k, f (X (n + (m - k) + i.val + 1) ω)| := by positivity
              linarith [h_nonneg, hM_nonneg]
            linarith [h_sum_bound]
          · linarith [h1, h2]
      _ = (2 * M)^2 := by ring
      _ ≤ (4 * M)^2 := by
          apply sq_le_sq'
          · have hM_nonneg : 0 ≤ M := by
              -- |f 0| ≤ M implies 0 ≤ M
              have : |f 0| ≤ M := hM 0
              exact le_trans (abs_nonneg _) this
            have : 0 ≤ 4 * M := by linarith
            linarith [this, hM_nonneg]
          · have hM_nonneg : 0 ≤ M := by
              have : |f 0| ≤ M := hM 0
              exact le_trans (abs_nonneg _) this
            linarith [hM_nonneg]

  -- The key insight: We can bound this by decomposing the long average
  -- and using triangle inequality with a common window of size k

  -- Introduce an intermediate window: (1/k) * ∑_{i<k} f(X_{n+i+1})
  -- Then: |long_avg - tail_avg|² ≤ 2|long_avg - window_avg|² + 2|window_avg - tail_avg|²

  -- The second term |window_avg - tail_avg|² can be bounded by hCf_unif since
  -- both are equal-weight windows of size k at positions n and n+(m-k)

  -- For the first term, we use that the long average (1/m) is close to any k-window (1/k)
  -- This follows from the fact that the long average is a weighted combination that
  -- includes the k-window with smaller weight

  -- However, the cleanest approach requires more machinery about weighted averages
  -- For now, we have established the integrand is bounded, which is the key
  -- integrability property needed for the convergence proof

  -- Apply l2_contractability_bound with weight vectors:
  --   p = (1/m, 1/m, ..., 1/m)  [m terms]
  --   q = (0, ..., 0, 1/k, ..., 1/k)  [m-k zeros, then k terms of 1/k]
  -- The sup |p - q| = 1/k, giving bound 2σ²(1-ρ) · (1/k) = Cf/k

  -- Use the provided covariance structure (passed as arguments)
  -- We need to relate this to Cf from the hypothesis
  -- Actually, hCf_unif tells us the bound is Cf/k, so we can deduce what Cf must be

  -- Define the sequence ξ on m elements
  let ξ : Fin m → Ω → ℝ := fun i ω => f (X (n + i.val + 1) ω)

  -- Define weight vectors p and q
  let p : Fin m → ℝ := fun _ => 1 / (m : ℝ)
  let q : Fin m → ℝ := fun i => if i.val < m - k then 0 else 1 / (k : ℝ)

  -- Verify these are probability distributions
  have hp_prob : (∑ i : Fin m, p i) = 1 ∧ ∀ i, 0 ≤ p i := by
    constructor
    · simp only [p, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
      have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr (Nat.lt_of_lt_of_le hk hkm)
      field_simp [ne_of_gt hm_pos]
    · intro i; simp only [p]; positivity

  have hq_prob : (∑ i : Fin m, q i) = 1 ∧ ∀ i, 0 ≤ q i := by
    constructor
    · -- Sum equals 1: only terms with i.val ≥ m-k contribute
      calc ∑ i : Fin m, q i
        = ∑ i ∈ Finset.filter (fun i => i.val < m - k) Finset.univ, q i +
          ∑ i ∈ Finset.filter (fun i => ¬(i.val < m - k)) Finset.univ, q i := by
            rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ) (p := fun i => i.val < m - k)]
      _ = 0 + ∑ i ∈ Finset.filter (fun i : Fin m => ¬(i.val < m - k)) Finset.univ, (1/(k:ℝ)) := by
            congr 1
            · apply Finset.sum_eq_zero
              intro i hi
              have : i.val < m - k := Finset.mem_filter.mp hi |>.2
              simp [q, this]
            · apply Finset.sum_congr rfl
              intro i hi
              have : ¬(i.val < m - k) := Finset.mem_filter.mp hi |>.2
              simp [q, this]
      _ = (Finset.filter (fun i : Fin m => ¬(i.val < m - k)) Finset.univ).card * (1/(k:ℝ)) := by
            simp [Finset.sum_const]
      _ = k * (1/(k:ℝ)) := by
            congr 1
            -- The number of i with i.val ≥ m-k is k
            have : (Finset.filter (fun i : Fin m => ¬(i.val < m - k)) Finset.univ).card = k := by
              have h_eq : Finset.filter (fun i : Fin m => ¬(i.val < m - k)) Finset.univ =
                          Finset.image (fun (j : Fin k) => (⟨(m - k) + j.val, by omega⟩ : Fin m)) Finset.univ := by
                ext i
                simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, not_lt]
                constructor
                · intro hi
                  use ⟨i.val - (m - k), by omega⟩
                  simp only []
                  ext; simp; omega
                · rintro ⟨j, _, rfl⟩
                  simp
              rw [h_eq, Finset.card_image_of_injective]
              · simp only [Finset.card_fin]
              · intro a b hab
                simp only [Fin.mk.injEq] at hab
                exact Fin.ext (by omega)
            simpa
      _ = 1 := by
            have hk_pos : (0:ℝ) < k := Nat.cast_pos.mpr hk
            field_simp [ne_of_gt hk_pos]
    · intro i; simp [q]; split_ifs <;> positivity

  -- Now we need to verify that ξ has the covariance structure
  have hξ_mean : ∀ i, ∫ ω, ξ i ω ∂μ = mf := by
    intro i
    simp [ξ]
    exact hmean (n + i.val + 1)

  have hξ_L2 : ∀ i, MemLp (fun ω => ξ i ω - mf) 2 μ := by
    intro i
    -- Reconstruct MemLp from boundedness (M, hM already available from line 1690)
    have : MemLp (fun ω => f (X (n + i.val + 1) ω)) 2 μ := by
      apply MemLp.of_bound (hf_meas.comp (hX_meas (n + i.val + 1))).aestronglyMeasurable M
      filter_upwards with ω
      simp [Real.norm_eq_abs]
      exact hM (X (n + i.val + 1) ω)
    simpa [ξ] using this.sub (memLp_const mf)

  have hξ_var : ∀ i, ∫ ω, (ξ i ω - mf)^2 ∂μ = (Real.sqrt σSqf) ^ 2 := by
    intro i
    simp [ξ]
    have : (Real.sqrt σSqf) ^ 2 = σSqf := Real.sq_sqrt hσSq_nonneg
    rw [this]
    exact hvar (n + i.val + 1)

  have hξ_cov : ∀ i j, i ≠ j → ∫ ω, (ξ i ω - mf) * (ξ j ω - mf) ∂μ = (Real.sqrt σSqf) ^ 2 * ρf := by
    intro i j hij
    simp [ξ]
    have : (Real.sqrt σSqf) ^ 2 = σSqf := Real.sq_sqrt hσSq_nonneg
    rw [this]
    apply hcov
    omega

  -- Apply l2_contractability_bound
  have h_bound := @L2Approach.l2_contractability_bound Ω _ μ _ m ξ mf
    (Real.sqrt σSqf) ρf hρ_bd hξ_mean hξ_L2 hξ_var hξ_cov p q hp_prob hq_prob

  -- Compute the supremum |p - q|
  -- p i = 1/m for all i
  -- q i = 0 if i.val < m - k, else 1/k
  -- So |p i - q i| = 1/m if i.val < m - k
  --                = |1/m - 1/k| if i.val ≥ m - k
  -- Since k ≤ m - k (from hkm), we have m ≥ 2k, so 1/k > 1/m
  -- Thus |1/m - 1/k| = 1/k - 1/m
  -- Therefore: sup |p i - q i| = max(1/m, 1/k - 1/m) = 1/k - 1/m
  --
  -- For the proof, we bound: 1/k - 1/m ≤ 1/k
  -- This gives a slightly looser but still valid bound
  have h_sup_bound : (⨆ i : Fin m, |p i - q i|) ≤ 1 / (k : ℝ) := by
    -- Show that for all i, |p i - q i| ≤ 1/k
    haveI : Nonempty (Fin m) := by
      apply Fin.pos_iff_nonempty.mp
      exact Nat.lt_of_lt_of_le hk hkm
    apply ciSup_le
    intro i
    simp only [p, q]
    have hk_pos : (0:ℝ) < k := Nat.cast_pos.mpr hk
    have hm_pos : (0:ℝ) < m := Nat.cast_pos.mpr (Nat.lt_of_lt_of_le hk hkm)
    split_ifs with hi
    · -- Case: i.val < m - k, so |1/m - 0| = 1/m ≤ 1/k
      simp only [sub_zero]
      rw [abs_of_pos (by positivity : (0:ℝ) < 1/m)]
      -- 1/m ≤ 1/k follows from k ≤ m
      -- Use: 1/a ≤ 1/b ↔ b ≤ a (for positive a, b)
      rw [one_div_le_one_div hm_pos hk_pos]
      exact Nat.cast_le.mpr hkm
    · -- Case: i.val ≥ m - k, so |1/m - 1/k| ≤ 1/k
      -- Since k ≤ m, we have 1/k ≥ 1/m, so 1/m - 1/k ≤ 0, thus |1/m - 1/k| = 1/k - 1/m
      have h_div_order : (1:ℝ)/m ≤ 1/k := by
        rw [one_div_le_one_div hm_pos hk_pos]
        exact Nat.cast_le.mpr hkm
      -- abs_of_nonpos: |1/m - 1/k| = -(1/m - 1/k) = 1/k - 1/m when 1/m - 1/k ≤ 0
      rw [abs_of_nonpos (by linarith : (1:ℝ)/m - 1/k ≤ 0)]
      -- Goal: 1/k - 1/m ≤ 1/k, which simplifies to 0 ≤ 1/m
      -- Since m > 0, we have 1/m > 0
      have : (0:ℝ) < 1/m := by positivity
      linarith

  -- The bound from l2_contractability_bound is 2·σSqf·(1-ρf)·(⨆ i, |p i - q i|)
  -- We have h_sup_bound : (⨆ i, |p i - q i|) ≤ 1/k
  -- So we can bound by 2·σSqf·(1-ρf)·(1/k)

  -- Now we need to show this is bounded by Cf/k
  -- The hypothesis hCf_unif tells us that for any two k-windows,
  -- the L² distance is ≤ Cf/k
  -- By the definition of contractability and the L² approach, Cf = 2·σSqf·(1-ρf)

  -- Simplify (Real.sqrt σSqf)^2 = σSqf
  have h_sqrt_sq : (Real.sqrt σSqf) ^ 2 = σSqf := Real.sq_sqrt hσSq_nonneg

  -- Strengthen h_bound using h_sup_bound
  have h_bound_strengthened : ∫ ω, (∑ i, p i * ξ i ω - ∑ i, q i * ξ i ω)^2 ∂μ ≤
      2 * σSqf * (1 - ρf) * (1 / (k : ℝ)) := by
    calc ∫ ω, (∑ i, p i * ξ i ω - ∑ i, q i * ξ i ω)^2 ∂μ
      ≤ 2 * (Real.sqrt σSqf) ^ 2 * (1 - ρf) * (⨆ i, |p i - q i|) := h_bound
    _ ≤ 2 * (Real.sqrt σSqf) ^ 2 * (1 - ρf) * (1 / (k : ℝ)) := by
        apply mul_le_mul_of_nonneg_left h_sup_bound
        apply mul_nonneg
        · apply mul_nonneg
          · linarith
          · exact sq_nonneg _
        · linarith [hρ_bd.2]
    _ = 2 * σSqf * (1 - ρf) * (1 / (k : ℝ)) := by rw [h_sqrt_sq]

  -- Now verify that the LHS of h_bound equals our goal's LHS
  have h_lhs_eq : (∫ ω, (∑ i, p i * ξ i ω - ∑ i, q i * ξ i ω)^2 ∂μ) =
      ∫ ω, ((1 / (m : ℝ)) * ∑ i : Fin m, f (X (n + i.val + 1) ω) -
            (1 / (k : ℝ)) * ∑ i : Fin k, f (X (n + (m - k) + i.val + 1) ω))^2 ∂μ := by
    congr 1
    ext ω
    congr 1
    -- Expand definitions of p, q, ξ
    simp only [p, q, ξ]
    -- LHS: ∑ i, p i * ξ i ω = ∑ i, (1/m) * f(X(n + i.val + 1) ω) = (1/m) * ∑ i, f(X(...))
    rw [show ∑ i : Fin m, (1 / (m : ℝ)) * f (X (n + i.val + 1) ω) =
             (1 / (m : ℝ)) * ∑ i : Fin m, f (X (n + i.val + 1) ω)
        by rw [← Finset.mul_sum]]
    -- RHS: ∑ i, q i * ξ i ω where q i = 0 if i.val < m-k, else 1/k
    -- So this equals ∑_{i : i.val ≥ m-k} (1/k) * f(X(n + i.val + 1) ω)
    -- Reindex: when i.val ≥ m-k, write i.val = (m-k) + j for j ∈ [0, k)
    have h_q_sum : ∑ i : Fin m, q i * f (X (n + i.val + 1) ω) =
        (1 / (k : ℝ)) * ∑ i : Fin k, f (X (n + (m - k) + i.val + 1) ω) := by
      -- Split sum based on whether i.val < m - k
      calc ∑ i : Fin m, q i * f (X (n + i.val + 1) ω)
        = ∑ i ∈ Finset.filter (fun i => i.val < m - k) Finset.univ, q i * f (X (n + i.val + 1) ω) +
          ∑ i ∈ Finset.filter (fun i => ¬(i.val < m - k)) Finset.univ, q i * f (X (n + i.val + 1) ω) := by
            rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ) (p := fun i => i.val < m - k)]
      _ = 0 + ∑ i ∈ Finset.filter (fun i : Fin m => ¬(i.val < m - k)) Finset.univ,
            (1 / (k : ℝ)) * f (X (n + i.val + 1) ω) := by
            congr 1
            · apply Finset.sum_eq_zero
              intro i hi
              have : i.val < m - k := Finset.mem_filter.mp hi |>.2
              simp [q, this]
            · apply Finset.sum_congr rfl
              intro i hi
              have : ¬(i.val < m - k) := Finset.mem_filter.mp hi |>.2
              simp [q, this]
      _ = (1 / (k : ℝ)) * ∑ i : Fin k, f (X (n + (m - k) + i.val + 1) ω) := by
            simp only [zero_add]
            rw [← Finset.mul_sum]
            congr 1
            -- Reindex: i with i.val ≥ m-k ↔ i = ⟨(m-k) + j.val, _⟩ for j : Fin k
            -- The filtered set equals the image of the map j ↦ ⟨(m-k) + j, _⟩
            trans (∑ i ∈ Finset.image (fun (j : Fin k) => (⟨(m - k) + j.val, by omega⟩ : Fin m)) Finset.univ,
                    f (X (n + i.val + 1) ω))
            · congr 1
              ext i
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
              constructor
              · intro hi
                use ⟨i.val - (m - k), by omega⟩
                simp only
                ext
                simp only
                omega
              · rintro ⟨j, _, rfl⟩
                simp only
                omega
            · -- Now the sum is over an image, apply sum_image with injectivity
              rw [Finset.sum_image]
              · congr 1
                ext j
                simp only
                ring
              -- Prove injectivity
              · intro j₁ _ j₂ _ h
                simp only [Fin.mk.injEq] at h
                exact Fin.ext (by omega)
    rw [h_q_sum]

  -- Prove the bound directly using the provided Cf
  calc ∫ ω, ((1 / (m : ℝ)) * ∑ i : Fin m, f (X (n + i.val + 1) ω) -
              (1 / (k : ℝ)) * ∑ i : Fin k, f (X (n + (m - k) + i.val + 1) ω))^2 ∂μ
      = ∫ ω, (∑ i, p i * ξ i ω - ∑ i, q i * ξ i ω)^2 ∂μ := h_lhs_eq.symm
    _ ≤ 2 * σSqf * (1 - ρf) * (1 / (k : ℝ)) := h_bound_strengthened
    _ = Cf / k := by rw [hCf_def]; ring

/-!
## Tail σ-algebra for sequences

Now using the canonical definitions from `Exchangeability.Tail.TailSigma`.

For backward compatibility in this file, we create a namespace with re-exports:
- `TailSigma.tailFamily X n` := `Tail.tailFamily X n` (future σ-algebra from index n onward)
- `TailSigma.tailSigma X` := `Tail.tailProcess X` (tail σ-algebra)
-/

namespace TailSigma

-- Re-export the definitions for backward compatibility
def tailFamily := @Exchangeability.Tail.tailFamily
def tailSigma := @Exchangeability.Tail.tailProcess

-- Re-export the lemmas for backward compatibility
lemma antitone_tailFamily {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    (X : ℕ → Ω → β) : Antitone (tailFamily X) :=
  Exchangeability.Tail.tailFamily_antitone X

lemma tailSigma_le_tailFamily {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    (X : ℕ → Ω → β) (n : ℕ) : tailSigma X ≤ tailFamily X n :=
  Exchangeability.Tail.tailProcess_le_tailFamily X n

lemma tailSigma_le {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    (X : ℕ → Ω → β) (hX_meas : ∀ i, Measurable (X i)) :
    tailSigma X ≤ (inferInstance : MeasurableSpace Ω) :=
  Exchangeability.Tail.tailProcess_le_ambient X hX_meas

end TailSigma

/-! ## Helper axioms (early section)

Axioms that don't depend on later definitions can go here.
-/

namespace Helpers

open Exchangeability.Probability.IntegrationHelpers

/-- **THEOREM (Subsequence a.e. convergence from L¹):**
If `αₙ → α` in L¹ (with measurability), there is a subsequence converging to `α`
almost everywhere.

This follows from the standard result that L¹ convergence implies convergence in measure,
and convergence in measure implies existence of an a.e. convergent subsequence. -/
theorem subseq_ae_of_L1
  {Ω : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  (alpha : ℕ → Ω → ℝ) (alpha_inf : Ω → ℝ)
  (h_alpha_meas : ∀ n, Measurable (alpha n))
  (h_alpha_inf_meas : Measurable alpha_inf)
  (h_integrable : ∀ n, Integrable (fun ω => alpha n ω - alpha_inf ω) μ)
  (h_L1_conv : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∫ ω, |alpha n ω - alpha_inf ω| ∂μ < ε) :
  ∃ (φ : ℕ → ℕ), StrictMono φ ∧
    ∀ᵐ ω ∂μ, Tendsto (fun k => alpha (φ k) ω) atTop (𝓝 (alpha_inf ω)) := by
  -- Step 1: Convert L¹ convergence to convergence in eLpNorm
  -- Use the fact that for integrable functions, eLpNorm 1 = ofReal (∫ |·|)
  -- Then transfer convergence via continuous_ofReal
  have h_eLpNorm_tendsto : Tendsto (fun n => eLpNorm (alpha n - alpha_inf) 1 μ) atTop (𝓝 0) := by
    -- First show the Bochner integral tends to 0
    have h_integral_tendsto : Tendsto (fun n => ∫ ω, |alpha n ω - alpha_inf ω| ∂μ) atTop (𝓝 0) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨N, hN⟩ := h_L1_conv ε hε
      use N
      intro n hn
      rw [Real.dist_eq, sub_zero, abs_of_nonneg]
      · exact hN n hn
      · exact integral_nonneg (fun ω => abs_nonneg _)

    -- Now transfer convergence via eLpNorm_one_eq_integral_abs and continuity of ofReal
    have : Tendsto (fun n => ENNReal.ofReal (∫ ω, |alpha n ω - alpha_inf ω| ∂μ)) atTop (𝓝 0) := by
      rw [← ENNReal.ofReal_zero]
      exact ENNReal.tendsto_ofReal h_integral_tendsto
    have h_eq : ∀ n, eLpNorm (alpha n - alpha_inf) 1 μ = ENNReal.ofReal (∫ ω, |alpha n ω - alpha_inf ω| ∂μ) := by
      intro n; exact eLpNorm_one_eq_integral_abs (h_integrable n)
    simp only [h_eq]
    exact this

  -- Step 2: eLpNorm convergence implies convergence in measure
  have h_tendstoInMeasure : TendstoInMeasure μ alpha atTop alpha_inf := by
    exact tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero
      (fun n => (h_alpha_meas n).aestronglyMeasurable)
      h_alpha_inf_meas.aestronglyMeasurable
      h_eLpNorm_tendsto

  -- Step 3: Extract almost-everywhere convergent subsequence
  exact h_tendstoInMeasure.exists_seq_tendsto_ae

/-- **AXIOM A10 (Step 5 packaging):** packaged existence of a directing kernel
with the pointwise identification for a given bounded measurable `f`. -/
axiom alpha_is_conditional_expectation_packaged
  {Ω : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  (X : ℕ → Ω → ℝ) (hX_contract : Exchangeability.Contractable μ X)
  (hX_meas : ∀ i, Measurable (X i))
  (f : ℝ → ℝ) (hf_meas : Measurable f) (alpha : ℕ → Ω → ℝ) :
  ∃ (nu : Ω → Measure ℝ),
    (∀ ω, IsProbabilityMeasure (nu ω)) ∧
    Measurable (fun ω => nu ω (Set.univ)) ∧
    (∀ n, ∀ᵐ ω ∂μ, alpha n ω = ∫ x, f x ∂(nu ω))

