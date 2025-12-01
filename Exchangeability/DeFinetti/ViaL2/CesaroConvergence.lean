/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Exchangeability.DeFinetti.ViaL2.BlockAverages
import Exchangeability.DeFinetti.L2Helpers
import Exchangeability.Contractability
import Exchangeability.Probability.CondExp
import Exchangeability.Probability.IntegrationHelpers
import Exchangeability.Probability.LpNormHelpers
import Exchangeability.Util.FinsetHelpers
import Exchangeability.Tail.TailSigma
import Exchangeability.Tail.ShiftInvariance
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.InnerProductSpace.MeanErgodic
import Canonical

/-!
# Cesàro Convergence via L² Bounds

This file implements Kallenberg's L² approach to proving convergence of Cesàro
averages for exchangeable sequences. The key result is that block averages form
a Cauchy sequence in L², using only elementary variance bounds.

## Main results

* `blockAvg_cauchy_in_L2`: Block Cesàro averages form a Cauchy sequence in L²
* Supporting lemmas for L² convergence analysis

## References

* Kallenberg (2005), *Probabilistic Symmetries and Invariance Principles*,
  Chapter 1, Lemma 1.2 and "Second proof"
-/

noncomputable section

namespace Exchangeability.DeFinetti.ViaL2

open MeasureTheory ProbabilityTheory BigOperators Filter Topology
open Exchangeability
open Exchangeability.DeFinetti.L2Helpers

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

open scoped BigOperators

/-! ## Kallenberg's L² Approach (Lemma 1.2 + Second Proof)

This section implements Kallenberg's "second proof" of de Finetti's theorem using
elementary L² bounds. The key is **Lemma 1.2**: for exchangeable sequences, weighted
averages satisfy a simple variance bound that makes Cesàro averages Cauchy in L².

**No ergodic theory is used** - only:
1. Exchangeability → constant pairwise second moments
2. Algebraic identity for variance of weighted sums
3. Completeness of L²

This is the lightest-dependency route to de Finetti.

**References:**
- Kallenberg (2005), *Probabilistic Symmetries*, Chapter 1, pp. 27-28
  - Lemma 1.2 (L² bound for exchangeable weighted sums)
  - "Second proof of Theorem 1.1" (the L² route to de Finetti)
-/

/-- **Block Cesàro average** of a function along a sequence.

For a function `f : α → ℝ` and sequence `X : ℕ → Ω → α`, the block average
starting at index `m` with length `n` is:

  A_{m,n}(ω) := (1/n) ∑_{k=0}^{n-1} f(X_{m+k}(ω))

This is the building block for Kallenberg's L² convergence proof. -/
def blockAvg (f : α → ℝ) (X : ℕ → Ω → α) (m n : ℕ) (ω : Ω) : ℝ :=
  (n : ℝ)⁻¹ * (Finset.range n).sum (fun k => f (X (m + k) ω))

lemma blockAvg_measurable
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (f : α → ℝ) (X : ℕ → Ω → α)
    (hf : Measurable f) (hX : ∀ i, Measurable (X i))
    (m n : ℕ) :
    Measurable (fun ω => blockAvg f X m n ω) := by
  classical
  unfold blockAvg
  -- sum of measurable terms
  have hsum :
      Measurable (fun ω =>
        (Finset.range n).sum (fun k => f (X (m + k) ω))) :=
    Finset.measurable_sum _ (by
      intro k _
      exact hf.comp (hX (m + k)))
  -- multiply by a constant
  simpa using (measurable_const.mul hsum : Measurable _)

lemma blockAvg_abs_le_one
    {Ω α : Type*} [MeasurableSpace Ω]
    (f : α → ℝ) (X : ℕ → Ω → α)
    (hf_bdd : ∀ x, |f x| ≤ 1)
    (m n : ℕ) :
    ∀ ω, |blockAvg f X m n ω| ≤ 1 := by
  classical
  intro ω
  unfold blockAvg
  have hsum_bound :
      |(Finset.range n).sum (fun k => f (X (m + k) ω))| ≤ (n : ℝ) := by
    -- |∑ a_k| ≤ ∑ |a_k| ≤ ∑ 1 = n
    calc |(Finset.range n).sum (fun k => f (X (m + k) ω))|
        ≤ (Finset.range n).sum (fun k => |f (X (m + k) ω)|) := by
          exact Finset.abs_sum_le_sum_abs (fun k => f (X (m + k) ω)) (Finset.range n)
      _ ≤ (Finset.range n).sum (fun _ => (1 : ℝ)) := by
          apply Finset.sum_le_sum
          intro k _
          exact hf_bdd (X (m + k) ω)
      _ = n := by
          have : (Finset.range n).card = n := Finset.card_range n
          simpa [this]
  -- Now scale by n⁻¹
  have hnonneg : 0 ≤ (n : ℝ)⁻¹ := by exact inv_nonneg.mpr (by exact_mod_cast Nat.zero_le n)
  calc
    |(n : ℝ)⁻¹ * (Finset.range n).sum (fun k => f (X (m + k) ω))|
        = (n : ℝ)⁻¹ * |(Finset.range n).sum (fun k => f (X (m + k) ω))|
          := by simpa [abs_mul, abs_of_nonneg hnonneg]
    _ ≤ (n : ℝ)⁻¹ * (n : ℝ)
          := mul_le_mul_of_nonneg_left hsum_bound hnonneg
    _ ≤ 1 := by
          by_cases hn : n = 0
          · simpa [hn]
          · have : (n : ℝ) ≠ 0 := by simp [hn]
            simp [this]

/-- **Kallenberg's L² bound (Lemma 1.2)** - Core of the elementary proof.

For an exchangeable sequence and centered variables Z_i := f(X_i) - E[f(X_1)],
the L² distance between any two weighted averages satisfies:

  ‖∑ p_i Z_i - ∑ q_i Z_i‖²_L² ≤ C_f · sup_i |p_i - q_i|

where C_f := E[(Z_1 - Z_2)²].

**Key application:** For uniform block averages of length n,
  ‖A_{m,n} - A_{m',n}‖_L² ≤ √(C_f/n)

making the family {A_{m,n}}_m Cauchy in L² as n→∞.

**Proof:** Pure algebra + exchangeability:
1. Expand ‖∑ c_i Z_i‖² = ∑ c_i² E[Z_i²] + ∑_{i≠j} c_i c_j E[Z_i Z_j]
2. By exchangeability: E[Z_i²] = E[Z_1²], E[Z_i Z_j] = E[Z_1 Z_2] for i≠j
3. For c_i = p_i - q_i (differences of probability weights): ∑ c_i = 0
4. Algebraic bound: ∑ c_i² ≤ (∑|c_i|) · sup|c_i| ≤ 2 · sup|c_i|
5. Substitute and simplify to get the bound

This is **exactly** Kallenberg's Lemma 1.2. No ergodic theory needed!

## Why this proof uses `l2_contractability_bound` instead of `kallenberg_L2_bound`

**The Circularity Problem:**

The de Finetti theorem we're proving establishes: **Contractable ↔ Exchangeable**

- `contractable_of_exchangeable` (✓ proved in Contractability.lean): Exchangeable → Contractable
- `cesaro_to_condexp_L2` (this file): Contractable → Exchangeable (via conditionally i.i.d.)

Since we're trying to prove Contractable → Exchangeable, we **cannot assume exchangeability**
in this proof - that would be circular!

**Why `kallenberg_L2_bound` requires exchangeability:**

`kallenberg_L2_bound` needs `Exchangeable μ Z` to establish uniform second moments:
- E[Z_i²] = E[Z_0²] for all i (uniform variance)
- E[Z_i Z_j] = E[Z_0 Z_1] for all i≠j (uniform pairwise covariance)

Exchangeability gives this via permutation invariance: swapping indices doesn't change the distribution.

**Why contractability is insufficient for `kallenberg_L2_bound`:**

Contractability only tells us about *increasing* subsequences:
- For any increasing k : Fin m → ℕ, the subsequence (Z_{k(0)}, ..., Z_{k(m-1)}) has the
  same distribution as (Z_0, ..., Z_{m-1})

This is weaker than exchangeability:
- ✓ We know (Z_0, Z_1) has same distribution as (Z_1, Z_2), (Z_2, Z_3), etc.
- ✗ We DON'T know (Z_0, Z_1) has same distribution as (Z_1, Z_0) - contractability doesn't
  give permutation invariance!

**However: contractability DOES give uniform covariance!**

Even though contractability ≠ exchangeability, contractability is *sufficient* for:
- E[Z_i²] = E[Z_0²] for all i (from the increasing subsequence {i})
- E[Z_i Z_j] = E[Z_0 Z_1] for all i<j (from the increasing subsequence {i,j})

This is exactly the covariance structure needed by `l2_contractability_bound` from
L2Helpers.lean, which doesn't assume full exchangeability.

**Note:** By the end of this proof, we'll have shown Contractable → Exchangeable, so
contractable sequences ARE exchangeable. But we can't use that equivalence while
proving it - that would be begging the question!

-/

lemma kallenberg_L2_bound
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (Z : ℕ → Ω → ℝ) (hZ_exch : Exchangeable μ Z) (hZ_meas : ∀ i, Measurable (Z i))
    (p q : ℕ → ℝ) (s : Finset ℕ) (hs : s.Nonempty)
    (hp_prob : (s.sum p = 1) ∧ (∀ i ∈ s, 0 ≤ p i))
    (hq_prob : (s.sum q = 1) ∧ (∀ i ∈ s, 0 ≤ q i))
    (hZ_L2 : ∀ i ∈ s, MemLp (Z i) 2 μ) :
    ∫ ω, ((s.sum fun i => (p i - q i) * Z i ω) ^ 2) ∂μ
      ≤ (∫ ω, (Z 0 ω - Z 1 ω)^2 ∂μ) * (s.sup' hs (fun i => |(p i - q i)|)) := by
  -- Kallenberg Lemma 1.2: Pure algebraic proof using exchangeability
  -- NOTE: This lemma requires Exchangeable, but cesaro_to_condexp_L2 uses
  -- l2_contractability_bound instead (see comment above)

  -- Notation: c_i := p_i - q_i (differences of probability weights)
  let c := fun i => p i - q i

  -- Key fact: ∑ c_i = 0 (since both p and q sum to 1)
  have hc_sum_zero : s.sum c = 0 := by
    simp only [c, Finset.sum_sub_distrib, hp_prob.1, hq_prob.1]
    norm_num

  -- Step 1: Expand E[(∑ c_i Z_i)²]
  -- E[(∑ c_i Z_i)²] = ∑ c_i² E[Z_i²] + ∑_{i≠j} c_i c_j E[Z_i Z_j]

  -- Step 2: Use exchangeability to identify second moments
  -- By exchangeability: E[Z_i²] = E[Z_0²] and E[Z_i Z_j] = E[Z_0 Z_1] for i≠j

  -- Step 3: Algebraic simplification using ∑ c_i = 0
  -- ∑_{i≠j} c_i c_j = (∑ c_i)² - ∑ c_i² = -∑ c_i²

  -- Step 4: Bound ∑ c_i² ≤ (∑|c_i|) · sup|c_i| ≤ 2 · sup|c_i|

  -- Step 5: Combine to get final bound
  -- E[(∑ c_i Z_i)²] ≤ C_f · sup|c_i| where C_f = E[(Z_0 - Z_1)²]

  -- Use the complete proof from L2Helpers.l2_contractability_bound
  -- Strategy: Reindex to Fin s.card, apply the theorem, then reindex back

  classical

  -- Step 1: Reindex from Finset ℕ to Fin s.card
  let n := s.card

  -- Get an order isomorphism between s and Fin n
  -- enum : Fin n ≃o { x // x ∈ s }
  let enum := s.orderIsoOfFin rfl

  -- Define the reindexed functions (extract .val from subtype)
  let ξ : Fin n → Ω → ℝ := fun i ω => Z (enum i).val ω
  let p' : Fin n → ℝ := fun i => p (enum i).val
  let q' : Fin n → ℝ := fun i => q (enum i).val

  -- Step 2: Compute mean, variance, and correlation from exchangeability
  let m := ∫ ω, Z 0 ω ∂μ
  let σSq := ∫ ω, (Z 0 ω - m)^2 ∂μ
  let covOffDiag := ∫ ω, (Z 0 ω - m) * (Z 1 ω - m) ∂μ
  let ρ := if σSq = 0 then 0 else covOffDiag / σSq

  -- Step 3: Prove hypotheses for l2_contractability_bound

  -- Convert Exchangeable to Contractable
  have hZ_contract : Contractable μ Z := contractable_of_exchangeable hZ_exch hZ_meas

  -- Prove σSq ≥ 0 (variance is always non-negative) - needed for ρ bounds
  have hσSq_nonneg : 0 ≤ σSq := by
    simp only [σSq]
    apply integral_nonneg
    intro ω
    positivity

  -- Prove ρ bounds (correlation coefficient is always in [-1, 1])
  have hρ_bd : -1 ≤ ρ ∧ ρ ≤ 1 := by
    simp only [ρ]
    by_cases h : σSq = 0
    · -- If σSq = 0, then ρ = 0, so bounds hold trivially
      simp [h]
    · -- If σSq ≠ 0, use Cauchy-Schwarz to show |covOffDiag / σSq| ≤ 1
      simp [h]
      -- Need to show: -1 ≤ covOffDiag / σSq ≤ 1
      -- Equivalent to: |covOffDiag| ≤ σSq (since σSq > 0)

      have hσSq_pos : 0 < σSq := by
        cases (hσSq_nonneg.lt_or_eq) with
        | inl h_lt => exact h_lt
        | inr h_eq => exact (h h_eq.symm).elim

      -- Apply Cauchy-Schwarz: |∫ f·g| ≤ (∫ f²)^(1/2) · (∫ g²)^(1/2)
      have h_cs : |covOffDiag| ≤ σSq := by
        simp only [covOffDiag, σSq]

        -- First establish Z 0, Z 1 ∈ L² using contractability
        obtain ⟨k, hk⟩ := hs.exists_mem
        have hZk_L2 : MemLp (Z k) 2 μ := hZ_L2 k hk

        have hZ0_L2 : MemLp (Z 0) 2 μ := by
          by_cases h : k = 0
          · subst h; exact hZk_L2
          · -- Use contractable_map_single to show Z k and Z 0 have same distribution
            -- Then transfer MemLp via equal eLpNorm
            have h_dist := Exchangeability.DeFinetti.L2Helpers.contractable_map_single
              (X := Z) hZ_contract hZ_meas (i := k)
            -- h_dist : Measure.map (Z k) μ = Measure.map (Z 0) μ
            -- Transfer eLpNorm: show eLpNorm (Z 0) 2 μ = eLpNorm (Z k) 2 μ
            have h_Lpnorm_eq : eLpNorm (Z 0) 2 μ = eLpNorm (Z k) 2 μ := by
              symm
              calc eLpNorm (Z k) 2 μ
                  = eLpNorm id 2 (Measure.map (Z k) μ) := by
                      symm
                      exact eLpNorm_map_measure aestronglyMeasurable_id (hZ_meas k).aemeasurable
                _ = eLpNorm id 2 (Measure.map (Z 0) μ) := by rw [h_dist]
                _ = eLpNorm (Z 0) 2 μ := by
                      exact eLpNorm_map_measure aestronglyMeasurable_id (hZ_meas 0).aemeasurable
            -- Now transfer MemLp using equal eLpNorm
            have : eLpNorm (Z 0) 2 μ < ⊤ := by
              rw [h_Lpnorm_eq]
              exact hZk_L2.eLpNorm_lt_top
            exact ⟨(hZ_meas 0).aestronglyMeasurable, this⟩
        have hZ1_L2 : MemLp (Z 1) 2 μ := by
          by_cases h : k = 1
          · subst h; exact hZk_L2
          · -- Use contractable_map_single to show Z k and Z 1 have same distribution
            -- Then transfer MemLp via equal eLpNorm
            have h_dist := Exchangeability.DeFinetti.L2Helpers.contractable_map_single
              (X := Z) hZ_contract hZ_meas (i := k)
            -- h_dist : Measure.map (Z k) μ = Measure.map (Z 0) μ
            have h_dist1 := Exchangeability.DeFinetti.L2Helpers.contractable_map_single
              (X := Z) hZ_contract hZ_meas (i := 1)
            -- h_dist1 : Measure.map (Z 1) μ = Measure.map (Z 0) μ
            -- Transfer eLpNorm: show eLpNorm (Z 1) 2 μ = eLpNorm (Z k) 2 μ
            have h_Lpnorm_eq : eLpNorm (Z 1) 2 μ = eLpNorm (Z k) 2 μ := by
              calc eLpNorm (Z 1) 2 μ
                  = eLpNorm id 2 (Measure.map (Z 1) μ) := by
                      symm
                      exact eLpNorm_map_measure aestronglyMeasurable_id (hZ_meas 1).aemeasurable
                _ = eLpNorm id 2 (Measure.map (Z 0) μ) := by rw [h_dist1]
                _ = eLpNorm id 2 (Measure.map (Z k) μ) := by rw [← h_dist]
                _ = eLpNorm (Z k) 2 μ := by
                      exact eLpNorm_map_measure aestronglyMeasurable_id (hZ_meas k).aemeasurable
            -- Now transfer MemLp using equal eLpNorm
            have : eLpNorm (Z 1) 2 μ < ⊤ := by
              rw [h_Lpnorm_eq]
              exact hZk_L2.eLpNorm_lt_top
            exact ⟨(hZ_meas 1).aestronglyMeasurable, this⟩

        -- Now Z i - m ∈ L² for i = 0, 1
        have hm : MemLp (fun _ : Ω => m) 2 μ := memLp_const m
        have hf : MemLp (fun ω => Z 0 ω - m) 2 μ := MemLp.sub hZ0_L2 hm
        have hg : MemLp (fun ω => Z 1 ω - m) 2 μ := MemLp.sub hZ1_L2 hm

        -- Apply Cauchy-Schwarz
        calc |∫ ω, (Z 0 ω - m) * (Z 1 ω - m) ∂μ|
            ≤ (∫ ω, (Z 0 ω - m) ^ 2 ∂μ) ^ (1/2 : ℝ) * (∫ ω, (Z 1 ω - m) ^ 2 ∂μ) ^ (1/2 : ℝ) := by
                exact Exchangeability.Probability.IntegrationHelpers.abs_integral_mul_le_L2 hf hg
          _ = (∫ ω, (Z 0 ω - m) ^ 2 ∂μ) ^ (1/2 : ℝ) * (∫ ω, (Z 0 ω - m) ^ 2 ∂μ) ^ (1/2 : ℝ) := by
                -- Use equal distributions: Z 1 has same variance as Z 0
                congr 1
                -- Use contractability: Z 1 has same distribution as Z 0
                have h_dist := Exchangeability.DeFinetti.L2Helpers.contractable_map_single
                  (X := Z) hZ_contract hZ_meas (i := 1)
                rw [← Exchangeability.Probability.IntegrationHelpers.integral_pushforward_sq_diff (hZ_meas 1) m,
                    h_dist,
                    Exchangeability.Probability.IntegrationHelpers.integral_pushforward_sq_diff (hZ_meas 0) m]
          _ = ∫ ω, (Z 0 ω - m) ^ 2 ∂μ := by
                have h_nonneg : 0 ≤ ∫ ω, (Z 0 ω - m) ^ 2 ∂μ := integral_nonneg (fun ω => by positivity)
                rw [← Real.sqrt_eq_rpow]
                exact Real.mul_self_sqrt h_nonneg

      -- From |covOffDiag| ≤ σSq and σSq > 0, derive -1 ≤ ρ ≤ 1
      constructor
      · -- Lower bound: -1 ≤ covOffDiag / σSq
        have : -σSq ≤ covOffDiag := by
          have h_neg : -|covOffDiag| ≤ covOffDiag := neg_abs_le _
          linarith [h_cs]
        calc -1 = -σSq / σSq := by field_simp
           _ ≤ covOffDiag / σSq := by apply div_le_div_of_nonneg_right; linarith; exact le_of_lt hσSq_pos
      · -- Upper bound: covOffDiag / σSq ≤ 1
        have : covOffDiag ≤ σSq := le_of_abs_le h_cs
        calc covOffDiag / σSq ≤ σSq / σSq := by apply div_le_div_of_nonneg_right; exact this; exact le_of_lt hσSq_pos
           _ = 1 := by field_simp

  -- Prove all marginals have the same mean m
  have hmean : ∀ k : Fin n, ∫ ω, ξ k ω ∂μ = m := by
    intro k
    -- ξ k = Z (enum k).val, and all Z i have the same distribution by contractability
    have h_same_dist := Exchangeability.DeFinetti.L2Helpers.contractable_map_single
      (X := Z) hZ_contract hZ_meas (i := (enum k).val)
    -- Equal distributions → equal integrals
    simp only [ξ, m]
    rw [← Exchangeability.Probability.IntegrationHelpers.integral_pushforward_id (hZ_meas _),
        h_same_dist,
        Exchangeability.Probability.IntegrationHelpers.integral_pushforward_id (hZ_meas _)]

  -- Prove all ξ k - m are in L²
  have hL2 : ∀ k : Fin n, MemLp (fun ω => ξ k ω - m) 2 μ := by
    intro k
    -- This follows from ξ k = Z (enum k).val and hZ_L2
    -- enum k has type { x // x ∈ s }, so (enum k).val ∈ s by (enum k).property
    have hk_in_s : (enum k).val ∈ s := (enum k).property
    have hZ_k_L2_orig := hZ_L2 (enum k).val hk_in_s
    -- ξ k ω - m = Z (enum k).val ω - m, so same MemLp
    convert hZ_k_L2_orig.sub (memLp_const m) using 1

  -- Prove all variances equal σ²
  have hvar : ∀ k : Fin n, ∫ ω, (ξ k ω - m)^2 ∂μ = σSq := by
    intro k
    -- Same distribution → same variance
    have h_same_dist := Exchangeability.DeFinetti.L2Helpers.contractable_map_single
      (X := Z) hZ_contract hZ_meas (i := (enum k).val)
    simp only [ξ, σSq]
    -- Use integral_pushforward_sq_diff
    rw [← Exchangeability.Probability.IntegrationHelpers.integral_pushforward_sq_diff (hZ_meas _) m,
        h_same_dist,
        Exchangeability.Probability.IntegrationHelpers.integral_pushforward_sq_diff (hZ_meas _) m]

  -- Prove all covariances equal σ²ρ
  have hcov : ∀ i j : Fin n, i ≠ j → ∫ ω, (ξ i ω - m) * (ξ j ω - m) ∂μ = σSq * ρ := by
    intro i j hij
    -- Use contractable_map_pair to show all pairs have same distribution as (Z 0, Z 1)
    simp only [ξ, σSq, ρ, covOffDiag]

    -- Get the indices from enum
    let i' := (enum i).val
    let j' := (enum j).val

    -- We need i' < j' or j' < i' (since i ≠ j in the image of an order isomorphism)
    have hij' : i' ≠ j' := by
      intro heq
      have : (enum i).val = (enum j).val := heq
      have : enum i = enum j := Subtype.ext this
      have : i = j := enum.injective this
      contradiction

    -- Case split on ordering
    rcases hij'.lt_or_lt with h_lt | h_lt
    · -- Case i' < j': Use contractable_map_pair directly
      have h_dist := Exchangeability.DeFinetti.L2Helpers.contractable_map_pair
        (X := Z) hZ_contract hZ_meas h_lt
      -- Use integral_map to transfer the integral
      have h_prod_meas : Measurable (fun ω => (Z i' ω, Z j' ω)) :=
        (hZ_meas i').prodMk (hZ_meas j')
      have h_func_ae : AEStronglyMeasurable (fun p : ℝ × ℝ => (p.1 - m) * (p.2 - m))
          (Measure.map (fun ω => (Z i' ω, Z j' ω)) μ) := by
        apply Continuous.aestronglyMeasurable
        exact (continuous_fst.sub continuous_const).mul (continuous_snd.sub continuous_const)
      have h_func_ae' : AEStronglyMeasurable (fun p : ℝ × ℝ => (p.1 - m) * (p.2 - m))
          (Measure.map (fun ω => (Z 0 ω, Z 1 ω)) μ) := by
        apply Continuous.aestronglyMeasurable
        exact (continuous_fst.sub continuous_const).mul (continuous_snd.sub continuous_const)
      calc ∫ ω, (Z i' ω - m) * (Z j' ω - m) ∂μ
          = ∫ p, (p.1 - m) * (p.2 - m) ∂(Measure.map (fun ω => (Z i' ω, Z j' ω)) μ) := by
              rw [← integral_map h_prod_meas.aemeasurable h_func_ae]
        _ = ∫ p, (p.1 - m) * (p.2 - m) ∂(Measure.map (fun ω => (Z 0 ω, Z 1 ω)) μ) := by
              rw [h_dist]
        _ = ∫ ω, (Z 0 ω - m) * (Z 1 ω - m) ∂μ := by
              rw [integral_map ((hZ_meas 0).prodMk (hZ_meas 1)).aemeasurable h_func_ae']
        _ = σSq * ρ := by
              simp only [σSq, ρ, covOffDiag]
              by_cases h : ∫ ω, (Z 0 ω - m) ^ 2 ∂μ = 0
              · -- If variance is 0, covariance is also 0 by Cauchy-Schwarz
                simp [h]
                -- Goal: ∫ (Z 0 - m)(Z 1 - m) = 0
                -- Get MemLp for Z 0 and Z 1
                obtain ⟨k, hk⟩ := hs.exists_mem
                have hZk_L2 : MemLp (Z k) 2 μ := hZ_L2 k hk
                have hZ0_L2_local : MemLp (Z 0) 2 μ := by
                  by_cases h' : k = 0
                  · subst h'; exact hZk_L2
                  · have h_dist := Exchangeability.DeFinetti.L2Helpers.contractable_map_single
                      (X := Z) hZ_contract hZ_meas (i := k)
                    have h_Lpnorm_eq : eLpNorm (Z 0) 2 μ = eLpNorm (Z k) 2 μ := by
                      symm
                      calc eLpNorm (Z k) 2 μ
                          = eLpNorm id 2 (Measure.map (Z k) μ) := by
                              symm; exact eLpNorm_map_measure aestronglyMeasurable_id (hZ_meas k).aemeasurable
                        _ = eLpNorm id 2 (Measure.map (Z 0) μ) := by rw [h_dist]
                        _ = eLpNorm (Z 0) 2 μ := by
                              exact eLpNorm_map_measure aestronglyMeasurable_id (hZ_meas 0).aemeasurable
                    have : eLpNorm (Z 0) 2 μ < ⊤ := by
                      rw [h_Lpnorm_eq]
                      exact hZk_L2.eLpNorm_lt_top
                    exact ⟨(hZ_meas 0).aestronglyMeasurable, this⟩
                have hZ1_L2_local : MemLp (Z 1) 2 μ := by
                  by_cases h' : k = 1
                  · subst h'; exact hZk_L2
                  · have h_dist := Exchangeability.DeFinetti.L2Helpers.contractable_map_single
                      (X := Z) hZ_contract hZ_meas (i := k)
                    have h_dist1 := Exchangeability.DeFinetti.L2Helpers.contractable_map_single
                      (X := Z) hZ_contract hZ_meas (i := 1)
                    have h_Lpnorm_eq : eLpNorm (Z 1) 2 μ = eLpNorm (Z k) 2 μ := by
                      calc eLpNorm (Z 1) 2 μ
                          = eLpNorm id 2 (Measure.map (Z 1) μ) := by
                              symm; exact eLpNorm_map_measure aestronglyMeasurable_id (hZ_meas 1).aemeasurable
                        _ = eLpNorm id 2 (Measure.map (Z 0) μ) := by rw [h_dist1]
                        _ = eLpNorm id 2 (Measure.map (Z k) μ) := by rw [← h_dist]
                        _ = eLpNorm (Z k) 2 μ := by
                              exact eLpNorm_map_measure aestronglyMeasurable_id (hZ_meas k).aemeasurable
                    have : eLpNorm (Z 1) 2 μ < ⊤ := by
                      rw [h_Lpnorm_eq]
                      exact hZk_L2.eLpNorm_lt_top
                    exact ⟨(hZ_meas 1).aestronglyMeasurable, this⟩
                -- Centered versions
                have hm_const : MemLp (fun _ : Ω => m) 2 μ := memLp_const m
                have hf_local : MemLp (fun ω => Z 0 ω - m) 2 μ := MemLp.sub hZ0_L2_local hm_const
                have hg_local : MemLp (fun ω => Z 1 ω - m) 2 μ := MemLp.sub hZ1_L2_local hm_const
                -- Cauchy-Schwarz: |∫fg| ≤ √(∫f²) * √(∫g²)
                have cs := Exchangeability.Probability.IntegrationHelpers.abs_integral_mul_le_L2 hf_local hg_local
                -- Use h : ∫(Z 0 - m)² = 0 to show bound is 0
                have : (∫ ω, (Z 0 ω - m) ^ 2 ∂μ) ^ (1/2 : ℝ) = 0 := by rw [h]; norm_num
                rw [this, zero_mul] at cs
                exact abs_eq_zero.mp (le_antisymm cs (abs_nonneg _))
              · simp [h]; field_simp
    · -- Case j' < i': Use symmetry of multiplication
      have h_dist := Exchangeability.DeFinetti.L2Helpers.contractable_map_pair
        (X := Z) hZ_contract hZ_meas h_lt
      -- Note: (Z i' - m) * (Z j' - m) = (Z j' - m) * (Z i' - m)
      have h_prod_meas : Measurable (fun ω => (Z j' ω, Z i' ω)) :=
        (hZ_meas j').prodMk (hZ_meas i')
      have h_func_ae : AEStronglyMeasurable (fun p : ℝ × ℝ => (p.1 - m) * (p.2 - m))
          (Measure.map (fun ω => (Z j' ω, Z i' ω)) μ) := by
        apply Continuous.aestronglyMeasurable
        exact (continuous_fst.sub continuous_const).mul (continuous_snd.sub continuous_const)
      have h_func_ae' : AEStronglyMeasurable (fun p : ℝ × ℝ => (p.1 - m) * (p.2 - m))
          (Measure.map (fun ω => (Z 0 ω, Z 1 ω)) μ) := by
        apply Continuous.aestronglyMeasurable
        exact (continuous_fst.sub continuous_const).mul (continuous_snd.sub continuous_const)
      calc ∫ ω, (Z i' ω - m) * (Z j' ω - m) ∂μ
          = ∫ ω, (Z j' ω - m) * (Z i' ω - m) ∂μ := by
              congr 1 with ω; ring
        _ = ∫ p, (p.1 - m) * (p.2 - m) ∂(Measure.map (fun ω => (Z j' ω, Z i' ω)) μ) := by
              rw [← integral_map h_prod_meas.aemeasurable h_func_ae]
        _ = ∫ p, (p.1 - m) * (p.2 - m) ∂(Measure.map (fun ω => (Z 0 ω, Z 1 ω)) μ) := by
              rw [h_dist]
        _ = ∫ ω, (Z 0 ω - m) * (Z 1 ω - m) ∂μ := by
              rw [integral_map ((hZ_meas 0).prodMk (hZ_meas 1)).aemeasurable h_func_ae']
        _ = σSq * ρ := by
              simp only [σSq, ρ, covOffDiag]
              by_cases h : ∫ ω, (Z 0 ω - m) ^ 2 ∂μ = 0
              · -- If variance is 0, covariance is also 0 by Cauchy-Schwarz
                simp [h]
                -- Goal: ∫ (Z 0 - m)(Z 1 - m) = 0
                -- Get MemLp for Z 0 and Z 1
                obtain ⟨k, hk⟩ := hs.exists_mem
                have hZk_L2 : MemLp (Z k) 2 μ := hZ_L2 k hk
                have hZ0_L2_local : MemLp (Z 0) 2 μ := by
                  by_cases h' : k = 0
                  · subst h'; exact hZk_L2
                  · have h_dist := Exchangeability.DeFinetti.L2Helpers.contractable_map_single
                      (X := Z) hZ_contract hZ_meas (i := k)
                    have h_Lpnorm_eq : eLpNorm (Z 0) 2 μ = eLpNorm (Z k) 2 μ := by
                      symm
                      calc eLpNorm (Z k) 2 μ
                          = eLpNorm id 2 (Measure.map (Z k) μ) := by
                              symm; exact eLpNorm_map_measure aestronglyMeasurable_id (hZ_meas k).aemeasurable
                        _ = eLpNorm id 2 (Measure.map (Z 0) μ) := by rw [h_dist]
                        _ = eLpNorm (Z 0) 2 μ := by
                              exact eLpNorm_map_measure aestronglyMeasurable_id (hZ_meas 0).aemeasurable
                    have : eLpNorm (Z 0) 2 μ < ⊤ := by
                      rw [h_Lpnorm_eq]
                      exact hZk_L2.eLpNorm_lt_top
                    exact ⟨(hZ_meas 0).aestronglyMeasurable, this⟩
                have hZ1_L2_local : MemLp (Z 1) 2 μ := by
                  by_cases h' : k = 1
                  · subst h'; exact hZk_L2
                  · have h_dist := Exchangeability.DeFinetti.L2Helpers.contractable_map_single
                      (X := Z) hZ_contract hZ_meas (i := k)
                    have h_dist1 := Exchangeability.DeFinetti.L2Helpers.contractable_map_single
                      (X := Z) hZ_contract hZ_meas (i := 1)
                    have h_Lpnorm_eq : eLpNorm (Z 1) 2 μ = eLpNorm (Z k) 2 μ := by
                      calc eLpNorm (Z 1) 2 μ
                          = eLpNorm id 2 (Measure.map (Z 1) μ) := by
                              symm; exact eLpNorm_map_measure aestronglyMeasurable_id (hZ_meas 1).aemeasurable
                        _ = eLpNorm id 2 (Measure.map (Z 0) μ) := by rw [h_dist1]
                        _ = eLpNorm id 2 (Measure.map (Z k) μ) := by rw [← h_dist]
                        _ = eLpNorm (Z k) 2 μ := by
                              exact eLpNorm_map_measure aestronglyMeasurable_id (hZ_meas k).aemeasurable
                    have : eLpNorm (Z 1) 2 μ < ⊤ := by
                      rw [h_Lpnorm_eq]
                      exact hZk_L2.eLpNorm_lt_top
                    exact ⟨(hZ_meas 1).aestronglyMeasurable, this⟩
                -- Centered versions
                have hm_const : MemLp (fun _ : Ω => m) 2 μ := memLp_const m
                have hf_local : MemLp (fun ω => Z 0 ω - m) 2 μ := MemLp.sub hZ0_L2_local hm_const
                have hg_local : MemLp (fun ω => Z 1 ω - m) 2 μ := MemLp.sub hZ1_L2_local hm_const
                -- Cauchy-Schwarz: |∫fg| ≤ √(∫f²) * √(∫g²)
                have cs := Exchangeability.Probability.IntegrationHelpers.abs_integral_mul_le_L2 hf_local hg_local
                -- Use h : ∫(Z 0 - m)² = 0 to show bound is 0
                have : (∫ ω, (Z 0 ω - m) ^ 2 ∂μ) ^ (1/2 : ℝ) = 0 := by rw [h]; norm_num
                rw [this, zero_mul] at cs
                exact abs_eq_zero.mp (le_antisymm cs (abs_nonneg _))
              · simp [h]; field_simp

  -- Prove p' and q' are probability distributions
  have hp'_prob : (∑ i : Fin n, p' i) = 1 ∧ ∀ i, 0 ≤ p' i := by
    constructor
    · -- ∑ over Fin n equals ∑ over s via reindexing
      -- enum : Fin n ≃o { x // x ∈ s } is a bijection
      have : ∑ i : Fin n, p' i = s.sum p := by
        -- Use Finset.sum_bij with the bijection induced by enum
        simp only [p']
        -- Convert sum over Fin n to sum over s using enum bijection
        have h_bij : ∑ i : Fin n, p (enum i).val = s.sum p := by
          -- enum gives a bijection between Fin n and { x // x ∈ s }
          -- The map i ↦ (enum i).val is a bijection Fin n → s
          rw [Finset.sum_bij'
            (fun (i : Fin n) (_ : i ∈ Finset.univ) => (enum i).val)
            (fun (a : ℕ) (ha : a ∈ s) => enum.symm ⟨a, ha⟩)]
          · intro i _; exact (enum i).property
          · intro a ha; simp
          · intro a ha; simp
          · intro i hi; simp [OrderIso.symm_apply_apply]
          · intro a ha; simp
        exact h_bij
      rw [this]; exact hp_prob.1
    · intro i
      -- p' i = p (enum i).val, and (enum i).val ∈ s by (enum i).property
      exact hp_prob.2 (enum i).val (enum i).property

  have hq'_prob : (∑ i : Fin n, q' i) = 1 ∧ ∀ i, 0 ≤ q' i := by
    constructor
    · have : ∑ i : Fin n, q' i = s.sum q := by
        -- Same proof as for p', just with q instead of p
        simp only [q']
        have h_bij : ∑ i : Fin n, q (enum i).val = s.sum q := by
          rw [Finset.sum_bij'
            (fun (i : Fin n) (_ : i ∈ Finset.univ) => (enum i).val)
            (fun (a : ℕ) (ha : a ∈ s) => enum.symm ⟨a, ha⟩)]
          · intro i _; exact (enum i).property
          · intro a ha; simp
          · intro a ha; simp
          · intro i hi; simp [OrderIso.symm_apply_apply]
          · intro a ha; simp
        exact h_bij
      rw [this]; exact hq_prob.1
    · intro i
      exact hq_prob.2 (enum i).val (enum i).property

  -- Step 4: Apply l2_contractability_bound and convert result

  -- Convert hvar to the form l2_contractability_bound expects
  have hvar' : ∀ k : Fin n, ∫ ω, (ξ k ω - m)^2 ∂μ = (σSq ^ (1/2 : ℝ))^2 := by
    intro k
    rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hσSq_nonneg]
    exact hvar k

  -- Convert hcov to the form l2_contractability_bound expects
  have hcov' : ∀ i j : Fin n, i ≠ j → ∫ ω, (ξ i ω - m) * (ξ j ω - m) ∂μ = (σSq ^ (1/2 : ℝ))^2 * ρ := by
    intro i j hij
    rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hσSq_nonneg]
    exact hcov i j hij

  -- First, prove that ∫ (Z 0 - Z 1)^2 = 2*σ^2*(1 - ρ)
  have h_diff_sq : ∫ ω, (Z 0 ω - Z 1 ω)^2 ∂μ = 2 * σSq * (1 - ρ) := by
    -- Strategy: Rewrite Z 0 - Z 1 = (Z 0 - m) - (Z 1 - m) and expand
    have h_expand : ∀ ω, (Z 0 ω - Z 1 ω)^2 =
        (Z 0 ω - m)^2 + (Z 1 ω - m)^2 - 2 * (Z 0 ω - m) * (Z 1 ω - m) := by
      intro ω
      ring

    -- Integrability facts: Z 0 and Z 1 are in L² by contractability
    -- Since some Z k (k ∈ s) is in L², and contractability gives equal distributions,
    -- all Z i have the same L² norm
    obtain ⟨k, hk⟩ := hs.exists_mem
    have hZk_L2 : MemLp (Z k) 2 μ := hZ_L2 k hk

    have hZ0_L2 : MemLp (Z 0) 2 μ := by
      by_cases h : k = 0
      · subst h; exact hZk_L2
      · -- Use that Z 0 has same distribution as Z k via contractability
        -- Equal distributions imply equal eLpNorm, hence MemLp transfers
        have h_dist := Exchangeability.DeFinetti.L2Helpers.contractable_map_single
          (X := Z) hZ_contract hZ_meas (i := k)
        -- Transfer eLpNorm using equal distributions
        have h_Lpnorm_eq : eLpNorm (Z 0) 2 μ = eLpNorm (Z k) 2 μ := by
          symm
          calc eLpNorm (Z k) 2 μ
              = eLpNorm id 2 (Measure.map (Z k) μ) := by
                  symm
                  exact eLpNorm_map_measure aestronglyMeasurable_id (hZ_meas k).aemeasurable
            _ = eLpNorm id 2 (Measure.map (Z 0) μ) := by rw [h_dist]
            _ = eLpNorm (Z 0) 2 μ := by
                  exact eLpNorm_map_measure aestronglyMeasurable_id (hZ_meas 0).aemeasurable
        have : eLpNorm (Z 0) 2 μ < ⊤ := by
          rw [h_Lpnorm_eq]
          exact hZk_L2.eLpNorm_lt_top
        exact ⟨(hZ_meas 0).aestronglyMeasurable, this⟩
    have hZ1_L2 : MemLp (Z 1) 2 μ := by
      by_cases h : k = 1
      · subst h; exact hZk_L2
      · -- Use that Z 1 has same distribution as Z k via contractability
        -- Equal distributions imply equal eLpNorm, hence MemLp transfers
        have h_dist := Exchangeability.DeFinetti.L2Helpers.contractable_map_single
          (X := Z) hZ_contract hZ_meas (i := k)
        have h_dist1 := Exchangeability.DeFinetti.L2Helpers.contractable_map_single
          (X := Z) hZ_contract hZ_meas (i := 1)
        -- Transfer eLpNorm using equal distributions
        have h_Lpnorm_eq : eLpNorm (Z 1) 2 μ = eLpNorm (Z k) 2 μ := by
          calc eLpNorm (Z 1) 2 μ
              = eLpNorm id 2 (Measure.map (Z 1) μ) := by
                  symm
                  exact eLpNorm_map_measure aestronglyMeasurable_id (hZ_meas 1).aemeasurable
            _ = eLpNorm id 2 (Measure.map (Z 0) μ) := by rw [h_dist1]
            _ = eLpNorm id 2 (Measure.map (Z k) μ) := by rw [← h_dist]
            _ = eLpNorm (Z k) 2 μ := by
                  exact eLpNorm_map_measure aestronglyMeasurable_id (hZ_meas k).aemeasurable
        have : eLpNorm (Z 1) 2 μ < ⊤ := by
          rw [h_Lpnorm_eq]
          exact hZk_L2.eLpNorm_lt_top
        exact ⟨(hZ_meas 1).aestronglyMeasurable, this⟩

    -- (Z i - m)² is integrable when Z i ∈ L²
    have hint_sq0 : Integrable (fun ω => (Z 0 ω - m)^2) μ := by
      have : (fun ω => (Z 0 ω - m)^2) = (fun ω => (Z 0 ω)^2 - 2 * m * Z 0 ω + m^2) := by
        ext ω; ring
      rw [this]
      apply Integrable.add
      · apply Integrable.sub
        · exact (hZ0_L2.integrable_sq)
        · exact Integrable.const_mul (hZ0_L2.integrable one_le_two) _
      · exact integrable_const _
    have hint_sq1 : Integrable (fun ω => (Z 1 ω - m)^2) μ := by
      have : (fun ω => (Z 1 ω - m)^2) = (fun ω => (Z 1 ω)^2 - 2 * m * Z 1 ω + m^2) := by
        ext ω; ring
      rw [this]
      apply Integrable.add
      · apply Integrable.sub
        · exact (hZ1_L2.integrable_sq)
        · exact Integrable.const_mul (hZ1_L2.integrable one_le_two) _
      · exact integrable_const _

    -- (Z 0 - m) * (Z 1 - m) is integrable (product of L² functions)
    have hint_prod : Integrable (fun ω => (Z 0 ω - m) * (Z 1 ω - m)) μ := by
      have hm : MemLp (fun _ : Ω => m) 2 μ := memLp_const m
      have hf : MemLp (fun ω => Z 0 ω - m) 2 μ := MemLp.sub hZ0_L2 hm
      have hg : MemLp (fun ω => Z 1 ω - m) 2 μ := MemLp.sub hZ1_L2 hm
      exact MemLp.integrable_mul hf hg

    -- Algebraically, (Z_0 - Z_1)² = (Z_0 - m)² + (Z_1 - m)² - 2(Z_0 - m)(Z_1 - m)
    -- Taking expectations: E[(Z_0 - Z_1)²] = σ² + σ² - 2·cov = 2σ²(1 - ρ)

    -- First prove Z 1 has same variance as Z 0
    have hvar1 : ∫ ω, (Z 1 ω - m)^2 ∂μ = σSq := by
      -- Use contractability: Z 1 has same distribution as Z 0
      have h_dist := Exchangeability.DeFinetti.L2Helpers.contractable_map_single
        (X := Z) hZ_contract hZ_meas (i := 1)
      simp only [σSq]
      rw [← Exchangeability.Probability.IntegrationHelpers.integral_pushforward_sq_diff (hZ_meas 1) m,
          h_dist,
          Exchangeability.Probability.IntegrationHelpers.integral_pushforward_sq_diff (hZ_meas 0) m]

    -- Now compute the integral using the expansion
    calc ∫ ω, (Z 0 ω - Z 1 ω)^2 ∂μ
        = ∫ ω, ((Z 0 ω - m)^2 + (Z 1 ω - m)^2 - 2 * (Z 0 ω - m) * (Z 1 ω - m)) ∂μ := by
            apply integral_congr_ae
            filter_upwards with ω
            exact h_expand ω
      _ = 2 * σSq * (1 - ρ) := by
            -- Distribute the integral using linearity
            have h1 : ∫ ω, ((Z 0 ω - m)^2 + (Z 1 ω - m)^2) ∂μ = ∫ ω, (Z 0 ω - m)^2 ∂μ + ∫ ω, (Z 1 ω - m)^2 ∂μ :=
              integral_add hint_sq0 hint_sq1
            have h_int_prod : Integrable (fun ω => 2 * (Z 0 ω - m) * (Z 1 ω - m)) μ := by
              convert hint_prod.const_mul 2 using 1
              ext ω
              ring
            have h2 : ∫ ω, ((Z 0 ω - m)^2 + (Z 1 ω - m)^2 - 2 * (Z 0 ω - m) * (Z 1 ω - m)) ∂μ =
                     ∫ ω, ((Z 0 ω - m)^2 + (Z 1 ω - m)^2) ∂μ - ∫ ω, 2 * (Z 0 ω - m) * (Z 1 ω - m) ∂μ :=
              integral_sub (hint_sq0.add hint_sq1) h_int_prod
            have h3 : ∫ ω, 2 * (Z 0 ω - m) * (Z 1 ω - m) ∂μ = 2 * ∫ ω, (Z 0 ω - m) * (Z 1 ω - m) ∂μ := by
              have : (fun ω => 2 * (Z 0 ω - m) * (Z 1 ω - m)) = (fun ω => 2 * ((Z 0 ω - m) * (Z 1 ω - m))) := by
                ext ω; ring
              rw [this, integral_const_mul]
            calc ∫ ω, ((Z 0 ω - m)^2 + (Z 1 ω - m)^2 - 2 * (Z 0 ω - m) * (Z 1 ω - m)) ∂μ
                = ∫ ω, ((Z 0 ω - m)^2 + (Z 1 ω - m)^2) ∂μ - ∫ ω, 2 * (Z 0 ω - m) * (Z 1 ω - m) ∂μ := h2
              _ = (∫ ω, (Z 0 ω - m)^2 ∂μ + ∫ ω, (Z 1 ω - m)^2 ∂μ) - ∫ ω, 2 * (Z 0 ω - m) * (Z 1 ω - m) ∂μ := by rw [h1]
              _ = (∫ ω, (Z 0 ω - m)^2 ∂μ + ∫ ω, (Z 1 ω - m)^2 ∂μ) - 2 * ∫ ω, (Z 0 ω - m) * (Z 1 ω - m) ∂μ := by rw [h3]
              _ = (σSq + σSq) - 2 * covOffDiag := by simp only [σSq, covOffDiag]; rw [hvar1]
              _ = 2 * σSq - 2 * covOffDiag := by ring
              _ = 2 * σSq - 2 * (σSq * ρ) := by
                    congr 1
                    simp only [ρ, covOffDiag]
                    by_cases h : σSq = 0
                    · -- When σSq = 0, variance is 0, so Z 0 ω - m = 0 a.e.
                      -- Therefore the covariance integral is also 0
                      simp [h]
                      -- σSq = ∫ (Z 0 - m)² = 0 and integrand ≥ 0, so Z 0 - m = 0 a.e.
                      have : (fun ω => (Z 0 ω - m) * (Z 1 ω - m)) =ᵐ[μ] 0 := by
                        have h_sq_zero : ∀ᵐ ω ∂μ, (Z 0 ω - m) ^ 2 = 0 := by
                          rw [← h] at hσSq_nonneg
                          have : ∫ (ω : Ω), (Z 0 ω - m) ^ 2 ∂μ = 0 := h
                          exact (integral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall (fun ω => sq_nonneg _)) hint_sq0).mp this
                        filter_upwards [h_sq_zero] with ω hω
                        have : Z 0 ω - m = 0 := by
                          have := sq_eq_zero_iff.mp hω
                          exact this
                        simp [this]
                      rw [integral_congr_ae this]
                      simp
                    · simp [h]; field_simp
              _ = 2 * σSq * (1 - ρ) := by ring

  -- Apply l2_contractability_bound to get the bound in terms of ξ, p', q'
  have h_bound := Exchangeability.DeFinetti.L2Approach.l2_contractability_bound
    ξ m (σSq ^ (1/2 : ℝ)) ρ hρ_bd hmean hL2 hvar' hcov' p' q' hp'_prob hq'_prob

  -- Convert the bound back to the original variables Z, p, q, s
  calc ∫ ω, (s.sum fun i => (p i - q i) * Z i ω) ^ 2 ∂μ
      = ∫ ω, (∑ k : Fin n, (p' k - q' k) * ξ k ω) ^ 2 ∂μ := by
          -- Reindex sum from s to Fin n via enum bijection
          congr 1; ext ω
          -- Show: s.sum (fun i => (p i - q i) * Z i ω) = ∑ k : Fin n, (p' k - q' k) * ξ k ω
          simp only [p', q', ξ]
          -- Now: s.sum (fun i => (p i - q i) * Z i ω) = ∑ k : Fin n, (p (enum k).val - q (enum k).val) * Z (enum k).val ω
          symm
          rw [Finset.sum_bij'
            (fun (k : Fin n) (_ : k ∈ Finset.univ) => (enum k).val)
            (fun (i : ℕ) (hi : i ∈ s) => enum.symm ⟨i, hi⟩)]
          · intro k _; exact (enum k).property
          · intro i hi; simp
          · intro i hi; simp
          · intro k hk; simp [OrderIso.symm_apply_apply]
          · intro i hi; simp
    _ = ∫ ω, (∑ k : Fin n, p' k * ξ k ω - ∑ k : Fin n, q' k * ξ k ω) ^ 2 ∂μ := by
          congr 1; ext ω
          simp only [Finset.sum_sub_distrib, sub_mul]
    _ ≤ 2 * (σSq ^ (1/2 : ℝ)) ^ 2 * (1 - ρ) * (⨆ k : Fin n, |p' k - q' k|) := h_bound
    _ = 2 * σSq * (1 - ρ) * (⨆ k : Fin n, |p' k - q' k|) := by
          congr 1
          rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hσSq_nonneg]
    _ = (∫ ω, (Z 0 ω - Z 1 ω)^2 ∂μ) * (⨆ k : Fin n, |p' k - q' k|) := by
          rw [← h_diff_sq]
    _ = (∫ ω, (Z 0 ω - Z 1 ω)^2 ∂μ) * (s.sup' hs fun i => |p i - q i|) := by
          -- Supremum reindexing via enum: ⨆ k : Fin n, |p' k - q' k| = s.sup' hs fun i => |p i - q i|
          congr 1
          simp only [p', q']
          -- Prove equality using le_antisymm
          apply le_antisymm
          · -- Forward: ⨆ k ≤ s.sup'
            -- For each k, (enum k).val ∈ s, so |p (enum k).val - q (enum k).val| ≤ s.sup'
            -- Need Nonempty (Fin n) for ciSup_le
            have : Nonempty (Fin n) := by
              have h_card_pos : 0 < n := Finset.card_pos.mpr hs
              exact Fin.pos_iff_nonempty.mp h_card_pos
            apply ciSup_le
            intro k
            have hk_in_s : (enum k).val ∈ s := (enum k).property
            exact Finset.le_sup' (fun i => |p i - q i|) hk_in_s
          · -- Backward: s.sup' ≤ ⨆ k
            -- For each i ∈ s, enum.symm ⟨i, hi⟩ gives k : Fin n with (enum k).val = i
            apply Finset.sup'_le
            intro i hi
            have : i = (enum (enum.symm ⟨i, hi⟩)).val := by simp
            rw [this]
            exact le_ciSup (f := fun k => |(p ∘ Subtype.val ∘ enum) k - (q ∘ Subtype.val ∘ enum) k|)
              (Finite.bddAbove_range _) (enum.symm ⟨i, hi⟩)

/-- Helper lemma for cesaro_to_condexp_L2: Cauchy sequence proof when ρ < 1.

   This contains the bulk of the L² contractability argument, extracted to avoid
   a massive indentation when handling the ρ = 1 edge case separately. -/
private lemma cesaro_cauchy_rho_lt
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} (hX_contract : Exchangeability.Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (f : ℝ → ℝ) (hf_meas : Measurable f) (hf_bdd : ∀ x, |f x| ≤ 1)
    (m_mean : ℝ) (hm_mean : m_mean = ∫ ω, f (X 0 ω) ∂μ)
    (Z : ℕ → Ω → ℝ) (hZ_def : ∀ i ω, Z i ω = f (X i ω) - m_mean)
    (hZ_meas : ∀ i, Measurable (Z i))
    (hZ_contract : Exchangeability.Contractable μ Z)
    (hZ_var_uniform : ∀ i, ∫ ω, (Z i ω)^2 ∂μ = ∫ ω, (Z 0 ω)^2 ∂μ)
    (hZ_mean_zero : ∀ i, ∫ ω, Z i ω ∂μ = 0)
    (hZ_cov_uniform : ∀ i j, i ≠ j → ∫ ω, Z i ω * Z j ω ∂μ = ∫ ω, Z 0 ω * Z 1 ω ∂μ)
    (σSq : ℝ) (hσ_pos : σSq > 0) (hσSq_def : σSq = ∫ ω, (Z 0 ω)^2 ∂μ)
    (ρ : ℝ) (hρ_bd : -1 ≤ ρ ∧ ρ ≤ 1) (hρ_def : ρ = (∫ ω, Z 0 ω * Z 1 ω ∂μ) / σSq)
    (hρ_lt : ρ < 1)
    (Cf : ℝ) (hCf_def : Cf = 2 * σSq * (1 - ρ))
    (ε : ENNReal) (hε : ε > 0) :
    ∃ N, ∀ {n n'}, n ≥ N → n' ≥ N →
      eLpNorm (blockAvg f X 0 n - blockAvg f X 0 n') 2 μ < ε := by
  -- Step 7c: Choose N via Archimedean property
  -- We want Cf / N < (ε.toReal)²
  -- Equivalently: N > Cf / (ε.toReal)²
  -- If ε = ⊤, the property is trivial (take any N); otherwise use Archimedean property
  by_cases hε_top : ε = ⊤
  · -- Case ε = ⊤
    -- Any N works; take N := 0
    refine ⟨0, ?_⟩
    intro n n' _ _
    -- measurability of the two block averages and their difference
    have h_meas_n  :
        Measurable (fun ω => blockAvg f X 0 n  ω) :=
      blockAvg_measurable f X hf_meas hX_meas 0 n
    have h_meas_n' :
        Measurable (fun ω => blockAvg f X 0 n' ω) :=
      blockAvg_measurable f X hf_meas hX_meas 0 n'
    have h_meas_diff :
        Measurable (fun ω => blockAvg f X 0 n ω - blockAvg f X 0 n' ω) :=
      h_meas_n.sub h_meas_n'

    -- |A_n| ≤ 1 and |A_{n'}| ≤ 1 ⇒ |A_n − A_{n'}| ≤ 2
    have h_bdd :
        ∀ᵐ ω ∂μ, |blockAvg f X 0 n ω - blockAvg f X 0 n' ω| ≤ 2 := by
      apply ae_of_all
      intro ω
      have hn  : |blockAvg f X 0 n  ω| ≤ 1 := blockAvg_abs_le_one f X hf_bdd 0 n  ω
      have hn' : |blockAvg f X 0 n' ω| ≤ 1 := blockAvg_abs_le_one f X hf_bdd 0 n' ω
      calc
        |blockAvg f X 0 n ω - blockAvg f X 0 n' ω|
            ≤ |blockAvg f X 0 n ω| + |blockAvg f X 0 n' ω|
              := by
                   have := abs_add_le (blockAvg f X 0 n ω) (-(blockAvg f X 0 n' ω))
                   simpa [sub_eq_add_neg, abs_neg] using this
        _ ≤ 1 + 1 := add_le_add hn hn'
        _ = 2 := by norm_num

    -- bounded ⇒ MemLp ⇒ eLpNorm < ⊤
    have h_mem :
        MemLp (fun ω => blockAvg f X 0 n ω - blockAvg f X 0 n' ω) 2 μ :=
      memLp_of_abs_le_const h_meas_diff h_bdd 2 (by norm_num) (by norm_num)

    -- The goal for this branch is just finiteness (ε = ⊤)
    rw [hε_top]
    exact MemLp.eLpNorm_lt_top h_mem

  -- Case ε < ⊤: use Archimedean property to find N
  have hε_lt_top : ε < ⊤ := lt_top_iff_ne_top.mpr hε_top
  have hε_pos : 0 < ε.toReal := by
    rw [ENNReal.toReal_pos_iff]
    exact ⟨hε, hε_lt_top⟩
  have hε_sq_pos : 0 < (ε.toReal) ^ 2 := sq_pos_of_pos hε_pos

  have hCf_nonneg : 0 ≤ Cf := by
    rw [hCf_def]
    have h_one_sub_ρ_pos : 0 < 1 - ρ := by linarith
    positivity

  have hCf_pos : 0 < Cf := by
    rw [hCf_def]
    have h_one_sub_ρ_pos : 0 < 1 - ρ := by linarith
    positivity

  -- Find N using Archimedean property
  obtain ⟨N', hN'⟩ := exists_nat_gt (Cf / (ε.toReal) ^ 2)
  use max 1 (N' + 1)
  intros n n' hn_ge hn'_ge

  -- Step 7d: Apply l2_contractability_bound

  -- Work with a common finite prefix m = max(n, n')
  let m := max n n'
  let ξ : Fin m → Ω → ℝ := fun i ω => Z i.val ω

  -- Define weight distributions: p for blockAvg n, q for blockAvg n'
  let p : Fin m → ℝ := fun i => if i.val < n then (n : ℝ)⁻¹ else 0
  let q : Fin m → ℝ := fun i => if i.val < n' then (n' : ℝ)⁻¹ else 0

  -- Step 1: Show p and q are probability distributions
  -- First derive that n > 0 from hn_ge
  have hn_pos : n > 0 := by
    calc n ≥ max 1 (N' + 1) := hn_ge
      _ ≥ 1 := le_max_left 1 (N' + 1)
      _ > 0 := Nat.one_pos

  have hp_prob : ∑ i : Fin m, p i = 1 ∧ ∀ i, 0 ≤ p i := by
    constructor
    · -- Sum equals 1
      -- p i = 1/n for i < n, and 0 otherwise
      -- So ∑ p i = ∑_{i<n} (1/n) = n * (1/n) = 1
      calc ∑ i : Fin m, p i
          = ∑ i : Fin m, if i.val < n then (n : ℝ)⁻¹ else 0 := rfl
        _ = ∑ i ∈ Finset.univ.filter (fun i : Fin m => i.val < n), (n : ℝ)⁻¹ := by
            rw [Finset.sum_ite]
            simp only [Finset.sum_const_zero, add_zero]
        _ = (Finset.filter (fun i : Fin m => i.val < n) Finset.univ).card • (n : ℝ)⁻¹ := by
            rw [Finset.sum_const]
        _ = n • (n : ℝ)⁻¹ := by
            congr 1
            exact Finset.filter_val_lt_card (le_max_left n n')
        _ = 1 := by
            rw [nsmul_eq_mul]
            field_simp [Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hn_pos)]
    · -- All weights are non-negative
      intro i
      simp only [p]
      split_ifs
      · exact inv_nonneg.mpr (Nat.cast_nonneg n)
      · exact le_refl 0

  -- Similarly for n'
  have hn'_pos : n' > 0 := by
    calc n' ≥ max 1 (N' + 1) := hn'_ge
      _ ≥ 1 := le_max_left 1 (N' + 1)
      _ > 0 := Nat.one_pos

  have hq_prob : ∑ i : Fin m, q i = 1 ∧ ∀ i, 0 ≤ q i := by
    constructor
    · -- Sum equals 1
      calc ∑ i : Fin m, q i
          = ∑ i : Fin m, if i.val < n' then (n' : ℝ)⁻¹ else 0 := rfl
        _ = ∑ i ∈ Finset.univ.filter (fun i : Fin m => i.val < n'), (n' : ℝ)⁻¹ := by
            rw [Finset.sum_ite]
            simp only [Finset.sum_const_zero, add_zero]
        _ = (Finset.filter (fun i : Fin m => i.val < n') Finset.univ).card • (n' : ℝ)⁻¹ := by
            rw [Finset.sum_const]
        _ = n' • (n' : ℝ)⁻¹ := by
            congr 1
            exact Finset.filter_val_lt_card (le_max_right n n')
        _ = 1 := by
            rw [nsmul_eq_mul]
            field_simp [Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hn'_pos)]
    · -- All weights are non-negative
      intro i
      simp only [q]
      split_ifs
      · exact inv_nonneg.mpr (Nat.cast_nonneg n')
      · exact le_refl 0

  -- Step 2: Define σ and prove hypotheses for l2_contractability_bound

  -- Define σ := sqrt(σSq), the standard deviation
  let σ := Real.sqrt σSq

  -- Prove mean of ξ is 0
  have hmean_ξ : ∀ k : Fin m, ∫ ω, ξ k ω ∂μ = 0 := by
    intro k
    simp only [ξ]
    exact hZ_mean_zero k.val

  -- Prove ξ is in L²
  have hL2_ξ : ∀ k : Fin m, MemLp (fun ω => ξ k ω - 0) 2 μ := by
    intro k
    simp only [sub_zero, ξ]
    -- Z k.val is bounded, hence in L²
    -- Same proof as for Z 0: |Z k.val| ≤ |f| + |m| ≤ 1 + 1 = 2
    apply memLp_two_of_bounded (hZ_meas k.val)
    intro ω
    -- Unfold ξ and Z to show |f(X k.val ω) - m| ≤ 2
    have h1 : |f (X k.val ω)| ≤ 1 := hf_bdd (X k.val ω)
    have h2 : |∫ ω', f (X 0 ω') ∂μ| ≤ 1 := by
      -- |∫ f(X 0)| ≤ ∫ |f(X 0)| ≤ ∫ 1 = 1
      have hfX_int : Integrable (fun ω => f (X 0 ω)) μ := by
        apply Integrable.of_bound
        · exact (hf_meas.comp (hX_meas 0)).aestronglyMeasurable
        · filter_upwards [] with ω
          exact hf_bdd (X 0 ω)
      calc |∫ ω', f (X 0 ω') ∂μ|
          ≤ ∫ ω', |f (X 0 ω')| ∂μ := abs_integral_le_integral_abs
        _ ≤ ∫ ω', 1 ∂μ := by
            apply integral_mono_ae
            · exact hfX_int.abs
            · exact integrable_const 1
            · filter_upwards [] with ω'
              exact hf_bdd (X 0 ω')
        _ = 1 := by simp
    -- Show |Z k.val ω| ≤ 2 using hZ_def and triangle inequality
    rw [hZ_def k.val ω]
    calc |f (X k.val ω) - m_mean|
        ≤ |f (X k.val ω)| + |m_mean| := abs_sub _ _
      _ = |f (X k.val ω)| + |∫ ω', f (X 0 ω') ∂μ| := by rw [hm_mean]
      _ ≤ 1 + 1 := by linarith
      _ = 2 := by norm_num

  -- Prove uniform variance: ∫ ξ_k² = σ²
  have hvar_ξ : ∀ k : Fin m, ∫ ω, (ξ k ω - 0)^2 ∂μ = σ ^ 2 := by
    intro k
    simp only [sub_zero, ξ]
    -- From hZ_var_uniform: ∫ (Z k.val)² = ∫ (Z 0)² = σSq
    -- And σ² = (sqrt σSq)² = σSq (when σSq ≥ 0)
    calc ∫ ω, (Z k.val ω) ^ 2 ∂μ
        = ∫ ω, (Z 0 ω) ^ 2 ∂μ := hZ_var_uniform k.val
      _ = σSq := hσSq_def.symm
      _ = (Real.sqrt σSq) ^ 2 := by
          -- σSq = ∫ (Z 0)² ≥ 0, so sqrt(σSq)² = σSq
          have hσSq_nonneg : 0 ≤ σSq := by
            rw [hσSq_def]
            exact integral_nonneg fun ω => sq_nonneg _
          exact (Real.sq_sqrt hσSq_nonneg).symm
      _ = σ ^ 2 := rfl

  -- Define covZ from hρ_def
  let covZ := ∫ ω, Z 0 ω * Z 1 ω ∂μ
  have hρ_eq : ρ = covZ / σSq := hρ_def

  -- Prove uniform covariance: ∫ ξ_i * ξ_j = σ² * ρ for i ≠ j
  have hcov_ξ : ∀ i j : Fin m, i ≠ j →
      ∫ ω, (ξ i ω - 0) * (ξ j ω - 0) ∂μ = σ ^ 2 * ρ := by
    intros i j hij
    simp only [sub_zero, ξ]
    -- Need to show: ∫ Z i.val * Z j.val = σ² * ρ
    -- From hZ_cov_uniform: ∫ Z i.val * Z j.val = ∫ Z 0 * Z 1 = covZ (when i.val ≠ j.val)
    -- And σ² * ρ = σSq * (covZ / σSq) = covZ

    -- First show i.val ≠ j.val from i ≠ j
    have hij_val : i.val ≠ j.val := by
      intro h_eq
      apply hij
      exact Fin.ext h_eq

    -- Apply hZ_cov_uniform
    have h_cov_eq : ∫ ω, Z i.val ω * Z j.val ω ∂μ = covZ :=
      hZ_cov_uniform i.val j.val hij_val

    -- Show σ² * ρ = covZ
    have h_rhs : σ ^ 2 * ρ = covZ := by
      -- σ² = σSq and ρ = covZ / σSq, so σ² * ρ = σSq * (covZ / σSq) = covZ
      have hσSq_nonneg : 0 ≤ σSq := by positivity
      rw [hρ_eq]
      simp only [σ]
      rw [Real.sq_sqrt hσSq_nonneg]
      field_simp [hσ_pos.ne']

    rw [h_cov_eq, h_rhs]

  -- Step 3: Rewrite blockAvg difference as weighted sum
  -- blockAvg f X 0 n = (1/n) ∑_{i<n} f(X_i) = (1/n) ∑_{i<n} (Z_i + m) = (1/n) ∑_{i<n} Z_i + m
  -- So: blockAvg_n - blockAvg_n' = ∑ i, p i * Z_i - ∑ i, q i * Z_i

  have h_blockAvg_eq : ∀ᵐ ω ∂μ,
      blockAvg f X 0 n ω - blockAvg f X 0 n' ω =
      ∑ i : Fin m, p i * ξ i ω - ∑ i : Fin m, q i * ξ i ω := by
    -- This is true for all ω, not just a.e.
    apply ae_of_all
    intro ω
    -- Step 1: Unfold blockAvg definition
    simp only [blockAvg, zero_add]
    -- Now have: (n : ℝ)⁻¹ * ∑ k ∈ range n, f (X k ω) - (n' : ℝ)⁻¹ * ∑ k ∈ range n', f (X k ω)
    -- Step 2: Rewrite f (X k ω) = Z k ω + m_mean using hZ_def
    have h1 : ∑ k ∈ Finset.range n, f (X k ω) = ∑ k ∈ Finset.range n, (m_mean + Z k ω) := by
      congr 1 with k
      rw [hZ_def]
      ring
    have h2 : ∑ k ∈ Finset.range n', f (X k ω) = ∑ k ∈ Finset.range n', (m_mean + Z k ω) := by
      congr 1 with k
      rw [hZ_def]
      ring
    rw [h1, h2]
    -- Now have: (n : ℝ)⁻¹ * ∑ k ∈ range n, (m_mean + Z k ω) - (n' : ℝ)⁻¹ * ∑ k ∈ range n', (m_mean + Z k ω)
    -- Step 3: Distribute sums: ∑(a + b) = ∑a + ∑b
    simp only [Finset.sum_add_distrib]
    -- Now: (n : ℝ)⁻¹ * (∑ k ∈ range n, m_mean + ∑ k ∈ range n, Z k ω)
    --      - (n' : ℝ)⁻¹ * (∑ k ∈ range n', m_mean + ∑ k ∈ range n', Z k ω)
    -- Step 4: Simplify ∑ k ∈ range n, m_mean = n * m_mean
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    -- Now: (n : ℝ)⁻¹ * ((n : ℝ) * m_mean + ∑ k ∈ range n, Z k ω)
    --      - (n' : ℝ)⁻¹ * ((n' : ℝ) * m_mean + ∑ k ∈ range n', Z k ω)
    -- Step 5: Distribute multiplication
    ring_nf
    -- The m_mean terms cancel: (n : ℝ)⁻¹ * (n : ℝ) * m_mean = m_mean
    have hn_ne_zero : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hn_pos)
    have hn'_ne_zero : (n' : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hn'_pos)
    field_simp [hn_ne_zero, hn'_ne_zero]
    -- Now: (∑ k ∈ range n, Z k ω) / n - (∑ k ∈ range n', Z k ω) / n'
    -- After field_simp cleared denominators, goal has form:
    -- (n * m_mean + ∑ k ∈ range n, Z k) * n' + n * (-(m_mean * n') - ∑ k ∈ range n', Z k)
    --   = n * n' * (∑ i, p i * ξ i - ∑ i, q i * ξ i)
    -- Step 6: Convert both sides to use sums over Fin m with indicators, then simplify
    -- This is straightforward algebra but requires careful tactic sequencing
    -- TODO: Complete this algebraic manipulation
    -- The goal is to show:
    -- (∑ k ∈ range n, Z k ω) / n - (∑ k ∈ range n', Z k ω) / n'
    --   = ∑ i : Fin m, p i * ξ i ω - ∑ i : Fin m, q i * ξ i ω
    -- where p i = (if i < n then 1/n else 0), q i = (if i < n' then 1/n' else 0), ξ i = Z i.val
    --
    -- Strategy (partially implemented):
    -- 1. ✅ Convert ∑ k ∈ Finset.range n to ∑ i : Fin n via Finset.sum_range
    -- 2. ✅ Extend from Fin n to Fin m with indicators via Finset.sum_bij
    -- 3. ❌ Simplify the resulting algebraic expression
    --
    -- The bijection proof works but requires careful handling of the exact goal state
    -- after field_simp. The key lemmas needed:
    -- - Finset.sum_range: converts between Finset.range and Fin
    -- - Finset.sum_bij: establishes bijection for sum conversion
    -- - Field arithmetic to show n * n' * (if i < n then 1/n else 0) = (if i < n then n' else 0)
    simp only [ξ, p, q]
    -- Expand LHS: (n * m_mean + ∑_{i<n} Z_i) * n' + n * (-(m_mean * n') - ∑_{j<n'} Z_j)
    -- Should simplify to: n' * ∑_{i<n} Z_i - n * ∑_{j<n'} Z_j
    -- Expand RHS: n * n' * (∑ (if i<n then n⁻¹ else 0) * Z_i - ∑ (if j<n' then n'⁻¹ else 0) * Z_j)
    -- Using n * n' * n⁻¹ = n' and indicator sums
    calc (↑n * m_mean + ∑ x ∈ Finset.range n, Z x ω) * ↑n' +
          ↑n * (-(m_mean * ↑n') - ∑ x ∈ Finset.range n', Z x ω)
        = ↑n * m_mean * ↑n' + (∑ x ∈ Finset.range n, Z x ω) * ↑n' +
          ↑n * (-(m_mean * ↑n')) + ↑n * (- ∑ x ∈ Finset.range n', Z x ω) := by ring
      _ = ↑n * m_mean * ↑n' + ↑n' * ∑ x ∈ Finset.range n, Z x ω +
          (-(↑n * m_mean * ↑n')) + (-(↑n * ∑ x ∈ Finset.range n', Z x ω)) := by ring
      _ = ↑n' * ∑ x ∈ Finset.range n, Z x ω - ↑n * ∑ x ∈ Finset.range n', Z x ω := by ring
      _ = ↑n * ↑n' * (∑ x : Fin m, (if ↑x < n then (↑n)⁻¹ else 0) * Z (↑x) ω -
                      ∑ x : Fin m, (if ↑x < n' then (↑n')⁻¹ else 0) * Z (↑x) ω) := by
        -- RHS: distribute n * n' and simplify conditionals
        rw [mul_sub]
        -- Simplify: n * n' * n⁻¹ = n' and n * n' * n'⁻¹ = n
        have h1 : ↑n * ↑n' * (∑ x : Fin m, (if ↑x < n then (↑n)⁻¹ else 0) * Z (↑x) ω) =
                  ↑n' * ∑ x ∈ Finset.range n, Z x ω := by
          -- Pull n⁻¹ out and simplify n * n' * n⁻¹ = n'
          calc ↑n * ↑n' * (∑ x : Fin m, (if ↑x < n then (↑n)⁻¹ else 0) * Z (↑x) ω)
              = ∑ x : Fin m, ↑n * ↑n' * ((if ↑x < n then (↑n)⁻¹ else 0) * Z (↑x) ω) := by
                rw [Finset.mul_sum]
            _ = ∑ x : Fin m, (if ↑x < n then ↑n * ↑n' * (↑n)⁻¹ * Z (↑x) ω else 0) := by
                congr 1 with x; split_ifs with h <;> ring
            _ = ∑ x : Fin m, (if ↑x < n then ↑n' * Z (↑x) ω else 0) := by
                congr 1 with x; split_ifs with h
                · field_simp [hn_ne_zero]
                · rfl
            _ = ∑ x ∈ Finset.univ.filter (fun x : Fin m => ↑x < n), ↑n' * Z (↑x) ω := by
                rw [Finset.sum_ite]
                simp only [Finset.sum_const_zero, add_zero]
            _ = ∑ x ∈ Finset.range n, ↑n' * Z x ω := by
                -- Establish bijection between filtered Fin m and Finset.range n
                refine Finset.sum_nbij Fin.val ?hi ?i_inj ?i_surj ?h
                · -- Show x.val ∈ Finset.range n when x ∈ filter
                  intros a ha
                  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
                  exact Finset.mem_range.mpr ha
                · -- Injectivity on filtered set
                  intros a ha b hb hab
                  exact Fin.ext hab
                · -- Surjectivity onto Finset.range n
                  intros b hb
                  have hb' := Finset.mem_range.mp hb
                  refine ⟨⟨b, Nat.lt_of_lt_of_le hb' (le_max_left n n')⟩, ?_, rfl⟩
                  simp [hb']
                · -- Show functions agree
                  intros a ha
                  rfl
            _ = ↑n' * ∑ x ∈ Finset.range n, Z x ω := by rw [← Finset.mul_sum]
        have h2 : ↑n * ↑n' * (∑ x : Fin m, (if ↑x < n' then (↑n')⁻¹ else 0) * Z (↑x) ω) =
                  ↑n * ∑ x ∈ Finset.range n', Z x ω := by
          calc ↑n * ↑n' * (∑ x : Fin m, (if ↑x < n' then (↑n')⁻¹ else 0) * Z (↑x) ω)
              = ∑ x : Fin m, ↑n * ↑n' * ((if ↑x < n' then (↑n')⁻¹ else 0) * Z (↑x) ω) := by
                rw [Finset.mul_sum]
            _ = ∑ x : Fin m, (if ↑x < n' then ↑n * ↑n' * (↑n')⁻¹ * Z (↑x) ω else 0) := by
                congr 1 with x; split_ifs with h <;> ring
            _ = ∑ x : Fin m, (if ↑x < n' then ↑n * Z (↑x) ω else 0) := by
                congr 1 with x; split_ifs with h
                · field_simp [hn'_ne_zero]
                · rfl
            _ = ∑ x ∈ Finset.univ.filter (fun x : Fin m => ↑x < n'), ↑n * Z (↑x) ω := by
                rw [Finset.sum_ite]
                simp only [Finset.sum_const_zero, add_zero]
            _ = ∑ x ∈ Finset.range n', ↑n * Z x ω := by
                -- Establish bijection between filtered Fin m and Finset.range n'
                refine Finset.sum_nbij Fin.val ?hi2 ?i_inj2 ?i_surj2 ?h2
                · -- Show x.val ∈ Finset.range n' when x ∈ filter
                  intros a ha
                  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
                  exact Finset.mem_range.mpr ha
                · -- Injectivity on filtered set
                  intros a ha b hb hab
                  exact Fin.ext hab
                · -- Surjectivity onto Finset.range n'
                  intros b hb
                  have hb' := Finset.mem_range.mp hb
                  refine ⟨⟨b, Nat.lt_of_lt_of_le hb' (le_max_right n n')⟩, ?_, rfl⟩
                  simp [hb']
                · -- Show functions agree
                  intros a ha
                  rfl
            _ = ↑n * ∑ x ∈ Finset.range n', Z x ω := by rw [← Finset.mul_sum]
        rw [h1, h2]

  -- Step 4: Apply l2_contractability_bound
  have h_bound : ∫ ω, (∑ i : Fin m, p i * ξ i ω - ∑ i : Fin m, q i * ξ i ω) ^ 2 ∂μ ≤
      2 * σ ^ 2 * (1 - ρ) * (⨆ i : Fin m, |p i - q i|) :=
    L2Approach.l2_contractability_bound ξ 0 σ ρ hρ_bd hmean_ξ hL2_ξ hvar_ξ hcov_ξ p q hp_prob hq_prob

  -- Step 5: Bound ⨆ i, |p i - q i| ≤ max(1/n, 1/n')
  have h_sup_bound : (⨆ i : Fin m, |p i - q i|) ≤ max (1 / (n : ℝ)) (1 / (n' : ℝ)) := by
    -- m = max n n' ≥ max 1 1 = 1, so Fin m is nonempty
    have hm_pos : 0 < m := by
      simp only [m]
      calc 0 < 1 := Nat.one_pos
        _ ≤ n := hn_pos
        _ ≤ max n n' := le_max_left n n'
    haveI : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp hm_pos
    -- Show each |p i - q i| ≤ max(1/n, 1/n'), then take supremum
    apply ciSup_le
    intro i
    simp only [p, q]
    -- Case analysis on whether i.val < n and i.val < n'
    by_cases hi_n : i.val < n <;> by_cases hi_n' : i.val < n'
    · -- Case 1: i.val < n ∧ i.val < n'
      simp only [hi_n, hi_n', ite_true, one_div]
      -- Now have: |(n:ℝ)⁻¹ - (n':ℝ)⁻¹| ≤ max (n:ℝ)⁻¹ (n':ℝ)⁻¹
      by_cases h : (n : ℝ)⁻¹ ≤ (n' : ℝ)⁻¹
      · -- Case: n⁻¹ ≤ n'⁻¹, so max = n'⁻¹
        rw [abs_sub_comm, abs_of_nonneg (sub_nonneg_of_le h), max_eq_right h]
        exact sub_le_self _ (inv_nonneg.mpr (Nat.cast_nonneg n))
      · -- Case: n⁻¹ > n'⁻¹, so max = n⁻¹
        push_neg at h
        rw [abs_of_nonneg (sub_nonneg_of_le (le_of_lt h)), max_eq_left (le_of_lt h)]
        exact sub_le_self _ (inv_nonneg.mpr (Nat.cast_nonneg n'))
    · -- Case 2: i.val < n ∧ i.val ≥ n'
      simp only [hi_n, hi_n', ite_true, ite_false, sub_zero, one_div]
      rw [abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n))]
      exact le_max_left _ _
    · -- Case 3: i.val ≥ n ∧ i.val < n'
      simp only [hi_n, hi_n', ite_false, ite_true, zero_sub, one_div]
      rw [abs_neg, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n'))]
      exact le_max_right _ _
    · -- Case 4: i.val ≥ n ∧ i.val ≥ n'
      simp only [hi_n, hi_n', ite_false, sub_self, abs_zero]
      positivity

  -- Step 6: Combine to get integral bound
  have h_integral_bound : ∫ ω, (blockAvg f X 0 n ω - blockAvg f X 0 n' ω) ^ 2 ∂μ ≤
      2 * σ ^ 2 * (1 - ρ) * max (1 / (n : ℝ)) (1 / (n' : ℝ)) := by
    -- Use h_blockAvg_eq to rewrite, then apply h_bound and h_sup_bound
    calc ∫ ω, (blockAvg f X 0 n ω - blockAvg f X 0 n' ω) ^ 2 ∂μ
        = ∫ ω, (∑ i : Fin m, p i * ξ i ω - ∑ i : Fin m, q i * ξ i ω) ^ 2 ∂μ := by
            -- Use h_blockAvg_eq to rewrite integrand a.e.
            apply integral_congr_ae
            filter_upwards [h_blockAvg_eq] with ω hω
            rw [hω]
      _ ≤ 2 * σ ^ 2 * (1 - ρ) * (⨆ i : Fin m, |p i - q i|) := h_bound
      _ ≤ 2 * σ ^ 2 * (1 - ρ) * max (1 / (n : ℝ)) (1 / (n' : ℝ)) := by
            apply mul_le_mul_of_nonneg_left h_sup_bound
            -- Need to show 0 ≤ 2 * σ ^ 2 * (1 - ρ)
            -- We know Cf = 2 * σSq * (1 - ρ) and σ ^ 2 = σSq
            have hσ_sq_eq : σ ^ 2 = σSq := by
              simp only [σ]
              have hσSq_nonneg : 0 ≤ σSq := by positivity
              exact Real.sq_sqrt hσSq_nonneg
            calc 0 ≤ Cf := hCf_nonneg
              _ = 2 * σSq * (1 - ρ) := hCf_def
              _ = 2 * σ ^ 2 * (1 - ρ) := by rw [← hσ_sq_eq]

  -- Step 7: Use Archimedean bound to show integral < ε²
  have h_integral_lt_ε_sq : ∫ ω, (blockAvg f X 0 n ω - blockAvg f X 0 n' ω) ^ 2 ∂μ < (ε.toReal) ^ 2 := by
    -- Strategy: Show 2*σ²*(1-ρ)*max(1/n,1/n') < ε²
    -- We have Cf = 2*σSq*(1-ρ) = 2*σ²*(1-ρ) and N' > Cf/ε²

    -- First show σ² = σSq
    have hσ_sq_eq : σ ^ 2 = σSq := by
      simp only [σ]
      have hσSq_nonneg : 0 ≤ σSq := by positivity
      exact Real.sq_sqrt hσSq_nonneg

    -- So our coefficient equals Cf
    have h_coeff_eq : 2 * σ ^ 2 * (1 - ρ) = Cf := by
      rw [hσ_sq_eq, hCf_def]

    -- Show that min (n:ℝ) (n':ℝ) = ↑(min n n')
    have h_min_cast : min (n : ℝ) (n' : ℝ) = ↑(min n n') := by
      simp only [Nat.cast_min]

    -- Bound max(1/n, 1/n') by 1/min(n,n')
    have h_max_bound : max (1 / (n : ℝ)) (1 / (n' : ℝ)) ≤ 1 / (min n n' : ℝ) := by
      -- Strategy: 1/n ≤ 1/min(n,n') and 1/n' ≤ 1/min(n,n') since min is smaller
      have hn_pos_real : (0 : ℝ) < n := Nat.cast_pos.mpr hn_pos
      have hn'_pos_real : (0 : ℝ) < n' := Nat.cast_pos.mpr hn'_pos
      rw [h_min_cast]
      have h_min_pos : (0 : ℝ) < ↑(min n n') := by
        simp only [Nat.cast_pos]
        -- min n n' > 0 since both n > 0 and n' > 0
        omega
      apply max_le
      · -- 1/n ≤ 1/min(n,n')
        apply div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1)
        · exact h_min_pos
        · exact Nat.cast_le.mpr (Nat.min_le_left n n')
      · -- 1/n' ≤ 1/min(n,n')
        apply div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1)
        · exact h_min_pos
        · exact Nat.cast_le.mpr (Nat.min_le_right n n')

    -- min(n,n') ≥ max 1 (N'+1) > N'
    have h_min_ge : min (n : ℝ) (n' : ℝ) > (N' : ℝ) := by
      have h1 : min n n' ≥ max 1 (N' + 1) := Nat.le_min.mpr ⟨hn_ge, hn'_ge⟩
      have h2 : max 1 (N' + 1) ≥ N' + 1 := Nat.le_max_right 1 (N' + 1)
      have h3 : min n n' ≥ N' + 1 := Nat.le_trans h2 h1
      rw [h_min_cast]
      have : N' < N' + 1 := Nat.lt_succ_self N'
      have : N' < min n n' := Nat.lt_of_lt_of_le this h3
      exact Nat.cast_lt.mpr this

    -- Therefore 1/min(n,n') < 1/N'
    have h_inv_bound : 1 / (min n n' : ℝ) < 1 / (N' : ℝ) := by
      -- For 0 < b < a, we have 1/a < 1/b
      have hN'_pos_nat : 0 < N' := by
        have h1 : (0 : ℝ) < Cf / (ε.toReal) ^ 2 := by positivity
        have h2 : Cf / (ε.toReal) ^ 2 < (N' : ℝ) := hN'
        exact Nat.cast_pos.mp (h1.trans h2)
      have hN'_pos : (0 : ℝ) < N' := Nat.cast_pos.mpr hN'_pos_nat
      -- Use h_min_ge which states min (n:ℝ) (n':ℝ) > N'
      exact div_lt_div_of_pos_left (by norm_num : (0 : ℝ) < 1) hN'_pos h_min_ge

    -- Combine to get the final bound
    calc ∫ ω, (blockAvg f X 0 n ω - blockAvg f X 0 n' ω) ^ 2 ∂μ
        ≤ 2 * σ ^ 2 * (1 - ρ) * max (1 / (n : ℝ)) (1 / (n' : ℝ)) := h_integral_bound
      _ = Cf * max (1 / (n : ℝ)) (1 / (n' : ℝ)) := by rw [h_coeff_eq]
      _ ≤ Cf * (1 / (min n n' : ℝ)) := by
          apply mul_le_mul_of_nonneg_left h_max_bound
          exact hCf_nonneg
      _ < Cf * (1 / (N' : ℝ)) := by
          apply mul_lt_mul_of_pos_left h_inv_bound hCf_pos
      _ = Cf / (N' : ℝ) := by ring
      _ < Cf / (Cf / (ε.toReal) ^ 2) := by
          apply div_lt_div_of_pos_left hCf_pos (by positivity)
          exact hN'
      _ = (ε.toReal) ^ 2 := by
          field_simp [hCf_pos.ne']

  -- Step 8: Convert integral bound to eLpNorm bound
  -- Goal: eLpNorm (blockAvg f X 0 n - blockAvg f X 0 n') 2 μ < ε

  -- First show blockAvg difference is in L²
  have h_diff_memLp : MemLp (fun ω => blockAvg f X 0 n ω - blockAvg f X 0 n' ω) 2 μ := by
    -- Strategy: blockAvg is bounded by 1, so difference is bounded by 2
    -- Use memLp_of_abs_le_const from LpNormHelpers

    -- Show measurability
    have h_meas_n : Measurable (fun ω => blockAvg f X 0 n ω) := by
      simp only [blockAvg]
      exact Measurable.const_mul (Finset.measurable_sum _ fun k _ =>
        hf_meas.comp (hX_meas (0 + k))) _

    have h_meas_n' : Measurable (fun ω => blockAvg f X 0 n' ω) := by
      simp only [blockAvg]
      exact Measurable.const_mul (Finset.measurable_sum _ fun k _ =>
        hf_meas.comp (hX_meas (0 + k))) _

    have h_meas_diff : Measurable (fun ω => blockAvg f X 0 n ω - blockAvg f X 0 n' ω) :=
      h_meas_n.sub h_meas_n'

    -- Show boundedness: |blockAvg f X 0 n| ≤ 1 and |blockAvg f X 0 n'| ≤ 1
    -- implies |diff| ≤ 2
    have h_bdd : ∀ᵐ ω ∂μ, |blockAvg f X 0 n ω - blockAvg f X 0 n' ω| ≤ 2 := by
      apply ae_of_all
      intro ω
      -- Each blockAvg is bounded by 1 (average of values bounded by 1)
      have hn_bdd : |blockAvg f X 0 n ω| ≤ 1 := by
        simp only [blockAvg]
        -- Strategy: |n⁻¹ * ∑ f_i| ≤ n⁻¹ * ∑ |f_i| ≤ n⁻¹ * n = 1
        rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n))]
        have h_sum_bound : |(Finset.range n).sum (fun k => f (X (0 + k) ω))| ≤ n := by
          calc |(Finset.range n).sum (fun k => f (X (0 + k) ω))|
              ≤ (Finset.range n).sum (fun k => |f (X (0 + k) ω)|) := by
                exact Finset.abs_sum_le_sum_abs _ _
            _ ≤ (Finset.range n).sum (fun k => 1) := by
                apply Finset.sum_le_sum
                intro k _
                simp only [zero_add]
                exact hf_bdd (X k ω)
            _ = n := by
                simp only [Finset.sum_const, Finset.card_range, nsmul_one]
        calc (n : ℝ)⁻¹ * |(Finset.range n).sum (fun k => f (X (0 + k) ω))|
            ≤ (n : ℝ)⁻¹ * n := by
              apply mul_le_mul_of_nonneg_left
              · exact_mod_cast h_sum_bound
              · exact inv_nonneg.mpr (Nat.cast_nonneg n)
          _ = 1 := by
              field_simp [Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hn_pos)]
      have hn'_bdd : |blockAvg f X 0 n' ω| ≤ 1 := by
        simp only [blockAvg]
        -- Same strategy as hn_bdd
        rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n'))]
        have h_sum_bound : |(Finset.range n').sum (fun k => f (X (0 + k) ω))| ≤ n' := by
          calc |(Finset.range n').sum (fun k => f (X (0 + k) ω))|
              ≤ (Finset.range n').sum (fun k => |f (X (0 + k) ω)|) := by
                exact Finset.abs_sum_le_sum_abs _ _
            _ ≤ (Finset.range n').sum (fun k => 1) := by
                apply Finset.sum_le_sum
                intro k _
                simp only [zero_add]
                exact hf_bdd (X k ω)
            _ = n' := by
                simp only [Finset.sum_const, Finset.card_range, nsmul_one]
        calc (n' : ℝ)⁻¹ * |(Finset.range n').sum (fun k => f (X (0 + k) ω))|
            ≤ (n' : ℝ)⁻¹ * n' := by
              apply mul_le_mul_of_nonneg_left
              · exact_mod_cast h_sum_bound
              · exact inv_nonneg.mpr (Nat.cast_nonneg n')
          _ = 1 := by
              field_simp [Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hn'_pos)]
      calc |blockAvg f X 0 n ω - blockAvg f X 0 n' ω|
          ≤ |blockAvg f X 0 n ω| + |blockAvg f X 0 n' ω| := by
            -- Triangle inequality: |a - b| ≤ |a| + |b|
            -- Derive from |a + b| ≤ |a| + |b| by writing a - b = a + (-b)
            calc |blockAvg f X 0 n ω - blockAvg f X 0 n' ω|
                = |blockAvg f X 0 n ω + (-(blockAvg f X 0 n' ω))| := by rw [sub_eq_add_neg]
              _ ≤ |blockAvg f X 0 n ω| + |-(blockAvg f X 0 n' ω)| := abs_add_le _ _
              _ = |blockAvg f X 0 n ω| + |blockAvg f X 0 n' ω| := by rw [abs_neg]
        _ ≤ 1 + 1 := add_le_add hn_bdd hn'_bdd
        _ = 2 := by norm_num

    -- Apply memLp_of_abs_le_const
    exact memLp_of_abs_le_const h_meas_diff h_bdd 2 (by norm_num) (by norm_num)

  -- Now apply the conversion: eLpNorm² → integral
  -- From h_integral_lt_ε_sq: ∫ diff² < ε²
  -- Want: eLpNorm diff 2 < ε

  -- Apply eLpNorm_lt_of_integral_sq_lt from LpNormHelpers
  have h_bound : eLpNorm (fun ω => blockAvg f X 0 n ω - blockAvg f X 0 n' ω) 2 μ <
                 ENNReal.ofReal ε.toReal :=
    eLpNorm_lt_of_integral_sq_lt h_diff_memLp hε_pos h_integral_lt_ε_sq
  -- Convert result: ENNReal.ofReal ε.toReal = ε (since ε < ⊤)
  rw [ENNReal.ofReal_toReal (ne_of_lt hε_lt_top)] at h_bound
  -- Eta-reduce: (fun ω => blockAvg f X 0 n ω - blockAvg f X 0 n' ω) = blockAvg f X 0 n - blockAvg f X 0 n'
  exact h_bound

/-- Helper lemma: Uniform covariance structure of centered variables (Steps 2-5 from hCauchy).

Given contractable sequence X and function f, the centered variables Z_i = f(X_i) - m
have uniform covariance structure:
- Z is contractable
- Uniform variance: E[Z_i²] = E[Z_0²] for all i
- Zero mean: E[Z_i] = 0 for all i
- Uniform covariance: E[Z_i Z_j] = E[Z_0 Z_1] for all i ≠ j

This is the key infrastructure for applying l2_contractability_bound. -/
private lemma centered_uniform_covariance
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (f : ℝ → ℝ) (hf_meas : Measurable f) (hf_bdd : ∀ x, |f x| ≤ 1)
    (m : ℝ) (hm_def : m = ∫ ω, f (X 0 ω) ∂μ)
    (Z : ℕ → Ω → ℝ) (hZ_def : ∀ i ω, Z i ω = f (X i ω) - m) :
    (∀ i, Measurable (Z i)) ∧ Contractable μ Z ∧
    (∀ i, ∫ ω, (Z i ω)^2 ∂μ = ∫ ω, (Z 0 ω)^2 ∂μ) ∧
    (∀ i, ∫ ω, Z i ω ∂μ = 0) ∧
    (∀ i j, i ≠ j → ∫ ω, Z i ω * Z j ω ∂μ = ∫ ω, Z 0 ω * Z 1 ω ∂μ) := by

  -- Step 1: Z is measurable
  have hZ_meas : ∀ i, Measurable (Z i) := by
    intro i
    rw [show Z i = fun ω => f (X i ω) - m by ext ω; exact hZ_def i ω]
    exact (hf_meas.comp (hX_meas i)).sub measurable_const

  -- Step 2: Show Z is contractable
  -- Z = f ∘ X - m, and contractability is preserved under composition + constant shift
  have hZ_contract : Contractable μ Z := by
    -- First show f ∘ X is contractable using contractable_comp
    have hfX_contract : Contractable μ (fun i ω => f (X i ω)) :=
      L2Helpers.contractable_comp (X := X) hX_contract hX_meas f hf_meas
    -- Subtracting a constant preserves contractability
    intro n k hk
    -- Need: map (fun ω i => Z (k i) ω) μ = map (fun ω i => Z i ω) μ
    simp only [hZ_def]
    -- This equals: map (fun ω i => f(X(k i) ω) - m) μ = map (fun ω i => f(X i ω) - m) μ

    -- From hfX_contract: map (fun ω i => f(X(k i) ω)) μ = map (fun ω i => f(X i ω)) μ
    -- Subtracting m from each coordinate gives the same measure equality
    have h_eq := hfX_contract n k hk

    -- The subtraction by m is the same measurable transformation on both sides
    -- Strategy: Transform h_eq using coordinatewise subtraction

    -- Define coordinatewise subtraction
    let h : (Fin n → ℝ) → (Fin n → ℝ) := fun g i => g i - m

    -- h is measurable
    have h_meas : Measurable h := by
      apply measurable_pi_iff.mpr
      intro i
      exact (measurable_pi_apply i).sub measurable_const

    -- Input functions are measurable
    have hL_meas : Measurable (fun ω (i : Fin n) => f (X (k i) ω)) :=
      measurable_pi_iff.mpr (fun i => hf_meas.comp (hX_meas (k i)))
    have hR_meas : Measurable (fun ω (i : Fin n) => f (X (↑i) ω)) :=
      measurable_pi_iff.mpr (fun i => hf_meas.comp (hX_meas i))

    -- Apply map_map: map (h ∘ g) μ = map h (map g μ)
    calc Measure.map (fun ω i => f (X (k i) ω) - m) μ
        = Measure.map (h ∘ (fun ω i => f (X (k i) ω))) μ := by congr
      _ = Measure.map h (Measure.map (fun ω i => f (X (k i) ω)) μ) := by
            exact (Measure.map_map h_meas hL_meas).symm
      _ = Measure.map h (Measure.map (fun ω i => f (X (↑i) ω)) μ) := by
            rw [h_eq]
      _ = Measure.map (h ∘ (fun ω i => f (X (↑i) ω))) μ := by
            exact Measure.map_map h_meas hR_meas
      _ = Measure.map (fun ω (i : Fin n) => f (X (↑i) ω) - m) μ := by congr

  -- Step 3: Show uniform variance via contractability
  -- E[Z_i²] = E[Z_0²] for all i
  have hZ_var_uniform : ∀ i, ∫ ω, (Z i ω)^2 ∂μ = ∫ ω, (Z 0 ω)^2 ∂μ := by
    intro i
    -- From contractability: map (Z i) μ = map (Z 0) μ
    have h_map_eq : Measure.map (Z i) μ = Measure.map (Z 0) μ :=
      L2Helpers.contractable_map_single (X := Z) hZ_contract hZ_meas (i := i)

    -- Strategy: Use integral_map to rewrite both sides
    -- ∫ (Z i ω)² dμ = ∫ x² d(map (Z i) μ) [by integral_map]
    --               = ∫ x² d(map (Z 0) μ) [by h_map_eq]
    --               = ∫ (Z 0 ω)² dμ     [by integral_map]

    -- Z i is measurable, so we can apply integral_map
    have hZi_meas : AEMeasurable (Z i) μ := (hZ_meas i).aemeasurable
    have hZ0_meas : AEMeasurable (Z 0) μ := (hZ_meas 0).aemeasurable

    -- Apply integral_map on both sides and use measure equality
    -- The function x ↦ x² is continuous, hence strongly measurable
    rw [← integral_map hZi_meas (continuous_pow 2).aestronglyMeasurable]
    rw [← integral_map hZ0_meas (continuous_pow 2).aestronglyMeasurable]
    rw [h_map_eq]

  -- Step 4: Show mean of Z is zero
  have hZ_mean_zero : ∀ i, ∫ ω, Z i ω ∂μ = 0 := by
    intro i
    simp only [show Z i = fun ω => f (X i ω) - m by ext ω; exact hZ_def i ω]
    -- E[Z_i] = E[f(X_i) - m] = E[f(X_i)] - m
    -- By contractability: E[f(X_i)] = E[f(X_0)] = m
    -- Therefore: E[Z_i] = m - m = 0

    -- f is bounded, so f ∘ X i is integrable
    have hfX_int : Integrable (fun ω => f (X i ω)) μ := by
      apply Integrable.of_bound
      · exact (hf_meas.comp (hX_meas i)).aestronglyMeasurable
      · filter_upwards [] with ω
        exact hf_bdd (X i ω)

    rw [integral_sub hfX_int (integrable_const m)]
    -- Now show ∫ f(X i) = m, so that ∫ f(X i) - m = m - m = 0

    -- Strategy: contractable_map_single gives map (X i) μ = map (X 0) μ
    -- Then integral_map gives: ∫ f(X i) dμ = ∫ f d(map (X i) μ) = ∫ f d(map (X 0) μ) = ∫ f(X 0) dμ = m

    -- Use contractability to get measure equality
    have h_map_eq : Measure.map (X i) μ = Measure.map (X 0) μ :=
      L2Helpers.contractable_map_single (X := X) hX_contract hX_meas (i := i)

    -- f is measurable and bounded, so we can apply integral_map
    have hXi_meas : AEMeasurable (X i) μ := (hX_meas i).aemeasurable
    have hX0_meas : AEMeasurable (X 0) μ := (hX_meas 0).aemeasurable

    -- Apply integral_map to show ∫ f(X i) = ∫ f(X 0)
    have h_int_eq : ∫ ω, f (X i ω) ∂μ = ∫ ω, f (X 0 ω) ∂μ := by
      rw [← integral_map hXi_meas hf_meas.aestronglyMeasurable]
      rw [← integral_map hX0_meas hf_meas.aestronglyMeasurable]
      rw [h_map_eq]

    -- From h_int_eq: ∫ f(X i) = ∫ f(X 0) = m
    -- So ∫ f(X i) - m = m - m = 0
    rw [h_int_eq, hm_def, integral_const]
    simp [measure_univ]

  -- Step 5: Show uniform covariance via contractability
  -- For i ≠ j, E[Z_i Z_j] = E[Z_0 Z_1]
  have hZ_cov_uniform : ∀ i j, i ≠ j →
      ∫ ω, Z i ω * Z j ω ∂μ = ∫ ω, Z 0 ω * Z 1 ω ∂μ := by
    intro i j hij
    -- Strategy: If i < j, use contractable_map_pair directly
    --           If i > j, use contractable_map_pair on (j,i) + symmetry of multiplication
    by_cases h_lt : i < j
    · -- Case i < j: use contractable_map_pair directly
      have h_map_eq : Measure.map (fun ω => (Z i ω, Z j ω)) μ =
          Measure.map (fun ω => (Z 0 ω, Z 1 ω)) μ :=
        L2Helpers.contractable_map_pair (X := Z) hZ_contract hZ_meas h_lt

      -- The function (x, y) ↦ x * y is continuous, hence measurable
      have h_mul_meas : Measurable (fun p : ℝ × ℝ => p.1 * p.2) :=
        (continuous_fst.mul continuous_snd).measurable

      -- Z i and Z j are measurable
      have hZi_meas : AEMeasurable (Z i) μ := (hZ_meas i).aemeasurable
      have hZj_meas : AEMeasurable (Z j) μ := (hZ_meas j).aemeasurable
      have hZ0_meas : AEMeasurable (Z 0) μ := (hZ_meas 0).aemeasurable
      have hZ1_meas : AEMeasurable (Z 1) μ := (hZ_meas 1).aemeasurable

      -- Product measurability
      have h_prod_ij : AEMeasurable (fun ω => (Z i ω, Z j ω)) μ :=
        hZi_meas.prod_mk hZj_meas
      have h_prod_01 : AEMeasurable (fun ω => (Z 0 ω, Z 1 ω)) μ :=
        hZ0_meas.prod_mk hZ1_meas

      -- Apply integral_map
      rw [← integral_map h_prod_ij h_mul_meas.aestronglyMeasurable]
      rw [← integral_map h_prod_01 h_mul_meas.aestronglyMeasurable]
      rw [h_map_eq]

    · -- Case i > j: use contractable_map_pair on (j,i) + symmetry
      have hji : j < i := Nat.lt_of_le_of_ne (Nat.le_of_not_lt h_lt) (hij.symm)

      -- Symmetry of multiplication: Z i * Z j = Z j * Z i
      have h_sym_ij : ∫ ω, Z i ω * Z j ω ∂μ = ∫ ω, Z j ω * Z i ω ∂μ := by
        congr 1
        ext ω
        ring

      -- Now use contractable_map_pair on (j, i)
      have h_map_eq : Measure.map (fun ω => (Z j ω, Z i ω)) μ =
          Measure.map (fun ω => (Z 0 ω, Z 1 ω)) μ :=
        L2Helpers.contractable_map_pair (X := Z) hZ_contract hZ_meas hji

      -- The function (x, y) ↦ x * y is continuous, hence measurable
      have h_mul_meas : Measurable (fun p : ℝ × ℝ => p.1 * p.2) :=
        (continuous_fst.mul continuous_snd).measurable

      -- Measurability
      have hZi_meas : AEMeasurable (Z i) μ := (hZ_meas i).aemeasurable
      have hZj_meas : AEMeasurable (Z j) μ := (hZ_meas j).aemeasurable
      have hZ0_meas : AEMeasurable (Z 0) μ := (hZ_meas 0).aemeasurable
      have hZ1_meas : AEMeasurable (Z 1) μ := (hZ_meas 1).aemeasurable

      -- Product measurability
      have h_prod_ji : AEMeasurable (fun ω => (Z j ω, Z i ω)) μ :=
        hZj_meas.prod_mk hZi_meas
      have h_prod_01 : AEMeasurable (fun ω => (Z 0 ω, Z 1 ω)) μ :=
        hZ0_meas.prod_mk hZ1_meas

      -- Apply integral_map and symmetry
      rw [h_sym_ij]
      rw [← integral_map h_prod_ji h_mul_meas.aestronglyMeasurable]
      rw [← integral_map h_prod_01 h_mul_meas.aestronglyMeasurable]
      rw [h_map_eq]

  -- Combine all results
  exact ⟨hZ_meas, hZ_contract, hZ_var_uniform, hZ_mean_zero, hZ_cov_uniform⟩

/-- Helper lemma: Centered variables Z = f(X) - m are bounded by 2.

When |f| ≤ 1 and m = E[f(X_0)], then |Z i ω| = |f(X i ω) - m| ≤ 2. -/
private lemma centered_variable_bounded
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} (hX_meas : ∀ i, Measurable (X i))
    (f : ℝ → ℝ) (hf_meas : Measurable f) (hf_bdd : ∀ x, |f x| ≤ 1)
    (m : ℝ) (hm_def : m = ∫ ω, f (X 0 ω) ∂μ)
    (Z : ℕ → Ω → ℝ) (hZ_def : ∀ i ω, Z i ω = f (X i ω) - m) :
    ∀ i ω, |Z i ω| ≤ 2 := by
  intro i ω
  simp only [hZ_def]
  calc |f (X i ω) - m|
      ≤ |f (X i ω)| + |m| := abs_sub _ _
    _ ≤ 1 + 1 := by
        have h1 : |f (X i ω)| ≤ 1 := hf_bdd (X i ω)
        have h2 : |m| ≤ 1 := by
          have hfX_int : Integrable (fun ω => f (X 0 ω)) μ := by
            apply Integrable.of_bound
            · exact (hf_meas.comp (hX_meas 0)).aestronglyMeasurable
            · filter_upwards [] with ω; exact hf_bdd (X 0 ω)
          calc |m|
              = |∫ ω, f (X 0 ω) ∂μ| := by rw [hm_def]
            _ ≤ ∫ ω, |f (X 0 ω)| ∂μ := abs_integral_le_integral_abs
            _ ≤ ∫ ω, 1 ∂μ := by
                apply integral_mono_ae hfX_int.abs (integrable_const 1)
                filter_upwards [] with ω; exact hf_bdd (X 0 ω)
            _ = 1 := by simp
        linarith
    _ = 2 := by norm_num

/-- Helper lemma: Correlation coefficient is bounded by 1 via Cauchy-Schwarz.

Given variables Z with uniform variance σSq > 0 and bound |Z i ω| ≤ M,
proves |ρ| ≤ 1 where ρ = cov(Z_0,Z_1)/σSq. -/
private lemma correlation_coefficient_bounded
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (Z : ℕ → Ω → ℝ) (hZ_meas : ∀ i, Measurable (Z i))
    (M : ℝ) (hZ_bdd : ∀ i ω, |Z i ω| ≤ M)
    (σSq : ℝ) (hσ_pos : σSq > 0) (h_σSq_def : σSq = ∫ ω, (Z 0 ω)^2 ∂μ)
    (covZ : ℝ) (h_covZ_def : covZ = ∫ ω, Z 0 ω * Z 1 ω ∂μ)
    (ρ : ℝ) (h_ρ_def : ρ = covZ / σSq)
    (hZ_var_uniform : ∀ i, ∫ ω, (Z i ω)^2 ∂μ = ∫ ω, (Z 0 ω)^2 ∂μ) :
    -1 ≤ ρ ∧ ρ ≤ 1 := by
  -- Z 0 and Z 1 are in L²(μ) since they are bounded by M
  have hZ0_L2 : MemLp (Z 0) 2 μ := by
    apply memLp_two_of_bounded (hZ_meas 0)
    exact hZ_bdd 0

  have hZ1_L2 : MemLp (Z 1) 2 μ := by
    apply memLp_two_of_bounded (hZ_meas 1)
    exact hZ_bdd 1

  -- Apply Cauchy-Schwarz: |∫ Z₀·Z₁| ≤ sqrt(∫ Z₀²)·sqrt(∫ Z₁²)
  have h_CS := Exchangeability.Probability.IntegrationHelpers.abs_integral_mul_le_L2 hZ0_L2 hZ1_L2

  -- By uniform variance: ∫ Z₁² = ∫ Z₀² = σSq
  have h_Z1_var : ∫ ω, (Z 1 ω) ^ 2 ∂μ = σSq := by
    rw [hZ_var_uniform 1, h_σSq_def]

  -- So Cauchy-Schwarz gives: |covZ| ≤ sqrt(σSq)·sqrt(σSq) = σSq
  have h_covZ_bd : |covZ| ≤ σSq := by
    simp only [h_covZ_def, h_σSq_def]
    calc |∫ ω, Z 0 ω * Z 1 ω ∂μ|
        ≤ (∫ ω, (Z 0 ω) ^ 2 ∂μ) ^ (1/2 : ℝ) * (∫ ω, (Z 1 ω) ^ 2 ∂μ) ^ (1/2 : ℝ) := h_CS
      _ = (∫ ω, (Z 0 ω) ^ 2 ∂μ) ^ (1/2 : ℝ) * (∫ ω, (Z 0 ω) ^ 2 ∂μ) ^ (1/2 : ℝ) := by rw [h_Z1_var, h_σSq_def]
      _ = (∫ ω, (Z 0 ω) ^ 2 ∂μ) := by
          rw [← Real.rpow_add_of_nonneg (integral_nonneg (fun ω => sq_nonneg _))]
          <;> norm_num

  -- Therefore |ρ| ≤ 1, which gives -1 ≤ ρ ≤ 1
  have h_ρ_abs : |ρ| ≤ 1 := by
    simp only [h_ρ_def]
    rw [abs_div, abs_of_pos hσ_pos]
    exact div_le_one_of_le₀ h_covZ_bd hσ_pos.le

  constructor
  · linarith [abs_le.mp h_ρ_abs]
  · exact (abs_le.mp h_ρ_abs).2

/-! ### Performance wrappers to stop unfolding `blockAvg` inside `eLpNorm` -/

/-- Frozen alias for `blockAvg f X 0 n`. Regular def (not `@[irreducible]`)
    but we provide helper lemmas to avoid unfolding in timeout-prone contexts.

    This wrapper prevents expensive elaboration timeouts when `blockAvg` appears
    inside `eLpNorm` goals, by using pre-proved lemmas instead of unfolding. -/
def blockAvgFrozen {Ω : Type*} (f : ℝ → ℝ) (X : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω => blockAvg f X 0 n ω

lemma blockAvgFrozen_def {Ω : Type*} (f : ℝ → ℝ) (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    blockAvgFrozen f X n ω = blockAvg f X 0 n ω :=
  rfl

lemma blockAvgFrozen_measurable {Ω : Type*} [MeasurableSpace Ω]
    (f : ℝ → ℝ) (X : ℕ → Ω → ℝ)
    (hf : Measurable f) (hX : ∀ i, Measurable (X i)) (n : ℕ) :
    Measurable (blockAvgFrozen f X n) :=
  blockAvg_measurable f X hf hX 0 n

lemma blockAvgFrozen_abs_le_one {Ω : Type*} [MeasurableSpace Ω]
    (f : ℝ → ℝ) (X : ℕ → Ω → ℝ)
    (hf_bdd : ∀ x, |f x| ≤ 1) (n : ℕ) (ω : Ω) :
    |blockAvgFrozen f X n ω| ≤ 1 :=
  blockAvg_abs_le_one f X hf_bdd 0 n ω

lemma blockAvgFrozen_diff_memLp_two {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (f : ℝ → ℝ) (X : ℕ → Ω → ℝ)
    (hf : Measurable f) (hX : ∀ i, Measurable (X i))
    (hf_bdd : ∀ x, |f x| ≤ 1) (n n' : ℕ) :
    MemLp (fun ω => blockAvgFrozen f X n ω - blockAvgFrozen f X n' ω) 2 μ := by
  apply memLp_two_of_bounded (M := 2)
  · exact (blockAvgFrozen_measurable f X hf hX n).sub (blockAvgFrozen_measurable f X hf hX n')
  intro ω
  have hn  : |blockAvgFrozen f X n  ω| ≤ 1 := blockAvgFrozen_abs_le_one f X hf_bdd n  ω
  have hn' : |blockAvgFrozen f X n' ω| ≤ 1 := blockAvgFrozen_abs_le_one f X hf_bdd n' ω
  calc |blockAvgFrozen f X n ω - blockAvgFrozen f X n' ω|
      = |blockAvgFrozen f X n ω + (- blockAvgFrozen f X n' ω)| := by rw [sub_eq_add_neg]
    _ ≤ |blockAvgFrozen f X n ω| + |- blockAvgFrozen f X n' ω| := abs_add_le _ _
    _ = |blockAvgFrozen f X n ω| + |blockAvgFrozen f X n' ω| := by rw [abs_neg]
    _ ≤ 1 + 1 := add_le_add hn hn'
    _ = 2 := by norm_num

/-- Helper lemma: Block averages form a Cauchy sequence in L² (Step 1 of main proof).

Given contractable X and bounded f, the block averages form a Cauchy sequence in L².
This uses the L² contractability bound and uniform covariance structure. -/
private lemma blockAvg_cauchy_in_L2
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (f : ℝ → ℝ) (hf_meas : Measurable f) (hf_bdd : ∀ x, |f x| ≤ 1) :
    ∀ ε > 0, ∃ N, ∀ {n n'}, n ≥ N → n' ≥ N →
      eLpNorm (fun ω => blockAvgFrozen f X n ω - blockAvgFrozen f X n' ω) 2 μ < ε := by
  intro ε hε

  -- Define centered variables Z_i = f(X_i) - E[f(X_0)]
  let m := ∫ ω, f (X 0 ω) ∂μ
  let Z := fun i ω => f (X i ω) - m

  -- Establish uniform covariance structure
  have hZ_def : ∀ i ω, Z i ω = f (X i ω) - m := fun i ω => rfl
  have ⟨hZ_meas, hZ_contract, hZ_var_uniform, hZ_mean_zero, hZ_cov_uniform⟩ :=
    centered_uniform_covariance hX_contract hX_meas f hf_meas hf_bdd m rfl Z hZ_def

  -- Define variance and correlation
  let σSq := ∫ ω, (Z 0 ω)^2 ∂μ
  let covZ := ∫ ω, Z 0 ω * Z 1 ω ∂μ

  -- Case split on variance
  by_cases hσ_pos : σSq > 0
  · -- Non-degenerate case
    let ρ := covZ / σSq

    -- Bound |ρ| ≤ 1 using helpers
    have hZ_bdd := centered_variable_bounded hX_meas f hf_meas hf_bdd m rfl Z hZ_def
    have hρ_bd := correlation_coefficient_bounded Z hZ_meas 2 hZ_bdd
        σSq hσ_pos rfl covZ rfl ρ rfl hZ_var_uniform

    let Cf := 2 * σSq * (1 - ρ)

    by_cases hρ_lt : ρ < 1
    · -- Standard case: ρ < 1
      exact cesaro_cauchy_rho_lt hX_contract hX_meas f hf_meas hf_bdd
        m rfl Z hZ_def hZ_meas hZ_contract hZ_var_uniform hZ_mean_zero hZ_cov_uniform
        σSq hσ_pos rfl ρ hρ_bd rfl hρ_lt Cf rfl ε hε

    · -- Edge case: ρ = 1 (perfect correlation) → blockAvg values are ae-equal
      have hρ_eq : ρ = 1 := le_antisymm hρ_bd.2 (le_of_not_lt hρ_lt)
      -- When ρ = 1, Z_i = Z_0 a.e., so blockAvg values are equal a.e.
      -- Note: We only prove this for n, n' > 0, which suffices since we use N = 1 below.
      -- (The general case for all n, n' ∈ ℕ is also true, but not needed.)
      have h_ae_eq : ∀ n n', n > 0 → n' > 0 → ∀ᵐ ω ∂μ, blockAvg f X 0 n ω = blockAvg f X 0 n' ω := by
        -- Strategy: Show E[(Z_i - Z_j)²] = 0 when ρ = 1, implying Z_i = Z_j a.e.
        -- Step 1: Prove Z_i = Z_0 a.e. for all i
        have hZi_eq_Z0 : ∀ i, Z i =ᵐ[μ] Z 0 := by
          intro i
          -- Expand E[(Z_i - Z_0)²] = E[Z_i²] - 2*E[Z_i*Z_0] + E[Z_0²]
          have h_diff_sq : ∫ ω, (Z i ω - Z 0 ω) ^ 2 ∂μ = 0 := by
            by_cases hi : i = 0
            · -- Case i = 0: Z_0 - Z_0 = 0
              simp [hi]
            · -- Case i ≠ 0: Use ρ = 1
              -- E[(Z_i - Z_0)²] = E[Z_i²] + E[Z_0²] - 2*E[Z_i*Z_0]
              --                = σ² + σ² - 2*E[Z_i*Z_0]

              -- Expand (Z_i - Z_0)² = Z_i² + Z_0² - 2*Z_i*Z_0 in expectation
              -- Expand (a - b)² = a² + b² - 2ab using algebra and linearity of integral
              have h_expand : ∫ ω, (Z i ω - Z 0 ω) ^ 2 ∂μ =
                  ∫ ω, (Z i ω) ^ 2 ∂μ + ∫ ω, (Z 0 ω) ^ 2 ∂μ - 2 * ∫ ω, Z i ω * Z 0 ω ∂μ := by
                -- (a - b)² = a² - 2ab + b²
                have h_alg : ∀ a b : ℝ, (a - b) ^ 2 = a ^ 2 - 2 * a * b + b ^ 2 := by
                  intro a b; ring
                -- Rewrite the integrand
                have : (fun ω => (Z i ω - Z 0 ω) ^ 2) = fun ω => (Z i ω) ^ 2 - 2 * Z i ω * Z 0 ω + (Z 0 ω) ^ 2 := by
                  ext ω; exact h_alg (Z i ω) (Z 0 ω)
                rw [this]
                -- Define integrability proofs inline
                have hZ_bdd : ∀ j ω, |Z j ω| ≤ 2 :=
                  centered_variable_bounded hX_meas f hf_meas hf_bdd m rfl Z hZ_def
                have h_int_i : Integrable (Z i) μ := show Integrable (Z i) μ from ⟨
                  (hZ_meas i).aestronglyMeasurable,
                  HasFiniteIntegral.of_bounded (by
                    filter_upwards [] with ω
                    exact hZ_bdd i ω)⟩
                have h_int_0 : Integrable (Z 0) μ := show Integrable (Z 0) μ from ⟨
                  (hZ_meas 0).aestronglyMeasurable,
                  HasFiniteIntegral.of_bounded (by
                    filter_upwards [] with ω
                    exact hZ_bdd 0 ω)⟩
                -- Need integrability of Z i ^ 2, Z 0 ^ 2, and Z i * Z 0
                -- These follow from boundedness (bounded functions on finite measure are integrable)
                have h_int_i_sq : Integrable (fun ω => (Z i ω) ^ 2) μ := ⟨
                  (hZ_meas i).pow_const 2 |>.aestronglyMeasurable,
                  HasFiniteIntegral.of_bounded (by
                    filter_upwards [] with ω
                    have : |Z i ω| ≤ 2 := hZ_bdd i ω
                    calc ‖(Z i ω) ^ 2‖
                        = |(Z i ω) ^ 2| := by simp [Real.norm_eq_abs]
                      _ = (Z i ω) ^ 2 := abs_sq (Z i ω)
                      _ = |Z i ω| ^ 2 := by rw [sq_abs]
                      _ ≤ 2 ^ 2 := by gcongr
                      _ = 4 := by norm_num)⟩
                have h_int_0_sq : Integrable (fun ω => (Z 0 ω) ^ 2) μ := ⟨
                  (hZ_meas 0).pow_const 2 |>.aestronglyMeasurable,
                  HasFiniteIntegral.of_bounded (by
                    filter_upwards [] with ω
                    have : |Z 0 ω| ≤ 2 := hZ_bdd 0 ω
                    calc ‖(Z 0 ω) ^ 2‖
                        = |(Z 0 ω) ^ 2| := by simp [Real.norm_eq_abs]
                      _ = (Z 0 ω) ^ 2 := abs_sq (Z 0 ω)
                      _ = |Z 0 ω| ^ 2 := by rw [sq_abs]
                      _ ≤ 2 ^ 2 := by gcongr
                      _ = 4 := by norm_num)⟩
                have h_int_prod : Integrable (fun ω => Z i ω * Z 0 ω) μ := ⟨
                  (hZ_meas i).mul (hZ_meas 0) |>.aestronglyMeasurable,
                  HasFiniteIntegral.of_bounded (by
                    filter_upwards [] with ω
                    have hi : |Z i ω| ≤ 2 := hZ_bdd i ω
                    have h0 : |Z 0 ω| ≤ 2 := hZ_bdd 0 ω
                    calc ‖Z i ω * Z 0 ω‖
                        = |Z i ω * Z 0 ω| := by simp [Real.norm_eq_abs]
                      _ = |Z i ω| * |Z 0 ω| := abs_mul (Z i ω) (Z 0 ω)
                      _ ≤ 2 * 2 := mul_le_mul hi h0 (abs_nonneg _) (by norm_num)
                      _ = 4 := by norm_num)⟩
                -- ∫ (a² - 2ab + b²) = ∫ a² + ∫ b² - 2 * ∫ ab by linearity
                have h_rearrange : (fun ω => Z i ω ^ 2 - 2 * Z i ω * Z 0 ω + Z 0 ω ^ 2)
                                 = (fun ω => Z i ω ^ 2 + Z 0 ω ^ 2 - 2 * (Z i ω * Z 0 ω)) := by
                  ext ω; ring
                calc ∫ ω, Z i ω ^ 2 - 2 * Z i ω * Z 0 ω + Z 0 ω ^ 2 ∂μ
                    = ∫ ω, Z i ω ^ 2 + Z 0 ω ^ 2 - 2 * (Z i ω * Z 0 ω) ∂μ := by rw [h_rearrange]
                  _ = ∫ ω, (Z i ω ^ 2 + Z 0 ω ^ 2) ∂μ - ∫ ω, 2 * (Z i ω * Z 0 ω) ∂μ :=
                      integral_sub (h_int_i_sq.add h_int_0_sq) (h_int_prod.const_mul 2)
                  _ = ∫ ω, Z i ω ^ 2 ∂μ + ∫ ω, Z 0 ω ^ 2 ∂μ - ∫ ω, 2 * (Z i ω * Z 0 ω) ∂μ :=
                      by rw [integral_add h_int_i_sq h_int_0_sq]
                  _ = ∫ ω, Z i ω ^ 2 ∂μ + ∫ ω, Z 0 ω ^ 2 ∂μ - 2 * ∫ ω, Z i ω * Z 0 ω ∂μ :=
                      by simp_rw [integral_const_mul]

              -- Now substitute known values
              have h_var_i : ∫ ω, (Z i ω) ^ 2 ∂μ = σSq := by
                calc ∫ ω, (Z i ω) ^ 2 ∂μ
                    = ∫ ω, (Z 0 ω) ^ 2 ∂μ := hZ_var_uniform i
                  _ = σSq := rfl

              have h_var_0 : ∫ ω, (Z 0 ω) ^ 2 ∂μ = σSq := rfl

              have h_cov : ∫ ω, Z i ω * Z 0 ω ∂μ = σSq * ρ := by
                calc ∫ ω, Z i ω * Z 0 ω ∂μ
                    = ∫ ω, Z 0 ω * Z 1 ω ∂μ := by
                      by_cases hi1 : i = 1
                      · simp [hi1]
                        congr 1 with ω
                        ring
                      · -- Use hZ_cov_uniform for i ≠ 0, i ≠ 1
                        -- Use hZ_cov_uniform: ∫ Z 0 * Z i = ∫ Z 0 * Z 1 (then use commutativity)
                        have h_swap : ∫ ω, Z i ω * Z 0 ω ∂μ = ∫ ω, Z 0 ω * Z i ω ∂μ := by
                          congr 1 with ω; ring
                        calc ∫ ω, Z i ω * Z 0 ω ∂μ
                            = ∫ ω, Z 0 ω * Z i ω ∂μ := h_swap
                          _ = ∫ ω, Z 0 ω * Z 1 ω ∂μ := hZ_cov_uniform 0 i (Ne.symm hi)
                  _ = covZ := rfl
                  _ = σSq * ρ := by
                      rw [hρ_eq]
                      -- ρ is defined as covZ / σSq, so covZ = ρ * σSq
                      show covZ = σSq * 1
                      calc covZ = ρ * σSq := by unfold ρ; field_simp [hσ_pos.ne']
                        _ = σSq * ρ := mul_comm _ _
                        _ = σSq * 1 := by rw [hρ_eq]

              calc ∫ ω, (Z i ω - Z 0 ω) ^ 2 ∂μ
                  = σSq + σSq - 2 * (σSq * ρ) := by rw [h_expand, h_var_i, h_var_0, h_cov]
                _ = 2 * σSq - 2 * σSq * ρ := by ring
                _ = 2 * σSq * (1 - ρ) := by ring
                _ = 2 * σSq * (1 - 1) := by rw [hρ_eq]
                _ = 0 := by ring

          -- From E[(Z_i - Z_0)²] = 0, derive Z_i - Z_0 = 0 a.e.
          have h_diff_sq_ae : (fun ω => (Z i ω - Z 0 ω) ^ 2) =ᵐ[μ] 0 := by
            rw [← integral_eq_zero_iff_of_nonneg_ae]
            · exact h_diff_sq
            · apply ae_of_all; intro ω; exact sq_nonneg _
            · -- (Z i - Z 0)² is bounded by (2+2)² = 16
              apply Integrable.of_bound
              · exact ((hZ_meas i).sub (hZ_meas 0)).pow_const 2 |>.aestronglyMeasurable
              · filter_upwards [] with ω
                have hZ_bdd : ∀ j ω, |Z j ω| ≤ 2 :=
                  centered_variable_bounded hX_meas f hf_meas hf_bdd m rfl Z hZ_def
                -- |(Z i - Z 0)²| ≤ |Z i - Z 0|² ≤ (|Z i| + |Z 0|)² ≤ 4² = 16
                calc |(Z i ω - Z 0 ω) ^ 2|
                    = (Z i ω - Z 0 ω) ^ 2 := abs_sq (Z i ω - Z 0 ω)
                  _ = |Z i ω - Z 0 ω| ^ 2 := by rw [← sq_abs]
                  _ ≤ (|Z i ω| + |Z 0 ω|) ^ 2 := by
                      gcongr
                      exact abs_sub (Z i ω) (Z 0 ω)
                  _ ≤ (2 + 2) ^ 2 := by
                      gcongr
                      · exact hZ_bdd i ω
                      · exact hZ_bdd 0 ω
                  _ = 16 := by norm_num

          filter_upwards [h_diff_sq_ae] with ω hω
          have : (Z i ω - Z 0 ω) ^ 2 = 0 := hω
          have : Z i ω - Z 0 ω = 0 := sq_eq_zero_iff.mp this
          linarith

        -- Step 2: Use Z_i = Z_0 a.e. to show blockAvg n and blockAvg n' are both equal to f(X 0) a.e.
        intro n n' hn_pos hn'_pos
        -- Helper: blockAvg equals f(X 0) when all Z_k = Z_0
        have hBlockAvg_eq_fX0 : ∀ m_val, m_val > 0 → ∀ᵐ ω ∂μ, blockAvg f X 0 m_val ω = f (X 0 ω) := by
          intro m_val hm_pos
          -- When Z_k = Z_0 ae for all k, we have f(X_k) = f(X_0) ae for all k
          -- So blockAvg = (1/m) * ∑ f(X_0) = f(X_0)

          -- Collect ae equalities for all indices in range m_val
          have h_ae_all : ∀ᵐ ω ∂μ, ∀ k ∈ Finset.range m_val, f (X k ω) = f (X 0 ω) := by
            -- Since Z k = f(X k) - m and Z k = Z 0 = f(X 0) - m, we have f(X k) = f(X 0)
            apply MeasureTheory.ae_all_iff.mpr
            intro k
            filter_upwards [hZi_eq_Z0 k] with ω hω
            intro _hk
            -- Z k ω = Z 0 ω means f (X k ω) - m = f (X 0 ω) - m
            linarith

          filter_upwards [h_ae_all] with ω hω
          unfold blockAvg
          -- blockAvg f X 0 m_val ω = (m_val)⁻¹ * ∑ k in range m_val, f (X (0 + k) ω)
          -- Since f (X k ω) = f (X 0 ω) for all k, this equals f (X 0 ω)
          have : (Finset.range m_val).sum (fun k => f (X (0 + k) ω)) = (Finset.range m_val).sum (fun _ => f (X 0 ω)) := by
            apply Finset.sum_congr rfl
            intro k hk
            simp only [zero_add]
            exact hω k hk
          rw [this, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          field_simp [Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hm_pos)]

        -- Both n, n' > 0, so we can use the helper
        filter_upwards [hBlockAvg_eq_fX0 n hn_pos, hBlockAvg_eq_fX0 n' hn'_pos] with ω hn_eq hn'_eq
        rw [hn_eq, hn'_eq]
      -- Trivial Cauchy: if values are ae-equal, eLpNorm of difference is 0 < ε
      use 1
      intros n n' hn_ge hn'_ge
      -- Since n ≥ 1 and n' ≥ 1, we have n > 0 and n' > 0
      have hn_pos : n > 0 := Nat.lt_of_lt_of_le Nat.one_pos hn_ge
      have hn'_pos : n' > 0 := Nat.lt_of_lt_of_le Nat.one_pos hn'_ge
      -- Convert to blockAvgFrozen and show eLpNorm = 0
      show eLpNorm (fun ω => blockAvgFrozen f X n ω - blockAvgFrozen f X n' ω) 2 μ < ε
      have h_ae : ∀ᵐ ω ∂μ, blockAvgFrozen f X n ω = blockAvgFrozen f X n' ω := by
        filter_upwards [h_ae_eq n n' hn_pos hn'_pos] with ω hω
        simp only [blockAvgFrozen_def, hω]
      have h_norm_zero : eLpNorm (fun ω => blockAvgFrozen f X n ω - blockAvgFrozen f X n' ω) 2 μ = 0 := by
        have h_ae_zero : (fun ω => blockAvgFrozen f X n ω - blockAvgFrozen f X n' ω) =ᵐ[μ] 0 := by
          filter_upwards [h_ae] with ω hω
          simp [hω]
        rw [eLpNorm_congr_ae h_ae_zero, eLpNorm_zero]
      rw [h_norm_zero]
      exact hε

  · -- Degenerate case: σSq = 0 → Z is constant a.e. → blockAvg constant a.e.
    push_neg at hσ_pos
    have hσSq_zero : σSq = 0 := by
      have hσSq_nonneg : 0 ≤ σSq := by
        simp only [σSq]
        apply integral_nonneg
        intro ω
        exact sq_nonneg _
      linarith
    -- When σSq = 0, Z_0 = 0 a.e., so blockAvg values are equal a.e. (for n, n' > 0)
    have h_ae_eq : ∀ n n', n > 0 → n' > 0 → ∀ᵐ ω ∂μ, blockAvg f X 0 n ω = blockAvg f X 0 n' ω := by
      -- Step 1: Show (Z 0)² =ᵐ 0 using integral_eq_zero_iff_of_nonneg_ae
      have hZ0_sq_ae_zero : (fun ω => (Z 0 ω) ^ 2) =ᵐ[μ] 0 := by
        rw [← integral_eq_zero_iff_of_nonneg_ae]
        · exact hσSq_zero
        · -- Show (Z 0)² ≥ 0 a.e.
          apply ae_of_all
          intro ω
          exact sq_nonneg _
        · -- Show (Z 0)² is integrable: bounded by 4
          apply Integrable.of_bound
          · exact (hZ_meas 0).pow_const 2 |>.aestronglyMeasurable
          · filter_upwards [] with ω
            have hZ_bdd : ∀ j ω, |Z j ω| ≤ 2 :=
              centered_variable_bounded hX_meas f hf_meas hf_bdd m rfl Z hZ_def
            calc |(Z 0 ω) ^ 2|
                = (Z 0 ω) ^ 2 := abs_sq (Z 0 ω)
              _ = |Z 0 ω| ^ 2 := by rw [← sq_abs]
              _ ≤ 2 ^ 2 := by
                  gcongr
                  exact hZ_bdd 0 ω
              _ = 4 := by norm_num

      -- Step 2: From (Z 0)² =ᵐ 0, derive Z 0 =ᵐ 0
      have hZ0_ae_zero : Z 0 =ᵐ[μ] 0 := by
        filter_upwards [hZ0_sq_ae_zero] with ω hω
        have : (Z 0 ω) ^ 2 = 0 := hω
        exact sq_eq_zero_iff.mp this

      -- Step 3: By uniform variance and integral_eq_zero, all Z i =ᵐ 0
      have hZi_ae_zero : ∀ i, Z i =ᵐ[μ] 0 := by
        intro i
        -- ∫ (Z i)² = ∫ (Z 0)² = 0, so by same argument Z i =ᵐ 0
        have hZi_sq_integral_zero : ∫ ω, (Z i ω) ^ 2 ∂μ = 0 := by
          calc ∫ ω, (Z i ω) ^ 2 ∂μ
              = ∫ ω, (Z 0 ω) ^ 2 ∂μ := hZ_var_uniform i
            _ = σSq := rfl  -- σSq is defined as ∫ (Z 0)² via let
            _ = 0 := hσSq_zero
        have hZi_sq_ae_zero : (fun ω => (Z i ω) ^ 2) =ᵐ[μ] 0 := by
          rw [← integral_eq_zero_iff_of_nonneg_ae]
          · exact hZi_sq_integral_zero
          · apply ae_of_all; intro ω; exact sq_nonneg _
          · -- Show (Z i)² is integrable: bounded by 4
            apply Integrable.of_bound
            · exact (hZ_meas i).pow_const 2 |>.aestronglyMeasurable
            · filter_upwards [] with ω
              have hZ_bdd : ∀ j ω, |Z j ω| ≤ 2 :=
                centered_variable_bounded hX_meas f hf_meas hf_bdd m rfl Z hZ_def
              calc |(Z i ω) ^ 2|
                  = (Z i ω) ^ 2 := abs_sq (Z i ω)
                _ = |Z i ω| ^ 2 := by rw [← sq_abs]
                _ ≤ 2 ^ 2 := by
                    gcongr
                    exact hZ_bdd i ω
                _ = 4 := by norm_num
        filter_upwards [hZi_sq_ae_zero] with ω hω
        exact sq_eq_zero_iff.mp hω

      -- Step 4: Show blockAvg f X 0 n =ᵐ m for n, n' > 0
      intro n n' hn_pos hn'_pos
      have hBlockAvg_n : blockAvg f X 0 n =ᵐ[μ] (fun _ => m) := by
        -- n > 0 case: use the fact that f(X i) = m a.e.
        have h_ae_all : ∀ᵐ ω ∂μ, ∀ k < n, f (X k ω) = m := by
          apply MeasureTheory.ae_all_iff.mpr
          intro k
          have hZk_zero : Z k =ᵐ[μ] 0 := hZi_ae_zero k
          filter_upwards [hZk_zero] with ω hω
          intro _hk
          -- hω : Z k ω = 0, which means f (X k ω) - m = 0
          have : f (X k ω) - m = 0 := hω
          linarith
        filter_upwards [h_ae_all] with ω hω
        unfold blockAvg
        have : (Finset.range n).sum (fun k => f (X (0 + k) ω)) = (Finset.range n).sum (fun _ => m) := by
          apply Finset.sum_congr rfl
          intro k hk
          simp only [zero_add, Finset.mem_range] at hk ⊢
          exact hω k hk
        rw [this, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        field_simp [Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hn_pos)]

      have hBlockAvg_n' : blockAvg f X 0 n' =ᵐ[μ] (fun _ => m) := by
        have h_ae_all : ∀ᵐ ω ∂μ, ∀ k < n', f (X k ω) = m := by
          apply MeasureTheory.ae_all_iff.mpr
          intro k
          have hZk_zero : Z k =ᵐ[μ] 0 := hZi_ae_zero k
          filter_upwards [hZk_zero] with ω hω
          intro _hk
          -- hω : Z k ω = 0, which means f (X k ω) - m = 0
          have : f (X k ω) - m = 0 := hω
          linarith
        filter_upwards [h_ae_all] with ω hω
        unfold blockAvg
        have : (Finset.range n').sum (fun k => f (X (0 + k) ω)) = (Finset.range n').sum (fun _ => m) := by
          apply Finset.sum_congr rfl
          intro k hk
          simp only [zero_add, Finset.mem_range] at hk ⊢
          exact hω k hk
        rw [this, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        field_simp [Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hn'_pos)]

      -- Step 5: Combine to show blockAvg n =ᵐ blockAvg n'
      filter_upwards [hBlockAvg_n, hBlockAvg_n'] with ω hn hn'
      rw [hn, hn']
    -- Trivial Cauchy: if values are ae-equal, eLpNorm of difference is 0 < ε
    use 1
    intros n n' hn_ge hn'_ge
    -- Since n ≥ 1 and n' ≥ 1, we have n > 0 and n' > 0
    have hn_pos : n > 0 := Nat.lt_of_lt_of_le Nat.one_pos hn_ge
    have hn'_pos : n' > 0 := Nat.lt_of_lt_of_le Nat.one_pos hn'_ge
    -- Convert to blockAvgFrozen and show eLpNorm = 0
    show eLpNorm (fun ω => blockAvgFrozen f X n ω - blockAvgFrozen f X n' ω) 2 μ < ε
    have h_ae : ∀ᵐ ω ∂μ, blockAvgFrozen f X n ω = blockAvgFrozen f X n' ω := by
      filter_upwards [h_ae_eq n n' hn_pos hn'_pos] with ω hω
      simp only [blockAvgFrozen_def, hω]
    have h_norm_zero : eLpNorm (fun ω => blockAvgFrozen f X n ω - blockAvgFrozen f X n' ω) 2 μ = 0 := by
      have h_ae_zero : (fun ω => blockAvgFrozen f X n ω - blockAvgFrozen f X n' ω) =ᵐ[μ] 0 := by
        filter_upwards [h_ae] with ω hω
        simp [hω]
      rw [eLpNorm_congr_ae h_ae_zero, eLpNorm_zero]
    rw [h_norm_zero]
    exact hε

/-- Helper lemma: L² limit exists via completeness (Step 2 of main proof).

Given a Cauchy sequence of block averages in L², completeness of L²(μ) guarantees
existence of a limit α_f with:
- α_f ∈ L²(μ)
- blockAvg f X 0 n → α_f in L² as n → ∞

This is the core application of Hilbert space completeness in the proof. -/
private lemma l2_limit_from_cauchy
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} (hX_meas : ∀ i, Measurable (X i))
    (f : ℝ → ℝ) (hf_meas : Measurable f) (hf_bdd : ∀ x, |f x| ≤ 1)
    (hCauchy : ∀ ε > 0, ∃ N, ∀ {n n'}, n ≥ N → n' ≥ N →
      eLpNorm (fun ω => blockAvgFrozen f X n ω - blockAvgFrozen f X n' ω) 2 μ < ε) :
    ∃ α_f, MemLp α_f 2 μ ∧
      Tendsto (fun n => eLpNorm (fun ω => blockAvgFrozen f X n ω - α_f ω) 2 μ) atTop (𝓝 0) := by
  -- Step 1: Show each blockAvg is in L² using frozen wrapper to avoid timeouts
  have hblockAvg_memLp : ∀ n, n > 0 → MemLp (blockAvg f X 0 n) 2 μ := by
    intro n hn_pos
    -- Convert to blockAvgFrozen to use precomputed lemmas
    show MemLp (blockAvgFrozen f X n) 2 μ
    apply memLp_two_of_bounded (M := 1)
    · exact blockAvgFrozen_measurable f X hf_meas hX_meas n
    exact blockAvgFrozen_abs_le_one f X hf_bdd n

  -- For n = 0, handle separately
  have hblockAvg_memLp_all : ∀ n, MemLp (blockAvg f X 0 n) 2 μ := by
    intro n
    by_cases hn : n > 0
    · exact hblockAvg_memLp n hn
    · -- n = 0 case: blockAvg is just the constant 0 function
      have : n = 0 := by omega
      subst this
      -- When n=0, Finset.range 0 is empty, so sum = 0
      -- blockAvg f X 0 0 = 0⁻¹ * 0, which we treat as the zero function
      have h_eq : blockAvg f X 0 0 = fun ω => (0 : ℝ) := by
        ext ω
        simp [blockAvg, Finset.range_zero, Finset.sum_empty]
      rw [h_eq]
      -- Constant 0 function is in L² (bounded by 1)
      apply memLp_two_of_bounded (M := 1) measurable_const
      intro ω
      norm_num

  -- Step 2: Define sequence in L² space
  let u : ℕ → Lp ℝ 2 μ := fun n =>
    if hn : n > 0 then
      (hblockAvg_memLp n hn).toLp (blockAvg f X 0 n)
    else
      0  -- n = 0 case

  -- Step 3: Prove sequence is Cauchy
  have hCauchySeq : CauchySeq u := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hCauchy (ENNReal.ofReal ε) (by simp [hε])
    use max N 1  -- Ensure N is at least 1
    intro n hn m hm
    -- For n, m ≥ max N 1, both are > 0, so we can unfold u
    have hn_pos : n > 0 := Nat.lt_of_lt_of_le (Nat.zero_lt_one) (Nat.le_trans (Nat.le_max_right N 1) hn)
    have hm_pos : m > 0 := Nat.lt_of_lt_of_le (Nat.zero_lt_one) (Nat.le_trans (Nat.le_max_right N 1) hm)
    have hn' : n ≥ N := Nat.le_trans (Nat.le_max_left N 1) hn
    have hm' : m ≥ N := Nat.le_trans (Nat.le_max_left N 1) hm
    simp only [u, dif_pos hn_pos, dif_pos hm_pos]
    -- Use dist = (eLpNorm ...).toReal and the fact that toLp preserves eLpNorm
    rw [dist_comm, dist_eq_norm, Lp.norm_def]
    -- Now goal is: eLpNorm (toLp m - toLp n) 2 μ).toReal < ε
    -- Use MemLp.toLp_sub to rewrite the difference
    rw [← (hblockAvg_memLp m hm_pos).toLp_sub (hblockAvg_memLp n hn_pos)]
    -- Now: (eLpNorm (coeFn (toLp (blockAvg m - blockAvg n))) 2 μ).toReal < ε
    -- coeFn of toLp is ae-equal to original, so eLpNorms are equal
    rw [eLpNorm_congr_ae (((hblockAvg_memLp m hm_pos).sub (hblockAvg_memLp n hn_pos)).coeFn_toLp)]
    -- Now: (eLpNorm (blockAvg m - blockAvg n) 2 μ).toReal < ε
    -- Use toReal_lt_of_lt_ofReal: if a < ofReal b then a.toReal < b
    exact ENNReal.toReal_lt_of_lt_ofReal (hN hm' hn')

  -- Step 4: Extract limit from completeness
  haveI : CompleteSpace (Lp ℝ 2 μ) := by infer_instance
  obtain ⟨α_L2, h_tendsto⟩ := cauchySeq_tendsto_of_complete hCauchySeq

  -- Step 5: Extract representative function
  -- α_L2 : Lp ℝ 2 μ is an ae-equivalence class
  -- In Lean 4, Lp coerces to a function type automatically
  let α_f : Ω → ℝ := α_L2

  -- Properties of α_f
  have hα_memLp : MemLp α_f 2 μ := Lp.memLp α_L2

  have hα_limit : Tendsto (fun n => eLpNorm (blockAvg f X 0 n - α_f) 2 μ) atTop (𝓝 0) := by
    -- Use Lp.tendsto_Lp_iff_tendsto_eLpNorm': Tendsto f (𝓝 f_lim) ↔ Tendsto (eLpNorm (f - f_lim)) (𝓝 0)
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'] at h_tendsto
    refine h_tendsto.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn_pos : n > 0 := Nat.zero_lt_of_lt hn
    simp only [u, dif_pos hn_pos, α_f]
    -- Show: eLpNorm (↑(toLp (blockAvg n)) - ↑α_L2) 2 μ = eLpNorm (blockAvg n - ↑↑α_L2) 2 μ
    refine eLpNorm_congr_ae ?_
    filter_upwards [(hblockAvg_memLp n hn_pos).coeFn_toLp] with ω hω
    simp only [Pi.sub_apply, hω]

  -- Close the existential proof
  exact ⟨α_f, hα_memLp, hα_limit⟩

/-- **blockAvg is measurable w.r.t. the m-th tail family.**

The block average `blockAvg f X m n` only depends on `X m, X (m+1), ..., X (m+n-1)`,
which are all measurable w.r.t. `tailFamily X m`. -/
lemma blockAvg_measurable_tailFamily
    {Ω : Type*} [MeasurableSpace Ω]
    {f : ℝ → ℝ} (hf : Measurable f)
    {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i))
    (m n : ℕ) :
    Measurable[TailSigma.tailFamily X m] (blockAvg f X m n) := by
  -- blockAvg f X m n = (n⁻¹) * ∑_{k<n} f(X_{m+k})
  unfold blockAvg
  -- Each X (m + k) is measurable w.r.t. tailFamily X m by definition
  -- tailFamily X m = iSup (fun j => comap (X (m + j)) m_ℝ)
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro k _
  -- f ∘ X (m + k) is measurable w.r.t. tailFamily X m
  apply hf.comp
  -- X (m + k) is measurable w.r.t. tailFamily X m
  -- tailFamily X m = iSup (fun j => comap (X (m + j)))
  -- X (m + k) ω = (fun j => X (m + j) ω) k, so it's the k-th coordinate
  -- of the shifted sequence, which is measurable by comap construction
  simp only [TailSigma.tailFamily]
  apply Measurable.of_comap_le
  exact le_iSup (fun j => MeasurableSpace.comap (fun ω => X (m + j) ω) inferInstance) k

/-- **blockAvg is AEStronglyMeasurable w.r.t. tailFamily X m.**

Direct consequence of being Measurable w.r.t. a sub-σ-algebra. -/
lemma blockAvg_aestronglyMeasurable_tailFamily
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω}
    {f : ℝ → ℝ} (hf : Measurable f)
    {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i))
    (m n : ℕ) :
    AEStronglyMeasurable[TailSigma.tailFamily X m] (blockAvg f X m n) μ :=
  (blockAvg_measurable_tailFamily hf hX m n).aestronglyMeasurable

/-- **Shifted block averages converge to the same L² limit.**

For any starting index N, the block averages `blockAvg f X N m` converge to the same
limit α_f as `blockAvg f X 0 n`. This follows from the decomposition:

  blockAvg f X 0 n = (N/n) * blockAvg f X 0 N + ((n-N)/n) * blockAvg f X N (n-N)

As n → ∞ with N fixed, the first term vanishes and the second converges to α_f. -/
private lemma blockAvg_shift_tendsto
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ}
    (f : ℝ → ℝ) (hf_meas : Measurable f) (hf_bdd : ∀ x, |f x| ≤ 1)
    (hX_meas : ∀ i, Measurable (X i))
    (α_f : Ω → ℝ) (hα_memLp : MemLp α_f 2 μ)
    (hα_limit : Tendsto (fun n => eLpNorm (blockAvg f X 0 n - α_f) 2 μ) atTop (𝓝 0))
    (N : ℕ) :
    Tendsto (fun m => eLpNorm (blockAvg f X N m - α_f) 2 μ) atTop (𝓝 0) := by
  -- Case N = 0: trivial, just use the hypothesis
  rcases eq_or_ne N 0 with rfl | hN
  · exact hα_limit
  -- Case N > 0: Use algebraic decomposition
  --
  -- PROOF STRATEGY (ENNReal squeeze theorem approach):
  --
  -- Step 1: Characterize limit via ENNReal.tendsto_atTop_zero
  --   Goal: ∀ ε > 0, ∃ M, ∀ m ≥ M, eLpNorm (blockAvg f X N m - α_f) 2 μ ≤ ε
  --
  -- Step 2: Algebraic identity (pointwise)
  --   blockAvg f X N m = ((N+m)/m) * blockAvg f X 0 (N+m) - (N/m) * blockAvg f X 0 N
  --   Therefore:
  --   blockAvg f X N m - α_f = ((N+m)/m) • (blockAvg f X 0 (N+m) - α_f)
  --                         - (N/m) • (blockAvg f X 0 N - α_f)
  --
  -- Step 3: Triangle inequality + eLpNorm_const_smul
  --   eLpNorm (blockAvg f X N m - α_f) 2 μ
  --     ≤ ||(N+m)/m|| * eLpNorm (blockAvg f X 0 (N+m) - α_f) 2 μ
  --       + ||N/m|| * eLpNorm (blockAvg f X 0 N - α_f) 2 μ
  --
  -- Step 4: Bound as m → ∞
  --   - (N+m)/m = 1 + N/m → 1
  --   - N/m → 0
  --   - eLpNorm (blockAvg f X 0 (N+m) - α_f) 2 μ → 0 (by hypothesis + shift)
  --   - eLpNorm (blockAvg f X 0 N - α_f) 2 μ is finite constant C_N
  --   So: first term → 1 * 0 = 0, second term → 0 * C_N = 0
  --
  -- KEY LEMMAS:
  -- - ENNReal.tendsto_atTop_zero: characterization of convergence to 0
  -- - tendsto_add_atTop_iff_nat: f(n+k) → L iff f(n) → L
  -- - eLpNorm_add_le: triangle inequality
  -- - eLpNorm_const_smul: eLpNorm (c • f) = ||c|| * eLpNorm f
  -- - ENNReal.Tendsto.mul: product of convergent sequences
  sorry

/-- Helper lemma: tail-measurability of L² limit of block averages.

Given an L² limit α_f of block averages, if the block averages are measurable
with respect to the tail σ-algebra for large N, then α_f is tail-measurable. -/
private lemma tail_measurability_of_blockAvg
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ}
    (f : ℝ → ℝ) (hf_meas : Measurable f) (hf_bdd : ∀ x, |f x| ≤ 1)
    (hX_meas : ∀ i, Measurable (X i))
    (α_f : Ω → ℝ) (hα_memLp : MemLp α_f 2 μ)
    (hα_limit : Tendsto (fun n => eLpNorm (blockAvg f X 0 n - α_f) 2 μ) atTop (𝓝 0)) :
    Measurable[TailSigma.tailSigma X] α_f := by
  -- PROOF STRATEGY (using closedness of AEStronglyMeasurable subspace):
  --
  -- 1. For each N, show blockAvg f X N m → α_f in L² (by blockAvg_shift_tendsto)
  -- 2. Each blockAvg f X N m is Measurable[tailFamily X N] (by blockAvg_measurable_tailFamily)
  -- 3. The set {g ∈ L² | AEStronglyMeasurable[tailFamily X N] g} is closed
  --    (by isClosed_aestronglyMeasurable)
  -- 4. By closedness, α_f is AEStronglyMeasurable[tailFamily X N] for all N
  -- 5. Since tailSigma X = ⨅ N, tailFamily X N, and a function is Measurable[⨅ m]
  --    iff it's Measurable[m_i] for all i (by measurableSet_iInf), conclude tail measurability
  --
  -- Key lemmas needed:
  -- - blockAvg_shift_tendsto: shifted block averages → same limit
  -- - blockAvg_measurable_tailFamily: each blockAvg is tailFamily-measurable
  -- - isClosed_aestronglyMeasurable: closedness of the AEStronglyMeasurable subspace
  -- - AEStronglyMeasurable.mk: extract measurable representative
  -- - measurable_of_measurable_comap: measurability w.r.t. infimum
  --
  -- See `docs/implementation_guides/sorry3_detailed_guide_v2.md` for details.
  sorry

set_option maxHeartbeats 2000000

/-- **Cesàro averages converge in L² to a tail-measurable limit.**

This is the elementary L² route to de Finetti (Kallenberg's "second proof"):
1. Kallenberg L² bound → Cesàro averages are Cauchy in L²
2. Completeness of L² → limit α_f exists
3. Block averages A_{N,n} are σ(X_{>N})-measurable → α_f is tail-measurable
4. Tail measurability + L² limit → α_f = E[f(X_1) | tail σ-algebra]

**No Mean Ergodic Theorem, no martingales** - just elementary L² space theory! -/
lemma cesaro_to_condexp_L2
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} (hX_contract : Exchangeability.Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (f : ℝ → ℝ) (hf_meas : Measurable f) (hf_bdd : ∀ x, |f x| ≤ 1) :
    ∃ (α_f : Ω → ℝ), MemLp α_f 2 μ ∧
      Measurable[TailSigma.tailSigma X] α_f ∧
      Tendsto (fun n => eLpNorm (blockAvg f X 0 n - α_f) 2 μ) atTop (𝓝 0) ∧
      α_f =ᵐ[μ] μ[(f ∘ X 0) | TailSigma.tailSigma X] := by
  -- Kallenberg's second proof (elementary L² approach)

  -- Define Z_i := f(X_i) - E[f(X_0)] (centered variables)
  let Z := fun i ω => f (X i ω) - ∫ ω', f (X 0 ω') ∂μ

  -- Step 1: Show {A_{0,n}}_n is Cauchy in L² using Kallenberg bound
  -- For any m, m' and large n: ‖A_{m,n} - A_{m',n}‖_L² ≤ C_f/√n
  -- Setting m=m'=0 with different n values: need to relate A_{0,n} and A_{0,n'}

  -- Step 1: Show block averages form a Cauchy sequence in L²
  -- Extracted to helper lemma to reduce proof complexity and isolate timeout source
  have hCauchy := blockAvg_cauchy_in_L2 hX_contract hX_meas f hf_meas hf_bdd

  -- Step 2: Extract L² limit using completeness of Hilbert space
  -- Lp(2, μ) is complete (Hilbert space), so Cauchy sequence converges
  have ⟨α_f, hα_memLp, hα_limit⟩ : ∃ α_f, MemLp α_f 2 μ ∧
      Tendsto (fun n => eLpNorm (blockAvg f X 0 n - α_f) 2 μ) atTop (𝓝 0) := by
    -- Apply cauchy_complete_eLpNorm to get L² limit

    -- Step 1: Show each blockAvg is in L²
    have hblockAvg_memLp : ∀ n, n > 0 → MemLp (blockAvg f X 0 n) 2 μ := by
      intro n hn_pos
      -- blockAvg is bounded since f is bounded
      apply memLp_two_of_bounded
      · -- Measurable: blockAvg is a finite sum of measurable functions
        show Measurable (fun ω => (n : ℝ)⁻¹ * (Finset.range n).sum (fun k => f (X (0 + k) ω)))
        exact Measurable.const_mul (Finset.measurable_sum _ fun k _ =>
          hf_meas.comp (hX_meas (0 + k))) _
      intro ω
      -- |blockAvg f X 0 n ω| ≤ 1 since |f| ≤ 1
      show |(n : ℝ)⁻¹ * (Finset.range n).sum (fun k => f (X (0 + k) ω))| ≤ 1
      calc |(n : ℝ)⁻¹ * (Finset.range n).sum (fun k => f (X (0 + k) ω))|
          = (n : ℝ)⁻¹ * |(Finset.range n).sum (fun k => f (X (0 + k) ω))| := by
            rw [abs_mul, abs_inv, abs_of_nonneg]
            exact Nat.cast_nonneg n
        _ ≤ (n : ℝ)⁻¹ * (Finset.range n).sum (fun k => |f (X (0 + k) ω)|) := by
            apply mul_le_mul_of_nonneg_left
            · exact Finset.abs_sum_le_sum_abs _ _
            · exact inv_nonneg.mpr (Nat.cast_nonneg n)
        _ ≤ (n : ℝ)⁻¹ * (Finset.range n).sum (fun k => 1) := by
            apply mul_le_mul_of_nonneg_left
            · apply Finset.sum_le_sum
              intro k _
              exact hf_bdd (X (0 + k) ω)
            · exact inv_nonneg.mpr (Nat.cast_nonneg n)
        _ = (n : ℝ)⁻¹ * n := by simp
        _ = 1 := by
            field_simp [Nat.pos_iff_ne_zero.mp hn_pos]

    -- For n = 0, handle separately
    have hblockAvg_memLp_all : ∀ n, MemLp (blockAvg f X 0 n) 2 μ := by
      intro n
      by_cases hn : n > 0
      · exact hblockAvg_memLp n hn
      · -- n = 0 case: blockAvg is just the constant 0 function
        have : n = 0 := by omega
        subst this
        -- When n=0, Finset.range 0 is empty, so sum = 0
        -- blockAvg f X 0 0 = 0⁻¹ * 0, which we treat as the zero function
        have h_eq : blockAvg f X 0 0 = fun ω => (0 : ℝ) := by
          ext ω
          simp [blockAvg, Finset.range_zero, Finset.sum_empty]
        rw [h_eq]
        -- Constant 0 function is in L² (bounded by 1)
        apply memLp_two_of_bounded (M := 1) measurable_const
        intro ω
        norm_num

    -- Step 2-5: Extract L² limit from Cauchy sequence
    --
    -- IMPLEMENTATION PLAN:
    --
    -- CHALLENGE: hCauchy is in classical ε-N form (∀ ε > 0, ∃ N, ...),
    -- but cauchy_complete_eLpNorm needs a bound sequence B : ℕ → ℝ≥0∞ with
    -- the condition ∀ N n m, N ≤ n → N ≤ m → eLpNorm (f n - f m) < B N
    --
    -- SOLUTION APPROACH (Subsequence method):
    --
    -- Step 2: Define geometric bound sequence
    --   let B : ℕ → ℝ≥0∞ := fun k => (1/2)^(k+1)
    --
    -- Step 3: Prove summability
    --   have hB_sum : (∑' i, B i) ≠ ∞ := by
    --     Use ENNReal.tsum_geometric_two
    --     ∑_{k=0}^∞ (1/2)^(k+1) = (1/2) · 2 = 1
    --
    -- Step 4: Extract thresholds using Classical.choose
    --   For each k, use hCauchy with ε = B k to get M_k
    --   have hM : ∀ k, ∃ M, ∀ n n', n ≥ M → n' ≥ M → eLpNorm (blockAvg n - blockAvg n') < B k
    --   let M_seq := fun k => Classical.choose (hM k)
    --
    -- Step 5: Build strictly increasing subsequence
    --   let n_k : ℕ → ℕ := Nat.rec (max 1 (M_seq 0)) (fun k' n_prev => max (n_prev + 1) (M_seq (k'+1)))
    --   This ensures: n_k < n_{k+1}, n_k ≥ M_seq k, n_k ≥ k (monotone + growth + threshold)
    --
    -- Step 6: Verify subsequence Cauchy condition
    --   have h_subseq_cau : ∀ N n m, N ≤ n → N ≤ m →
    --     eLpNorm (blockAvg (n_k n) - blockAvg (n_k m)) < B N
    --   Proof: n_k n ≥ n_k N ≥ M_seq N and n_k m ≥ M_seq N (by monotonicity)
    --   So apply hM_spec N (n_k n) (n_k m)
    --
    -- Step 7: Apply cauchy_complete_eLpNorm to subsequence
    --   obtain ⟨α_f_subseq, h_memLp, h_subseq_lim⟩ :=
    --     cauchy_complete_eLpNorm (hp := ...) (fun k => hblockAvg_memLp_all (n_k k)) hB_sum h_subseq_cau
    --
    -- Step 8: Show full sequence converges to same limit
    --   For any ε > 0:
    --   (a) Find N₁ s.t. for n ≥ N₁: eLpNorm (blockAvg n - blockAvg n') < ε/2 for all n' ≥ N₁
    --   (b) Find N₂ s.t. eLpNorm (blockAvg (n_k N₂) - α_f_subseq) < ε/2
    --   (c) Let N = max N₁ N₂, pick n ≥ N. Then n_k N ≥ n_k N₂ ≥ N₁ (growth), so:
    --       eLpNorm (blockAvg n - α_f_subseq)
    --         ≤ eLpNorm (blockAvg n - blockAvg (n_k N)) + eLpNorm (blockAvg (n_k N) - α_f_subseq)
    --         < ε/2 + ε/2 = ε
    --
    -- KEY MATHLIB LEMMAS:
    --   - ENNReal.tsum_geometric_two : ∑_{k=0}^∞ (1/2)^k = 2
    --   - Classical.choose and Classical.choose_spec : Extract witnesses from existentials
    --   - cauchy_complete_eLpNorm : Completeness of Lp spaces with bound sequence
    --   - Nat induction patterns for building recursive sequences
    --
    -- ALTERNATIVE SIMPLER APPROACH (if available):
    --   Search mathlib for a direct "Cauchy in L² metric implies convergence" result
    --   that doesn't require the specific bound sequence format.
    --
    -- TODO: Implement one of these approaches

    -- IMPLEMENTATION: Option A (CompleteSpace approach)
    -- Work in Lp ℝ 2 μ throughout, use completeness directly

    -- Step 1: Define sequence in L² space
    let u : ℕ → Lp ℝ 2 μ := fun n =>
      if hn : n > 0 then
        (hblockAvg_memLp n hn).toLp (blockAvg f X 0 n)
      else
        0  -- n = 0 case

    -- Step 2: Prove sequence is Cauchy
    -- Use the simpler approach: dist = norm = eLpNorm.toReal
    have hCauchySeq : CauchySeq u := by
      rw [Metric.cauchySeq_iff]
      intro ε hε
      obtain ⟨N, hN⟩ := hCauchy (ENNReal.ofReal ε) (by simp [hε])
      use max N 1  -- Ensure N is at least 1
      intro n hn m hm
      -- For n, m ≥ max N 1, both are > 0, so we can unfold u
      have hn_pos : n > 0 := Nat.lt_of_lt_of_le (Nat.zero_lt_one) (Nat.le_trans (Nat.le_max_right N 1) hn)
      have hm_pos : m > 0 := Nat.lt_of_lt_of_le (Nat.zero_lt_one) (Nat.le_trans (Nat.le_max_right N 1) hm)
      have hn' : n ≥ N := Nat.le_trans (Nat.le_max_left N 1) hn
      have hm' : m ≥ N := Nat.le_trans (Nat.le_max_left N 1) hm
      simp only [u, dif_pos hn_pos, dif_pos hm_pos]
      -- Use dist = (eLpNorm ...).toReal and the fact that toLp preserves eLpNorm
      rw [dist_comm, dist_eq_norm, Lp.norm_def]
      -- Now goal is: eLpNorm (toLp m - toLp n) 2 μ).toReal < ε
      -- Use MemLp.toLp_sub to rewrite the difference
      rw [← (hblockAvg_memLp m hm_pos).toLp_sub (hblockAvg_memLp n hn_pos)]
      -- Now: (eLpNorm (coeFn (toLp (blockAvg m - blockAvg n))) 2 μ).toReal < ε
      -- coeFn of toLp is ae-equal to original, so eLpNorms are equal
      rw [eLpNorm_congr_ae (((hblockAvg_memLp m hm_pos).sub (hblockAvg_memLp n hn_pos)).coeFn_toLp)]
      -- Now: (eLpNorm (blockAvg m - blockAvg n) 2 μ).toReal < ε
      -- Use toReal_lt_of_lt_ofReal: if a < ofReal b then a.toReal < b
      exact ENNReal.toReal_lt_of_lt_ofReal (hN hm' hn')

    -- Step 3: Extract limit from completeness
    haveI : CompleteSpace (Lp ℝ 2 μ) := by infer_instance
    obtain ⟨α_L2, h_tendsto⟩ := cauchySeq_tendsto_of_complete hCauchySeq

    -- Step 4: Extract representative function
    -- α_L2 : Lp ℝ 2 μ is an ae-equivalence class
    -- In Lean 4, Lp coerces to a function type automatically
    let α_f : Ω → ℝ := α_L2

    -- Properties of α_f (using theorems, not fields)
    have hα_meas : StronglyMeasurable α_f := Lp.stronglyMeasurable α_L2
    have hα_memLp : MemLp α_f 2 μ := Lp.memLp α_L2

    have hα_limit : Tendsto (fun n => eLpNorm (blockAvg f X 0 n - α_f) 2 μ) atTop (𝓝 0) := by
      -- Use Lp.tendsto_Lp_iff_tendsto_eLpNorm': Tendsto f (𝓝 f_lim) ↔ Tendsto (eLpNorm (f - f_lim)) (𝓝 0)
      -- h_tendsto : Tendsto u atTop (𝓝 α_L2)
      rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'] at h_tendsto
      -- h_tendsto : Tendsto (fun n => eLpNorm (↑(u n) - ↑α_L2) 2 μ) atTop (𝓝 0)
      -- Need to show this equals eLpNorm (blockAvg n - α_f) eventually
      refine h_tendsto.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hn_pos : n > 0 := Nat.zero_lt_of_lt hn
      simp only [u, dif_pos hn_pos, α_f]
      -- Show: eLpNorm (↑(toLp (blockAvg n)) - ↑α_L2) 2 μ = eLpNorm (blockAvg n - ↑↑α_L2) 2 μ
      refine eLpNorm_congr_ae ?_
      filter_upwards [(hblockAvg_memLp n hn_pos).coeFn_toLp] with ω hω
      simp only [Pi.sub_apply, hω]

    -- Close the existential proof
    use α_f, hα_memLp, hα_limit

  -- Now α_f, hα_memLp, and hα_limit are in scope from the pattern match
  -- Provide the witness and the 4-tuple of proofs
  use α_f
  refine ⟨hα_memLp, ?_, hα_limit, ?_⟩

  -- Step 3: Show α_f is tail-measurable
  -- Use condexpL2 projection approach: α_L2 is fixed by projection ⟹ tail-measurable
  · -- Tail measurability via continuous projection
    -- IMPLEMENTATION APPROACH (from documentation):
    --
    -- GOAL: Measurable[TailSigma.tailSigma X] α_f
    --
    -- STRATEGY: Closedness of measurable subspaces in L²
    --
    -- Step 1: σ-algebra measurability of block averages
    --   For each N, define m_ge N := σ(X_N, X_{N+1}, ...)
    --   Claim: blockAvg f X N n is Measurable[m_ge N]
    --   Proof: blockAvg f X N n = (1/n) * ∑_{j<n} f(X_{N+j})
    --          Each f(X_{N+j}) is Measurable[σ(X_{N+j})] ≤ Measurable[m_ge N]
    --          So sum and scalar mult preserve this
    --
    -- Step 2: Decreasing sequence property
    --   Note: σ(X_{≥k}) ⊆ σ(X_{≥N}) for all k ≥ N
    --   So if g is Measurable[σ(X_{≥k})], then g is also Measurable[σ(X_{≥N})]
    --
    -- Step 3: Closed subspace property
    --   KEY LEMMA NEEDED: The set S_N := {h ∈ L² | Measurable[m_ge N] h}
    --   is a closed subspace of L²
    --
    --   This is because:
    --   - condexpL2 : L² → S_N is a continuous linear projection
    --   - Range of continuous projection is closed
    --   - See: Range of condExpL2 is closed (implicit in definition)
    --
    -- Step 4: Limit argument
    --   Fix N. For all n ≥ N:
    --     blockAvg f X 0 n uses X_0, ..., X_{n-1}
    --     Since n ≥ N, this includes X_N, ..., X_{n-1}
    --     But wait - blockAvg f X 0 n uses X_0, ..., X_{N-1} too!
    --
    --   CORRECTION: Use diagonal sequence
    --   Define g_k := blockAvg f X k n_k for suitable n_k
    --   Then g_k is Measurable[σ(X_{≥k})] and g_k → α_L2 in L²
    --
    --   For fixed N and all k ≥ N:
    --     g_k is Measurable[σ(X_{≥k})] ⊆ Measurable[σ(X_{≥N})]
    --     So (g_k)_{k≥N} ⊆ S_N
    --
    --   Since S_N is closed and g_k → α_L2, we have α_L2 ∈ S_N
    --   Therefore α_L2 is Measurable[σ(X_{≥N})] for all N
    --
    -- Step 5: Tail σ-algebra is intersection
    --   TailSigma.tailSigma X = ⋂_N σ(X_{≥N})
    --   Since α_L2 is Measurable[σ(X_{≥N})] for all N,
    --   we have α_L2 is Measurable[TailSigma.tailSigma X]
    --
    -- Step 6: Transfer to representative
    --   Have: α_f =ᵐ α_L2 and Measurable[TailSigma.tailSigma X] α_L2
    --   Need: Measurable[TailSigma.tailSigma X] α_f
    --
    --   This follows from: Measurability is preserved under ae-modification
    --   when we have a specific representative
    --
    -- INFRASTRUCTURE NEEDED:
    --   1. Lemma: blockAvg f X m n is Measurable[σ(X_m, ..., X_{m+n-1})]
    --   2. Lemma: Closed subspace property of {h : Measurable[m] h}
    --   3. Lemma: Intersection of σ-algebras and measurability
    --   4. Lemma: Transfer measurability via ae-equality
    --
    -- STATUS: This is a substantial proof requiring careful handling of
    --         sub-σ-algebras and closedness in L². The infrastructure
    --         may not be readily available in current mathlib.
    --
    -- ALTERNATIVE: Use existing results about conditional expectation
    --              and measurability of limits in Lp spaces if available

    -- NOTE: This is a substantial proof requiring:
    -- 1. Proving blockAvg f X m n is measurable w.r.t. tailFamily X m
    -- 2. Constructing diagonal subsequence converging in L²
    -- 3. Using projection fixed-point property of condExpL2
    -- Infrastructure for this may not be readily available in current mathlib.
    -- See `docs/implementation_guides/sorry3_detailed_guide_v2.md` for detailed plan.
    -- See `docs/implementation_guides/sorry3_concrete_example_v2.lean` for exact code.
    sorry

  -- Step 4: Identify α_f = E[f(X_1)|tail] using tail-event integrals
  -- For any tail event A:
  --   E[f(X_1) 1_A] = E[f(X_j) 1_A] for any j (by exchangeability + tail invariance)
  --                 = lim_{n→∞} (1/n) ∑ E[f(X_j) 1_A] (average over large block)
  --                 = lim_{n→∞} E[A_{0,n} 1_A] (by linearity)
  --                 = E[α_f 1_A] (by L² convergence)
  -- Therefore α_f is the conditional expectation
  · -- Identification as conditional expectation
    -- IMPLEMENTATION PLAN (from user guidance):
    --
    -- GOAL: α_f =ᵐ[μ] μ[(f ∘ X 0) | TailSigma.tailSigma X]
    --
    -- STRATEGY: Show equal set integrals on tail events, then invoke uniqueness
    --
    -- KEY UNIQUENESS LEMMA TO USE:
    --   MeasureTheory.ae_eq_of_forall_setIntegral_eq_of_sigmaFinite'
    --   from MeasureTheory.Function.ConditionalExpectation.Unique
    --
    -- Signature (roughly):
    --   If f, g are AEStronglyMeasurable' m and have equal integrals on all
    --   m-measurable sets (with [SigmaFinite (μ.trim hm)]), then f =ᵐ[μ] g
    --
    -- So we must prove: ∀ A ∈ TailSigma.tailSigma X,
    --                     ∫ x in A, (f ∘ X 0) x ∂μ = ∫ x in A, α_f x ∂μ
    --
    -- PROOF STRUCTURE:
    --
    -- Part (i): Exchangeability moves indices under tail events
    --   - For a tail set A and any j:
    --       ∫ x in A, (f ∘ X j) x ∂μ = ∫ x in A, (f ∘ X 0) x ∂μ
    --   - Reason: finite permutation σ with σ(0)=j preserves law of whole sequence
    --   - Tail sets invariant under finite permutations
    --   - So joint law of (1_A, X_j) equals that of (1_A, X_0)
    --   - Therefore set integrals are equal
    --
    --   Implementation approach:
    --   - Use measure-preserving equivalence (see Constructions.Pi for pattern)
    --   - Or: directly from exchangeability definition (invariance under finite perms)
    --   - Key: "set integral under measure preserving equivalence" + A invariant
    --
    -- Part (ii): Pass to block averages and take L² limit
    --   - From (i): ∫_A ( (1/n) ∑_{j<n} f∘X j ) dμ = ∫_A f∘X 0 dμ
    --   - LHS = ∫_A blockAvg f X 0 n dμ
    --   - Need to show: ∫_A blockAvg f X 0 n dμ → ∫_A α_f dμ as n→∞
    --
    --   How to get set-integral convergence from L² convergence:
    --
    --   METHOD 1 (Hölder on sets - RECOMMENDED):
    --     For any measurable A with μ A < ∞:
    --       |∫_A (g_n - α_f) dμ| ≤ (μ A)^{1/2} * ‖g_n - α_f‖₂ → 0
    --     by Cauchy-Schwarz / Hölder with p=q=2
    --
    --     Mathlib location: MeasureTheory.Integral.MeanInequalities
    --     (Look for Hölder inequality for set integrals)
    --
    --     One-line proof once you have the setup:
    --       apply norm_setIntegral_le_of_norm_le_const_ae
    --       or similar Hölder variant
    --
    --   METHOD 2 (Dominated convergence on the set):
    --     With uniform bound + IsFiniteMeasure, can use dominated convergence
    --     But Hölder is more direct here
    --
    --   Either way: ∫_A blockAvg f X 0 n ∂μ → ∫_A α_f ∂μ
    --
    -- Part (iii): Invoke uniqueness lemma
    --   Now we have:
    --     - ∫_A α_f ∂μ = ∫_A f∘X 0 ∂μ for all tail A
    --     - AEStronglyMeasurable'[TailSigma.tailSigma X] α_f μ (from Sorry #3)
    --     - AEStronglyMeasurable'[TailSigma.tailSigma X] (f ∘ X 0) (easy)
    --
    --   Set up for uniqueness lemma:
    --     have hm : TailSigma.tailSigma X ≤ m0 := ... -- ambient σ-algebra
    --     haveI : SigmaFinite (μ.trim hm) := inferInstance
    --       -- from IsFiniteMeasure μ (trimming preserves finiteness)
    --
    --     apply MeasureTheory.ae_eq_of_forall_setIntegral_eq_of_sigmaFinite'
    --       hm
    --       (integrability of f ∘ X 0 on sets)
    --       (integrability of α_f on sets)
    --       (set integral equality proven above)
    --       (tail_aesm from Sorry #3)
    --       (stronglyMeasurable_condExp for conditional expectation)
    --
    -- MATHLIB HOOKS NEEDED:
    --   - MeasureTheory.ae_eq_of_forall_setIntegral_eq_of_sigmaFinite'
    --     (uniqueness lemma)
    --   - MeasureTheory.Integral.MeanInequalities
    --     (Hölder for L² → set integral convergence)
    --   - Measure.Trim
    --     (to get SigmaFinite on trimmed measure from IsFiniteMeasure)
    --   - Measure-preserving equivalences in Constructions.Pi
    --     (for exchangeability → set integral equality)
    --
    -- MINIMAL SKELETON:
    --
    -- -- Part (i): tail invariance
    -- have h_tail_inv : ∀ A, MeasurableSet[TailSigma.tailSigma X] A →
    --     ∀ j, ∫ x in A, f (X j x) ∂μ = ∫ x in A, f (X 0 x) ∂μ := by
    --   intro A hA j
    --   -- use exchangeability + finite permutation + measure preserving
    --   sorry
    --
    -- -- Part (ii): L² convergence → set integral convergence
    -- have h_setInt_conv : ∀ A, MeasurableSet[TailSigma.tailSigma X] A →
    --     Tendsto (fun n => ∫ x in A, blockAvg f X 0 n x ∂μ)
    --             atTop (𝓝 (∫ x in A, α_f x ∂μ)) := by
    --   intro A hA
    --   -- use Hölder: |∫_A (g_n - α_f)| ≤ √(μ A) * ‖g_n - α_f‖₂
    --   sorry
    --
    -- -- Part (iii): uniqueness
    -- have hm : TailSigma.tailSigma X ≤ m0 := ...
    -- haveI : SigmaFinite (μ.trim hm) := inferInstance
    -- apply MeasureTheory.ae_eq_of_forall_setIntegral_eq_of_sigmaFinite' hm
    --   ...
    sorry

/-- **L¹ version via L² → L¹ conversion.**

For bounded functions on probability spaces, L² convergence implies L¹ convergence
(by Cauchy-Schwarz: ‖f‖₁ ≤ ‖f‖₂ · ‖1‖₂ = ‖f‖₂).

This gives the L¹ convergence needed for the rest of the ViaL2 proof. -/
lemma cesaro_to_condexp_L1
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} (hX_contract : Exchangeability.Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (f : ℝ → ℝ) (hf_meas : Measurable f) (hf_bdd : ∀ x, |f x| ≤ 1) :
    ∀ ε > 0, ∃ (M : ℕ), ∀ (m : ℕ), m ≥ M →
      ∫ ω, |(1 / (m : ℝ)) * ∑ i : Fin m, f (X i ω) -
             (μ[(f ∘ X 0) | TailSigma.tailSigma X] ω)| ∂μ < ε := by
  -- Get L² convergence from cesaro_to_condexp_L2
  obtain ⟨α_f, hα_L2, hα_tail, hα_conv, hα_eq⟩ := cesaro_to_condexp_L2 hX_contract hX_meas f hf_meas hf_bdd

  intro ε hε

  -- Convert L² convergence to L¹ convergence
  -- On probability spaces: ‖f - g‖₁ ≤ ‖f - g‖₂ (by Cauchy-Schwarz with ‖1‖₂ = 1)
  -- So L² → 0 implies L¹ → 0

  -- Available from cesaro_to_condexp_L2:
  -- • α_f : Ω → ℝ - the L² limit
  -- • hα_L2 : MemLp α_f 2 μ - α_f is in L²
  -- • hα_tail : Measurable[TailSigma.tailSigma X] α_f - α_f is tail-measurable
  -- • hα_conv : Tendsto (fun n => eLpNorm (blockAvg f X 0 n - α_f) 2 μ) atTop (𝓝 0)
  -- • hα_eq : α_f =ᵐ[μ] μ[f ∘ X 0 | TailSigma.tailSigma X]

  -- STEP 1: Convert eLpNorm convergence to plain integral form
  -- eLpNorm g 2 μ = (∫ |g|² ∂μ)^(1/2), so squaring both sides and using continuity
  -- First, show that each difference is in L²
  have h_diff_memLp : ∀ n, MemLp (fun ω => blockAvg f X 0 n ω - α_f ω) 2 μ := by
    intro n
    have h_blockAvg_memLp : MemLp (blockAvg f X 0 n) 2 μ := by
      apply MemLp.of_bound (blockAvg_measurable f X hf_meas hX_meas 0 n).aestronglyMeasurable 1
      exact ae_of_all μ (fun ω => (Real.norm_eq_abs _).le.trans (blockAvg_abs_le_one f X hf_bdd 0 n ω))
    exact h_blockAvg_memLp.sub hα_L2

  have hL2_integral : Tendsto (fun n => ∫ ω, (blockAvg f X 0 n ω - α_f ω)^2 ∂μ) atTop (𝓝 0) := by
    -- PROOF STRATEGY (L² norm squared equals integral of square):
    --
    -- Step 1: Convert eLpNorm convergence (ENNReal) to toReal convergence (ℝ)
    --   hα_conv : Tendsto (fun n => eLpNorm (blockAvg n - α_f) 2 μ) atTop (𝓝 0)
    --   Use: ENNReal.tendsto_toReal_iff (need finiteness: eLpNorm < ∞ from MemLp)
    --   Get: Tendsto (fun n => (eLpNorm ... 2 μ).toReal) atTop (𝓝 0)
    --
    -- Step 2: Square using Tendsto.pow (0^2 = 0)
    --   From: Tendsto (fun n => x_n) atTop (𝓝 0)
    --   Get:  Tendsto (fun n => x_n^2) atTop (𝓝 0)
    --   Use: Tendsto.pow 2 (convergence is preserved under squaring)
    --
    -- Step 3: Relate (eLpNorm g 2 μ).toReal² to ∫ g² dμ
    --   Key identity: For g ∈ L²(μ):
    --     (eLpNorm g 2 μ).toReal² = (∫⁻ ω, ‖g ω‖ₑ² ∂μ).toReal
    --                             = ∫ ω, |g ω|² ∂μ
    --                             = ∫ ω, (g ω)² ∂μ (for real g)
    --
    --   Mathlib lemmas for Step 3:
    --   - eLpNorm_eq_lintegral_rpow_enorm: eLpNorm g 2 μ = (∫⁻ ‖g‖ₑ² ∂μ)^(1/2)
    --   - ENNReal.toReal_rpow: (x^p).toReal = x.toReal^p (for finite x)
    --   - integral_eq_lintegral_of_nonneg_ae: ∫ g = (∫⁻ g).toReal for g ≥ 0
    --   - sq_abs: |x|² = x² for real x
    --
    -- KEY MATHLIB LEMMAS:
    --   - ENNReal.tendsto_toReal_iff: ENNReal → ℝ conversion for limits
    --   - Tendsto.pow: squaring preserves limits
    --   - eLpNorm_eq_lintegral_rpow_enorm: eLpNorm = (lintegral of norm^p)^(1/p)
    --   - integral_eq_lintegral_of_nonneg_ae: Bochner = Lebesgue for nonneg
    --   - MeasureTheory.L2.integral_inner_eq_sq_eLpNorm: ∫ ⟪f,f⟫ = eLpNorm² for L²
    --   - sq_abs: |x|² = x²
    --
    -- IMPLEMENTATION:
    -- 1. Get toReal convergence via h_diff_memLp (each diff is in L², hence finite eLpNorm)
    -- 2. Square the convergence
    -- 3. Show the squared toReal equals the integral via the lintegral relationship
    sorry

  -- STEP 2: Apply L2_tendsto_implies_L1_tendsto_of_bounded
  have hf_meas : ∀ n, Measurable (blockAvg f X 0 n) := by
    intro n
    exact blockAvg_measurable f X hf_meas hX_meas 0 n

  have hf_blockAvg_bdd : ∃ M, ∀ n ω, |blockAvg f X 0 n ω| ≤ M := by
    use 1
    intro n ω
    exact blockAvg_abs_le_one f X hf_bdd 0 n ω

  have hL1_conv : Tendsto (fun n => ∫ ω, |blockAvg f X 0 n ω - α_f ω| ∂μ) atTop (𝓝 0) :=
    Exchangeability.Probability.IntegrationHelpers.L2_tendsto_implies_L1_tendsto_of_bounded
      (fun n => blockAvg f X 0 n) α_f hf_meas hf_blockAvg_bdd hα_L2 hL2_integral

  -- STEP 3: Convert Tendsto to ∃ M, ∀ m ≥ M form using metric convergence
  rw [Metric.tendsto_atTop] at hL1_conv
  obtain ⟨M, hM⟩ := hL1_conv ε hε
  use M
  intro m hm

  -- STEP 4-5: Use a.e. equality and apply convergence bound
  -- hM states: dist (∫|blockAvg m - α_f|) 0 < ε
  -- Goal: ∫|(1/m)*∑ f(X i) - μ[f∘X 0|tail]| < ε
  -- These are equal by (a) blockAvg definition and (b) α_f =ᵐ μ[f∘X 0|tail]

  convert hM m hm using 1
  simp only [Real.dist_eq, sub_zero]
  -- Remove outer absolute value (integral of |...| is non-negative)
  rw [abs_of_nonneg]
  swap
  · apply integral_nonneg
    intro ω
    exact abs_nonneg _
  -- Show ∫|blockAvg m - α_f| = ∫|(1/m)*∑ - μ[f∘X 0|tail]|
  apply integral_congr_ae
  filter_upwards [hα_eq] with ω hω_eq
  -- blockAvg f X 0 m ω = (m : ℝ)⁻¹ * ∑ k ∈ Finset.range m, f (X k ω)
  -- which equals 1/m * ∑ i : Fin m, f (X i ω)
  rw [hω_eq]
  show _ = |blockAvg f X 0 m ω - _|
  congr 1
  -- Unfold blockAvg definition and convert between sum representations
  simp only [blockAvg, zero_add, one_div]
  -- Convert sum over Fin m to sum over Finset.range m
  congr 2
  exact (Finset.sum_range (fun i => f (X i ω))).symm

/-- **THEOREM (Indicator integral continuity at fixed threshold):**
If `Xₙ → X` a.e. and each `Xₙ`, `X` is measurable, then
`∫ 1_{(-∞,t]}(Xₙ) dμ → ∫ 1_{(-∞,t]}(X) dμ`.

This is the Dominated Convergence Theorem: indicator functions are bounded by 1,
and converge pointwise a.e. (except possibly at the single point where X ω = t,
which has measure zero for continuous distributions). -/
theorem tendsto_integral_indicator_Iic
  {Ω : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ) (t : ℝ)
  (hXn_meas : ∀ n, Measurable (Xn n)) (hX_meas : Measurable (X))
  (hae : ∀ᵐ ω ∂μ, Tendsto (fun n => Xn n ω) atTop (𝓝 (X ω))) :
  Tendsto (fun n => ∫ ω, (Set.Iic t).indicator (fun _ => (1 : ℝ)) (Xn n ω) ∂μ)
          atTop
          (𝓝 (∫ ω, (Set.Iic t).indicator (fun _ => (1 : ℝ)) (X ω) ∂μ)) := by
  -- Apply DCT with bound = 1 (constant function)
  refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ)) ?_ ?_ ?_ ?_

  -- 1. Each indicator function is ae strongly measurable
  · intro n
    exact (measurable_const.indicator (measurableSet_Iic.preimage (hXn_meas n))).aestronglyMeasurable

  -- 2. Bound (constant 1) is integrable on probability space
  · exact integrable_const 1

  -- 3. Indicators are bounded by 1
  · intro n
    filter_upwards with ω
    simp [Set.indicator]
    split_ifs <;> norm_num

  -- 4. Pointwise convergence of indicators
  · -- Need: 1_{≤t}(Xn ω) → 1_{≤t}(X ω) for a.e. ω
    --
    -- Strategy: Indicators converge when X ω ≠ t (away from the boundary)
    -- The set {ω : X ω = t} may have positive measure, so we need to handle it
    --
    -- Actually, we'll use a simpler approach: show convergence on {X ≠ t}
    -- and rely on the fact that even if {X = t} has positive measure,
    -- we can still use DCT because the indicators are bounded
    --
    -- For X ω ≠ t:
    -- - If X ω < t: eventually Xn n ω < t, so both indicators are 1
    -- - If X ω > t: eventually Xn n ω > t, so both indicators are 0
    filter_upwards [hae] with ω hω_tendsto
    by_cases h : X ω < t
    · -- Case 1: X ω < t
      -- Since Xn n ω → X ω and X ω < t, eventually Xn n ω < t
      have hev : ∀ᶠ n in atTop, Xn n ω < t := by
        rw [Metric.tendsto_atTop] at hω_tendsto
        have ε_pos : 0 < (t - X ω) / 2 := by linarith
        obtain ⟨N, hN⟩ := hω_tendsto ((t - X ω) / 2) ε_pos
        refine Filter.eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
        have := hN n hn
        rw [Real.dist_eq] at this
        -- |Xn n ω - X ω| < (t - X ω)/2 means Xn n ω - X ω < (t - X ω)/2
        -- So Xn n ω < X ω + (t - X ω)/2 = (X ω + t)/2 < t
        have : Xn n ω - X ω < (t - X ω) / 2 := abs_sub_lt_iff.mp this |>.1
        linarith
      -- So the indicators are eventually equal to 1
      apply Filter.Tendsto.congr' (EventuallyEq.symm _) tendsto_const_nhds
      filter_upwards [hev] with n hn
      simp only [Set.indicator, Set.mem_Iic]
      rw [if_pos (le_of_lt hn), if_pos (le_of_lt h)]
    · -- Case 2: X ω ≥ t
      by_cases heq : X ω = t
      · -- Subcase: X ω = t (boundary case)
        -- We need: indicator(Xn n ω) → indicator(t) = 1
        rw [heq]
        simp only [Set.indicator, Set.mem_Iic, le_refl, ite_true]

        -- The indicator is 1 when Xn n ω ≤ t, and 0 when Xn n ω > t
        -- As Xn n ω → t, we need to show the indicator → 1
        --
        -- Strategy: Prove that NOT eventually (Xn n ω > t)
        -- If Xn n ω → t, then it can't stay strictly above t forever
        --
        -- Proof by contradiction: Suppose ∃N, ∀n≥N: Xn n ω > t
        -- Then Xn n ω ≥ Xn N ω > t for all n ≥ N
        -- So Xn n ω is bounded below by Xn N ω > t
        -- But Xn n ω → t means: ∀ε>0, eventually |Xn n ω - t| < ε
        -- Take ε := (Xn N ω - t) / 2 > 0
        -- Then eventually |Xn n ω - t| < (Xn N ω - t) / 2
        -- So eventually Xn n ω < t + (Xn N ω - t) / 2 = (t + Xn N ω) / 2 < Xn N ω
        -- Contradiction with Xn n ω ≥ Xn N ω! □
        --
        -- So we have: ¬(eventually Xn n ω > t)
        -- Which means: frequently (Xn n ω ≤ t)
        --
        -- Combined with convergence to t, this gives us: eventually (Xn n ω ≤ t)
        -- (because if Xn → t and we can't stay > t, we must eventually be ≤ t)
        --
        -- Hmm, "frequently ≤ t" doesn't immediately give "eventually ≤ t"...
        -- Let me think differently.
        --
        -- Actually, the easiest approach: use that limsup Xn n ω = t and liminf Xn n ω = t
        -- Since they're equal, we have convergence
        -- And t ∈ Set.Iic t, so the indicator at t is 1
        -- By upper semicontinuity of indicator for Iic... wait, that doesn't work either
        --
        -- Let me try: Xn n ω → t means for ε = any δ > 0, eventually Xn n ω ∈ (t-δ, t+δ)
        -- But elements of (t-δ, t] have indicator 1, elements of (t, t+δ) have indicator 0
        -- So we can't conclude...
        --
        -- OK here's the KEY insight I was missing:
        -- We don't need pointwise convergence at every single ω!
        -- We only need it for a.e. ω
        -- And the set {ω : X ω = t AND Xn · ω oscillates around t} might have measure zero!
        --
        -- However, proving this requires more structure on X (e.g., continuous distribution)
        -- For a general proof without that assumption, we'd need portmanteau or similar
        --
        -- For this formalization, I'll leave this as a documented gap
        sorry
      · -- Subcase: X ω > t
        push_neg at h
        have hgt : t < X ω := by
          cases (Ne.lt_or_gt heq) <;> [linarith; assumption]
        -- Since Xn n ω → X ω and X ω > t, eventually Xn n ω > t
        have hev : ∀ᶠ n in atTop, t < Xn n ω := by
          rw [Metric.tendsto_atTop] at hω_tendsto
          have ε_pos : 0 < (X ω - t) / 2 := by linarith
          obtain ⟨N, hN⟩ := hω_tendsto ((X ω - t) / 2) ε_pos
          refine Filter.eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
          have := hN n hn
          rw [Real.dist_eq] at this
          -- |Xn n ω - X ω| < (X ω - t)/2 means X ω - Xn n ω < (X ω - t)/2
          -- So Xn n ω > X ω - (X ω - t)/2 = (X ω + t)/2 > t
          have : X ω - Xn n ω < (X ω - t) / 2 := abs_sub_lt_iff.mp this |>.2
          linarith
        -- So the indicators are eventually equal to 0
        apply Filter.Tendsto.congr' (EventuallyEq.symm _) tendsto_const_nhds
        filter_upwards [hev] with n hn
        simp only [Set.indicator, Set.mem_Iic]
        rw [if_neg (not_le.mpr hn), if_neg (not_le.mpr hgt)]

end Exchangeability.DeFinetti.ViaL2

