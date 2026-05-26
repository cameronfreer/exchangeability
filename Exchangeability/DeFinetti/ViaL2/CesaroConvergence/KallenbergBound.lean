/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Exchangeability.Probability.CenteredVariables

/-!
# Kallenberg's L² Bound (Lemma 1.2)

The L² distance bound for weighted averages of an exchangeable sequence — the
"Lemma 1.2" of Kallenberg (2005). Self-contained algebraic statement; this file
is not used by the rest of the ViaL2 proof (which proceeds through
`l2_contractability_bound` to avoid the Exchangeable hypothesis), but it is the
clean form of the original Kallenberg argument and is retained here for
documentation.

## Main results

* `kallenberg_L2_bound`: the L² distance bound, with full Exchangeable hypothesis

## References

* Kallenberg (2005), *Probabilistic Symmetries and Invariance Principles*,
  Chapter 1, Lemma 1.2
-/

noncomputable section

namespace Exchangeability.DeFinetti.ViaL2

open MeasureTheory ProbabilityTheory BigOperators Filter Topology
open Exchangeability
open Exchangeability.DeFinetti.L2Helpers
open Exchangeability.Probability.CenteredVariables

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
          · -- Use Contractable.map_single to show Z k and Z 0 have same distribution
            -- Then transfer MemLp via equal eLpNorm
            have h_dist := Contractable.map_single
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
                _ = eLpNorm (Z 0) 2 μ := eLpNorm_map_measure aestronglyMeasurable_id (hZ_meas 0).aemeasurable
            -- Now transfer MemLp using equal eLpNorm
            have : eLpNorm (Z 0) 2 μ < ⊤ := by
              rw [h_Lpnorm_eq]
              exact hZk_L2.eLpNorm_lt_top
            exact ⟨(hZ_meas 0).aestronglyMeasurable, this⟩
        have hZ1_L2 : MemLp (Z 1) 2 μ := by
          by_cases h : k = 1
          · subst h; exact hZk_L2
          · -- Use Contractable.map_single to show Z k and Z 1 have same distribution
            -- Then transfer MemLp via equal eLpNorm
            have h_dist := Contractable.map_single
              (X := Z) hZ_contract hZ_meas (i := k)
            -- h_dist : Measure.map (Z k) μ = Measure.map (Z 0) μ
            have h_dist1 := Contractable.map_single
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
                _ = eLpNorm (Z k) 2 μ := eLpNorm_map_measure aestronglyMeasurable_id (hZ_meas k).aemeasurable
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
            ≤ (∫ ω, (Z 0 ω - m) ^ 2 ∂μ) ^ (1/2 : ℝ) * (∫ ω, (Z 1 ω - m) ^ 2 ∂μ) ^ (1/2 : ℝ) := Exchangeability.Probability.IntegrationHelpers.abs_integral_mul_le_L2 hf hg
          _ = (∫ ω, (Z 0 ω - m) ^ 2 ∂μ) ^ (1/2 : ℝ) * (∫ ω, (Z 0 ω - m) ^ 2 ∂μ) ^ (1/2 : ℝ) := by
                -- Use equal distributions: Z 1 has same variance as Z 0
                congr 1
                -- Use contractability: Z 1 has same distribution as Z 0
                have h_dist := Contractable.map_single
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
    have h_same_dist := Contractable.map_single
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
    have h_same_dist := Contractable.map_single
      (X := Z) hZ_contract hZ_meas (i := (enum k).val)
    simp only [ξ, σSq]
    -- Use integral_pushforward_sq_diff
    rw [← Exchangeability.Probability.IntegrationHelpers.integral_pushforward_sq_diff (hZ_meas _) m,
        h_same_dist,
        Exchangeability.Probability.IntegrationHelpers.integral_pushforward_sq_diff (hZ_meas _) m]

  -- Prove all covariances equal σ²ρ
  have hcov : ∀ i j : Fin n, i ≠ j → ∫ ω, (ξ i ω - m) * (ξ j ω - m) ∂μ = σSq * ρ := by
    intro i j hij
    -- Use Contractable.map_pair to show all pairs have same distribution as (Z 0, Z 1)
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
    rcases hij'.lt_or_gt with h_lt | h_lt
    · -- Case i' < j': Use Contractable.map_pair directly
      have h_dist := Contractable.map_pair
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
                  · have h_dist := Contractable.map_single
                      (X := Z) hZ_contract hZ_meas (i := k)
                    have h_Lpnorm_eq : eLpNorm (Z 0) 2 μ = eLpNorm (Z k) 2 μ := by
                      symm
                      calc eLpNorm (Z k) 2 μ
                          = eLpNorm id 2 (Measure.map (Z k) μ) := by
                              symm; exact eLpNorm_map_measure aestronglyMeasurable_id (hZ_meas k).aemeasurable
                        _ = eLpNorm id 2 (Measure.map (Z 0) μ) := by rw [h_dist]
                        _ = eLpNorm (Z 0) 2 μ := eLpNorm_map_measure aestronglyMeasurable_id (hZ_meas 0).aemeasurable
                    have : eLpNorm (Z 0) 2 μ < ⊤ := by
                      rw [h_Lpnorm_eq]
                      exact hZk_L2.eLpNorm_lt_top
                    exact ⟨(hZ_meas 0).aestronglyMeasurable, this⟩
                have hZ1_L2_local : MemLp (Z 1) 2 μ := by
                  by_cases h' : k = 1
                  · subst h'; exact hZk_L2
                  · have h_dist := Contractable.map_single
                      (X := Z) hZ_contract hZ_meas (i := k)
                    have h_dist1 := Contractable.map_single
                      (X := Z) hZ_contract hZ_meas (i := 1)
                    have h_Lpnorm_eq : eLpNorm (Z 1) 2 μ = eLpNorm (Z k) 2 μ := by
                      calc eLpNorm (Z 1) 2 μ
                          = eLpNorm id 2 (Measure.map (Z 1) μ) := by
                              symm; exact eLpNorm_map_measure aestronglyMeasurable_id (hZ_meas 1).aemeasurable
                        _ = eLpNorm id 2 (Measure.map (Z 0) μ) := by rw [h_dist1]
                        _ = eLpNorm id 2 (Measure.map (Z k) μ) := by rw [← h_dist]
                        _ = eLpNorm (Z k) 2 μ := eLpNorm_map_measure aestronglyMeasurable_id (hZ_meas k).aemeasurable
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
      have h_dist := Contractable.map_pair
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
                  · have h_dist := Contractable.map_single
                      (X := Z) hZ_contract hZ_meas (i := k)
                    have h_Lpnorm_eq : eLpNorm (Z 0) 2 μ = eLpNorm (Z k) 2 μ := by
                      symm
                      calc eLpNorm (Z k) 2 μ
                          = eLpNorm id 2 (Measure.map (Z k) μ) := by
                              symm; exact eLpNorm_map_measure aestronglyMeasurable_id (hZ_meas k).aemeasurable
                        _ = eLpNorm id 2 (Measure.map (Z 0) μ) := by rw [h_dist]
                        _ = eLpNorm (Z 0) 2 μ := eLpNorm_map_measure aestronglyMeasurable_id (hZ_meas 0).aemeasurable
                    have : eLpNorm (Z 0) 2 μ < ⊤ := by
                      rw [h_Lpnorm_eq]
                      exact hZk_L2.eLpNorm_lt_top
                    exact ⟨(hZ_meas 0).aestronglyMeasurable, this⟩
                have hZ1_L2_local : MemLp (Z 1) 2 μ := by
                  by_cases h' : k = 1
                  · subst h'; exact hZk_L2
                  · have h_dist := Contractable.map_single
                      (X := Z) hZ_contract hZ_meas (i := k)
                    have h_dist1 := Contractable.map_single
                      (X := Z) hZ_contract hZ_meas (i := 1)
                    have h_Lpnorm_eq : eLpNorm (Z 1) 2 μ = eLpNorm (Z k) 2 μ := by
                      calc eLpNorm (Z 1) 2 μ
                          = eLpNorm id 2 (Measure.map (Z 1) μ) := by
                              symm; exact eLpNorm_map_measure aestronglyMeasurable_id (hZ_meas 1).aemeasurable
                        _ = eLpNorm id 2 (Measure.map (Z 0) μ) := by rw [h_dist1]
                        _ = eLpNorm id 2 (Measure.map (Z k) μ) := by rw [← h_dist]
                        _ = eLpNorm (Z k) 2 μ := eLpNorm_map_measure aestronglyMeasurable_id (hZ_meas k).aemeasurable
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
          · intro i hi; simp
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
          · intro i hi; simp
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
        have h_dist := Contractable.map_single
          (X := Z) hZ_contract hZ_meas (i := k)
        -- Transfer eLpNorm using equal distributions
        have h_Lpnorm_eq : eLpNorm (Z 0) 2 μ = eLpNorm (Z k) 2 μ := by
          symm
          calc eLpNorm (Z k) 2 μ
              = eLpNorm id 2 (Measure.map (Z k) μ) := by
                  symm
                  exact eLpNorm_map_measure aestronglyMeasurable_id (hZ_meas k).aemeasurable
            _ = eLpNorm id 2 (Measure.map (Z 0) μ) := by rw [h_dist]
            _ = eLpNorm (Z 0) 2 μ := eLpNorm_map_measure aestronglyMeasurable_id (hZ_meas 0).aemeasurable
        have : eLpNorm (Z 0) 2 μ < ⊤ := by
          rw [h_Lpnorm_eq]
          exact hZk_L2.eLpNorm_lt_top
        exact ⟨(hZ_meas 0).aestronglyMeasurable, this⟩
    have hZ1_L2 : MemLp (Z 1) 2 μ := by
      by_cases h : k = 1
      · subst h; exact hZk_L2
      · -- Use that Z 1 has same distribution as Z k via contractability
        -- Equal distributions imply equal eLpNorm, hence MemLp transfers
        have h_dist := Contractable.map_single
          (X := Z) hZ_contract hZ_meas (i := k)
        have h_dist1 := Contractable.map_single
          (X := Z) hZ_contract hZ_meas (i := 1)
        -- Transfer eLpNorm using equal distributions
        have h_Lpnorm_eq : eLpNorm (Z 1) 2 μ = eLpNorm (Z k) 2 μ := by
          calc eLpNorm (Z 1) 2 μ
              = eLpNorm id 2 (Measure.map (Z 1) μ) := by
                  symm
                  exact eLpNorm_map_measure aestronglyMeasurable_id (hZ_meas 1).aemeasurable
            _ = eLpNorm id 2 (Measure.map (Z 0) μ) := by rw [h_dist1]
            _ = eLpNorm id 2 (Measure.map (Z k) μ) := by rw [← h_dist]
            _ = eLpNorm (Z k) 2 μ := eLpNorm_map_measure aestronglyMeasurable_id (hZ_meas k).aemeasurable
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
      have h_dist := Contractable.map_single
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
          · intro k hk; simp
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

end Exchangeability.DeFinetti.ViaL2
