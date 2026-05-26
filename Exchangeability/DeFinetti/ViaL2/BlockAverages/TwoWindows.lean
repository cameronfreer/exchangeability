/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Exchangeability.DeFinetti.ViaL2.BlockAverages.Covariance
import Exchangeability.DeFinetti.ViaL2.WindowMachinery

/-!
# BlockAverages — Two-window L² bound

`l2_bound_two_windows_uniform`: L² distance between block averages over two
windows of the same length is bounded by a uniform constant. Uses the
covariance structure from `BlockAverages/Covariance.lean`.
-/

noncomputable section

namespace Exchangeability.DeFinetti.ViaL2

open MeasureTheory ProbabilityTheory BigOperators Filter Topology
open Exchangeability
open Exchangeability.DeFinetti.L2Helpers

variable {Ω : Type*} [MeasurableSpace Ω]

open scoped BigOperators

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
          ∑ b : {t // t ∈ S}, wS b.1 = ∑ t ∈ S, wS t := Finset.sum_attach (s := S) (f := fun t => wS t)
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
    (X : ℕ → Ω → ℝ)
    (hX_meas : ∀ i, Measurable (X i))
    (f : ℝ → ℝ) (hf_meas : Measurable f)
    (hf_bdd : ∃ M, ∀ x, |f x| ≤ M)
    -- Accept Cf and covariance structure as arguments
    (Cf mf σSqf ρf : ℝ)
    (hCf_def : Cf = 2 * σSqf * (1 - ρf))
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

end Exchangeability.DeFinetti.ViaL2
