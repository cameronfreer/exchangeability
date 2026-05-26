/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Exchangeability.DeFinetti.ViaL2.BlockAverages.Covariance

/-!
# BlockAverages — Long vs. tail L² bound

`l2_bound_long_vs_tail`: the second L² Cauchy bound, comparing a long window
average to a tail-shifted average. Together with `l2_bound_two_windows_uniform`
(`BlockAverages/TwoWindows.lean`) this drives the Cauchy property of block
averages used in `CesaroConvergence/Cauchy.lean`.

Also exposes `get_covariance_constant`, the helper that packages the
covariance structure of `f ∘ X` into a single shared bound `Cf` passed to
both `l2_bound_two_windows_uniform` and this file's main lemma.
-/

noncomputable section

namespace Exchangeability.DeFinetti.ViaL2

open MeasureTheory ProbabilityTheory BigOperators Filter Topology
open Exchangeability
open Exchangeability.DeFinetti.L2Helpers

variable {Ω : Type*} [MeasurableSpace Ω]

open scoped BigOperators

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
    Contractable.comp hX_contract hX_meas f hf_meas

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

lemma l2_bound_long_vs_tail
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
    (hρ_bd : -1 ≤ ρf ∧ ρf ≤ 1)
    (n m k : ℕ) (hk : 0 < k) (hkm : k ≤ m) :
    ∫ ω, ((1 / (m : ℝ)) * ∑ i : Fin m, f (X (n + i.val + 1) ω) -
          (1 / (k : ℝ)) * ∑ i : Fin k, f (X (n + (m - k) + i.val + 1) ω))^2 ∂μ
      ≤ Cf / k := by
  -- Express the difference of the two averages as a single weighted combination
  -- `∑ p_i Y_i - ∑ q_i Y_i = ∑ (p_i - q_i) Y_i` over `Fin m` and apply
  -- `L2Approach.l2_contractability_bound`. The uniform bound on `|p_i - q_i|`
  -- is `1/k`, giving the final `Cf/k`.
  obtain ⟨M, hM⟩ := hf_bdd
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
    -- Reconstruct MemLp from boundedness (M, hM already available above)
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
                ring_nf
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


end Exchangeability.DeFinetti.ViaL2
