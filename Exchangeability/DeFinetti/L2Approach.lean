/-
Copyright (c) 2025 exchangeability contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: exchangeability contributors
-/
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Second Proof of de Finetti via L² Contractability

This file implements Kallenberg's "Second proof" via the L² contractability bound
(Lemma 1.2, page 26).

## Main approach

This provides an elementary route to de Finetti's theorem without invoking the full
Mean Ergodic Theorem machinery. Instead, it uses a direct L² bound to show that
empirical distributions contract toward their limit.

## Main result

* `l2_contractability_bound`: Kallenberg's Lemma 1.2

## References

* Olav Kallenberg (2005), *Probabilistic Symmetries and Invariance Principles*,
  Springer, Chapter 1, page 26 (Lemma 1.2).
  
  **Lemma 1.2** (L²-bound): Let ξ₁,...,ξₙ ∈ L² with E ξⱼ = m, var(ξⱼ) = σ² < ∞,
  and cov(ξᵢ,ξⱼ) = σ²ρ for all i ≠ j, and fix any distributions (p₁,...,pₙ) and
  (q₁,...,qₙ) on {1,...,n}. Then
  
  E(∑ᵢ pᵢξᵢ - ∑ᵢ qᵢξᵢ)² ≤ 2σ²(1-ρ) sup_j |pⱼ - qⱼ|.

-/

noncomputable section

namespace Exchangeability.DeFinetti.L2Approach

open MeasureTheory BigOperators

variable {α : Type*} [MeasurableSpace α]
variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Kallenberg's Lemma 1.2**: L² contractability bound for exchangeable sequences.

Given ξ₁,...,ξₙ ∈ L² with common mean m, variance σ² < ∞, and
cov(ξᵢ,ξⱼ) = σ²ρ for all i ≠ j, then for any distributions p, q on {1,...,n}:

  E(∑ᵢ pᵢξᵢ - ∑ᵢ qᵢξᵢ)² ≤ 2σ²(1-ρ) sup_j |pⱼ - qⱼ|

This provides an elementary route to the convergence without invoking the
full Mean Ergodic Theorem machinery.
-/
theorem l2_contractability_bound
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (n : ℕ) (ξ : Fin n → Ω → ℝ)
    (m : ℝ) (σSq ρ : ℝ)
    (_hσ_pos : 0 ≤ σSq) (_hρ_bd : -1 ≤ ρ ∧ ρ ≤ 1)
    (_hmean : ∀ k, ∫ ω, ξ k ω ∂μ = m)
    (_hL2 : ∀ k, MemLp (fun ω => ξ k ω - m) 2 μ)
    (_hvar : ∀ k, ∫ ω, (ξ k ω - m)^2 ∂μ = σSq)
    (_hcov : ∀ i j, i ≠ j → ∫ ω, (ξ i ω - m) * (ξ j ω - m) ∂μ = σSq * ρ)
    (p q : Fin n → ℝ)
    (_hp_prob : (∑ i, p i) = 1 ∧ ∀ i, 0 ≤ p i)
    (_hq_prob : (∑ i, q i) = 1 ∧ ∀ i, 0 ≤ q i) :
    ∫ ω, (∑ i, p i * ξ i ω - ∑ i, q i * ξ i ω)^2 ∂μ ≤
      2 * σSq * (1 - ρ) * (⨆ i, |p i - q i|) := by
  -- Proof following Kallenberg page 26, Lemma 1.2 exactly
  
  -- Put cⱼ = pⱼ - qⱼ
  let c : Fin n → ℝ := fun i => p i - q i
  
  -- Note that ∑ⱼ cⱼ = 0
  have hc_sum : ∑ j, c j = 0 := by
    simp only [c]
    have hp := _hp_prob.1
    have hq := _hq_prob.1
    rw [Finset.sum_sub_distrib, hp, hq]
    ring
  
  -- and ∑ⱼ |cⱼ| ≤ 2
  have hc_abs_sum : ∑ j, |c j| ≤ 2 := by
    classical
    let Pos := Finset.univ.filter fun j : Fin n => 0 ≤ c j
    let Neg := Finset.univ.filter fun j : Fin n => c j < 0

    have hsplit_c : ∑ j ∈ Pos, c j + ∑ j ∈ Neg, c j = 0 := by
      have h := Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
        (p := fun j : Fin n => 0 ≤ c j) (f := fun j => c j)
      have hsum_univ : ∑ j ∈ (Finset.univ : Finset (Fin n)), c j = 0 := by
        simpa using hc_sum
      simpa [Pos, Neg, hsum_univ]
        using h

    have hbalance : ∑ j ∈ Pos, c j = -∑ j ∈ Neg, c j :=
      eq_neg_of_add_eq_zero_left hsplit_c

    have hsplit_abs : ∑ j, |c j| = ∑ j ∈ Pos, |c j| + ∑ j ∈ Neg, |c j| := by
      have h := Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
        (p := fun j : Fin n => 0 ≤ c j) (f := fun j => |c j|)
      simpa [Pos, Neg] using h.symm

    have habs_pos : ∑ j ∈ Pos, |c j| = ∑ j ∈ Pos, c j := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      exact abs_of_nonneg (Finset.mem_filter.mp hj).2

    have habs_neg : ∑ j ∈ Neg, |c j| = -∑ j ∈ Neg, c j := by
      have hterm : ∀ j ∈ Neg, |c j| = -c j := fun j hj => abs_of_neg (Finset.mem_filter.mp hj).2
      calc ∑ j ∈ Neg, |c j|
          = ∑ j ∈ Neg, (-c j) := Finset.sum_congr rfl hterm
      _ = -∑ j ∈ Neg, c j := by simp [Finset.sum_neg_distrib]

    have hdouble : ∑ j, |c j| = 2 * ∑ j ∈ Pos, c j := by
      calc ∑ j, |c j|
          = ∑ j ∈ Pos, |c j| + ∑ j ∈ Neg, |c j| := hsplit_abs
      _ = ∑ j ∈ Pos, c j + (-∑ j ∈ Neg, c j) := by
            simp [habs_pos, habs_neg]
      _ = ∑ j ∈ Pos, c j + ∑ j ∈ Pos, c j := by simp [hbalance]
      _ = 2 * ∑ j ∈ Pos, c j := by ring

    have hle_p : ∑ j ∈ Pos, c j ≤ ∑ j ∈ Pos, p j := by
      refine Finset.sum_le_sum ?_
      intro j _
      have hq_nn : 0 ≤ q j := _hq_prob.2 j
      calc c j = p j - q j := rfl
         _ ≤ p j := sub_le_self _ hq_nn

    have hsubset : Pos ⊆ (Finset.univ : Finset (Fin n)) := by
      intro j hj; exact Finset.mem_univ j

    have hle_one : ∑ j ∈ Pos, p j ≤ 1 := by
      have hsum_le := Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun j _ _ => _hp_prob.2 j)
      simpa [_hp_prob.1] using hsum_le

    calc ∑ j, |c j|
        = 2 * ∑ j ∈ Pos, c j := hdouble
      _ ≤ 2 * ∑ j ∈ Pos, p j := by
            exact (mul_le_mul_of_nonneg_left hle_p (by norm_num))
      _ ≤ 2 * 1 := by
            exact (mul_le_mul_of_nonneg_left hle_one (by norm_num))
      _ = 2 := by ring
  
  -- Step 1: E(∑cᵢξᵢ)² = E(∑cᵢ(ξᵢ-m))² using ∑cⱼ = 0
  have step1 : ∫ ω, (∑ i, c i * ξ i ω)^2 ∂μ =
               ∫ ω, (∑ i, c i * (ξ i ω - m))^2 ∂μ := by
    congr 1
    ext ω
    have : ∑ i, c i * ξ i ω = ∑ i, c i * (ξ i ω - m) := by
      conv_lhs => arg 2; ext i; rw [show ξ i ω = (ξ i ω - m) + m by ring]
      simp only [mul_add, Finset.sum_add_distrib]
      rw [add_eq_left]
      simp [← Finset.sum_mul, hc_sum]
    exact congrArg (· ^ 2) this
  
  -- Step 2: = ∑ᵢⱼ cᵢcⱼ cov(ξᵢ, ξⱼ) by expanding square and linearity
  have step2 : ∫ ω, (∑ i, c i * (ξ i ω - m))^2 ∂μ =
               ∑ i, ∑ j, c i * c j * ∫ ω, (ξ i ω - m) * (ξ j ω - m) ∂μ := by
    -- The products are integrable because their integrals exist (given by _hvar and _hcov)
    have h_integrable : ∀ i j, Integrable (fun ω => (ξ i ω - m) * (ξ j ω - m)) μ := by
      classical
      intro i j
      have h_mul : MemLp (fun ω => (ξ i ω - m) * (ξ j ω - m)) 1 μ :=
        (MemLp.mul' (hf := _hL2 j) (hφ := _hL2 i) : _)
      simpa [memLp_one_iff_integrable]
        using h_mul
    
    -- Now expand the square and apply linearity
    calc ∫ ω, (∑ i, c i * (ξ i ω - m))^2 ∂μ
        = ∫ ω, ∑ i, ∑ j, (c i * c j) * ((ξ i ω - m) * (ξ j ω - m)) ∂μ := by
            congr 1; ext ω
            rw [sq, Finset.sum_mul_sum]
            apply Finset.sum_congr rfl
            intro i _; apply Finset.sum_congr rfl
            intro j _; ring
      _ = ∑ i, ∑ j, ∫ ω, (c i * c j) * ((ξ i ω - m) * (ξ j ω - m)) ∂μ := by
            rw [integral_finset_sum _ (fun i _ => ?_)]
            congr 1; ext i
            rw [integral_finset_sum _ (fun j _ => ?_)]
            · exact (h_integrable i j).const_mul (c i * c j)
            · exact integrable_finset_sum _ (fun j _ => (h_integrable i j).const_mul _)
      _ = ∑ i, ∑ j, c i * c j * ∫ ω, (ξ i ω - m) * (ξ j ω - m) ∂μ := by
            congr 1; ext i; congr 1; ext j
            rw [integral_const_mul]
  
  -- Step 3: = σ²ρ(∑cᵢ)² + σ²(1-ρ)∑cᵢ² by separating i=j from i≠j
  have step3 : ∑ i, ∑ j, c i * c j * ∫ ω, (ξ i ω - m) * (ξ j ω - m) ∂μ =
               σSq * ρ * (∑ i, c i)^2 + σSq * (1 - ρ) * ∑ i, (c i)^2 := by
    -- Split the double sum into diagonal (i=j) and off-diagonal (i≠j)
    -- Diagonal terms: ∑ᵢ cᵢ² ∫(ξᵢ-m)² = ∑ᵢ cᵢ² · σ²
    have h_diag : ∑ i, c i * c i * ∫ ω, (ξ i ω - m) * (ξ i ω - m) ∂μ =
                  σSq * ∑ i, (c i)^2 := by
      trans (∑ i, (c i)^2 * σSq)
      · congr 1; ext i
        have hvar_i := _hvar i
        have h_sq : (fun ω => (ξ i ω - m) * (ξ i ω - m)) = (fun ω => (ξ i ω - m)^2) := by
          funext ω; ring
        calc c i * c i * ∫ ω, (ξ i ω - m) * (ξ i ω - m) ∂μ
            = (c i)^2 * ∫ ω, (ξ i ω - m)^2 ∂μ := by rw [h_sq]; ring
          _ = (c i)^2 * σSq := by rw [hvar_i]
      · rw [← Finset.sum_mul]; ring
    
    -- Off-diagonal: ∑ᵢ≠ⱼ cᵢcⱼ ∫(ξᵢ-m)(ξⱼ-m) = ∑ᵢ≠ⱼ cᵢcⱼ · σ²ρ
    have h_offdiag : ∑ i, ∑ j with j ≠ i, 
                     c i * c j * ∫ ω, (ξ i ω - m) * (ξ j ω - m) ∂μ =
                     σSq * ρ * ∑ i, ∑ j with j ≠ i, c i * c j := by
      sorry -- Apply _hcov to transform each off-diagonal term
    
    -- Relate off-diagonal sum to (∑cᵢ)²
    have h_offdiag_expand : ∑ i, ∑ j with j ≠ i, c i * c j =
                            (∑ i, c i)^2 - ∑ i, (c i)^2 := by
      sorry -- Expand (∑cᵢ)² and split into diagonal/off-diagonal
    
    sorry -- Combine diagonal and off-diagonal to get final form
  
  -- Step 4: = σ²(1-ρ)∑cᵢ² since (∑cᵢ)² = 0
  have step4 : σSq * ρ * (∑ i, c i)^2 + σSq * (1 - ρ) * ∑ i, (c i)^2 =
               σSq * (1 - ρ) * ∑ i, (c i)^2 := by
    rw [hc_sum]
    simp [zero_pow (Nat.succ_ne_zero 1)]
  
  -- Step 5: ≤ σ²(1-ρ)∑|cᵢ| sup|cⱼ| since cᵢ² ≤ |cᵢ| sup|cⱼ|
  have step5 : ∑ i, (c i)^2 ≤ ∑ i, |c i| * (⨆ j, |c j|) := by
    sorry -- Use supremum bound on each cᵢ²
  
  -- Nonnegativity lemmas
  have hσ_1ρ_nonneg : 0 ≤ σSq * (1 - ρ) := by
    apply mul_nonneg _hσ_pos
    linarith [_hρ_bd.2]  -- ρ ≤ 1 implies 0 ≤ 1 - ρ
  
  have hsup_nonneg : 0 ≤ ⨆ j, |c j| := by
    sorry -- Supremum of nonnegative values
  
  -- Step 6: ≤ 2σ²(1-ρ) sup|cⱼ| since ∑|cᵢ| ≤ 2
  calc ∫ ω, (∑ i, p i * ξ i ω - ∑ i, q i * ξ i ω)^2 ∂μ
      = ∫ ω, (∑ i, c i * ξ i ω)^2 ∂μ := by
        congr 1
        ext ω
        congr 1
        conv_lhs => rw [← Finset.sum_sub_distrib]
        simp only [c]
        congr 1
        ext i
        ring
    _ = ∫ ω, (∑ i, c i * (ξ i ω - m))^2 ∂μ := step1
    _ = ∑ i, ∑ j, c i * c j * ∫ ω, (ξ i ω - m) * (ξ j ω - m) ∂μ := step2
    _ = σSq * ρ * (∑ i, c i)^2 + σSq * (1 - ρ) * ∑ i, (c i)^2 := step3
    _ = σSq * (1 - ρ) * ∑ i, (c i)^2 := step4
    _ ≤ σSq * (1 - ρ) * (∑ i, |c i| * (⨆ j, |c j|)) := by
        apply mul_le_mul_of_nonneg_left step5 hσ_1ρ_nonneg
    _ = σSq * (1 - ρ) * ((∑ i, |c i|) * (⨆ j, |c j|)) := by
        rw [Finset.sum_mul]
    _ ≤ σSq * (1 - ρ) * (2 * (⨆ j, |c j|)) := by
        apply mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hc_abs_sum hsup_nonneg) hσ_1ρ_nonneg
    _ = 2 * σSq * (1 - ρ) * (⨆ i, |p i - q i|) := by ring_nf; rfl

end Exchangeability.DeFinetti.L2Approach
