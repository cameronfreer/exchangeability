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
    simp [← Finset.sum_sub_distrib, hp, hq]
  
  -- and ∑ⱼ |cⱼ| ≤ 2
  have hc_abs_sum : ∑ j, |c j| ≤ 2 := by
    -- Key insight: For distributions p, q with ∑pⱼ = ∑qⱼ = 1 and cⱼ = pⱼ - qⱼ:
    -- Let J₊ = {j : cⱼ ≥ 0} and J₋ = {j : cⱼ < 0}
    -- Then ∑ⱼ∈J₊ cⱼ = -∑ⱼ∈J₋ cⱼ (since ∑cⱼ = 0)
    -- Also ∑ⱼ∈J₊ cⱼ ≤ ∑ⱼ∈J₊ pⱼ ≤ 1 (since qⱼ ≥ 0)
    -- So ∑|cⱼ| = ∑ⱼ∈J₊ cⱼ + ∑ⱼ∈J₋ |cⱼ| = 2·∑ⱼ∈J₊ cⱼ ≤ 2
    sorry
    -- TODO: Formalize using Finset.sum_filter on nonneg/neg parts
    -- Key lemmas needed:
    --   1. Split sum by sign: ∑f = ∑(f on {x : f x ≥ 0}) + ∑(f on {x : f x < 0})
    --   2. Balance: ∑cⱼ = 0 implies positive part = negative part
    --   3. Bound: ∑ⱼ∈J₊ cⱼ = ∑ⱼ∈J₊ (pⱼ - qⱼ) ≤ ∑ⱼ∈J₊ pⱼ ≤ 1
  
  -- Step 1: E(∑cᵢξᵢ)² = E(∑cᵢ(ξᵢ-m))² using ∑cⱼ = 0
  have step1 : ∫ ω, (∑ i, c i * ξ i ω)^2 ∂μ =
               ∫ ω, (∑ i, c i * (ξ i ω - m))^2 ∂μ := by
    congr 1
    ext ω
    have : ∑ i, c i * ξ i ω = ∑ i, c i * (ξ i ω - m) := by
      rw [← Finset.sum_sub_distrib]
      simp only [mul_sub]
      rw [Finset.sum_sub_distrib, sub_eq_self]
      calc ∑ i, c i * m = (∑ i, c i) * m := Finset.sum_mul.symm
         _ = 0 * m := by rw [hc_sum]
         _ = 0 := zero_mul _
    exact congrArg (· ^ 2) this
  
  -- Step 2: = ∑ᵢⱼ cᵢcⱼ cov(ξᵢ, ξⱼ) by expanding square and linearity
  have step2 : ∫ ω, (∑ i, c i * (ξ i ω - m))^2 ∂μ =
               ∑ i, ∑ j, c i * c j * ∫ ω, (ξ i ω - m) * (ξ j ω - m) ∂μ := by
    -- Expand (∑ᵢ cᵢ(ξᵢ-m))² = ∑ᵢⱼ cᵢcⱼ(ξᵢ-m)(ξⱼ-m)
    conv_lhs => 
      arg 1; ext ω
      rw [sq]
      rw [Finset.sum_mul_sum]
    -- Simplify the product structure
    conv_lhs =>
      arg 1; ext ω
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    -- Now: ∫ (∑ᵢⱼ cᵢcⱼ(ξᵢ-m)(ξⱼ-m))
    -- Apply integral_finset_sum twice to pull sums outside
    sorry
    -- This needs: ∫ ∑ᵢⱼ f(i,j,ω) = ∑ᵢⱼ ∫ f(i,j,ω)
    -- Each term c_i * c_j * (ξ_i - m) * (ξ_j - m) is integrable
    -- Can use integral_finset_sum from MeasureTheory
  
  -- Step 3: = σ²ρ(∑cᵢ)² + σ²(1-ρ)∑cᵢ² by separating i=j from i≠j
  have step3 : ∑ i, ∑ j, c i * c j * ∫ ω, (ξ i ω - m) * (ξ j ω - m) ∂μ =
               σSq * ρ * (∑ i, c i)^2 + σSq * (1 - ρ) * ∑ i, (c i)^2 := by
    -- Split the double sum into diagonal (i=j) and off-diagonal (i≠j)
    -- Diagonal terms: ∑ᵢ cᵢ² ∫(ξᵢ-m)² = ∑ᵢ cᵢ² · σ²
    have h_diag : ∑ i in Finset.univ, c i * c i * ∫ ω, (ξ i ω - m) * (ξ i ω - m) ∂μ =
                  σSq * ∑ i, (c i)^2 := by
      rw [← Finset.sum_mul]
      congr 1
      ext i
      have hvar_i := _hvar i
      calc c i * c i * ∫ ω, (ξ i ω - m) * (ξ i ω - m) ∂μ
          = (c i)^2 * ∫ ω, (ξ i ω - m)^2 ∂μ := by ring_nf; rfl
        _ = (c i)^2 * σSq := by rw [hvar_i]
    
    -- Off-diagonal: ∑ᵢ≠ⱼ cᵢcⱼ ∫(ξᵢ-m)(ξⱼ-m) = ∑ᵢ≠ⱼ cᵢcⱼ · σ²ρ
    have h_offdiag : ∑ i, ∑ j in (Finset.univ.filter (· ≠ i)), 
                     c i * c j * ∫ ω, (ξ i ω - m) * (ξ j ω - m) ∂μ =
                     σSq * ρ * ∑ i, ∑ j in (Finset.univ.filter (· ≠ i)), c i * c j := by
      -- Apply _hcov to each off-diagonal term
      rw [← Finset.sum_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      have hj_ne : j ≠ i := Finset.mem_filter.mp hj |>.2
      have hcov_ij := _hcov i j hj_ne
      calc c i * c j * ∫ ω, (ξ i ω - m) * (ξ j ω - m) ∂μ
          = c i * c j * (σSq * ρ) := by rw [hcov_ij]
        _ = σSq * ρ * (c i * c j) := by ring
    
    -- Relate off-diagonal sum to (∑cᵢ)²
    have h_offdiag_expand : ∑ i, ∑ j in (Finset.univ.filter (· ≠ i)), c i * c j =
                            (∑ i, c i)^2 - ∑ i, (c i)^2 := by
      -- Use (∑cᵢ)² = ∑ᵢⱼ cᵢcⱼ = (∑ᵢ cᵢ²) + (∑ᵢ≠ⱼ cᵢcⱼ)
      have h_sq_expand : (∑ i, c i)^2 = ∑ i, ∑ j, c i * c j := by
        rw [Finset.sum_mul_sum]
        rfl
      -- Split into diagonal and off-diagonal
      have h_split : ∑ i, ∑ j, c i * c j = 
                     (∑ i, c i * c i) + (∑ i, ∑ j in (Finset.univ.filter (· ≠ i)), c i * c j) := by
        apply Finset.sum_congr rfl
        intro i _
        -- For each i, split the inner sum over j into j=i and j≠i
        conv_lhs => 
          rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => j = i) (fun j => c i * c j)]
        congr 1
        · -- The filter (j = i) gives just the singleton {i}
          have : Finset.filter (fun j => j = i) Finset.univ = {i} := by
            ext j
            simp [Finset.mem_filter, Finset.mem_singleton]
          rw [this, Finset.sum_singleton]
        · -- The filter (j ≠ i) is what we want
          congr 1
          ext j
          simp [Finset.mem_filter]
      calc ∑ i, ∑ j in (Finset.univ.filter (· ≠ i)), c i * c j
          = (∑ i, c i)^2 - ∑ i, c i * c i := by
            rw [h_sq_expand, h_split]; ring
        _ = (∑ i, c i)^2 - ∑ i, (c i)^2 := by
            congr 1; ext i; ring
    
    -- Combine diagonal and off-diagonal
    calc ∑ i, ∑ j, c i * c j * ∫ ω, (ξ i ω - m) * (ξ j ω - m) ∂μ
        = (∑ i, c i * c i * ∫ ω, (ξ i ω - m) * (ξ i ω - m) ∂μ) + 
          (∑ i, ∑ j in (Finset.univ.filter (· ≠ i)), c i * c j * ∫ ω, (ξ i ω - m) * (ξ j ω - m) ∂μ) := by
            sorry
            -- Split using sum_filter_add_sum_filter_not on inner sum
      _ = σSq * ∑ i, (c i)^2 + σSq * ρ * ∑ i, ∑ j in (Finset.univ.filter (· ≠ i)), c i * c j := by
            rw [h_diag, h_offdiag]
      _ = σSq * ∑ i, (c i)^2 + σSq * ρ * ((∑ i, c i)^2 - ∑ i, (c i)^2) := by
            rw [h_offdiag_expand]
      _ = σSq * ∑ i, (c i)^2 + σSq * ρ * (∑ i, c i)^2 - σSq * ρ * ∑ i, (c i)^2 := by
            ring
      _ = σSq * ρ * (∑ i, c i)^2 + (σSq - σSq * ρ) * ∑ i, (c i)^2 := by
            ring
      _ = σSq * ρ * (∑ i, c i)^2 + σSq * (1 - ρ) * ∑ i, (c i)^2 := by
            ring
  
  -- Step 4: = σ²(1-ρ)∑cᵢ² since (∑cᵢ)² = 0
  have step4 : σSq * ρ * (∑ i, c i)^2 + σSq * (1 - ρ) * ∑ i, (c i)^2 =
               σSq * (1 - ρ) * ∑ i, (c i)^2 := by
    rw [hc_sum]
    simp [zero_pow (Nat.succ_ne_zero 1)]
  
  -- Step 5: ≤ σ²(1-ρ)∑|cᵢ| sup|cⱼ| since cᵢ² ≤ |cᵢ| sup|cⱼ|
  have step5 : ∑ i, (c i)^2 ≤ ∑ i, |c i| * (⨆ j, |c j|) := by
    -- Each cᵢ² = |cᵢ|² ≤ |cᵢ| · sup|cⱼ|
    apply Finset.sum_le_sum
    intro i _
    have h_sq : (c i)^2 = |c i|^2 := sq_abs (c i)
    rw [h_sq]
    have h_le : |c i| ≤ ⨆ j, |c j| := by
      apply le_ciSup
      · -- Bounded above: Finset.univ is finite
        use (Finset.univ.image (fun j => |c j|)).sup id
        intro y ⟨j, hj⟩
        rw [← hj]
        exact Finset.le_sup (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩)
      · -- i is in the index set (always true for Fin n)
        exact Finset.mem_univ i
    calc |c i|^2 = |c i| * |c i| := sq _
       _ ≤ |c i| * (⨆ j, |c j|) := mul_le_mul_of_nonneg_left h_le (abs_nonneg _)
  
  -- Nonnegativity lemmas
  have hσ_1ρ_nonneg : 0 ≤ σSq * (1 - ρ) := by
    apply mul_nonneg _hσ_pos
    linarith [_hρ_bd.2]  -- ρ ≤ 1 implies 0 ≤ 1 - ρ
  
  have hsup_nonneg : 0 ≤ ⨆ j, |c j| := by
    -- Supremum of nonnegative values is nonnegative
    apply ciSup_nonneg
    intro j
    exact abs_nonneg _
  
  -- Step 6: ≤ 2σ²(1-ρ) sup|cⱼ| since ∑|cᵢ| ≤ 2
  calc ∫ ω, (∑ i, p i * ξ i ω - ∑ i, q i * ξ i ω)^2 ∂μ
      = ∫ ω, (∑ i, c i * ξ i ω)^2 ∂μ := by congr; ext; simp [c]
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
