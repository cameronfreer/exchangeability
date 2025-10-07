/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Elementary Proof of de Finetti via L² Contractability

This file develops an **elementary proof** of de Finetti's theorem using Kallenberg's
L² contractability bound, avoiding the full Mean Ergodic Theorem machinery from the
Koopman operator approach.

## Mathematical background

The Mean Ergodic Theorem (see `KoopmanMeanErgodic.lean`) provides a deep connection
between de Finetti's theorem and ergodic theory, but requires sophisticated functional
analysis. Kallenberg observed that for exchangeable sequences with finite variance,
a much simpler **direct L² bound** suffices to prove convergence.

**Key insight:** For exchangeable sequences `ξ₁, ξ₂, ...` with constant correlation
`ρ`, weighted averages with different weights are close in L²:

  `E(∑ pᵢξᵢ - ∑ qᵢξᵢ)² ≤ 2σ²(1-ρ) sup_j |pⱼ - qⱼ|`

As `n → ∞` in exchangeable sequences, the correlation `ρ → 1`, making the bound go to 0.
This shows that *all* weighted averages converge to the same limit (the tail σ-algebra).

## Comparison of approaches

**L² approach (this file):**
- ✅ Elementary: Uses only basic L² estimates and Cauchy-Schwarz
- ✅ Direct: Proves convergence via explicit bounds
- ✅ Quantitative: Gives explicit rates of convergence
- ❌ Requires finite variance assumption
- ❌ Less general than ergodic approach

**Ergodic approach** (`KoopmanMeanErgodic.lean`, `ProjectionLemmas.lean`):
- ✅ Works for all L² functions (not just finite variance)
- ✅ Deep connection to dynamical systems and ergodic theory
- ✅ Generalizes beyond exchangeability
- ❌ Requires sophisticated functional analysis (orthogonal projections, fixed-point subspaces)
- ❌ Less elementary

## Application to de Finetti

The L² contractability bound proves that:
1. **Empirical averages converge:** `n⁻¹ ∑ᵢ₌₁ⁿ ξᵢ` converges in L² as `n → ∞`
2. **The limit is tail-measurable:** Any two weighted averages with similar weights
   give similar results, forcing the limit to be independent of the weights
3. **Conditionally i.i.d. structure:** The exchangeable sequence is conditionally
   independent given the limiting average (the tail σ-algebra)

This provides a complete proof of de Finetti's theorem without the Koopman operator.

## Main result

* `l2_contractability_bound`: **Kallenberg's Lemma 1.2** - the key L² bound for
  weighted averages of exchangeable sequences with constant correlation

## Implementation notes

The proof closely follows Kallenberg (2005), page 26. The calculation is elementary
but requires careful tracking of diagonal vs. off-diagonal terms in the covariance
expansion. The key steps are:

1. Reduce to centered variables: `∑ cᵢξᵢ = ∑ cᵢ(ξᵢ - m)` when `∑ cᵢ = 0`
2. Expand the L² norm: `E(∑ cᵢ(ξᵢ - m))² = ∑ᵢⱼ cᵢcⱼ cov(ξᵢ, ξⱼ)`
3. Separate diagonal and off-diagonal: `= σ²∑cᵢ² + σ²ρ∑ᵢ≠ⱼ cᵢcⱼ`
4. Simplify using `∑cᵢ = 0`: `= σ²(1-ρ)∑cᵢ²`
5. Bound by supremum: `∑cᵢ² ≤ (sup|cᵢ|)(∑|cᵢ|) ≤ 2 sup|cᵢ|`

## References

* Kallenberg, "Probabilistic Symmetries and Invariance Principles" (2005), Chapter 1,
  Lemma 1.2 (page 26)
* This is presented as the "second proof" of de Finetti's theorem, contrasting with
  the ergodic approach (Kallenberg's "first proof")
-/

noncomputable section

namespace Exchangeability.DeFinetti.L2Approach

open MeasureTheory BigOperators

variable {α : Type*} [MeasurableSpace α]
variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Step 1:** Centering reduction - when coefficients sum to zero, we can replace
variables with centered variables in weighted sums. -/
lemma integral_sq_weighted_sum_eq_centered {μ : Measure Ω}
    {n : ℕ} (ξ : Fin n → Ω → ℝ) (c : Fin n → ℝ) (m : ℝ)
    (hc_sum : ∑ i, c i = 0) :
    ∫ ω, (∑ i, c i * ξ i ω)^2 ∂μ = ∫ ω, (∑ i, c i * (ξ i ω - m))^2 ∂μ := by
  congr 1; ext ω; congr 1
  conv_lhs => arg 2; ext i; rw [show ξ i ω = (ξ i ω - m) + m by ring]
  simp only [mul_add, Finset.sum_add_distrib, add_eq_left, ← Finset.sum_mul, hc_sum]
  ring

/-- **Step 2:** Expand L² norm as bilinear form - converts integral of square to
double sum of covariances. -/
lemma integral_sq_weighted_sum_eq_double_sum {μ : Measure Ω}
    {n : ℕ} (η : Fin n → Ω → ℝ) (c : Fin n → ℝ)
    (h_integrable : ∀ i j, Integrable (fun ω => η i ω * η j ω) μ) :
    ∫ ω, (∑ i, c i * η i ω)^2 ∂μ =
    ∑ i, ∑ j, c i * c j * ∫ ω, η i ω * η j ω ∂μ := by
  calc ∫ ω, (∑ i, c i * η i ω)^2 ∂μ
      = ∫ ω, ∑ i, ∑ j, (c i * c j) * (η i ω * η j ω) ∂μ := by
          congr 1; ext ω
          rw [sq, Finset.sum_mul_sum]
          apply Finset.sum_congr rfl
          intro i _; apply Finset.sum_congr rfl
          intro j _; ring
    _ = ∑ i, ∑ j, ∫ ω, (c i * c j) * (η i ω * η j ω) ∂μ := by
          rw [integral_finset_sum _ (fun i _ => ?_)]
          congr 1; ext i
          rw [integral_finset_sum _ (fun j _ => ?_)]
          · exact (h_integrable i j).const_mul (c i * c j)
          · exact integrable_finset_sum _ (fun j _ => (h_integrable i j).const_mul _)
    _ = ∑ i, ∑ j, c i * c j * ∫ ω, η i ω * η j ω ∂μ := by
          congr 1; ext i; congr 1; ext j
          rw [integral_const_mul]

/-- **Step 3:** Separate diagonal from off-diagonal terms in covariance expansion. -/
lemma double_sum_covariance_formula {n : ℕ} {c : Fin n → ℝ} (σSq ρ : ℝ)
    (cov_diag : ℝ) (cov_offdiag : ℝ)
    (h_diag : cov_diag = σSq)
    (h_offdiag : cov_offdiag = σSq * ρ) :
    ∑ i, ∑ j, c i * c j * (if i = j then cov_diag else cov_offdiag) =
    σSq * ρ * (∑ i, c i)^2 + σSq * (1 - ρ) * ∑ i, (c i)^2 := by
  -- Split into diagonal and off-diagonal
  have h_diag_sum : ∑ i, c i * c i * cov_diag = σSq * ∑ i, (c i)^2 := by
    simp [h_diag, ← Finset.sum_mul, pow_two]; ring
  have h_offdiag_sum : ∑ i, ∑ j with j ≠ i, c i * c j * cov_offdiag =
      σSq * ρ * ∑ i, ∑ j with j ≠ i, c i * c j := by
    simp [h_offdiag, Finset.mul_sum, mul_assoc, mul_comm]
  have h_offdiag_expand :
      ∑ i, ∑ j with j ≠ i, c i * c j = (∑ i, c i)^2 - ∑ i, (c i)^2 := by
    classical
    have h_sq : (∑ i, c i)^2 = ∑ i, ∑ j, c i * c j := by
      rw [pow_two, Finset.sum_mul_sum (s := (Finset.univ : Finset (Fin n)))
        (t := (Finset.univ : Finset (Fin n))) (f := fun i => c i) (g := fun j => c j)]
    have h_inner_split : ∀ i, ∑ j, c i * c j = c i * c i + ∑ j with j ≠ i, c i * c j := by
      intro i; classical
      conv_lhs => rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => j = i)]
      congr 1
      have : Finset.filter (fun j => j = i) Finset.univ = {i} := by ext j; simp [eq_comm]
      simp [this]
    have h_split :
        ∑ i, ∑ j, c i * c j = ∑ i, c i * c i + ∑ i, ∑ j with j ≠ i, c i * c j := by
      simp_rw [h_inner_split]; simp [Finset.sum_add_distrib]
    calc ∑ i, ∑ j with j ≠ i, c i * c j
        = ∑ i, ∑ j, c i * c j - ∑ i, c i * c i := by linarith [h_split]
      _ = (∑ i, c i)^2 - ∑ i, (c i)^2 := by simp [h_sq, pow_two]
  -- Now split the original double sum
  classical
  have h_inner_split : ∀ i, ∑ j, c i * c j * (if i = j then cov_diag else cov_offdiag) =
      c i * c i * cov_diag + ∑ j with j ≠ i, c i * c j * cov_offdiag := by
    intro i; classical
    conv_lhs => rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => j = i)]
    congr 1
    · have : Finset.filter (fun j => j = i) Finset.univ = {i} := by ext j; simp [eq_comm]
      simp [this]
    · apply Finset.sum_congr rfl; intro j hj
      simp [Ne.symm (Finset.mem_filter.mp hj).2]
  have h_split : ∑ i, ∑ j, c i * c j * (if i = j then cov_diag else cov_offdiag) =
      ∑ i, c i * c i * cov_diag + ∑ i, ∑ j with j ≠ i, c i * c j * cov_offdiag := by
    simp_rw [h_inner_split]; simp [Finset.sum_add_distrib]
  calc ∑ i, ∑ j, c i * c j * (if i = j then cov_diag else cov_offdiag)
      = ∑ i, c i * c i * cov_diag + ∑ i, ∑ j with j ≠ i, c i * c j * cov_offdiag := h_split
    _ = σSq * ∑ i, (c i)^2 + σSq * ρ * ((∑ i, c i)^2 - ∑ i, (c i)^2) := by
          rw [h_diag_sum, h_offdiag_sum, h_offdiag_expand]
    _ = σSq * ρ * (∑ i, c i)^2 + σSq * (1 - ρ) * ∑ i, (c i)^2 := by ring

/-- **Step 4:** When coefficients sum to zero, the correlation term vanishes. -/
lemma covariance_formula_zero_sum {n : ℕ} {c : Fin n → ℝ} (σSq ρ : ℝ)
    (hc_sum : ∑ i, c i = 0) :
    σSq * ρ * (∑ i, c i)^2 + σSq * (1 - ρ) * ∑ i, (c i)^2 =
    σSq * (1 - ρ) * ∑ i, (c i)^2 := by
  rw [hc_sum]; simp [zero_pow (Nat.succ_ne_zero 1)]

/-- **Step 5:** Sum of squares bounded by L¹ norm times supremum. -/
lemma sum_sq_le_sum_abs_mul_sup {n : ℕ} {c : Fin n → ℝ} :
    ∑ i, (c i)^2 ≤ ∑ i, |c i| * (⨆ j, |c j|) := by
  have hbdd : BddAbove (Set.range fun j : Fin n => |c j|) := ⟨∑ k, |c k|, by
    intro y ⟨k, hk⟩; rw [← hk]
    exact Finset.single_le_sum (fun i _ => abs_nonneg (c i)) (Finset.mem_univ k)⟩
  apply Finset.sum_le_sum; intro i _
  calc (c i)^2 = |c i|^2 := (sq_abs _).symm
     _ = |c i| * |c i| := sq _
     _ ≤ |c i| * (⨆ j, |c j|) := mul_le_mul_of_nonneg_left (le_ciSup hbdd i) (abs_nonneg _)

/-- **Step 6:** Combine all steps into final bound. Takes the chain of equalities and
inequalities from the previous steps and produces the final L² contractability bound. -/
lemma l2_bound_from_steps {n : ℕ} {c p q : Fin n → ℝ} (σSq ρ : ℝ)
    (hσSq_nonneg : 0 ≤ σSq) (hρ_bd : ρ ≤ 1)
    (hc_def : c = fun i => p i - q i)
    (hc_abs_sum : ∑ i, |c i| ≤ 2)
    (step5 : ∑ i, (c i)^2 ≤ ∑ i, |c i| * (⨆ j, |c j|)) :
    σSq * (1 - ρ) * ∑ i, (c i)^2 ≤ 2 * σSq * (1 - ρ) * (⨆ i, |p i - q i|) := by
  have hbdd : BddAbove (Set.range fun j : Fin n => |c j|) := ⟨∑ k, |c k|, by
    intro y ⟨k, hk⟩; rw [← hk]
    exact Finset.single_le_sum (fun i _ => abs_nonneg (c i)) (Finset.mem_univ k)⟩
  have hσ_1ρ_nonneg : 0 ≤ σSq * (1 - ρ) := mul_nonneg hσSq_nonneg (by linarith)
  have hsup_nonneg : 0 ≤ ⨆ j, |c j| := by
    by_cases h : Nonempty (Fin n)
    · obtain ⟨j0⟩ := h
      calc (0 : ℝ) ≤ |c j0| := abs_nonneg _
        _ ≤ ⨆ j, |c j| := le_ciSup hbdd j0
    · haveI : IsEmpty (Fin n) := not_nonempty_iff.mp h
      have : (Set.range fun j : Fin n => |c j|) = ∅ := by
        ext x; simp only [Set.mem_range, Set.mem_empty_iff_false, iff_false]
        rintro ⟨j, _⟩; exact IsEmpty.false j
      rw [iSup, this, Real.sSup_empty]
  calc σSq * (1 - ρ) * ∑ i, (c i)^2
      ≤ σSq * (1 - ρ) * (∑ i, |c i| * (⨆ j, |c j|)) :=
          mul_le_mul_of_nonneg_left step5 hσ_1ρ_nonneg
    _ = σSq * (1 - ρ) * ((∑ i, |c i|) * (⨆ j, |c j|)) := by rw [Finset.sum_mul]
    _ ≤ σSq * (1 - ρ) * (2 * (⨆ j, |c j|)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hc_abs_sum hsup_nonneg) hσ_1ρ_nonneg
    _ = 2 * σSq * (1 - ρ) * (⨆ j, |c j|) := by ring
    _ = 2 * σSq * (1 - ρ) * (⨆ i, |p i - q i|) := by simp [hc_def]

/--
**Kallenberg's Lemma 1.2:** L² contractability bound for weighted averages of
exchangeable sequences.

**Statement:** Given `ξ₁, ..., ξₙ ∈ L²` with:
- Common mean: `E[ξⱼ] = m` for all `j`
- Common variance: `Var(ξⱼ) = σ²` for all `j`
- **Constant correlation:** `Cov(ξᵢ, ξⱼ) = σ²ρ` for all `i ≠ j`

Then for any probability distributions `p = (p₁, ..., pₙ)` and `q = (q₁, ..., qₙ)`:

  `E[(∑ᵢ pᵢξᵢ - ∑ᵢ qᵢξᵢ)²] ≤ 2σ²(1-ρ) sup_j |pⱼ - qⱼ|`

**Mathematical significance:** This is the key lemma for Kallenberg's "elementary"
proof of de Finetti's theorem. It shows that weighted averages with similar weights
give similar results in L², with an **explicit quantitative bound**.

**Intuition:** For exchangeable sequences:
1. The correlation `ρ` measures how "exchangeable" the sequence is
2. When `ρ ≈ 1`, all the `ξᵢ` are highly correlated (nearly equal)
3. The bound `2σ²(1-ρ)` goes to 0 as `ρ → 1`
4. This forces all weighted averages to converge to the same limit

**Why constant correlation?** Exchangeable sequences have a special covariance
structure: all pairs `(ξᵢ, ξⱼ)` with `i ≠ j` have the same correlation. This
follows from the symmetry - if we swap indices, the distribution doesn't change,
so the covariance must be the same for all off-diagonal pairs.

**Connection to de Finetti:** For an infinite exchangeable sequence, the finite
sub-sequences have correlations `ρₙ → 1` as `n → ∞` (they become "more exchangeable").
Applying this lemma shows:
- Empirical averages `n⁻¹ ∑ᵢ ξᵢ` form a Cauchy sequence in L²
- They converge to a limit `ξ̄` (the tail σ-algebra)
- The limit is independent of the weights chosen
- This yields de Finetti's representation

**Proof strategy:**
1. **Centering:** Define `cⱼ = pⱼ - qⱼ`, noting that `∑ cⱼ = 0` (both are probability
   distributions). Use this to replace `ξⱼ` with `ξⱼ - m` (centered variables).

2. **Expand the square:** Use linearity of expectation to expand:
   ```
   E[(∑ cᵢ(ξᵢ-m))²] = ∑ᵢⱼ cᵢcⱼ E[(ξᵢ-m)(ξⱼ-m)]
                    = ∑ᵢⱼ cᵢcⱼ Cov(ξᵢ,ξⱼ)
   ```

3. **Separate diagonal from off-diagonal:**
   ```
   = ∑ᵢ cᵢ² σ² + ∑ᵢ≠ⱼ cᵢcⱼ σ²ρ
     (using Var(ξᵢ) = σ², Cov(ξᵢ,ξⱼ) = σ²ρ)
   = σ²∑cᵢ² + σ²ρ(∑ᵢcᵢ)² - σ²ρ∑cᵢ²
     (since ∑ᵢ≠ⱼ cᵢcⱼ = (∑cᵢ)² - ∑cᵢ²)
   = σ²(1-ρ)∑cᵢ²  (using ∑cᵢ = 0)
   ```

4. **Bound the sum of squares:**
   ```
   ∑cᵢ² ≤ (sup|cᵢ|) · (∑|cᵢ|) ≤ (sup|cᵢ|) · 2
   ```
   The final inequality uses `∑|cᵢ| ≤ 2` (the L¹ distance between two probability
   distributions is at most 2).

5. **Combine:** Putting it together gives the desired bound.

**Historical note:** This is Kallenberg's "second proof" of de Finetti's theorem
(Chapter 1, Lemma 1.2). It's more elementary than the ergodic approach but requires
finite variance. The elegance is that it reduces a sophisticated theorem to a
straightforward L² calculation.

**Comparison with ergodic approach:** The Mean Ergodic Theorem gives the same
convergence result via abstract functional analysis (orthogonal projections in
Hilbert space). This lemma gives an explicit bound and a direct proof, at the
cost of requiring finite variance.
-/
theorem l2_contractability_bound
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} (ξ : Fin n → Ω → ℝ)
    (m : ℝ) (σ ρ : ℝ)
    (_hρ_bd : -1 ≤ ρ ∧ ρ ≤ 1)
    (_hmean : ∀ k, ∫ ω, ξ k ω ∂μ = m)
    (_hL2 : ∀ k, MemLp (fun ω => ξ k ω - m) 2 μ)
    (_hvar : ∀ k, ∫ ω, (ξ k ω - m)^2 ∂μ = σ ^ 2)
    (_hcov : ∀ i j, i ≠ j → ∫ ω, (ξ i ω - m) * (ξ j ω - m) ∂μ = σ ^ 2 * ρ)
    (p q : Fin n → ℝ)
    (_hp_prob : (∑ i, p i) = 1 ∧ ∀ i, 0 ≤ p i)
    (_hq_prob : (∑ i, q i) = 1 ∧ ∀ i, 0 ≤ q i) :
    ∫ ω, (∑ i, p i * ξ i ω - ∑ i, q i * ξ i ω)^2 ∂μ ≤
      2 * σ ^ 2 * (1 - ρ) * (⨆ i, |p i - q i|) := by
  -- Proof following Kallenberg page 26, Lemma 1.2 exactly
  
  classical
  let c : Fin n → ℝ := fun i => p i - q i
  set σSq : ℝ := σ ^ 2

  have hc_sum : ∑ j, c j = 0 := by
    simp only [c, Finset.sum_sub_distrib, _hp_prob.1, _hq_prob.1]; ring
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

    have habs_pos : ∑ j ∈ Pos, |c j| = ∑ j ∈ Pos, c j :=
      Finset.sum_congr rfl
        (fun j hj => abs_of_nonneg (Finset.mem_filter.mp hj).2)

    have habs_neg : ∑ j ∈ Neg, |c j| = -∑ j ∈ Neg, c j :=
      calc ∑ j ∈ Neg, |c j|
          = ∑ j ∈ Neg, (-c j) :=
              Finset.sum_congr rfl
                (fun j hj => abs_of_neg (Finset.mem_filter.mp hj).2)
        _ = -∑ j ∈ Neg, c j := by simp [Finset.sum_neg_distrib]

    have hdouble : ∑ j, |c j| = 2 * ∑ j ∈ Pos, c j :=
      calc ∑ j, |c j|
          = ∑ j ∈ Pos, |c j| + ∑ j ∈ Neg, |c j| := hsplit_abs
        _ = ∑ j ∈ Pos, c j + (-∑ j ∈ Neg, c j) := by simp [habs_pos, habs_neg]
        _ = ∑ j ∈ Pos, c j + ∑ j ∈ Pos, c j := by simp [hbalance]
        _ = 2 * ∑ j ∈ Pos, c j := by ring

    have hle_p : ∑ j ∈ Pos, c j ≤ ∑ j ∈ Pos, p j :=
      Finset.sum_le_sum fun j _ => sub_le_self _ (_hq_prob.2 j)

    have hle_one : ∑ j ∈ Pos, p j ≤ 1 :=
      calc ∑ j ∈ Pos, p j ≤ ∑ j, p j :=
            Finset.sum_le_sum_of_subset_of_nonneg (fun j _ => Finset.mem_univ j)
              (fun j _ _ => _hp_prob.2 j)
        _ = 1 := _hp_prob.1

    calc ∑ j, |c j|
        = 2 * ∑ j ∈ Pos, c j := hdouble
      _ ≤ 2 * ∑ j ∈ Pos, p j := mul_le_mul_of_nonneg_left hle_p (by norm_num)
      _ ≤ 2 * 1 := mul_le_mul_of_nonneg_left hle_one (by norm_num)
      _ = 2 := by norm_num
  
  -- Step 1: E(∑cᵢξᵢ)² = E(∑cᵢ(ξᵢ-m))² using ∑cⱼ = 0
  have step1 : ∫ ω, (∑ i, c i * ξ i ω)^2 ∂μ =
               ∫ ω, (∑ i, c i * (ξ i ω - m))^2 ∂μ :=
    integral_sq_weighted_sum_eq_centered ξ c m hc_sum
  
  -- Step 2: = ∑ᵢⱼ cᵢcⱼ cov(ξᵢ, ξⱼ) by expanding square and linearity
  have h_integrable :
      ∀ i j, Integrable (fun ω => (ξ i ω - m) * (ξ j ω - m)) μ := fun i j => by
    classical
    have h_mul : MemLp (fun ω => (ξ i ω - m) * (ξ j ω - m)) 1 μ :=
      (MemLp.mul' (hf := _hL2 j) (hφ := _hL2 i) : _)
    simpa [memLp_one_iff_integrable] using h_mul
  have step2 : ∫ ω, (∑ i, c i * (ξ i ω - m))^2 ∂μ =
               ∑ i, ∑ j, c i * c j * ∫ ω, (ξ i ω - m) * (ξ j ω - m) ∂μ :=
    integral_sq_weighted_sum_eq_double_sum (fun i => fun ω => ξ i ω - m) c h_integrable
  
  -- Step 3: = σ²ρ(∑cᵢ)² + σ²(1-ρ)∑cᵢ² by separating i=j from i≠j
  have step3 : ∑ i, ∑ j, c i * c j * ∫ ω, (ξ i ω - m) * (ξ j ω - m) ∂μ =
               σSq * ρ * (∑ i, c i)^2 + σSq * (1 - ρ) * ∑ i, (c i)^2 := by
    have hvar : ∀ k, ∫ ω, (ξ k ω - m)^2 ∂μ = σSq := fun k => _hvar k
    have hcov :
        ∀ i j, i ≠ j → ∫ ω, (ξ i ω - m) * (ξ j ω - m) ∂μ = σSq * ρ :=
      fun i j hij => _hcov i j hij
    trans (∑ i, ∑ j, c i * c j * (if i = j then σSq else σSq * ρ))
    · congr 1; ext i; congr 1; ext j
      split_ifs with h
      · subst h
        have h_sq :
            (fun ω => (ξ i ω - m) * (ξ i ω - m)) = (fun ω => (ξ i ω - m)^2) := by
          funext ω; ring
        rw [h_sq]; exact congr_arg (c i * c i * ·) (hvar i)
      · exact congr_arg (c i * c j * ·) (hcov i j h)
    · exact double_sum_covariance_formula σSq ρ σSq (σSq * ρ) rfl rfl
  
  -- Step 4: = σ²(1-ρ)∑cᵢ² since (∑cᵢ)² = 0
  have step4 : σSq * ρ * (∑ i, c i)^2 + σSq * (1 - ρ) * ∑ i, (c i)^2 =
               σSq * (1 - ρ) * ∑ i, (c i)^2 :=
    covariance_formula_zero_sum σSq ρ hc_sum

  -- Steps 5-6: Combine inequalities to get final bound
  have step5 : ∑ i, (c i)^2 ≤ ∑ i, |c i| * (⨆ j, |c j|) :=
    sum_sq_le_sum_abs_mul_sup

  calc ∫ ω, (∑ i, p i * ξ i ω - ∑ i, q i * ξ i ω)^2 ∂μ
      = ∫ ω, (∑ i, c i * ξ i ω)^2 ∂μ := by
          congr 1; ext ω; congr 1
          conv_lhs => rw [← Finset.sum_sub_distrib]
          simp only [c]; congr 1; ext i; ring
    _ = ∫ ω, (∑ i, c i * (ξ i ω - m))^2 ∂μ := step1
    _ = ∑ i, ∑ j, c i * c j * ∫ ω, (ξ i ω - m) * (ξ j ω - m) ∂μ := step2
    _ = σSq * ρ * (∑ i, c i)^2 + σSq * (1 - ρ) * ∑ i, (c i)^2 := step3
    _ = σSq * (1 - ρ) * ∑ i, (c i)^2 := step4
    _ ≤ 2 * σSq * (1 - ρ) * (⨆ i, |p i - q i|) :=
          l2_bound_from_steps σSq ρ (sq_nonneg σ) _hρ_bd.2 rfl hc_abs_sum step5
    _ = 2 * σ ^ 2 * (1 - ρ) * (⨆ i, |p i - q i|) := by
          simp [σSq, pow_two, mul_comm, mul_left_comm, mul_assoc]

end Exchangeability.DeFinetti.L2Approach
