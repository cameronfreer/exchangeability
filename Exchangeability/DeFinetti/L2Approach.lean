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
   E[(∑ cᵢ(ξᵢ-m))²] = ∑ᵢⱼ cᵢcⱼ E[(ξᵢ-m)(ξⱼ-m)] = ∑ᵢⱼ cᵢcⱼ Cov(ξᵢ,ξⱼ)
   ```

3. **Separate diagonal from off-diagonal:**
   ```
   = ∑ᵢ cᵢ² σ² + ∑ᵢ≠ⱼ cᵢcⱼ σ²ρ  (using Var(ξᵢ) = σ², Cov(ξᵢ,ξⱼ) = σ²ρ)
   = σ²∑cᵢ² + σ²ρ(∑ᵢcᵢ)² - σ²ρ∑cᵢ²  (since ∑ᵢ≠ⱼ cᵢcⱼ = (∑cᵢ)² - ∑cᵢ²)
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
      classical
      -- Rewrite each off-diagonal term using the covariance hypothesis.
      have h_cov_term :
          ∀ i j, j ≠ i → c i * c j * ∫ ω, (ξ i ω - m) * (ξ j ω - m) ∂μ =
            σSq * ρ * (c i * c j) := by
        intro i j hj
        have hcov_ij := _hcov i j (Ne.symm hj)
        simp [hcov_ij, mul_comm, mul_assoc]
      -- Apply the previous identity term-by-term inside the sums.
      have h_rewrite :
          ∑ i, ∑ j with j ≠ i, c i * c j * ∫ ω, (ξ i ω - m) * (ξ j ω - m) ∂μ
            = ∑ i, ∑ j with j ≠ i, σSq * ρ * (c i * c j) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j hj
        exact h_cov_term i j (Finset.mem_filter.mp hj |>.2)
      -- Factor the constant σSq * ρ out of the double sum.
      have h_factor :
          ∑ i, ∑ j with j ≠ i, σSq * ρ * (c i * c j)
            = σSq * ρ * ∑ i, ∑ j with j ≠ i, c i * c j := by
        simp [Finset.mul_sum, mul_assoc]
      calc
        ∑ i, ∑ j with j ≠ i, c i * c j * ∫ ω, (ξ i ω - m) * (ξ j ω - m) ∂μ
            = ∑ i, ∑ j with j ≠ i, σSq * ρ * (c i * c j) := h_rewrite
        _ = σSq * ρ * ∑ i, ∑ j with j ≠ i, c i * c j := h_factor
    
    -- Relate off-diagonal sum to (∑cᵢ)²
    have h_offdiag_expand : ∑ i, ∑ j with j ≠ i, c i * c j =
                            (∑ i, c i)^2 - ∑ i, (c i)^2 := by
      classical
      -- Expand the square as a double sum.
      have h_sq : (∑ i, c i)^2 = ∑ i, ∑ j, c i * c j := by
        simpa [pow_two] using
          (Finset.sum_mul_sum (s := (Finset.univ : Finset (Fin n)))
            (t := (Finset.univ : Finset (Fin n))) (f := fun i => c i) (g := fun j => c j))
      -- Separate diagonal from off-diagonal contributions.
      have h_inner_split : ∀ i, ∑ j, c i * c j =
          c i * c i + ∑ j with j ≠ i, c i * c j := by
        intro i
        classical
        conv_lhs => rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => j = i)]
        congr 1
        · have : Finset.filter (fun j => j = i) Finset.univ = {i} := by
            ext j; simp [eq_comm]
          simp [this]
      have h_split : ∑ i, ∑ j, c i * c j =
          ∑ i, c i * c i + ∑ i, ∑ j with j ≠ i, c i * c j := by
        simp_rw [h_inner_split]
        simp [Finset.sum_add_distrib]
      -- Rearranging gives the desired identity.
      have h_offdiag_eq : ∑ i, ∑ j with j ≠ i, c i * c j =
          ∑ i, ∑ j, c i * c j - ∑ i, c i * c i := by
        linarith [h_split]
      calc
        ∑ i, ∑ j with j ≠ i, c i * c j
            = ∑ i, ∑ j, c i * c j - ∑ i, c i * c i := h_offdiag_eq
        _ = (∑ i, c i)^2 - ∑ i, (c i)^2 := by
              simp [h_sq, pow_two, h_offdiag_eq.symm]
    
    -- Combine diagonal and off-diagonal contributions.
    have : ∑ i, ∑ j, c i * c j * ∫ ω, (ξ i ω - m) * (ξ j ω - m) ∂μ =
        σSq * ρ * (∑ i, c i)^2 + σSq * (1 - ρ) * ∑ i, (c i)^2 := by
      classical
      -- Split the integral double sum into diagonal and off-diagonal parts.
      have h_inner_split : ∀ i,
          ∑ j, c i * c j * ∫ ω, (ξ i ω - m) * (ξ j ω - m) ∂μ =
            c i * c i * ∫ ω, (ξ i ω - m) * (ξ i ω - m) ∂μ +
              ∑ j with j ≠ i, c i * c j * ∫ ω, (ξ i ω - m) * (ξ j ω - m) ∂μ := by
        intro i
        classical
        conv_lhs => rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => j = i)]
        congr 1
        · have : Finset.filter (fun j => j = i) Finset.univ = {i} := by
            ext j; simp [eq_comm]
          simp [this]
      have h_split : ∑ i, ∑ j, c i * c j * ∫ ω, (ξ i ω - m) * (ξ j ω - m) ∂μ =
          ∑ i, c i * c i * ∫ ω, (ξ i ω - m) * (ξ i ω - m) ∂μ +
            ∑ i, ∑ j with j ≠ i, c i * c j * ∫ ω, (ξ i ω - m) * (ξ j ω - m) ∂μ := by
        simp_rw [h_inner_split]
        simp [Finset.sum_add_distrib]
      -- Apply diagonal and off-diagonal evaluations.
      calc
        ∑ i, ∑ j, c i * c j * ∫ ω, (ξ i ω - m) * (ξ j ω - m) ∂μ
            = ∑ i, c i * c i * ∫ ω, (ξ i ω - m) * (ξ i ω - m) ∂μ +
                ∑ i, ∑ j with j ≠ i, c i * c j * ∫ ω, (ξ i ω - m) * (ξ j ω - m) ∂μ := h_split
        _ = σSq * ∑ i, (c i)^2 + σSq * ρ * ((∑ i, c i)^2 - ∑ i, (c i)^2) := by
              rw [h_diag, h_offdiag, h_offdiag_expand]
        _ = σSq * ρ * (∑ i, c i)^2 + σSq * (1 - ρ) * ∑ i, (c i)^2 := by ring
    exact this
  
  -- Step 4: = σ²(1-ρ)∑cᵢ² since (∑cᵢ)² = 0
  have step4 : σSq * ρ * (∑ i, c i)^2 + σSq * (1 - ρ) * ∑ i, (c i)^2 =
               σSq * (1 - ρ) * ∑ i, (c i)^2 := by
    rw [hc_sum]
    simp [zero_pow (Nat.succ_ne_zero 1)]
  
  -- Step 5: ≤ σ²(1-ρ)∑|cᵢ| sup|cⱼ| since cᵢ² ≤ |cᵢ| sup|cⱼ|
  have step5 : ∑ i, (c i)^2 ≤ ∑ i, |c i| * (⨆ j, |c j|) := by
    apply Finset.sum_le_sum
    intro i _
    have h_sq : (c i)^2 = |c i|^2 := (sq_abs _).symm
    rw [h_sq]
    have hbdd : BddAbove (Set.range fun j : Fin n => |c j|) := ⟨∑ k, |c k|, by
      intro y ⟨k, hk⟩
      rw [← hk]
      exact Finset.single_le_sum (fun i _ => abs_nonneg (c i)) (Finset.mem_univ k)⟩
    have h_le : |c i| ≤ ⨆ j, |c j| := le_ciSup hbdd i
    calc |c i|^2 = |c i| * |c i| := sq _
       _ ≤ |c i| * (⨆ j, |c j|) := mul_le_mul_of_nonneg_left h_le (abs_nonneg _)
  
  -- Nonnegativity lemmas
  have hσ_1ρ_nonneg : 0 ≤ σSq * (1 - ρ) := by
    apply mul_nonneg _hσ_pos
    linarith [_hρ_bd.2]  -- ρ ≤ 1 implies 0 ≤ 1 - ρ
  
  have hsup_nonneg : 0 ≤ ⨆ j, |c j| := by
    have hbdd : BddAbove (Set.range fun j : Fin n => |c j|) := ⟨∑ k, |c k|, by
      intro y ⟨k, hk⟩
      rw [← hk]
      exact Finset.single_le_sum (fun i _ => abs_nonneg (c i)) (Finset.mem_univ k)⟩
    by_cases h : Nonempty (Fin n)
    · obtain ⟨j0⟩ := h
      calc (0 : ℝ)
          ≤ |c j0| := abs_nonneg _
        _ ≤ ⨆ j, |c j| := le_ciSup hbdd j0
    · -- When Fin n is empty, the supremum is over an empty set
      -- In this case, all values are vacuously nonnegative
      haveI : IsEmpty (Fin n) := not_nonempty_iff.mp h
      have : (Set.range fun j : Fin n => |c j|) = ∅ := by
        ext x
        simp only [Set.mem_range, Set.mem_empty_iff_false, iff_false]
        rintro ⟨j, _⟩
        exact IsEmpty.false j
      rw [iSup, this, Real.sSup_empty]
  
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
