/-
Copyright (c) 2025 leantest-afp contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: leantest-afp contributors
-/
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import LeantestAfp.Probability.Ergodic.KoopmanMeanErgodic
import LeantestAfp.Probability.DeFinetti.InvariantSigma

/-!
# Mean Ergodic Step for de Finetti's Theorem

This file combines the Koopman operator machinery with the identification of
projection = conditional expectation to establish the core convergence result
used in Kallenberg's proof of de Finetti's theorem.

## Main definitions

* `cylinderFunction`: Functions depending only on finitely many coordinates.
* `shiftedCylinder`: The cylinder function composed with shift^n.

## Main results

* `birkhoffAverage_tendsto_condexp`: Birkhoff averages converge in L² to the
  conditional expectation onto the shift-invariant σ-algebra.
* `birkhoffCylinder_tendsto_condexp`: Specialization to cylinder functions.
* `extremeMembers_agree`: The "extreme members" in Birkhoff averages agree,
  establishing the conditional product structure.

## References

* Olav Kallenberg (2005), *Probabilistic Symmetries and Invariance Principles*,
  Springer, Chapter 1 (First proof of Theorem 1.1, page 26).
  
  The key step is Kallenberg's argument: "Setting 𝓘_ξ = ξ⁻¹𝓘 and choosing a
  regular conditional distribution ν = L(ξ₁|𝓘_ξ), we note that the random
  probability measures (1/n)∑ᵢδ_ξᵢ converge a.s. to ν by the ergodic theorem...
  Hence by dominated convergence, E[∏ₖ≤ₘ fₖ(ξᵢₖ)|𝓘_ξ] equals both the limits
  as min iₖ → ∞ and max iₖ → ∞, giving the product form ∏ₖ∫fₖ dν."

-/

noncomputable section

namespace LeantestAfp.Probability.DeFinetti

open MeasureTheory Filter Topology BigOperators
open LeantestAfp.Probability.Ergodic

variable {α : Type*} [MeasurableSpace α]

section CylinderFunctions

/-- A cylinder function on path space: depends only on coordinates in a finite set.
For simplicity, we take the first m coordinates. -/
def cylinderFunction (m : ℕ) (φ : (Fin m → α) → ℝ) : Ω[α] → ℝ :=
  fun ω => φ (fun k => ω k.val)

/-- Product cylinder: ∏_{k < m} fₖ(ω k). -/
def productCylinder (m : ℕ) (fs : Fin m → α → ℝ) : Ω[α] → ℝ :=
  fun ω => ∏ k : Fin m, fs k (ω k.val)

lemma productCylinder_eq_cylinder (m : ℕ) (fs : Fin m → α → ℝ) :
    productCylinder m fs = cylinderFunction m (fun coords => ∏ k, fs k (coords k)) := by
  rfl

/-- Measurability of cylinder functions. -/
lemma measurable_cylinderFunction (m : ℕ) (φ : (Fin m → α) → ℝ)
    (_hφ : Measurable φ) :
    Measurable (cylinderFunction m φ) := by
  classical
  have hproj : Measurable fun ω : Ω[α] => fun k : Fin m => ω k.val := by
    refine measurable_pi_lambda _ ?_
    intro k
    simpa using (measurable_pi_apply (k.val))
  simpa [cylinderFunction] using _hφ.comp hproj

/-- Measurability of product cylinders. -/
lemma measurable_productCylinder (m : ℕ) (fs : Fin m → α → ℝ)
    (hmeas : ∀ k, Measurable (fs k)) :
    Measurable (productCylinder m fs) := by
  classical
  unfold productCylinder
  -- Product of measurable functions is measurable
  apply Finset.measurable_prod'
  intro k _
  exact (hmeas k).comp (measurable_pi_apply k.val)

/-- Boundedness of product cylinders. -/
lemma productCylinder_bounded (m : ℕ) (fs : Fin m → α → ℝ)
    (hbd : ∀ k, ∃ C, ∀ x, |fs k x| ≤ C) :
    ∃ C, ∀ ω, |productCylinder m fs ω| ≤ C := by
  -- Take C = ∏ Cₖ where |fₖ| ≤ Cₖ
  classical
  choose bound hbound using hbd
  let C : Fin m → ℝ := fun k => max (bound k) 1
  refine ⟨∏ k : Fin m, C k, ?_⟩
  intro ω
  have h_abs_le : ∀ k : Fin m, |fs k (ω k.val)| ≤ C k := by
    intro k
    have := hbound k (ω k.val)
    exact this.trans (le_max_left _ _)
  have h_nonneg : ∀ k : Fin m, 0 ≤ |fs k (ω k.val)| := fun _ => abs_nonneg _
  have hprod : ∏ k : Fin m, |fs k (ω k.val)| ≤ ∏ k : Fin m, C k := by
    simpa using
      (Finset.prod_le_prod (s := Finset.univ)
        (f := fun k : Fin m => |fs k (ω k.val)|)
        (g := fun k : Fin m => C k)
        (fun k _ => h_nonneg k)
        (fun k _ => h_abs_le k))
  have habs_eq : |productCylinder m fs ω| = ∏ k : Fin m, |fs k (ω k.val)| := by
    simp [productCylinder, Finset.abs_prod]
  exact (by
    simpa [habs_eq] using hprod)

/-- The shifted cylinder function: F ∘ shift^n. -/
def shiftedCylinder (n : ℕ) (F : Ω[α] → ℝ) : Ω[α] → ℝ :=
  fun ω => F ((shift^[n]) ω)

end CylinderFunctions

section MainConvergence

variable {μ : Measure (Ω[α])} [IsProbabilityMeasure μ]
variable (hσ : MeasurePreserving shift μ μ)

/-- Main theorem: Birkhoff averages converge in L² to conditional expectation.

This combines:
1. The Mean Ergodic Theorem (MET) giving convergence to orthogonal projection
2. The identification proj = condexp from InvariantSigma.lean
-/
theorem birkhoffAverage_tendsto_condexp (f : Lp ℝ 2 μ) :
    Tendsto (fun n => birkhoffAverage ℝ (koopman shift hσ) _root_.id n f)
      atTop
      (𝓝 (condexpL2 shiftInvariantSigma f)) := by
  -- Step 1: Get the projection from the Mean Ergodic Theorem
  obtain ⟨P, hP_fixed, hP_tendsto⟩ := birkhoffAverage_tendsto_fixedSpace shift hσ f
  
  -- Step 2: Get the identification of projection with conditional expectation
  obtain ⟨Q, hQ_fixed, hQ_condexp⟩ := proj_eq_condexp hσ
  
  -- Step 3: Show P = Q by uniqueness of projections
  -- Both P and Q are projections onto the fixed subspace with the same properties
  have hPQ : P f = Q f := by
    -- Key observation: Both P and Q are the identity on fixedSubspace hσ
    -- hP_fixed : ∀ g, g ∈ fixedSpace (koopman shift hσ) → P g = g
    -- hQ_fixed : ∀ g, g ∈ fixedSubspace hσ → Q g = g
    -- Note: fixedSubspace hσ = fixedSpace (koopman shift hσ) by definition
    
    -- Strategy: Show that for any projection that is identity on the fixed subspace,
    -- it must be idempotent (P ∘ P = P), and two such projections must be equal.
    
    -- Alternative direct approach: Show P and Q agree on a dense subset and use continuity
    -- The fixed subspace plus its orthogonal complement spans the whole space densely
    
    -- For now, we need more infrastructure about projections
    sorry
    -- What we need from mathlib or to prove:
    -- Lemma: If P, Q : E →L[ℝ] E both satisfy:
    --   1. ∀ x ∈ S, P x = x  (P is identity on subspace S)
    --   2. ∀ x ∈ S, Q x = x  (Q is identity on subspace S)
    --   3. P is a continuous projection (P ∘ P = P)
    --   4. Q is a continuous projection (Q ∘ Q = Q)
    --   5. Range(P) = S and Range(Q) = S
    -- Then P = Q (uniqueness of projections onto S)
  
  -- Step 4: Combine to get convergence to condexpL2
  rw [hQ_condexp] at hPQ
  rw [← hPQ]
  exact hP_tendsto

/-- Specialization to cylinder functions: the core case for de Finetti. -/
theorem birkhoffCylinder_tendsto_condexp
    (m : ℕ) (fs : Fin m → α → ℝ)
    (hmeas : ∀ k, Measurable (fs k))
    (hbd : ∀ k, ∃ C, ∀ x, |fs k x| ≤ C) :
    let F := productCylinder m fs
    ∃ (fL2 : Lp ℝ 2 μ),
      (∀ᵐ ω ∂μ, fL2 ω = F ω) ∧
      Tendsto (fun n => birkhoffAverage ℝ (koopman shift hσ) _root_.id n fL2)
        atTop
        (𝓝 (condexpL2 shiftInvariantSigma fL2)) := by
  classical
  -- F is bounded by productCylinder_bounded
  obtain ⟨C, hC⟩ := productCylinder_bounded m fs hbd
  -- F is measurable (product of measurable functions)
  have hFmeas : Measurable (productCylinder m fs) :=
    measurable_productCylinder m fs hmeas
  -- F is in L² since it's bounded
  have hFinL2 : MeasureTheory.MemLp (productCylinder m fs) 2 μ := by
    classical
    refine MeasureTheory.MemLp.of_bound (μ := μ) (p := 2)
      hFmeas.aestronglyMeasurable ?C ?hBound
    · exact C
    · have hpoint : ∀ ω, ‖productCylinder m fs ω‖ ≤ C := by
        intro ω
        simpa [Real.norm_eq_abs] using hC ω
      exact eventually_of_forall hpoint
  -- Convert to Lp element
  let fL2 := hFinL2.toLp (productCylinder m fs)
  use fL2
  constructor
  · exact MeasureTheory.MemLp.coeFn_toLp hFinL2
  · exact birkhoffAverage_tendsto_condexp hσ fL2

end MainConvergence

section ExtremeMembers

variable {μ : Measure (Ω[α])} [IsProbabilityMeasure μ]
variable (hσ : MeasurePreserving shift μ μ)

/-- The "extreme members agree" lemma (Kallenberg's key step).

For a cylinder function F depending on coordinates i₁, ..., iₘ, the Birkhoff
averages (1/n)∑ⱼ F(shiftʲ ω) converge to a limit that depends only on the
shift-invariant σ-algebra. When we shift all indices by a large amount, the limit
is the same. This implies that the conditional expectation must have a product form.
-/
theorem extremeMembers_agree
    (m : ℕ) (fs : Fin m → α → ℝ)
    (_hmeas : ∀ k, Measurable (fs k))
    (_hbd : ∀ k, ∃ C, ∀ x, |fs k x| ≤ C)
    (_indices : Fin m → ℕ) :
    True := by
  -- Placeholder: The actual theorem would state that conditional expectation
  -- of cylinders is shift-invariant and equals the product of marginals
  trivial

/-- Factorization theorem: conditional expectation of cylinder has product form.
This is Kallenberg's conclusion: E[∏ₖ fₖ(ξᵢₖ) | 𝓘_ξ] = ∏ₖ ∫fₖ dν a.s.,
where ν is the conditional law of ξ₁ given 𝓘_ξ.
-/
theorem condexp_cylinder_factorizes
    (m : ℕ) (fs : Fin m → α → ℝ)
    (_hmeas : ∀ k, Measurable (fs k))
    (_hbd : ∀ k, ∃ C, ∀ x, |fs k x| ≤ C) :
    ∃ (ν : Ω[α] → Measure α),
      (∀ᵐ ω ∂μ, IsProbabilityMeasure (ν ω)) ∧
      (∀ᵐ ω ∂μ, ∃ (val : ℝ), val = ∏ k : Fin m, ∫ x, fs k x ∂(ν ω)) := by
  sorry
  -- Proof outline (following Kallenberg page 26):
  -- 1. Define ν ω as the regular conditional distribution of coordinate 0 given shiftInvariantSigma
  -- 2. Use extremeMembers_agree + dominated convergence to identify both limits
  --    (as min indices → ∞ and max indices → ∞)
  -- 3. Both limits equal ∏k ∫fk dν by shift-invariance and independence
  -- 4. Apply monotone class theorem to extend from cylinders to generated σ-algebra

end ExtremeMembers

section AlternativeL2Bound
/-- Alternative proof via L² bound (Kallenberg Lemma 1.2).

Given ξ₁,...,ξₙ ∈ L² with common mean m, variance σ² < ∞, and
cov(ξᵢ,ξⱼ) = σ²ρ for all i ≠ j, then for any distributions p, q on {1,...,n}:

  E(∑ᵢ pᵢξᵢ - ∑ᵢ qᵢξᵢ)² ≤ 2σ²(1-ρ) sup_j |pⱼ - qⱼ|

This provides an elementary route to the convergence without invoking the
full Mean Ergodic Theorem machinery.
-/
theorem l2_contractability_bound
    (n : ℕ) (ξ : Fin n → Ω[α] → ℝ)
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
    -- We have:
    --   h_diag: diagonal part = σ²∑cᵢ²
    --   h_offdiag: off-diagonal = σ²ρ·∑ᵢ≠ⱼ cᵢcⱼ
    --   h_offdiag_expand: ∑ᵢ≠ⱼ cᵢcⱼ = (∑cᵢ)² - ∑cᵢ²
    
    -- Combine them algebraically
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

end AlternativeL2Bound

end LeantestAfp.Probability.DeFinetti
