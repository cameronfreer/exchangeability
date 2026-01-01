/-
Copyright (c) 2025 The Exchangeability Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Exchangeability.DeFinetti.ViaKoopman.BlockInjection
import Exchangeability.DeFinetti.ViaKoopman.CesaroConvergence
import Exchangeability.Contractability

/-!
# Contractable Factorization for de Finetti's Theorem

This file implements the **disjoint-block averaging argument** from Kallenberg's "first proof"
of de Finetti's theorem. The key insight is that contractability (invariance under strictly
monotone subsequences) directly yields product factorization of conditional expectations,
without using permutations or exchangeability.

## Main definitions

* `blockAvg m n k f ω`: Block average of `f` at position `k` with `m` blocks of size `n`.
  Computes `(1/n) * ∑_{j=0}^{n-1} f(ω(k*n + j))`.

## Main results

* `blockAvg_tendsto_condExp`: Block averages converge L¹ to conditional expectation.
* `product_L1_convergence`: Product of block averages converges L¹ to product of CEs.
* `condexp_product_factorization_contractable`: For contractable measures,
  `CE[∏ fᵢ(ωᵢ) | mSI] = ∏ CE[fᵢ(ω₀) | mSI]` a.e.

## Mathematical context

The proof proceeds as follows:

1. **Block injection**: For each choice function `j : Fin m → Fin n`, select one element
   from each of `m` disjoint blocks of size `n` via `blockInjection`.

2. **Contractability application**: Since `blockInjection` is strictly monotone,
   contractability gives: `∫ ∏ fᵢ(ωᵢ) dμ = ∫ ∏ fᵢ(ω(ρⱼ(i))) dμ` for each `j`.

3. **Averaging over choices**: Summing over all `j : Fin m → Fin n` and dividing by `n^m`
   gives: `∫ ∏ fᵢ(ωᵢ) dμ = ∫ ∏ blockAvg_i dμ`.

4. **L¹ convergence**: As `n → ∞`, block averages converge to conditional expectations
   (reusing Cesàro machinery from `CesaroConvergence.lean`).

5. **Conclusion**: Taking limits yields the product factorization of conditional expectations.

## References

* Kallenberg (2005), *Probabilistic Symmetries and Invariance Principles*, Chapter 1
-/

open Filter MeasureTheory

noncomputable section

namespace Exchangeability.DeFinetti.ViaKoopman

open MeasureTheory Filter Topology ProbabilityTheory
open Exchangeability.Ergodic
open Exchangeability.PathSpace
open Exchangeability.DeFinetti
open scoped BigOperators

variable {α : Type*} [MeasurableSpace α]

-- Short notation for shift-invariant σ-algebra (used throughout this file)
local notation "mSI" => shiftInvariantSigma (α := α)

/-! ### Block Average Definition -/

/-- Block average of function `f` at position `k` with `m` blocks of size `n`.

For coordinate `k < m`, computes the average of `f(ω(k*n + j))` over `j ∈ {0, ..., n-1}`.
This is the Cesàro average of `f` starting at coordinate `k*n`. -/
def blockAvg (m n : ℕ) (k : Fin m) (f : α → ℝ) (ω : ℕ → α) : ℝ :=
  if hn : n = 0 then 0
  else (1 / (n : ℝ)) * (Finset.range n).sum (fun j => f (ω (k.val * n + j)))

@[simp]
lemma blockAvg_zero_n (m : ℕ) (k : Fin m) (f : α → ℝ) (ω : ℕ → α) :
    blockAvg m 0 k f ω = 0 := by
  simp [blockAvg]

lemma blockAvg_pos_n {m n : ℕ} (hn : 0 < n) (k : Fin m) (f : α → ℝ) (ω : ℕ → α) :
    blockAvg m n k f ω = (1 / (n : ℝ)) * (Finset.range n).sum (fun j => f (ω (k.val * n + j))) := by
  simp [blockAvg, Nat.pos_iff_ne_zero.mp hn]

/-! ### Block Average and Shifted Cesàro Averages -/

/-- Block average at position k equals Cesàro average starting at k*n.

This connects block averages to the existing Cesàro convergence machinery. -/
lemma blockAvg_eq_cesaro_shifted {m n : ℕ} (hn : 0 < n) (k : Fin m) (f : α → ℝ) (ω : ℕ → α) :
    blockAvg m n k f ω =
      (1 / (n : ℝ)) * (Finset.range n).sum (fun j => f ((shift^[k.val * n] ω) j)) := by
  rw [blockAvg_pos_n hn]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [shift_iterate_apply]
  congr 1
  -- j + k.val * n = k.val * n + j
  ring

/-! ### Measurability of Block Averages -/

lemma measurable_blockAvg {m n : ℕ} (k : Fin m) {f : α → ℝ} (hf : Measurable f) :
    Measurable (blockAvg (α := α) m n k f) := by
  unfold blockAvg
  by_cases hn : n = 0
  · simp only [hn, ↓reduceDIte, measurable_const]
  · simp only [hn, ↓reduceDIte]
    apply Measurable.const_mul
    apply Finset.measurable_sum
    intro j _
    exact hf.comp (measurable_pi_apply _)

/-! ### Block Average L¹ Convergence

The key observation is that block average at position k is a Cesàro average starting at k*n.
By `condexp_precomp_iterate_eq`, the conditional expectation of `f(ω(k*n))` equals CE[f(ω₀) | mSI].
The existing Cesàro convergence machinery then gives L¹ convergence. -/

section BlockAvgConvergence

variable {μ : Measure (Ω[α])} [IsProbabilityMeasure μ] [StandardBorelSpace α]

/-- Block averages converge in L¹ to conditional expectation.

For each fixed k, as n → ∞:
`∫ |blockAvg m n k f ω - μ[f(ω₀) | mSI] ω| dμ → 0`

This follows from the Cesàro convergence theorem since blockAvg at position k
is a Cesàro average starting at coordinate k*n, and by `condexp_precomp_iterate_eq`,
the target CE is the same regardless of the starting position. -/
lemma blockAvg_tendsto_condExp
    (hσ : MeasurePreserving shift μ μ) (m : ℕ) (k : Fin m)
    {f : α → ℝ} (hf : Measurable f) (hf_bd : ∃ C, ∀ x, |f x| ≤ C) :
    Tendsto (fun n =>
      ∫ ω, |blockAvg m (n + 1) k f ω - μ[(fun ω => f (ω 0)) | mSI] ω| ∂μ)
      atTop (𝓝 0) := by
  -- Key insight: blockAvg m (n+1) k f ω = (A n) (shift^[k*(n+1)] ω)
  -- where A n is the standard Cesàro average.
  --
  -- Proof strategy:
  -- 1. blockAvg = A ∘ shift^[offset] (by blockAvg_eq_cesaro_shifted)
  -- 2. CE is shift-invariant: Y = Y ∘ shift^[p] a.e. (for shift-invariant σ-algebra)
  -- 3. By measure-preserving substitution: ∫ |blockAvg - Y| = ∫ |A - Y|
  -- 4. Apply L¹ Cesàro convergence (from CesaroConvergence.lean)
  --
  -- The L¹ Cesàro convergence lemma (L1_cesaro_convergence_bounded) is private in
  -- CesaroConvergence.lean, so this proof is marked sorry pending refactoring to
  -- export that result publicly.
  sorry

end BlockAvgConvergence

/-! ### Contractability and Block Average Factorization

The core of Kallenberg's first proof: contractability gives integral factorization
via averaging over all choice functions. -/

section Contractability

variable {μ : Measure (Ω[α])} [IsProbabilityMeasure μ] [StandardBorelSpace α]

/-- For contractable μ, integral of product equals integral of product with reindexed coordinates.

Given strict monotone k : Fin m → ℕ, contractability says:
`∫ ∏ᵢ fᵢ(ωᵢ) dμ = ∫ ∏ᵢ fᵢ(ω(k(i))) dμ`

This is the fundamental identity that lets us swap between original and reindexed coordinates. -/
lemma integral_prod_reindex_of_contractable
    (hContract : ∀ (m' : ℕ) (k : Fin m' → ℕ), StrictMono k →
        Measure.map (fun ω i => ω (k i)) μ = Measure.map (fun ω (i : Fin m') => ω i.val) μ)
    {m : ℕ} (fs : Fin m → α → ℝ)
    (hfs_meas : ∀ i, Measurable (fs i))
    (hfs_bd : ∀ i, ∃ C, ∀ x, |fs i x| ≤ C)
    {k : Fin m → ℕ} (hk : StrictMono k) :
    ∫ ω, (∏ i : Fin m, fs i (ω i.val)) ∂μ =
    ∫ ω, (∏ i : Fin m, fs i (ω (k i))) ∂μ := by
  -- Use contractability: μ ∘ (ω ↦ (ω(k(0)), ..., ω(k(m-1)))) = μ ∘ (ω ↦ (ω₀, ..., ω_{m-1}))
  have h_map := hContract m k hk
  -- The measurable function for mapping to Fin m → α
  have h_meas_orig : Measurable (fun ω (i : Fin m) => ω i.val : Ω[α] → (Fin m → α)) := by
    rw [measurable_pi_iff]; intro i; exact measurable_pi_apply _
  have h_meas_reindex : Measurable (fun ω i => ω (k i) : Ω[α] → (Fin m → α)) := by
    rw [measurable_pi_iff]; intro i; exact measurable_pi_apply _
  -- The integrand on Fin m → α
  let F : (Fin m → α) → ℝ := fun ω' => ∏ i, fs i (ω' i)
  have hF_meas_base : Measurable F := by
    apply Finset.measurable_prod
    intro i _
    exact (hfs_meas i).comp (measurable_pi_apply i)
  have hF_meas : AEStronglyMeasurable F (Measure.map (fun ω (i : Fin m) => ω i.val) μ) :=
    hF_meas_base.aestronglyMeasurable
  -- Rewrite both sides using integral_map
  have hF_meas' : AEStronglyMeasurable F (Measure.map (fun ω i => ω (k i)) μ) :=
    hF_meas_base.aestronglyMeasurable
  calc ∫ ω, (∏ i : Fin m, fs i (ω i.val)) ∂μ
    _ = ∫ ω', F ω' ∂(Measure.map (fun ω (i : Fin m) => ω i.val) μ) := by
        rw [integral_map h_meas_orig.aemeasurable hF_meas]
    _ = ∫ ω', F ω' ∂(Measure.map (fun ω i => ω (k i)) μ) := by rw [h_map]
    _ = ∫ ω, (∏ i : Fin m, fs i (ω (k i))) ∂μ := by
        rw [integral_map h_meas_reindex.aemeasurable hF_meas']

/-- Averaging over all choice functions yields product of block averages.

For any bounded measurable fs : Fin m → α → ℝ:
`∫ ∏ᵢ fᵢ(ωᵢ) dμ = ∫ ∏ᵢ blockAvg m n i fᵢ ω dμ`

This is proved by:
1. For each j : Fin m → Fin n, contractability gives ∫ ∏ fᵢ(ωᵢ) = ∫ ∏ fᵢ(ω(ρⱼ(i)))
2. Sum over all j and divide by n^m to get block averages
-/
lemma integral_prod_eq_integral_blockAvg
    (hσ : MeasurePreserving shift μ μ)
    (hContract : ∀ (m' : ℕ) (k : Fin m' → ℕ), StrictMono k →
        Measure.map (fun ω i => ω (k i)) μ = Measure.map (fun ω (i : Fin m') => ω i.val) μ)
    {m n : ℕ} (hn : 0 < n)
    (fs : Fin m → α → ℝ)
    (hfs_meas : ∀ i, Measurable (fs i))
    (hfs_bd : ∀ i, ∃ C, ∀ x, |fs i x| ≤ C) :
    ∫ ω, (∏ i : Fin m, fs i (ω i.val)) ∂μ =
    ∫ ω, (∏ i : Fin m, blockAvg m n i (fs i) ω) ∂μ := by
  -- The proof uses averaging over all choice functions j : Fin m → Fin n.
  --
  -- Key steps:
  -- 1. For each j, blockInjection m n j is strictly monotone
  -- 2. By contractability, ∫ ∏ fᵢ(ωᵢ) = ∫ ∏ fᵢ(ω(ρⱼ(i))) for each j
  -- 3. The integral is independent of j, so we can average over all j
  -- 4. (1/n^m) * ∑_j ∏ fᵢ(ω(ρⱼ(i))) = ∏ blockAvg_i
  --
  -- The key observation is that for fixed ω and i:
  -- (1/n^m) * ∑_{j : Fin m → Fin n} f_i(ω(i*n + j(i)))
  -- = (1/n^m) * n^{m-1} * ∑_{l=0}^{n-1} f_i(ω(i*n + l))
  -- = (1/n) * ∑_{l=0}^{n-1} f_i(ω(i*n + l))
  -- = blockAvg m n i (f_i) ω
  --
  -- The product distributes because each f_i depends only on j(i), and the
  -- coordinates j(i) for different i are independent in the sum.

  -- Step 1: For each j : Fin m → Fin n, contractability gives equal integrals
  have h_each_j : ∀ j : Fin m → Fin n,
      ∫ ω, (∏ i : Fin m, fs i (ω i.val)) ∂μ =
      ∫ ω, (∏ i : Fin m, fs i (ω (blockInjection m n j i.val))) ∂μ := by
    intro j
    -- blockInjection is strictly monotone
    have h_mono : StrictMono (blockInjection m n j) := blockInjection_strictMono m n hn j
    -- Define k(i) = blockInjection m n j i for i : Fin m
    let k : Fin m → ℕ := fun i => blockInjection m n j i.val
    -- k is strictly monotone (restriction of strictly monotone function to Fin m)
    have hk_mono : StrictMono k := by
      intro i i' hii'
      exact h_mono hii'
    -- Apply contractability
    exact integral_prod_reindex_of_contractable hContract fs hfs_meas hfs_bd hk_mono

  -- Step 2: Since all integrals are equal, we can average over j
  -- Let S = (Fin m → Fin n), the set of all choice functions
  -- LHS = (1/|S|) * ∑_{j ∈ S} ∫ ∏ fᵢ(ωᵢ) = LHS (constant)
  -- RHS = ∫ (1/|S|) * ∑_{j ∈ S} ∏ fᵢ(ω(ρⱼ(i))) = ∫ ∏ blockAvg_i

  -- Step 3: Show that the averaged sum equals product of block averages
  -- This is the key algebraic identity
  -- TODO: Formalize the averaging argument showing
  -- (1/n^m) * ∑_{j : Fin m → Fin n} ∏_i f_i(ω(i*n + j(i))) = ∏_i blockAvg m n i f_i ω
  --
  -- The proof uses independence of coordinates in the sum:
  -- For each i, j(i) ranges over Fin n independently of other j(i').
  -- So the sum factorizes as a product of sums.
  sorry

end Contractability

/-! ### Product L¹ Convergence via Telescoping -/

section ProductConvergence

variable {μ : Measure (Ω[α])} [IsProbabilityMeasure μ] [StandardBorelSpace α]

/-- Telescoping bound for product differences.

|∏ Aᵢ - ∏ Bᵢ| ≤ m * C^{m-1} * max |Aᵢ - Bᵢ|

when |Aᵢ|, |Bᵢ| ≤ C for all i.

Note: When m = 0, both products are 1, so the LHS is 0 and the RHS is 0.
For m > 0, we use Finset.univ.sup' with nonemptiness. -/
lemma prod_diff_bound {m : ℕ} {A B : Fin m → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hA : ∀ i, |A i| ≤ C) (hB : ∀ i, |B i| ≤ C) :
    |∏ i, A i - ∏ i, B i| ≤
      if h : 0 < m then m * C^(m - 1) * (Finset.univ.sup' ⟨⟨0, h⟩, Finset.mem_univ _⟩ (fun i => |A i - B i|))
      else 0 := by
  -- When m = 0, both products are 1, LHS = |1 - 1| = 0
  by_cases hm : 0 < m
  · simp only [hm, ↓reduceDIte]
    -- Standard telescoping identity:
    -- ∏ᵢ Aᵢ - ∏ᵢ Bᵢ = ∑ⱼ (∏_{i<j} Aᵢ) * (Aⱼ - Bⱼ) * (∏_{i>j} Bᵢ)
    --
    -- Taking absolute values and using |Aᵢ|, |Bᵢ| ≤ C:
    -- |∏ Aᵢ - ∏ Bᵢ| ≤ ∑ⱼ C^{j} * |Aⱼ - Bⱼ| * C^{m-1-j}
    --              = C^{m-1} * ∑ⱼ |Aⱼ - Bⱼ|
    --              ≤ C^{m-1} * m * max_j |Aⱼ - Bⱼ|
    --              = m * C^{m-1} * max_j |Aⱼ - Bⱼ|
    --
    -- TODO: Formalize using Finset.prod_sub_prod or induction on m
    sorry
  · simp only [hm, ↓reduceDIte]
    -- m = 0, so both products over Fin 0 are empty, hence equal to 1
    have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm
    subst hm0
    simp only [Finset.univ_eq_empty, Finset.prod_empty, sub_self, abs_zero, le_refl]

/-- Product of block averages converges L¹ to product of conditional expectations.

`∫ |∏ blockAvg_i - ∏ CE[fᵢ(ω₀) | mSI]| dμ → 0` as n → ∞

Proof uses telescoping bound and individual L¹ convergence of each blockAvg_i. -/
lemma product_blockAvg_L1_convergence
    (hσ : MeasurePreserving shift μ μ)
    {m : ℕ} (fs : Fin m → α → ℝ)
    (hfs_meas : ∀ i, Measurable (fs i))
    (hfs_bd : ∀ i, ∃ C, ∀ x, |fs i x| ≤ C) :
    Tendsto (fun n =>
      ∫ ω, |∏ i : Fin m, blockAvg m (n + 1) i (fs i) ω -
           ∏ i : Fin m, μ[(fun ω => fs i (ω 0)) | mSI] ω| ∂μ)
      atTop (𝓝 0) := by
  -- Proof strategy:
  --
  -- 1. Apply prod_diff_bound pointwise:
  --    |∏ blockAvg_i - ∏ CE_i| ≤ m * C^{m-1} * max_i |blockAvg_i - CE_i|
  --
  -- 2. Integrate both sides:
  --    ∫ |∏ blockAvg_i - ∏ CE_i| ≤ m * C^{m-1} * ∫ max_i |blockAvg_i - CE_i|
  --
  -- 3. Use ∫ max_i |·| ≤ ∑_i ∫ |·| (or domination by sum):
  --    ≤ m * C^{m-1} * ∑_i ∫ |blockAvg_i - CE_i|
  --
  -- 4. By blockAvg_tendsto_condExp, each term → 0:
  --    ∫ |blockAvg_i - CE_i| → 0 for each i
  --
  -- 5. Finite sum of things → 0 is → 0.
  --
  -- TODO: Formalize using prod_diff_bound and blockAvg_tendsto_condExp
  sorry

end ProductConvergence

/-! ### Kernel Independence from Contractability

The main result: for contractable measures, the product factorization of conditional expectations
holds almost surely, giving kernel independence. -/

section KernelIndependence

variable {μ : Measure (Ω[α])} [IsProbabilityMeasure μ] [StandardBorelSpace α]

/-- For contractable measures, product of CEs equals CE of product.

`CE[∏ fᵢ(ωᵢ) | mSI] = ∏ CE[fᵢ(ω₀) | mSI]` a.e.

This is the key factorization that yields conditional i.i.d. -/
theorem condexp_product_factorization_contractable
    (hσ : MeasurePreserving shift μ μ)
    (hContract : ∀ (m : ℕ) (k : Fin m → ℕ), StrictMono k →
        Measure.map (fun ω i => ω (k i)) μ = Measure.map (fun ω (i : Fin m) => ω i.val) μ)
    {m : ℕ} (fs : Fin m → α → ℝ)
    (hfs_meas : ∀ i, Measurable (fs i))
    (hfs_bd : ∀ i, ∃ C, ∀ x, |fs i x| ≤ C) :
    μ[(fun ω => ∏ i : Fin m, fs i (ω i.val)) | mSI] =ᵐ[μ]
    (fun ω => ∏ i : Fin m, μ[(fun ω' => fs i (ω' 0)) | mSI] ω) := by
  -- Proof strategy:
  --
  -- **Step 1**: By integral_prod_eq_integral_blockAvg (using contractability):
  --   For all n > 0: ∫ ∏ fᵢ(ωᵢ) dμ = ∫ ∏ blockAvg_i dμ
  --
  -- **Step 2**: By product_blockAvg_L1_convergence:
  --   ∫ |∏ blockAvg_i - ∏ CE[fᵢ(ω₀)]| → 0 as n → ∞
  --
  -- **Step 3**: L¹ convergence implies convergence of integrals:
  --   Since ∫ ∏ blockAvg_i is constant = ∫ ∏ fᵢ(ωᵢ) (by Step 1),
  --   and ∫ |∏ blockAvg_i - ∏ CE| → 0 (by Step 2),
  --   we have ∫ ∏ fᵢ(ωᵢ) = ∫ ∏ CE[fᵢ(ω₀)]
  --
  -- **Step 4**: Restrict to shift-invariant sets s ∈ mSI:
  --   The same argument applies when integrating over any s ∈ mSI,
  --   because reindexing by strictly monotone functions preserves
  --   shift-invariant sets: if s ∈ mSI, then (reindex ρ)⁻¹(s) = s.
  --
  --   This gives: ∫_s ∏ fᵢ(ωᵢ) = ∫_s ∏ CE[fᵢ(ω₀)] for all s ∈ mSI
  --
  -- **Step 5**: By uniqueness of conditional expectation:
  --   CE[∏ fᵢ(ωᵢ) | mSI] =ᵐ ∏ CE[fᵢ(ω₀) | mSI]
  --
  -- TODO: Formalize using integral_prod_eq_integral_blockAvg,
  -- product_blockAvg_L1_convergence, and ae_eq_condExp_of_forall_setIntegral_eq
  sorry

end KernelIndependence

end Exchangeability.DeFinetti.ViaKoopman
