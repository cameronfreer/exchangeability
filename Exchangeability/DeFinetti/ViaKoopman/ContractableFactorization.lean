/-
Copyright (c) 2025 The Exchangeability Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Exchangeability.DeFinetti.ViaKoopman.BlockInjection
import Exchangeability.DeFinetti.ViaKoopman.CesaroConvergence
import Exchangeability.Contractability
import Exchangeability.DeFinetti.ViaL2.MoreL2Helpers

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

/-- Block averages of bounded functions are bounded.

If |f x| ≤ C for all x, then |blockAvg m n k f ω| ≤ C for all ω.
This follows because blockAvg is a convex combination of values of f. -/
lemma blockAvg_abs_le {m n : ℕ} (k : Fin m) {f : α → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hf_bd : ∀ x, |f x| ≤ C) (ω : Ω[α]) :
    |blockAvg m n k f ω| ≤ C := by
  unfold blockAvg
  by_cases hn : n = 0
  · simp only [hn, ↓reduceDIte, abs_zero]
    exact hC
  · simp only [hn, ↓reduceDIte]
    have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
    -- |blockAvg| = |(1/n) * ∑ f(ω(k*n + j))| ≤ (1/n) * ∑ |f(ω(k*n + j))| ≤ (1/n) * n * C = C
    calc |1 / (n : ℝ) * ∑ j ∈ Finset.range n, f (ω (k.val * n + j))|
      _ = |1 / (n : ℝ)| * |∑ j ∈ Finset.range n, f (ω (k.val * n + j))| := abs_mul _ _
      _ ≤ |1 / (n : ℝ)| * ∑ j ∈ Finset.range n, |f (ω (k.val * n + j))| := by
          apply mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (abs_nonneg _)
      _ ≤ (1 / (n : ℝ)) * ∑ j ∈ Finset.range n, C := by
          rw [abs_of_pos (by positivity : (1 : ℝ) / n > 0)]
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply Finset.sum_le_sum
          intro j _
          exact hf_bd _
      _ = (1 / (n : ℝ)) * (n * C) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ = C := by field_simp

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

  -- Define the standard Cesàro average and conditional expectation target
  let A := fun n : ℕ => fun ω : Ω[α] =>
    (1 / ((n + 1) : ℝ)) * (Finset.range (n + 1)).sum (fun j => f (ω j))
  let Y := fun ω : Ω[α] => μ[(fun ω' => f (ω' 0)) | mSI] ω

  -- The offset depends on n: offset_n = k.val * (n + 1)
  let offset := fun n : ℕ => k.val * (n + 1)

  -- Key fact 1: blockAvg = A ∘ shift^[offset]
  have h_blockAvg_eq : ∀ n, ∀ ω, blockAvg m (n + 1) k f ω = A n (shift^[offset n] ω) := by
    intro n ω
    -- blockAvg m (n+1) k f ω = (1/(n+1)) * ∑_{j ∈ range(n+1)} f(ω(k.val*(n+1) + j))
    --                       = (1/(n+1)) * ∑_{j ∈ range(n+1)} f((shift^[k.val*(n+1)] ω) j)
    --                       = A n (shift^[offset n] ω)
    -- Use blockAvg_eq_cesaro_shifted which establishes this connection
    rw [blockAvg_eq_cesaro_shifted (Nat.succ_pos n)]
    -- Align coercions: ↑n.succ = ↑n + 1 as reals, and n.succ = n + 1 as naturals
    simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one]
    -- Now definitionally equal since offset n = k.val * (n + 1)
    rfl

  -- Key fact 2: Y is shift-invariant (CE w.r.t. mSI is constant on shift orbits)
  have hf_int : Integrable (fun ω : Ω[α] => f (ω 0)) μ := by
    obtain ⟨C, hC⟩ := hf_bd
    exact integrable_of_bounded_measurable (hf.comp (measurable_pi_apply 0)) C (fun ω => hC (ω 0))

  have h_Y_shift_inv : ∀ p : ℕ, (fun ω => Y (shift^[p] ω)) =ᵐ[μ] Y := by
    intro p
    -- CE[f(ω₀) | mSI] is mSI-measurable, and for mSI-measurable functions,
    -- f ∘ shift^[p] = f pointwise (by shiftInvariantSigma_measurable_shift_eq)
    --
    -- Step 1: Y is mSI-measurable
    have hY_meas : Measurable[mSI] Y := stronglyMeasurable_condExp.measurable
    -- Step 2: By induction on p, Y ∘ shift^[p] = Y pointwise
    have h_eq : ∀ p : ℕ, (fun ω => Y (shift^[p] ω)) = Y := by
      intro p
      induction p with
      | zero =>
        -- shift^[0] = id, so (fun ω => Y (id ω)) = Y
        rfl
      | succ p ih =>
        ext ω
        -- shift^[p+1] = shift ∘ shift^[p]
        simp only [Function.iterate_succ', Function.comp_apply]
        -- Y (shift (shift^[p] ω)) = Y ω
        -- First use ih: Y (shift^[p] ω') = Y ω' for all ω'
        -- So we need: Y (shift (shift^[p] ω)) = Y (shift^[p] ω) = Y ω
        have h := shiftInvariantSigma_measurable_shift_eq Y hY_meas
        -- h : (fun ω => Y (shift ω)) = Y
        -- So Y (shift ω') = Y ω' for all ω'
        calc Y (shift (shift^[p] ω))
          _ = Y (shift^[p] ω) := congrFun h (shift^[p] ω)
          _ = Y ω := congrFun ih ω
    -- Step 3: Pointwise equality implies a.e. equality
    exact EventuallyEq.of_eq (h_eq p)

  -- Reduce to standard Cesàro convergence via measure-preserving substitution
  have h_eq : ∀ n, ∫ ω, |blockAvg m (n + 1) k f ω - Y ω| ∂μ = ∫ ω, |A n ω - Y ω| ∂μ := by
    intro n
    -- Step 1: Substitute blockAvg = A ∘ shift^[offset]
    have h1 : ∫ ω, |blockAvg m (n + 1) k f ω - Y ω| ∂μ =
              ∫ ω, |A n (shift^[offset n] ω) - Y ω| ∂μ := by
      congr 1; ext ω; rw [h_blockAvg_eq]
    -- Step 2: Use Y shift-invariance: Y ω = Y (shift^[offset n] ω) a.e.
    have h2 : ∫ ω, |A n (shift^[offset n] ω) - Y ω| ∂μ =
              ∫ ω, |A n (shift^[offset n] ω) - Y (shift^[offset n] ω)| ∂μ := by
      apply integral_congr_ae
      filter_upwards [h_Y_shift_inv (offset n)] with ω hω
      rw [hω]
    -- Step 3: Apply measure-preserving substitution
    have h_pres := hσ.iterate (offset n)
    have h3 : ∫ ω, |A n (shift^[offset n] ω) - Y (shift^[offset n] ω)| ∂μ =
              ∫ ω, |A n ω - Y ω| ∂μ := by
      -- Use integral substitution under measure-preserving map
      -- ∫ F(T ω) dμ = ∫ F dμ when T is measure-preserving
      --
      -- Define F := fun ω => |A n ω - Y ω|
      -- Then LHS = ∫ (F ∘ shift^[offset n]) dμ = ∫ F d(μ.map shift^[offset n]) = ∫ F dμ
      -- The last step uses h_pres.map_eq : μ.map shift^[offset n] = μ
      --
      -- Strategy from CesaroConvergence.lean:
      -- 1. Use integral_map_of_stronglyMeasurable to relate ∫ F dν and ∫ (F ∘ T) dμ
      -- 2. Use h_pres.map_eq to get ν = μ
      have h_smeas : StronglyMeasurable (fun ω : Ω[α] => |A n ω - Y ω|) := by
        -- A n is measurable (Cesàro average = const * finite sum of measurable functions)
        have hA_meas : Measurable (A n) := by
          simp only [A]
          apply Measurable.const_mul
          apply Finset.measurable_sum
          intro j _
          exact hf.comp (measurable_pi_apply j)
        -- Y is the conditional expectation, which is mSI-strongly measurable
        -- Use the same pattern as line 179 in this file
        have hY_meas_mSI : Measurable[mSI] Y := stronglyMeasurable_condExp.measurable
        -- Convert mSI-measurable to full measurable via shiftInvariantSigma_le
        have hY_meas : Measurable Y :=
          hY_meas_mSI.mono (shiftInvariantSigma_le (α := α)) le_rfl
        -- The difference is measurable
        have hDiff_meas : Measurable (fun ω => A n ω - Y ω) := hA_meas.sub hY_meas
        -- The absolute value of a measurable real function is measurable
        -- Use continuous_abs.measurable.comp pattern
        have hAbs_meas : Measurable (fun ω => |A n ω - Y ω|) :=
          continuous_abs.measurable.comp hDiff_meas
        -- Convert Measurable to StronglyMeasurable (for real-valued functions on standard Borel)
        exact hAbs_meas.stronglyMeasurable
      -- Rewrite using integral_map_of_stronglyMeasurable
      rw [← integral_map_of_stronglyMeasurable h_pres.measurable h_smeas, h_pres.map_eq]
    rw [h1, h2, h3]

  -- Apply L1_cesaro_convergence_bounded
  rw [show (fun n => ∫ ω, |blockAvg m (n + 1) k f ω - Y ω| ∂μ) =
          (fun n => ∫ ω, |A n ω - Y ω| ∂μ) from funext h_eq]
  exact L1_cesaro_convergence_bounded hσ f hf hf_bd

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

  -- Step 2: Key algebraic identity - product of block averages equals averaged sum
  -- Using Fintype.prod_sum: ∏ i, ∑ k, f i k = ∑ φ, ∏ i, f i (φ i)
  --
  -- The identity is:
  -- ∏ i, blockAvg m n i (fs i) ω = (1/n)^m * ∑_{j : Fin m → Fin n} ∏ i, fs i (ω(i*n + j(i)))
  --
  -- Proof:
  -- 1. blockAvg m n i (fs i) ω = (1/n) * ∑_{k=0}^{n-1} fs i (ω(i*n + k))
  -- 2. ∏ i, (1/n) * ∑_k f_i(k) = ∏ i, ∑_k (1/n) * f_i(k)  (pull scalar into sum)
  -- 3. ∏ i, ∑_k g_i(k) = ∑_φ ∏ i, g_i(φ(i))  (Fintype.prod_sum)
  -- 4. ∑_φ ∏ i, (1/n) * f_i(φ(i)) = ∑_φ (1/n)^m * ∏ i, f_i(φ(i))  (factor out)
  -- 5. = (1/n)^m * ∑_φ ∏ i, f_i(φ(i))

  -- Step 3: LHS is constant in j, so equals average over all j
  -- Since h_each_j says LHS = RHS(j) for each j, and LHS doesn't depend on j:
  --   n^m * LHS = ∑_j LHS = ∑_j RHS(j)
  have h_card : Fintype.card (Fin m → Fin n) = n^m := by simp [Fintype.card_fun, Fintype.card_fin]

  -- Case n = 0: vacuously true (no choice functions exist)
  -- Case m = 0: both sides are ∫ 1 dμ = 1

  -- The averaging argument:
  -- LHS = (1/n^m) * ∑_j ∫ ∏ fᵢ(ω(blockInjection)) dμ  (since LHS is constant in j)
  --     = (1/n^m) * ∫ ∑_j ∏ fᵢ(ω(blockInjection)) dμ  (Fubini - finite sum)
  --     = ∫ (1/n^m) * ∑_j ∏ fᵢ(ω(i*n + j(i))) dμ
  --     = ∫ ∏ blockAvg_i dμ  (algebraic identity)

  -- Step 4: The key algebraic identity
  -- For each ω, we need to show:
  --   ∏ i, blockAvg m n i (fs i) ω = (1/n^m) * ∑_{j : Fin m → Fin n} ∏ i, fs i (ω(i*n + j(i)))
  --
  -- This follows from Fintype.prod_sum and the definition of blockAvg:
  --   ∏ i, ((1/n) * ∑_{k ∈ range n} fs i (ω(i*n + k)))
  -- = (1/n)^m * ∏ i, ∑_{k ∈ range n} fs i (ω(i*n + k))
  -- = (1/n)^m * ∑_{φ : Fin m → Fin n} ∏ i, fs i (ω(i*n + φ(i)))  (by Fintype.prod_sum)

  have h_prod_blockAvg_eq : ∀ ω, ∏ i : Fin m, blockAvg m n i (fs i) ω =
      (1 / (n : ℝ)^m) * ∑ j : Fin m → Fin n, ∏ i : Fin m, fs i (ω (i.val * n + (j i).val)) := by
    intro ω
    -- The proof uses Fintype.prod_sum to distribute product over sums:
    --   ∏ i, ∑_k f i k = ∑_φ ∏ i, f i (φ i)
    --
    -- Applied to blockAvg:
    --   ∏ i, (1/n) * ∑_{k=0}^{n-1} fs i (ω(i*n + k))
    -- = (1/n)^m * ∏ i, ∑_{k=0}^{n-1} fs i (ω(i*n + k))
    -- = (1/n)^m * ∑_{φ : Fin m → Fin n} ∏ i, fs i (ω(i*n + φ(i)))

    -- Step 1: Unfold blockAvg using the non-zero block size
    simp_rw [blockAvg_pos_n hn]

    -- Step 2: Pull (1/n) out of each factor
    -- ∏ i, (1/n) * (∑_j ...) = (∏ i, (1/n)) * ∏ i, (∑_j ...)
    --                        = (1/n)^m * ∏ i, (∑_j ...)
    have h_factor : ∏ i : Fin m, (1 / (n : ℝ)) * (Finset.range n).sum (fun j => fs i (ω (i.val * n + j))) =
        (1 / (n : ℝ))^m * ∏ i : Fin m, (Finset.range n).sum (fun j => fs i (ω (i.val * n + j))) := by
      -- Use Finset.prod_mul_distrib: ∏ i, f i * g i = (∏ i, f i) * (∏ i, g i)
      rw [Finset.prod_mul_distrib]
      -- Now: (∏ i, 1/n) * (∏ i, ∑_j ...) = (1/n)^m * (∏ i, ∑_j ...)
      congr 1
      -- (∏ i, 1/n) = (1/n)^m
      rw [Finset.prod_const, Finset.card_fin]

    rw [h_factor]
    -- Goal: (1/n)^m * ∏ i, (∑_{j ∈ range n} ...) = (1/n^m) * ∑_φ ∏ i, ...

    -- Step 3: Convert from Finset.range n to Fin n
    -- ∑ j ∈ Finset.range n, f j = ∑ j : Fin n, f j.val (by Fin.sum_univ_eq_sum_range)
    have h_range_to_fin : ∀ i : Fin m, (Finset.range n).sum (fun j => fs i (ω (i.val * n + j))) =
        ∑ j : Fin n, fs i (ω (i.val * n + j.val)) := by
      intro i
      conv_lhs => rw [← Fin.sum_univ_eq_sum_range (fun j => fs i (ω (i.val * n + j))) n]

    simp_rw [h_range_to_fin]

    -- Step 4: Apply Fintype.prod_sum: ∏ i, ∑ j, f i j = ∑ φ, ∏ i, f i (φ i)
    rw [Fintype.prod_sum]

    -- Goal: (1/n)^m * ∑ φ, ∏ i, f i (φ i) = (1/n^m) * ∑ φ, ∏ i, f i (φ i)
    -- Just need (1/n)^m = 1/(n^m)
    congr 1
    rw [one_div, one_div, inv_pow]

  -- Step 5: Combine h_each_j with h_prod_blockAvg_eq
  -- By h_each_j: ∀ j, ∫ ∏ fs(ωᵢ) = ∫ ∏ fs(ω(i*n + j(i)))
  -- Sum over j: n^m * ∫ ∏ fs(ωᵢ) = ∑_j ∫ ∏ fs(ω(i*n + j(i)))
  -- By Fubini: = ∫ ∑_j ∏ fs(ω(i*n + j(i)))
  -- By h_prod_blockAvg_eq: = ∫ n^m * ∏ blockAvg
  -- Divide by n^m: ∫ ∏ fs(ωᵢ) = ∫ ∏ blockAvg

  -- RHS: ∫ ∏ blockAvg = ∫ (1/n^m) * ∑_j ∏ fs(ω(i*n + j(i))) (by h_prod_blockAvg_eq)
  simp_rw [h_prod_blockAvg_eq]

  -- ∫ (1/n^m) * ∑_j ... = (1/n^m) * ∫ ∑_j ...
  rw [integral_mul_left]

  -- ∫ ∑_j ... = ∑_j ∫ ... (Fubini for finite sum)
  rw [integral_finset_sum]
  · -- Goal: ∫ ∏ fs(ωᵢ) = (1/n^m) * ∑_j ∫ ∏ fs(ω(i*n + j(i)))
    --
    -- By h_each_j: each ∫ ∏ fs(ω(i*n + j(i))) = ∫ ∏ fs(ωᵢ)
    -- (using blockInjection_val_lt: blockInjection m n j i.val = i*n + j(i))
    -- So: ∑_j ∫ ∏ fs(ω(i*n + j(i))) = n^m * ∫ ∏ fs(ωᵢ)
    -- Thus: (1/n^m) * n^m * ∫ ∏ fs(ωᵢ) = ∫ ∏ fs(ωᵢ)

    have h_each_term : ∀ j : Fin m → Fin n,
        ∫ ω, ∏ i : Fin m, fs i (ω (i.val * n + (j i).val)) ∂μ =
        ∫ ω, ∏ i : Fin m, fs i (ω i.val) ∂μ := by
      intro j
      -- Use h_each_j and blockInjection_val_lt
      rw [h_each_j j]
      -- The integrands match because blockInjection m n j i.val = i.val * n + (j i).val
      congr 1
      ext ω
      apply Finset.prod_congr rfl
      intro i _
      rw [blockInjection_val_lt]

    rw [Finset.sum_congr rfl (fun j _ => h_each_term j)]
    rw [Finset.sum_const, Finset.card_univ, h_card, nsmul_eq_mul]

    -- Goal: ∫ ∏ fs(ωᵢ) = (1/n^m) * (n^m * ∫ ∏ fs(ωᵢ))
    have hn_ne_zero : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    have hn_pow_ne_zero : (n : ℝ)^m ≠ 0 := pow_ne_zero m hn_ne_zero
    rw [Nat.cast_pow]
    field_simp

  -- Integrability: bounded measurable functions on prob space are integrable
  intro j _
  -- Get bound constants for each fs
  choose Cs hCs using hfs_bd
  -- Define the integrand for clarity
  let F : Ω[α] → ℝ := fun a => ∏ i : Fin m, fs i (a (i.val * n + (j i).val))
  -- Measurability: product of measurable functions is measurable
  have h_meas : Measurable F :=
    Finset.measurable_prod _ (fun i _ => (hfs_meas i).comp (measurable_pi_apply _))
  -- Apply Integrable.of_bound
  refine Integrable.of_bound h_meas.aestronglyMeasurable (∏ i : Fin m, |Cs i|) ?_
  filter_upwards with a
  rw [Real.norm_eq_abs]
  -- Bound: |∏ fs i (...)| = ∏ |fs i (...)| ≤ ∏ |Cs i|
  show |F a| ≤ _
  simp only [F]
  rw [Finset.abs_prod]
  apply Finset.prod_le_prod
  · intro i _; exact abs_nonneg _
  · intro i _; exact le_trans (hCs i _) (le_abs_self _)

end Contractability

/-! ### Product L¹ Convergence via Telescoping -/

section ProductConvergence

variable {μ : Measure (Ω[α])} [IsProbabilityMeasure μ] [StandardBorelSpace α]

/-- Telescoping bound for product differences with general bound C.

Extends `abs_prod_sub_prod_le` (which requires bound 1) to general bounds via normalization.
For functions bounded by C > 0:
  |∏ A - ∏ B| ≤ C^{m-1} * ∑ |A_i - B_i|

This is derived from abs_prod_sub_prod_le by dividing by C. -/
lemma abs_prod_sub_prod_le_general {m : ℕ} (A B : Fin m → ℝ) {C : ℝ} (hC : 0 < C)
    (hA : ∀ i, |A i| ≤ C) (hB : ∀ i, |B i| ≤ C) :
    |∏ i, A i - ∏ i, B i| ≤ C^(m - 1) * ∑ i, |A i - B i| := by
  by_cases hm : m = 0
  · subst hm
    simp only [Finset.univ_eq_empty, Finset.prod_empty, Finset.sum_empty,
      sub_self, abs_zero, mul_zero, le_refl]
  -- m > 0: normalize by C and apply abs_prod_sub_prod_le
  have hm_pos : 0 < m := Nat.pos_of_ne_zero hm
  -- Define normalized functions
  let A' : Fin m → ℝ := fun i => A i / C
  let B' : Fin m → ℝ := fun i => B i / C
  -- Show normalized functions are bounded by 1
  have hA' : ∀ i, |A' i| ≤ 1 := fun i => by
    simp only [A', abs_div, abs_of_pos hC]
    exact div_le_one_of_le₀ (hA i) (le_of_lt hC)
  have hB' : ∀ i, |B' i| ≤ 1 := fun i => by
    simp only [B', abs_div, abs_of_pos hC]
    exact div_le_one_of_le₀ (hB i) (le_of_lt hC)
  -- Apply abs_prod_sub_prod_le to normalized functions
  have h_norm := Exchangeability.DeFinetti.ViaL2.abs_prod_sub_prod_le A' B' hA' hB'
  -- Relate normalized products to original products
  have h_prod_A : ∏ i, A' i = (∏ i, A i) / C^m := by
    simp only [A', Finset.prod_div_distrib, Finset.prod_const, Finset.card_fin]
  have h_prod_B : ∏ i, B' i = (∏ i, B i) / C^m := by
    simp only [B', Finset.prod_div_distrib, Finset.prod_const, Finset.card_fin]
  have h_sum : ∑ i, |A' i - B' i| = (∑ i, |A i - B i|) / C := by
    simp only [A', B']
    -- Transform each term: |A x / C - B x / C| = |A x - B x| / C
    have h_term : ∀ x, |A x / C - B x / C| = |A x - B x| / C := fun x => by
      have : A x / C - B x / C = (A x - B x) / C := by field_simp
      rw [this, abs_div, abs_of_pos hC]
    simp only [h_term]
    -- Now apply Finset.sum_div
    rw [Finset.sum_div]
  -- Main calculation
  have hCm_pos : 0 < C^m := pow_pos hC m
  calc |∏ i, A i - ∏ i, B i|
    _ = |C^m * (∏ i, A' i) - C^m * (∏ i, B' i)| := by
        rw [h_prod_A, h_prod_B]
        simp only [mul_div_cancel₀ _ (ne_of_gt hCm_pos)]
    _ = |C^m * ((∏ i, A' i) - (∏ i, B' i))| := by ring_nf
    _ = C^m * |∏ i, A' i - ∏ i, B' i| := by
        rw [abs_mul, abs_of_pos hCm_pos]
    _ ≤ C^m * ∑ i, |A' i - B' i| := by
        apply mul_le_mul_of_nonneg_left h_norm (le_of_lt hCm_pos)
    _ = C^m * ((∑ i, |A i - B i|) / C) := by rw [h_sum]
    _ = C^(m - 1) * ∑ i, |A i - B i| := by
        cases m with
        | zero => simp at hm
        | succ n =>
          simp only [Nat.succ_sub_one]
          field_simp
          ring

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
    -- Case C = 0: All |A i|, |B i| ≤ 0, so A = B = 0, so LHS = 0
    by_cases hC' : C = 0
    · have hA0 : ∀ i, A i = 0 := fun i => abs_eq_zero.mp (le_antisymm (hC' ▸ hA i) (abs_nonneg _))
      have hB0 : ∀ i, B i = 0 := fun i => abs_eq_zero.mp (le_antisymm (hC' ▸ hB i) (abs_nonneg _))
      -- Both products are 0, so LHS = |0 - 0| = 0 ≤ RHS
      simp only [hA0, hB0, sub_self, abs_zero, Finset.prod_const, Finset.card_fin, zero_pow hm.ne']
      -- Goal: 0 ≤ m * C^(m-1) * sup'(...)(fun _ => 0)
      -- The sup' of the constant function 0 is 0
      have h_sup_zero : Finset.univ.sup' ⟨⟨0, hm⟩, Finset.mem_univ _⟩ (fun _ : Fin m => (0 : ℝ)) = 0 := by
        apply le_antisymm
        · apply Finset.sup'_le
          intro i _
          exact le_refl 0
        · exact Finset.le_sup'_of_le (fun _ => (0 : ℝ)) (Finset.mem_univ ⟨0, hm⟩) (le_refl 0)
      simp only [h_sup_zero, mul_zero, le_refl]
    -- Case C > 0: Use abs_prod_sub_prod_le_general
    have hC_pos : 0 < C := lt_of_le_of_ne hC (Ne.symm hC')
    have h_gen := abs_prod_sub_prod_le_general A B hC_pos hA hB
    -- Now bound sum by m * max
    have h_sum_le_m_max : ∑ i : Fin m, |A i - B i| ≤
        m * Finset.univ.sup' ⟨⟨0, hm⟩, Finset.mem_univ _⟩ (fun i => |A i - B i|) := by
      calc ∑ i : Fin m, |A i - B i|
        _ ≤ ∑ _i : Fin m, Finset.univ.sup' ⟨⟨0, hm⟩, Finset.mem_univ _⟩ (fun i => |A i - B i|) := by
            apply Finset.sum_le_sum
            intro i hi
            exact Finset.le_sup' (fun i => |A i - B i|) hi
        _ = Finset.card (Finset.univ : Finset (Fin m)) •
              Finset.univ.sup' ⟨⟨0, hm⟩, Finset.mem_univ _⟩ (fun i => |A i - B i|) := by
            rw [Finset.sum_const]
        _ = (m : ℝ) * Finset.univ.sup' ⟨⟨0, hm⟩, Finset.mem_univ _⟩ (fun i => |A i - B i|) := by
            rw [Finset.card_fin, nsmul_eq_mul]
    calc |∏ i, A i - ∏ i, B i|
      _ ≤ C^(m - 1) * ∑ i, |A i - B i| := h_gen
      _ ≤ C^(m - 1) * ((m : ℝ) * Finset.univ.sup' ⟨⟨0, hm⟩, Finset.mem_univ _⟩ (fun i => |A i - B i|)) := by
          apply mul_le_mul_of_nonneg_left h_sum_le_m_max
          exact pow_nonneg hC _
      _ = ↑m * C^(m - 1) * Finset.univ.sup' ⟨⟨0, hm⟩, Finset.mem_univ _⟩ (fun i => |A i - B i|) := by ring
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
  -- **Proof Strategy using abs_prod_sub_prod_le and blockAvg_tendsto_condExp**
  --
  -- Case m = 0: Both products are 1, so the difference is 0 and ∫ 0 dμ = 0 → 0.
  --
  -- Case m > 0: Use the telescoping bound from abs_prod_sub_prod_le.
  --
  -- **Step 1**: Get uniform bound C for all fs i.
  --   Using hfs_bd : ∀ i, ∃ C_i, ∀ x, |fs i x| ≤ C_i
  --   Define C := max_i C_i + 1, so |fs i x| ≤ C for all i, x.
  --
  -- **Step 2**: Show that block averages and CEs are bounded by C.
  --   - Block average is a convex combination, so inherits the bound.
  --   - CE of bounded function is bounded (by ae_bdd_condExp_of_ae_bdd).
  --
  -- **Step 3**: Use abs_prod_sub_prod_le with normalization.
  --   Define f'_i := blockAvg / C and g'_i := CE / C, so |f'|, |g'| ≤ 1.
  --   By abs_prod_sub_prod_le: |∏ f'_i - ∏ g'_i| ≤ ∑ |f'_i - g'_i|.
  --   Rescaling: |∏ blockAvg - ∏ CE| ≤ C^{m-1} ∑ |blockAvg_i - CE_i|.
  --
  -- **Step 4**: Integrate and use Fubini.
  --   ∫ |∏ blockAvg - ∏ CE| ≤ C^{m-1} ∑_i ∫ |blockAvg_i - CE_i|.
  --
  -- **Step 5**: Apply blockAvg_tendsto_condExp for each i.
  --   Each term ∫ |blockAvg_i - CE_i| → 0 by blockAvg_tendsto_condExp.
  --   Finite sum of things → 0 is → 0 (by tendsto_finset_sum).
  --
  -- **Key ingredients from MoreL2Helpers.lean**:
  --   - abs_prod_sub_prod_le (line 4624): |∏ f - ∏ g| ≤ ∑ |f_i - g_i| for |f|, |g| ≤ 1
  --   - prod_tendsto_L1_of_L1_tendsto (line 4670): Alternative direct approach

  -- Handle m = 0 case first
  by_cases hm : m = 0
  · subst hm
    simp only [Finset.univ_eq_empty, Finset.prod_empty, sub_self, abs_zero, integral_zero]
    exact tendsto_const_nhds
  -- m > 0 case
  have hm_pos : 0 < m := Nat.pos_of_ne_zero hm

  -- Step 1: Get uniform bound C > 0 for all fs i
  have hC_exists : ∃ C > 0, ∀ i, ∀ x, |fs i x| ≤ C := by
    choose Cs hCs using hfs_bd
    -- Use max of bounds + 1 to ensure positivity
    use (Finset.univ.sup' ⟨⟨0, hm_pos⟩, Finset.mem_univ _⟩ (fun i => |Cs i|)) + 1
    constructor
    · -- maxC > 0 since we add 1
      exact add_pos_of_nonneg_of_pos (Finset.le_sup'_of_le _ (Finset.mem_univ ⟨0, hm_pos⟩)
        (abs_nonneg _)) one_pos
    intro i x
    have h1 : |fs i x| ≤ Cs i := hCs i x
    have h2 : Cs i ≤ |Cs i| := le_abs_self _
    have h3 : |Cs i| ≤ Finset.univ.sup' ⟨⟨0, hm_pos⟩, Finset.mem_univ _⟩ (fun i => |Cs i|) :=
      Finset.le_sup' (fun i => |Cs i|) (Finset.mem_univ i)
    linarith
  obtain ⟨C, hC_pos, hC_bd⟩ := hC_exists

  -- Step 2: Upper bound using telescoping
  -- Define the upper bound sequence
  let upper := fun n => C^(m - 1) * ∑ i : Fin m,
    ∫ ω, |blockAvg m (n + 1) i (fs i) ω - μ[(fun ω => fs i (ω 0)) | mSI] ω| ∂μ

  -- Show the upper bound tends to 0
  have h_upper_tendsto : Tendsto upper atTop (𝓝 0) := by
    simp only [upper]
    rw [← mul_zero (C^(m - 1))]
    apply Tendsto.const_mul
    -- Sum of limits = limit of sums
    have h_sum_zero : (∑ _ : Fin m, (0 : ℝ)) = 0 := Finset.sum_const_zero
    rw [← h_sum_zero]
    apply tendsto_finset_sum
    intro i _
    exact blockAvg_tendsto_condExp hσ m i (hfs_meas i) ⟨C, fun x => hC_bd i x⟩

  -- Apply squeeze theorem
  apply squeeze_zero
  · intro n
    exact integral_nonneg (fun _ => abs_nonneg _)
  · intro n
    -- Need: ∫ |∏ blockAvg - ∏ CE| ≤ upper n = C^{m-1} * ∑_i ∫ |blockAvg_i - CE_i|
    --
    -- **Key steps (all use standard measure theory):**
    --
    -- 1. Block averages are bounded by C:
    --    |blockAvg m n k f ω| ≤ C by blockAvg_abs_le
    --
    -- 2. Conditional expectations are bounded by C (a.e.):
    --    |μ[f | mSI]| ≤ μ[|f| | mSI] ≤ C a.e. (by condexp monotonicity)
    --
    -- 3. Pointwise bound (a.e.) using abs_prod_sub_prod_le_general:
    --    |∏ blockAvg - ∏ CE| ≤ C^{m-1} * ∑ |blockAvg_i - CE_i|
    --
    -- 4. Integrate both sides using integral_mono_ae:
    --    ∫ |∏ blockAvg - ∏ CE| ≤ ∫ C^{m-1} * ∑ |blockAvg_i - CE_i|
    --                          = C^{m-1} * ∫ ∑ |blockAvg_i - CE_i|
    --                          = C^{m-1} * ∑_i ∫ |blockAvg_i - CE_i|  (Fubini)
    --                          = upper n
    --
    -- The integrability conditions follow from:
    -- - Bounded measurable functions on probability spaces are integrable
    -- - Products and sums of integrable functions are integrable
    -- - condexp preserves integrability
    --
    -- Technical lemmas needed from mathlib:
    -- - MeasureTheory.abs_condexp_le: |μ[f | m]| ≤ μ[|f| | m] a.e.
    -- - MeasureTheory.condexp_mono: f ≤ g a.e. → μ[f | m] ≤ μ[g | m] a.e.
    -- - Integrability of products/sums of bounded functions

    -- Let A_i = blockAvg and B_i = condexp
    let A : Fin m → Ω[α] → ℝ := fun i ω => blockAvg m (n + 1) i (fs i) ω
    let B : Fin m → Ω[α] → ℝ := fun i ω => μ[(fun ω' => fs i (ω' 0)) | mSI] ω

    -- Bound on block averages (everywhere)
    have hA_bd : ∀ i ω, |A i ω| ≤ C := by
      intro i ω
      exact blockAvg_abs_le i (le_of_lt hC_pos) (fun x => hC_bd i x) ω

    -- Bound on conditional expectations (a.e.)
    -- Uses ae_bdd_condExp_of_ae_bdd: bounded f implies bounded condexp
    have hB_bd : ∀ᵐ ω ∂μ, ∀ i, |B i ω| ≤ C := by
      rw [ae_all_iff]
      intro i
      -- Create NNReal version of C for ae_bdd_condExp_of_ae_bdd
      let R : NNReal := Real.toNNReal C
      have hR_eq : (R : ℝ) = C := Real.coe_toNNReal C (le_of_lt hC_pos)
      -- The function fs i ∘ (· 0) is bounded by C pointwise
      have h_fs_bdd : ∀ᵐ ω' ∂μ, |fs i (ω' 0)| ≤ (R : ℝ) := by
        rw [hR_eq]
        exact Eventually.of_forall (fun ω' => hC_bd i _)
      -- Apply ae_bdd_condExp_of_ae_bdd with explicit type annotations
      have h_condexp_bd : ∀ᵐ ω ∂μ, |(μ[(fun ω' => fs i (ω' 0)) | mSI]) ω| ≤ (R : ℝ) :=
        ae_bdd_condExp_of_ae_bdd h_fs_bdd
      simp only [hR_eq] at h_condexp_bd
      exact h_condexp_bd

    -- Pointwise bound a.e. using abs_prod_sub_prod_le_general
    have h_pointwise : ∀ᵐ ω ∂μ, |∏ i, A i ω - ∏ i, B i ω| ≤
        C^(m - 1) * ∑ i, |A i ω - B i ω| := by
      filter_upwards [hB_bd] with ω hBω
      exact abs_prod_sub_prod_le_general (fun i => A i ω) (fun i => B i ω)
        hC_pos (fun i => hA_bd i ω) hBω

    -- Integrability helpers
    have hA_int : ∀ i, Integrable (A i) μ := fun i =>
      Integrable.of_bound (measurable_blockAvg i (hfs_meas i)).aestronglyMeasurable C
        (by filter_upwards with ω; rw [Real.norm_eq_abs]; exact hA_bd i ω)

    have hB_int : ∀ i, Integrable (B i) μ := fun _ => integrable_condExp

    have hAB_diff_int : ∀ i, Integrable (fun ω => A i ω - B i ω) μ := fun i =>
      Integrable.sub (hA_int i) (hB_int i)

    -- Product of A is integrable (bounded measurable)
    -- Bound: |∏ A i| ≤ ∏ |A i| ≤ C^m
    have hprodA_int : Integrable (fun ω => ∏ i, A i ω) μ := by
      have h_meas : AEStronglyMeasurable (fun ω => ∏ i : Fin m, A i ω) μ :=
        Finset.aestronglyMeasurable_fun_prod (μ := μ) Finset.univ
          (fun i _ => (measurable_blockAvg i (hfs_meas i)).aestronglyMeasurable)
      apply Integrable.of_bound h_meas (C^m)
      filter_upwards with ω
      rw [Real.norm_eq_abs, Finset.abs_prod]
      calc ∏ i : Fin m, |A i ω|
        _ ≤ ∏ _i : Fin m, C := Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => hA_bd i ω)
        _ = C^m := by rw [Finset.prod_const, Finset.card_fin]

    -- Product of B is integrable (bounded condexp)
    have hprodB_int : Integrable (fun ω => ∏ i, B i ω) μ := by
      have h_meas : AEStronglyMeasurable (fun ω => ∏ i : Fin m, B i ω) μ :=
        Finset.aestronglyMeasurable_fun_prod (μ := μ) Finset.univ
          (fun i _ => integrable_condExp.aestronglyMeasurable)
      have h_bd : ∀ᵐ ω ∂μ, ‖∏ i : Fin m, B i ω‖ ≤ C^m := by
        filter_upwards [hB_bd] with ω hBω
        rw [Real.norm_eq_abs, Finset.abs_prod]
        calc ∏ i : Fin m, |B i ω|
          _ ≤ ∏ _i : Fin m, C := Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => hBω i)
          _ = C^m := by rw [Finset.prod_const, Finset.card_fin]
      exact Integrable.of_bound h_meas (C^m) h_bd

    -- Integrate the pointwise bound
    calc ∫ ω, |∏ i, A i ω - ∏ i, B i ω| ∂μ
      _ ≤ ∫ ω, C^(m - 1) * ∑ i, |A i ω - B i ω| ∂μ := by
          apply integral_mono_ae
          · exact (hprodA_int.sub hprodB_int).abs
          · apply Integrable.const_mul
            apply integrable_finset_sum
            intro i _
            exact (hAB_diff_int i).abs
          · exact h_pointwise
      _ = C^(m - 1) * ∫ ω, ∑ i, |A i ω - B i ω| ∂μ := integral_const_mul _ _
      _ = C^(m - 1) * ∑ i, ∫ ω, |A i ω - B i ω| ∂μ := by
          congr 1
          rw [integral_finset_sum]
          intro i _
          exact (hAB_diff_int i).abs
      _ = upper n := rfl
  · exact h_upper_tendsto

end ProductConvergence

/-! ### Path-Space Measure Invariance from Contractability

The key insight (Kallenberg's first proof): finite-dimensional contractability upgrades to
full path-space measure invariance via the π-λ theorem. This avoids the need for
"conditional contractability" or disintegration. -/

section MeasureInvariance

variable {μ : Measure (Ω[α])} [IsProbabilityMeasure μ]

/-- Finite-dimensional contractability upgrades to path-space measure invariance.

Given contractability (finite marginals on `{k(0), ..., k(m-1)}` equal marginals on `{0, ..., m-1}`),
we show that the pushforward under reindexing by any strictly monotone ρ equals the original
measure. This is the π-λ argument: finite marginal equality → full measure equality. -/
lemma measure_map_reindexBlock_eq_of_contractable
    (hContract : ∀ (m : ℕ) (k : Fin m → ℕ), StrictMono k →
        Measure.map (fun ω i => ω (k i)) μ = Measure.map (fun ω (i : Fin m) => ω i.val) μ)
    {m n : ℕ} (hn : 0 < n) (j : Fin m → Fin n) :
    Measure.map (reindexBlock m n j) μ = μ := by
  -- Use measure_eq_of_fin_marginals_eq_prob: two probability measures are equal
  -- if all finite marginals agree
  have hReindex_meas : Measurable (reindexBlock (α := α) m n j) := measurable_reindexBlock m n j

  -- The pushforward is still a probability measure
  haveI : IsProbabilityMeasure (Measure.map (reindexBlock m n j) μ) :=
    Measure.isProbabilityMeasure_map hReindex_meas.aemeasurable

  apply Exchangeability.measure_eq_of_fin_marginals_eq_prob (α := α)

  -- For each N, show finite marginals agree
  intro N S _hS

  -- Compute finite marginals via Measure.map_map
  rw [Measure.map_map (measurable_prefixProj (α := α)) hReindex_meas]

  -- prefixProj N ∘ reindexBlock m n j = fun ω i => ω (blockInjection m n j i.val)
  have h_comp : prefixProj (α := α) N ∘ reindexBlock m n j =
      fun ω (i : Fin N) => ω (blockInjection m n j i.val) := by
    ext ω i
    simp only [Function.comp_apply, prefixProj_apply, reindexBlock_apply]

  rw [h_comp]

  -- The key: use contractability with k := fun i : Fin N => blockInjection m n j i.val
  -- This k is strictly monotone since blockInjection is strictly monotone
  have hk_mono : StrictMono (fun i : Fin N => blockInjection m n j i.val) := by
    intro i₁ i₂ hi
    exact blockInjection_strictMono m n hn j hi

  -- Apply contractability
  have hMarg := hContract N (fun i : Fin N => blockInjection m n j i.val) hk_mono

  -- hMarg says: map (fun ω i => ω (blockInjection m n j i.val)) μ = map (fun ω i => ω i.val) μ
  -- The RHS is exactly map (prefixProj N) μ, so we're done
  calc Measure.map (fun ω (i : Fin N) => ω (blockInjection m n j i.val)) μ S
    _ = Measure.map (fun ω (i : Fin N) => ω i.val) μ S := by rw [hMarg]
    _ = Measure.map (prefixProj (α := α) N) μ S := rfl

/-- Set integral equality from measure invariance and set invariance.

If the measure is invariant under reindexing (μ = μ ∘ reindexBlock⁻¹) and the set is invariant
under reindexing (s = reindexBlock⁻¹(s)), then ∫_s f ∘ reindexBlock = ∫_s f.

This is the key lemma that replaces "conditional contractability". -/
lemma setIntegral_comp_reindexBlock_eq
    (hμ : Measure.map (reindexBlock (α := α) m n j) μ = μ)
    {s : Set (Ω[α])} (hs_meas : MeasurableSet s)
    (hs_inv : reindexBlock m n j ⁻¹' s = s)
    {f : Ω[α] → ℝ} (hf_meas : AEMeasurable f μ) :
    ∫ ω in s, f (reindexBlock m n j ω) ∂μ = ∫ ω in s, f ω ∂μ := by
  -- Key idea:
  -- ∫_s f ∘ T dμ = ∫_{T⁻¹(s)} f ∘ T dμ   (since T⁻¹(s) = s)
  --              = ∫_s f d(μ ∘ T⁻¹)      (change of variables via setIntegral_map_preimage)
  --              = ∫_s f dμ              (since μ ∘ T⁻¹ = μ)

  have hT_meas : Measurable (reindexBlock (α := α) m n j) := measurable_reindexBlock m n j

  -- Use set invariance and apply setIntegral_map_preimage
  calc ∫ ω in s, f (reindexBlock m n j ω) ∂μ
    _ = ∫ ω in reindexBlock m n j ⁻¹' s, f (reindexBlock m n j ω) ∂μ := by rw [hs_inv]
    _ = ∫ ω in s, f ω ∂μ := setIntegral_map_preimage (reindexBlock m n j) hT_meas hμ f s hs_meas hf_meas

end MeasureInvariance

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
  -- We use ae_eq_condExp_of_forall_setIntegral_eq:
  -- If g is mSI-measurable and ∫_s g = ∫_s f for all mSI-sets s,
  -- then g =ᵐ μ[f | mSI].

  -- Handle m = 0 case separately (empty products are both 1)
  by_cases hm : m = 0
  · subst hm
    -- Both products over Fin 0 are empty, hence equal to 1
    simp only [Finset.univ_eq_empty, Finset.prod_empty]
    -- Goal: μ[(fun _ => 1) | mSI] =ᵐ (fun _ => 1)
    -- CE of constant is constant
    have h_const : μ[(fun _ : Ω[α] => (1 : ℝ)) | mSI] = fun _ => 1 :=
      condExp_const (m := shiftInvariantSigma) shiftInvariantSigma_le (1 : ℝ)
    rw [h_const]

  -- m > 0 case: Fin m is nonempty
  have hm_nonempty : Nonempty (Fin m) := ⟨⟨0, Nat.pos_of_ne_zero hm⟩⟩

  -- The target function (product of CEs)
  -- Define as product of functions, which is what Finset.stronglyMeasurable_prod produces
  let g : Ω[α] → ℝ := ∏ i : Fin m, (fun ω => μ[(fun ω' => fs i (ω' 0)) | mSI] ω)

  -- g is mSI-measurable (product of conditional expectations)
  have hg_meas : StronglyMeasurable[mSI] g :=
    Finset.stronglyMeasurable_prod (f := fun i ω => μ[(fun ω' => fs i (ω' 0)) | mSI] ω)
      Finset.univ (fun i _ => stronglyMeasurable_condExp)

  -- Note: g ω = ∏ i, CE_i ω by Finset.prod_apply
  have hg_apply : ∀ ω, g ω = ∏ i : Fin m, μ[(fun ω' => fs i (ω' 0)) | mSI] ω :=
    fun ω => Finset.prod_apply ω Finset.univ (fun i => μ[(fun ω' => fs i (ω' 0)) | mSI])

  -- The source function (product of coordinate evaluations)
  let f : Ω[α] → ℝ := fun ω => ∏ i : Fin m, fs i (ω i.val)

  -- f is integrable (bounded measurable function on probability space)
  have hf_int : Integrable f μ := by
    choose Cs hCs using hfs_bd
    have huniv_nonempty : Finset.univ.Nonempty := Finset.univ_nonempty_iff.mpr hm_nonempty
    let C := (Finset.univ.sup' huniv_nonempty (fun i : Fin m => |Cs i|)) + 1
    have hC_pos : 0 < C := add_pos_of_nonneg_of_pos
      (Finset.le_sup'_of_le _ (Finset.mem_univ ⟨0, Nat.pos_of_ne_zero hm⟩) (abs_nonneg _)) one_pos
    have hC_bd : ∀ i x, |fs i x| ≤ C := by
      intro i x
      have h1 : |fs i x| ≤ Cs i := hCs i x
      have h2 : Cs i ≤ |Cs i| := le_abs_self _
      have h3 : |Cs i| ≤ Finset.univ.sup' huniv_nonempty (fun i : Fin m => |Cs i|) :=
        Finset.le_sup' (fun i => |Cs i|) (Finset.mem_univ i)
      linarith
    have h_meas : Measurable f := Finset.measurable_prod _ (fun i _ =>
      (hfs_meas i).comp (measurable_pi_apply _))
    apply Integrable.of_bound h_meas.aestronglyMeasurable (C^(Fintype.card (Fin m)))
    filter_upwards with ω
    rw [Real.norm_eq_abs, Finset.abs_prod]
    calc ∏ i : Fin m, |fs i (ω i.val)|
      _ ≤ ∏ _i : Fin m, C := Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => hC_bd i _)
      _ = C^(Fintype.card (Fin m)) := by rw [Finset.prod_const, Finset.card_univ]

  -- g is integrable (bounded product of conditional expectations)
  have hg_int : Integrable g μ := by
    choose Cs hCs using hfs_bd
    have huniv_nonempty : Finset.univ.Nonempty := Finset.univ_nonempty_iff.mpr hm_nonempty
    let C := (Finset.univ.sup' huniv_nonempty (fun i : Fin m => |Cs i|)) + 1
    have hC_pos : 0 < C := add_pos_of_nonneg_of_pos
      (Finset.le_sup'_of_le _ (Finset.mem_univ ⟨0, Nat.pos_of_ne_zero hm⟩) (abs_nonneg _)) one_pos
    have hC_bd : ∀ i x, |fs i x| ≤ C := by
      intro i x
      have h1 : |fs i x| ≤ Cs i := hCs i x
      have h2 : Cs i ≤ |Cs i| := le_abs_self _
      have h3 : |Cs i| ≤ Finset.univ.sup' huniv_nonempty (fun i : Fin m => |Cs i|) :=
        Finset.le_sup' (fun i => |Cs i|) (Finset.mem_univ i)
      linarith
    -- Each CE is bounded by C
    have hCE_bd : ∀ᵐ ω ∂μ, ∀ i, |μ[(fun ω' => fs i (ω' 0)) | mSI] ω| ≤ C := by
      rw [ae_all_iff]
      intro i
      let R : NNReal := Real.toNNReal C
      have hR_eq : (R : ℝ) = C := Real.coe_toNNReal C (le_of_lt hC_pos)
      have h_fs_bdd : ∀ᵐ ω' ∂μ, |fs i (ω' 0)| ≤ (R : ℝ) := by
        rw [hR_eq]
        exact Eventually.of_forall (fun ω' => hC_bd i _)
      have h_condexp_bd : ∀ᵐ ω ∂μ, |(μ[(fun ω' => fs i (ω' 0)) | mSI]) ω| ≤ (R : ℝ) :=
        ae_bdd_condExp_of_ae_bdd h_fs_bdd
      simp only [hR_eq] at h_condexp_bd
      exact h_condexp_bd
    -- mSI-measurable implies pi-measurable since mSI ≤ pi
    have h_meas : AEStronglyMeasurable g μ :=
      (hg_meas.mono shiftInvariantSigma_le).aestronglyMeasurable
    apply Integrable.of_bound h_meas (C^(Fintype.card (Fin m)))
    filter_upwards [hCE_bd] with ω hCEω
    rw [Real.norm_eq_abs]
    -- Use hg_apply: g ω = ∏ i, CE_i ω
    rw [hg_apply ω, Finset.abs_prod]
    calc ∏ i : Fin m, |μ[(fun ω' => fs i (ω' 0)) | mSI] ω|
      _ ≤ ∏ _i : Fin m, C := Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => hCEω i)
      _ = C^(Fintype.card (Fin m)) := by rw [Finset.prod_const, Finset.card_univ]

  -- Key step: integrals match on mSI-sets
  -- This follows from:
  -- 1. ∫_s ∏ f = ∫_s ∏ blockAvg for all n (by contractability + block averaging)
  -- 2. ∫_s |∏ blockAvg - ∏ CE| → 0 (by L¹ convergence)
  -- 3. Therefore ∫_s ∏ f = ∫_s ∏ CE = ∫_s g
  have hg_eq : ∀ s : Set (Ω[α]), MeasurableSet[mSI] s → μ s < ⊤ →
      ∫ ω in s, g ω ∂μ = ∫ ω in s, f ω ∂μ := by
    intro s hs _
    -- **Proof strategy:**
    -- Use the L¹ convergence of block averages to g, combined with the
    -- set-restricted integral equality, to establish ∫_s g = ∫_s f.
    --
    -- Key steps:
    -- 1. For each n, ∫_s f = ∫_s (∏ blockAvg_n) (by averaging argument on mSI-sets)
    -- 2. L¹ convergence: ∫ |∏ blockAvg_n - g| → 0
    -- 3. For sets of finite measure, L¹ convergence implies ∫_s (∏ blockAvg_n) → ∫_s g
    -- 4. Since ∫_s f = ∫_s (∏ blockAvg_n) for all n, we have ∫_s f = ∫_s g
    --
    -- The key technical lemma (h_setIntegral_eq_blockAvg) uses:
    -- - reindex_blockInjection_preimage_shiftInvariant for mSI-set invariance
    -- - contractability for the marginal distribution equality
    -- - Fubini averaging argument to get the block average product

    -- Get the shift-invariance property of s
    have hs_inv : isShiftInvariant s := (mem_shiftInvariantSigma_iff (α := α)).mp hs

    -- Define the block average product sequence
    let blockAvgProd : ℕ → Ω[α] → ℝ := fun n ω =>
      ∏ i : Fin m, blockAvg m (n + 1) i (fs i) ω

    -- **Step 1**: For each n, ∫_s f = ∫_s (blockAvgProd n)
    -- This follows from the averaging argument adapted to mSI-sets.
    -- The key is that for mSI-sets, the preimage under block injection reindexing
    -- equals the original set (by reindex_blockInjection_preimage_shiftInvariant).
    have h_setIntegral_eq_blockAvg : ∀ n : ℕ,
        ∫ ω in s, f ω ∂μ = ∫ ω in s, blockAvgProd n ω ∂μ := by
      intro n
      -- The proof follows the same structure as integral_prod_eq_integral_blockAvg,
      -- adapted for set integrals on mSI-sets.
      --
      -- Key insight: For mSI-sets s, the conditional expectation CE[f | mSI] determines
      -- the set integral: ∫_s f = ∫_s CE[f | mSI]. By conditional contractability
      -- (contractability of conditional measures μ_ξ for a.e. ξ in mSI-space),
      -- CE[f | mSI] = CE[f ∘ T_j | mSI] where T_j is reindexing by blockInjection.
      --
      -- The mathematical argument:
      -- 1. For mSI s: T_j⁻¹(s) = s (by reindex_blockInjection_preimage_shiftInvariant)
      -- 2. For mSI-measurable h: h ∘ T_j = h (pointwise, from step 1 for indicators)
      -- 3. For mSI 1_s: 1_s ∘ T_j = 1_s, so ∫_s (f ∘ T_j) = ∫ 1_s · (f ∘ T_j)
      --                = ∫ (1_s ∘ T_j) · (f ∘ T_j) = ∫ (1_s · f) ∘ T_j
      -- 4. By conditional contractability: CE[f | mSI] = CE[f ∘ T_j | mSI] a.e.
      -- 5. Therefore: ∫_s f = ∫_s CE[f | mSI] = ∫_s CE[f ∘ T_j | mSI] = ∫_s (f ∘ T_j)
      --
      -- The full averaging argument then gives ∫_s f = ∫_s blockAvgProd n.

      -- **Proof using π-λ upgraded measure invariance (Kallenberg's first proof)**
      --
      -- The key insight: we don't need "conditional contractability".
      -- Instead, we use:
      -- 1. μ is invariant under reindexBlock (from measure_map_reindexBlock_eq_of_contractable)
      -- 2. s is invariant under reindexBlock (from reindex_blockInjection_preimage_shiftInvariant)
      -- 3. These combine via setIntegral_comp_reindexBlock_eq to give set integral equality

      -- Step 1: For each j : Fin m → Fin (n+1), get the invariance properties
      have hn1_pos : 0 < n + 1 := Nat.succ_pos n

      have h_each_j_setIntegral : ∀ j : Fin m → Fin (n + 1),
          ∫ ω in s, f ω ∂μ = ∫ ω in s, f (reindexBlock m (n + 1) j ω) ∂μ := by
        intro j
        -- Measure invariance from π-λ upgrade
        have hμ_inv : Measure.map (reindexBlock m (n + 1) j) μ = μ :=
          measure_map_reindexBlock_eq_of_contractable hContract hn1_pos j
        -- Set invariance for mSI sets
        -- Note: reindexBlock m n j = fun ω => ω ∘ blockInjection m n j
        have h_preimage_eq : reindexBlock m (n + 1) j ⁻¹' s =
            (fun ω => ω ∘ blockInjection m (n + 1) j) ⁻¹' s := rfl
        have hs_reindex_inv : reindexBlock m (n + 1) j ⁻¹' s = s := by
          rw [h_preimage_eq]
          exact reindex_blockInjection_preimage_shiftInvariant hn1_pos j s hs_inv
        -- f is measurable
        have hf_meas : Measurable f := Finset.measurable_prod _ (fun i _ =>
          (hfs_meas i).comp (measurable_pi_apply _))
        -- Apply set integral equality
        -- hs_inv : isShiftInvariant s, so hs_inv.1 : MeasurableSet s
        exact (setIntegral_comp_reindexBlock_eq hμ_inv hs_inv.1
          hs_reindex_inv hf_meas.aemeasurable).symm

      -- Step 2: The algebraic identity (same as in integral_prod_eq_integral_blockAvg)
      -- blockAvgProd n ω = (1/(n+1)^m) * ∑_j ∏_i fs_i(ω(i*(n+1) + j(i)))
      have h_prod_blockAvg_eq : ∀ ω, blockAvgProd n ω =
          (1 / ((n + 1) : ℝ)^m) * ∑ j : Fin m → Fin (n + 1),
            ∏ i : Fin m, fs i (ω (i.val * (n + 1) + (j i).val)) := by
        intro ω
        simp only [blockAvgProd]
        simp_rw [blockAvg_pos_n hn1_pos]
        -- Normalize ↑(n + 1) to ↑n + 1 for consistency
        simp only [Nat.cast_add, Nat.cast_one]
        have h_factor : ∏ i : Fin m, (1 / ((n : ℝ) + 1)) *
            (Finset.range (n + 1)).sum (fun k => fs i (ω (i.val * (n + 1) + k))) =
            (1 / ((n : ℝ) + 1))^m * ∏ i : Fin m,
              (Finset.range (n + 1)).sum (fun k => fs i (ω (i.val * (n + 1) + k))) := by
          rw [Finset.prod_mul_distrib]
          congr 1
          rw [Finset.prod_const, Finset.card_fin]
        rw [h_factor]
        have h_range_to_fin : ∀ i : Fin m,
            (Finset.range (n + 1)).sum (fun k => fs i (ω (i.val * (n + 1) + k))) =
            ∑ k : Fin (n + 1), fs i (ω (i.val * (n + 1) + k.val)) := by
          intro i
          conv_lhs => rw [← Fin.sum_univ_eq_sum_range (fun k => fs i (ω (i.val * (n + 1) + k))) (n + 1)]
        simp_rw [h_range_to_fin]
        rw [Fintype.prod_sum]
        congr 1
        rw [one_div, one_div, inv_pow]

      -- Step 3: Combine using averaging argument
      -- ∫_s f = ∫_s f ∘ T_j for each j (by h_each_j_setIntegral)
      -- Sum over j and average: ∫_s f = (1/N) * ∑_j ∫_s (f ∘ T_j)
      -- Swap sum and integral (finite sum): = ∫_s [(1/N) * ∑_j (f ∘ T_j)]
      -- By algebraic identity: = ∫_s blockAvgProd n

      simp_rw [h_prod_blockAvg_eq]

      -- Get bound for integrability
      choose Cs hCs using hfs_bd
      have huniv_nonempty : Finset.univ.Nonempty := Finset.univ_nonempty_iff.mpr hm_nonempty
      let C := (Finset.univ.sup' huniv_nonempty (fun i : Fin m => |Cs i|)) + 1
      have hC_pos : 0 < C := add_pos_of_nonneg_of_pos
        (Finset.le_sup'_of_le _ (Finset.mem_univ ⟨0, Nat.pos_of_ne_zero hm⟩) (abs_nonneg _)) one_pos
      have hC_bd : ∀ i x, |fs i x| ≤ C := by
        intro i x
        have h1 : |fs i x| ≤ Cs i := hCs i x
        have h2 : Cs i ≤ |Cs i| := le_abs_self _
        have h3 : |Cs i| ≤ Finset.univ.sup' huniv_nonempty (fun i : Fin m => |Cs i|) :=
          Finset.le_sup' (fun i => |Cs i|) (Finset.mem_univ i)
        linarith

      -- The RHS simplifies to the same as LHS
      -- ∫_s (1/(n+1)^m * ∑_j ...) = (1/(n+1)^m) * ∫_s (∑_j ...) = (1/(n+1)^m) * ∑_j ∫_s ...
      -- Each ∫_s ... = ∫_s f by h_each_j_setIntegral
      -- So RHS = (1/(n+1)^m) * (n+1)^m * ∫_s f = ∫_s f = LHS

      -- Convert to simpler form
      have h_rhs_eq : ∫ ω in s, (1 / ((n + 1) : ℝ)^m) * ∑ j : Fin m → Fin (n + 1),
            ∏ i : Fin m, fs i (ω (i.val * (n + 1) + (j i).val)) ∂μ =
          (1 / ((n + 1) : ℝ)^m) * ∫ ω in s, ∑ j : Fin m → Fin (n + 1),
            ∏ i : Fin m, fs i (ω (i.val * (n + 1) + (j i).val)) ∂μ := by
        rw [integral_mul_left]

      rw [h_rhs_eq]

      -- Swap finite sum and integral (integrability check below)
      rw [integral_finset_sum Finset.univ]
      · -- Now: ∫_s f = (1/(n+1)^m) * ∑_j ∫_s ∏_i fs_i(ω(i*(n+1) + j(i)))
        -- Use h_each_j_setIntegral and blockInjection_val_lt
        have h_each_term : ∀ j : Fin m → Fin (n + 1),
            ∫ ω in s, ∏ i : Fin m, fs i (ω (i.val * (n + 1) + (j i).val)) ∂μ =
            ∫ ω in s, f ω ∂μ := by
          intro j
          rw [h_each_j_setIntegral j]
          -- The integrands match because reindexBlock applies blockInjection
          congr 1
          ext ω
          apply Finset.prod_congr rfl
          intro i _
          simp only [reindexBlock_apply, blockInjection_val_lt]

        rw [Finset.sum_congr rfl (fun j _ => h_each_term j)]
        rw [Finset.sum_const, Finset.card_univ]
        have h_card : Fintype.card (Fin m → Fin (n + 1)) = (n + 1)^m := by
          simp [Fintype.card_fun, Fintype.card_fin]
        rw [h_card, nsmul_eq_mul]

        -- Goal: ∫_s f = (1/(n+1)^m) * ((n+1)^m * ∫_s f)
        have hn1_ne_zero : ((n : ℝ) + 1) ≠ 0 := by positivity
        have hn1_pow_ne_zero : ((n : ℝ) + 1)^m ≠ 0 := pow_ne_zero m hn1_ne_zero
        -- Normalize coercions
        simp only [Nat.cast_add, Nat.cast_one, Nat.cast_pow]
        field_simp

      -- Integrability of each term in the sum
      intro j _
      let F : Ω[α] → ℝ := fun ω => ∏ i : Fin m, fs i (ω (i.val * (n + 1) + (j i).val))
      have h_meas : Measurable F :=
        Finset.measurable_prod _ (fun i _ => (hfs_meas i).comp (measurable_pi_apply _))
      apply Integrable.integrableOn
      refine Integrable.of_bound h_meas.aestronglyMeasurable (C^(Fintype.card (Fin m))) ?_
      filter_upwards with ω
      rw [Real.norm_eq_abs]
      show |F ω| ≤ _
      simp only [F]
      rw [Finset.abs_prod]
      calc ∏ i : Fin m, |fs i (ω (i.val * (n + 1) + (j i).val))|
        _ ≤ ∏ _i : Fin m, C := Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => hC_bd i _)
        _ = C^(Fintype.card (Fin m)) := by rw [Finset.prod_const, Finset.card_univ]

    -- **Step 2**: The block averages converge to g in L¹
    have h_L1_conv := product_blockAvg_L1_convergence hσ fs hfs_meas hfs_bd

    -- **Step 3**: L¹ convergence implies set integral convergence
    -- For a set of finite measure, |∫_s (f_n - f)| ≤ ∫_s |f_n - f| ≤ ∫ |f_n - f| → 0
    have h_setIntegral_conv : Tendsto (fun n => ∫ ω in s, blockAvgProd n ω ∂μ)
        atTop (𝓝 (∫ ω in s, g ω ∂μ)) := by
      -- Use that L¹ convergence of fₙ → g implies ∫_s fₙ → ∫_s g for any measurable set s
      -- Since |∫_s (fₙ - g)| ≤ ∫_s |fₙ - g| ≤ ∫ |fₙ - g| → 0
      apply Metric.tendsto_atTop.mpr
      intro ε hε
      obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp h_L1_conv ε hε
      refine ⟨N, fun n hn => ?_⟩
      specialize hN n hn
      simp only [Real.dist_eq, sub_zero] at hN
      rw [abs_of_nonneg (integral_nonneg (fun _ => abs_nonneg _))] at hN
      rw [Real.dist_eq]
      -- Get a uniform bound C on all fs i
      choose Cs hCs using hfs_bd
      have huniv_nonempty : Finset.univ.Nonempty := Finset.univ_nonempty_iff.mpr hm_nonempty
      let C := (Finset.univ.sup' huniv_nonempty (fun i : Fin m => |Cs i|)) + 1
      have hC_pos : 0 < C := add_pos_of_nonneg_of_pos
        (Finset.le_sup'_of_le _ (Finset.mem_univ ⟨0, Nat.pos_of_ne_zero hm⟩) (abs_nonneg _)) one_pos
      have hC_bd : ∀ i x, |fs i x| ≤ C := by
        intro i x
        have h1 : |fs i x| ≤ Cs i := hCs i x
        have h2 : Cs i ≤ |Cs i| := le_abs_self _
        have h3 : |Cs i| ≤ Finset.univ.sup' huniv_nonempty (fun i : Fin m => |Cs i|) :=
          Finset.le_sup' (fun i => |Cs i|) (Finset.mem_univ i)
        linarith
      -- Integrability of blockAvgProd n
      have h_int_blockAvg : Integrable (blockAvgProd n) μ := by
        have h_meas_n : Measurable (blockAvgProd n) :=
          Finset.measurable_prod _ (fun i _ => measurable_blockAvg i (hfs_meas i))
        apply Integrable.of_bound h_meas_n.aestronglyMeasurable (C^(Fintype.card (Fin m)))
        filter_upwards with ω
        rw [Real.norm_eq_abs, Finset.abs_prod]
        have : ∏ i : Fin m, |blockAvg m (n + 1) i (fs i) ω| ≤ ∏ _i : Fin m, C := by
          apply Finset.prod_le_prod (fun i _ => abs_nonneg _)
          intro i _
          exact blockAvg_abs_le i (le_of_lt hC_pos) (fun x => hC_bd i x) ω
        calc ∏ i, |blockAvg m (n + 1) i (fs i) ω|
          _ ≤ ∏ _i : Fin m, C := this
          _ = C ^ Fintype.card (Fin m) := by rw [Finset.prod_const, Finset.card_univ]
      -- Integrability of |blockAvgProd n - g|
      have h_int_diff : Integrable (fun ω => |blockAvgProd n ω - g ω|) μ :=
        Integrable.abs (h_int_blockAvg.sub hg_int)
      -- blockAvgProd n and g are related by hg_apply
      -- We need to convert between them for the final bound
      have h_eq_integrands : (fun ω => |blockAvgProd n ω - g ω|) =
          (fun ω => |∏ i : Fin m, blockAvg m (n + 1) i (fs i) ω -
                    ∏ i : Fin m, μ[(fun ω' => fs i (ω' 0)) | mSI] ω|) := by
        ext ω
        congr 1
        rw [hg_apply ω]
      -- The key bound: |∫_s (fₙ - g)| ≤ ∫_s |fₙ - g| ≤ ∫ |fₙ - g| < ε
      calc |∫ ω in s, blockAvgProd n ω ∂μ - ∫ ω in s, g ω ∂μ|
        _ = |∫ ω in s, (blockAvgProd n ω - g ω) ∂μ| := by
            rw [← integral_sub h_int_blockAvg.integrableOn hg_int.integrableOn]
        _ ≤ ∫ ω in s, |blockAvgProd n ω - g ω| ∂μ := abs_integral_le_integral_abs
        _ ≤ ∫ ω, |blockAvgProd n ω - g ω| ∂μ := by
            apply setIntegral_le_integral h_int_diff
            filter_upwards with ω
            exact abs_nonneg _
        _ = ∫ ω, |∏ i : Fin m, blockAvg m (n + 1) i (fs i) ω -
                  ∏ i : Fin m, μ[(fun ω' => fs i (ω' 0)) | mSI] ω| ∂μ := by
            rw [h_eq_integrands]
        _ < ε := hN

    -- **Step 4**: Since ∫_s f = ∫_s (blockAvgProd n) for all n (constant sequence),
    -- and ∫_s (blockAvgProd n) → ∫_s g, we have ∫_s g = ∫_s f
    have h_const_seq : ∀ n, ∫ ω in s, blockAvgProd n ω ∂μ = ∫ ω in s, f ω ∂μ :=
      fun n => (h_setIntegral_eq_blockAvg n).symm
    have h_const_tendsto : Tendsto (fun _ : ℕ => ∫ ω in s, f ω ∂μ) atTop
        (𝓝 (∫ ω in s, f ω ∂μ)) := tendsto_const_nhds
    have h_seq_eq : (fun n => ∫ ω in s, blockAvgProd n ω ∂μ) = fun _ => ∫ ω in s, f ω ∂μ :=
      funext h_const_seq
    rw [h_seq_eq] at h_setIntegral_conv
    exact tendsto_nhds_unique h_setIntegral_conv h_const_tendsto

  -- g is integrable on mSI-sets of finite measure
  have hg_int_finite : ∀ s, MeasurableSet[mSI] s → μ s < ⊤ → IntegrableOn g s μ := by
    intro s _ _
    exact hg_int.integrableOn

  -- Apply uniqueness of conditional expectation
  -- ae_eq_condExp_of_forall_setIntegral_eq gives: g =ᵐ μ[f | mSI]
  -- We need: μ[f | mSI] =ᵐ g (goal is CE =ᵐ product of CEs)
  -- Note: the theorem expects AEStronglyMeasurable[mSI] g μ, so use hg_meas directly
  have h_ae_eq : g =ᵐ[μ] μ[f | mSI] :=
    ae_eq_condExp_of_forall_setIntegral_eq shiftInvariantSigma_le
      hf_int hg_int_finite hg_eq hg_meas.aestronglyMeasurable

  -- The goal is μ[f | mSI] =ᵐ (fun ω => ∏ i, CE_i ω)
  -- We have: g =ᵐ μ[f | mSI] and g ω = ∏ i, CE_i ω (by hg_apply)
  -- So: μ[f | mSI] =ᵐ g = (fun ω => g ω) = (fun ω => ∏ i, CE_i ω)
  have h_g_eq : g = fun ω => ∏ i : Fin m, μ[(fun ω' => fs i (ω' 0)) | mSI] ω :=
    funext hg_apply
  rw [h_g_eq] at h_ae_eq
  exact h_ae_eq.symm

end KernelIndependence

end Exchangeability.DeFinetti.ViaKoopman
