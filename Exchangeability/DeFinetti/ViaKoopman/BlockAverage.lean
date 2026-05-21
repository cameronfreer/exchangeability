/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Exchangeability.DeFinetti.ViaKoopman.BlockInjection
import Exchangeability.DeFinetti.ViaKoopman.CesaroConvergence
import Exchangeability.DeFinetti.ViaKoopman.DirectingKernel
import Exchangeability.Contractability
import Exchangeability.Util.ProductBounds

/-!
# Block Averages for Contractable Factorization

This file defines block averages and proves their L¹ convergence to conditional expectations.
These are the foundational lemmas for the disjoint-block averaging argument in Kallenberg's
"first proof" of de Finetti's theorem.

## Main definitions

* `blockAvg m n k f ω`: Block average of `f` at position `k` with `m` blocks of size `n`.
  Computes `(1/n) * ∑_{j=0}^{n-1} f(ω(k*n + j))`.

## Main results

* `blockAvg_tendsto_condExp`: Block averages converge L¹ to conditional expectation.
* `integral_prod_reindex_of_contractable`: Contractability gives integral equality under reindexing.
* `integral_prod_eq_integral_blockAvg`: Averaging over choice functions yields block averages.

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

omit [MeasurableSpace α] in
@[nolint unusedArguments]
lemma blockAvg_pos_n {m n : ℕ} (hn : 0 < n) (k : Fin m) (f : α → ℝ) (ω : ℕ → α) :
    blockAvg m n k f ω = (1 / (n : ℝ)) * (Finset.range n).sum (fun j => f (ω (k.val * n + j))) := by
  simp [blockAvg, Nat.pos_iff_ne_zero.mp hn]

/-! ### Block Average and Shifted Cesàro Averages -/

omit [MeasurableSpace α] in
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

@[measurability, fun_prop]
lemma measurable_blockAvg {m n : ℕ} (k : Fin m) {f : α → ℝ} (hf : Measurable f) :
    Measurable (blockAvg (α := α) m n k f) := by
  unfold blockAvg
  by_cases hn : n = 0
  · simp only [hn, ↓reduceDIte, measurable_const]
  · simp only [hn, ↓reduceDIte]
    exact (Finset.measurable_sum _ fun j _ => hf.comp (measurable_pi_apply _)).const_mul _

omit [MeasurableSpace α] in
/-- Block averages of bounded functions are bounded.

If |f x| ≤ C for all x, then |blockAvg m n k f ω| ≤ C for all ω.
This follows because blockAvg is a convex combination of values of f. -/
@[nolint unusedArguments]
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
  have hf_int : Integrable (fun ω : Ω[α] => f (ω 0)) μ :=
    let ⟨C, hC⟩ := hf_bd
    integrable_of_bounded_measurable (hf.comp (measurable_pi_apply 0)) C fun ω => hC (ω 0)

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
        have hA_meas : Measurable (A n) := by fun_prop
        -- Y is the conditional expectation, measurable via shiftInvariantSigma_le
        have hY_meas : Measurable Y :=
          stronglyMeasurable_condExp.measurable.mono (shiftInvariantSigma_le (α := α)) le_rfl
        exact (continuous_abs.measurable.comp (hA_meas.sub hY_meas)).stronglyMeasurable
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

omit [IsProbabilityMeasure μ] [StandardBorelSpace α] in
/-- For contractable μ, integral of product equals integral of product with reindexed coordinates.

Given strict monotone k : Fin m → ℕ, contractability says:
`∫ ∏ᵢ fᵢ(ωᵢ) dμ = ∫ ∏ᵢ fᵢ(ω(k(i))) dμ`

This is the fundamental identity that lets us swap between original and reindexed coordinates. -/
@[nolint unusedArguments]
lemma integral_prod_reindex_of_contractable
    (hContract : ∀ (m' : ℕ) (k : Fin m' → ℕ), StrictMono k →
        Measure.map (fun ω i => ω (k i)) μ = Measure.map (fun ω (i : Fin m') => ω i.val) μ)
    {m : ℕ} (fs : Fin m → α → ℝ)
    (hfs_meas : ∀ i, Measurable (fs i))
    (_hfs_bd : ∀ i, ∃ C, ∀ x, |fs i x| ≤ C)
    {k : Fin m → ℕ} (hk : StrictMono k) :
    ∫ ω, (∏ i : Fin m, fs i (ω i.val)) ∂μ =
    ∫ ω, (∏ i : Fin m, fs i (ω (k i))) ∂μ := by
  -- Use contractability: μ ∘ (ω ↦ (ω(k(0)), ..., ω(k(m-1)))) = μ ∘ (ω ↦ (ω₀, ..., ω_{m-1}))
  have h_map := hContract m k hk
  -- The measurable function for mapping to Fin m → α
  have h_meas_orig : Measurable (fun ω (i : Fin m) => ω i.val : Ω[α] → (Fin m → α)) :=
    by
      fun_prop
  have h_meas_reindex : Measurable (fun ω i => ω (k i) : Ω[α] → (Fin m → α)) :=
    by
      fun_prop
  -- The integrand on Fin m → α
  let F : (Fin m → α) → ℝ := fun ω' => ∏ i, fs i (ω' i)
  have hF_meas_base : Measurable F :=
    Finset.measurable_prod _ fun i _ => (hfs_meas i).comp (measurable_pi_apply i)
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

omit [StandardBorelSpace α] in
/-- Averaging over all choice functions yields product of block averages.

For any bounded measurable fs : Fin m → α → ℝ:
`∫ ∏ᵢ fᵢ(ωᵢ) dμ = ∫ ∏ᵢ blockAvg m n i fᵢ ω dμ`

This is proved by:
1. For each j : Fin m → Fin n, contractability gives ∫ ∏ fᵢ(ωᵢ) = ∫ ∏ fᵢ(ω(ρⱼ(i)))
2. Sum over all j and divide by n^m to get block averages
-/
@[nolint unusedArguments]
lemma integral_prod_eq_integral_blockAvg
    (_hσ : MeasurePreserving shift μ μ)
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
    have hk_mono : StrictMono k := fun _ _ hii' => h_mono hii'
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
  have h_card : Fintype.card (Fin m → Fin n) = n^m := by simp [Fintype.card_fin]

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
  rw [integral_const_mul]

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

end Exchangeability.DeFinetti.ViaKoopman
