/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Exchangeability.DeFinetti.ViaKoopman.BlockAverage

/-!
# Contractable Factorization: Product Convergence and Kernel Independence

This file completes the **disjoint-block averaging argument** from Kallenberg's "first proof"
of de Finetti's theorem. Building on `BlockAverage.lean` (which defines block averages and
establishes their L¹ convergence), this file proves:

## Main results

* `product_blockAvg_L1_convergence`: Product of block averages converges L¹ to product of CEs.
* `measure_map_reindexBlock_eq_of_contractable`: Contractability implies path-space measure
  invariance under block reindexing (via π-λ theorem).
* `condexp_product_factorization_contractable`: For contractable measures,
  `CE[∏ fᵢ(ωᵢ) | mSI] = ∏ CE[fᵢ(ω₀) | mSI]` a.e.

## Mathematical context

The proof proceeds as follows:

1. **L¹ convergence of products**: Using the telescoping bound and individual L¹ convergence
   of block averages (from `BlockAverage.lean`), we show that products of block averages
   converge to products of conditional expectations.

2. **Measure invariance from contractability**: The π-λ theorem upgrades finite-dimensional
   contractability to full path-space measure invariance under block reindexing.

3. **CE product factorization**: Combining L¹ convergence with measure invariance and
   uniqueness of conditional expectation yields the key factorization result.

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

/-- For a finite family `fs : Fin m → α → ℝ` (with `0 < m`) where each `fs i` is bounded,
there exists a single positive constant bounding all `fs i` uniformly.

Construction: take the max of the individual bounds (in absolute value), then add 1
to ensure strict positivity. -/
private lemma exists_uniform_pos_bound_fin
    {β : Type*} {m : ℕ} (hm_pos : 0 < m) {fs : Fin m → β → ℝ}
    (hfs_bd : ∀ i, ∃ C, ∀ x, |fs i x| ≤ C) :
    ∃ C > 0, ∀ i x, |fs i x| ≤ C := by
  classical
  choose Cs hCs using hfs_bd
  have huniv_nonempty : (Finset.univ : Finset (Fin m)).Nonempty :=
    ⟨⟨0, hm_pos⟩, Finset.mem_univ _⟩
  refine ⟨(Finset.univ.sup' huniv_nonempty (fun i => |Cs i|)) + 1, ?_, ?_⟩
  · exact add_pos_of_nonneg_of_pos
      (Finset.le_sup'_of_le _ (Finset.mem_univ ⟨0, hm_pos⟩) (abs_nonneg _)) one_pos
  · intro i x
    have h1 : |fs i x| ≤ Cs i := hCs i x
    have h2 : Cs i ≤ |Cs i| := le_abs_self _
    have h3 : |Cs i| ≤ Finset.univ.sup' huniv_nonempty (fun i => |Cs i|) :=
      Finset.le_sup' (fun i => |Cs i|) (Finset.mem_univ i)
    linarith

/-! ### Product L¹ Convergence via Telescoping -/

section ProductConvergence

variable {μ : Measure (Ω[α])} [IsProbabilityMeasure μ] [StandardBorelSpace α]

/-- Telescoping bound for product differences with general bound C.

Extends `abs_prod_sub_prod_le` (which requires bound 1) to general bounds via normalization.
For functions bounded by C > 0:
  |∏ A - ∏ B| ≤ C^{m-1} * ∑ |A_i - B_i|

This is derived from abs_prod_sub_prod_le by dividing by C. -/
private lemma abs_prod_sub_prod_le_general {m : ℕ} (A B : Fin m → ℝ) {C : ℝ} (hC : 0 < C)
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
    simp only [A', abs_div, abs_of_pos hC]; exact div_le_one_of_le₀ (hA i) (le_of_lt hC)
  have hB' : ∀ i, |B' i| ≤ 1 := fun i => by
    simp only [B', abs_div, abs_of_pos hC]; exact div_le_one_of_le₀ (hB i) (le_of_lt hC)
  -- Apply abs_prod_sub_prod_le to normalized functions
  have h_norm := Exchangeability.Util.abs_prod_sub_prod_le A' B' hA' hB'
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
  --   - abs_prod_sub_prod_le: |∏ f - ∏ g| ≤ ∑ |f_i - g_i| for |f|, |g| ≤ 1
  --   - prod_tendsto_L1_of_L1_tendsto: Alternative direct approach

  -- Handle m = 0 case first
  by_cases hm : m = 0
  · subst hm
    simp only [Finset.univ_eq_empty, Finset.prod_empty, sub_self, abs_zero, integral_zero]
    exact tendsto_const_nhds
  -- m > 0 case
  have hm_pos : 0 < m := Nat.pos_of_ne_zero hm

  -- Step 1: Get uniform bound C > 0 for all fs i
  obtain ⟨C, hC_pos, hC_bd⟩ := exists_uniform_pos_bound_fin hm_pos hfs_bd

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
    exact tendsto_finset_sum _ fun i _ =>
      blockAvg_tendsto_condExp hσ m i (hfs_meas i) ⟨C, fun x => hC_bd i x⟩

  -- Apply squeeze theorem
  apply squeeze_zero
  · exact fun n => integral_nonneg (fun _ => abs_nonneg _)
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
    have hA_bd : ∀ i ω, |A i ω| ≤ C := fun i ω =>
      blockAvg_abs_le i (le_of_lt hC_pos) (fun x => hC_bd i x) ω

    -- Bound on conditional expectations (a.e.)
    -- Uses ae_bdd_condExp_of_ae_bdd: bounded f implies bounded condexp
    have hB_bd : ∀ᵐ ω ∂μ, ∀ i, |B i ω| ≤ C := by
      rw [ae_all_iff]
      intro i
      -- Create NNReal version of C for ae_bdd_condExp_of_ae_bdd
      let R : NNReal := Real.toNNReal C
      have hR_eq : (R : ℝ) = C := Real.coe_toNNReal C (le_of_lt hC_pos)
      -- The function fs i ∘ (· 0) is bounded by C pointwise
      have h_fs_bdd : ∀ᵐ ω' ∂μ, |fs i (ω' 0)| ≤ (R : ℝ) :=
        hR_eq.symm ▸ Eventually.of_forall (fun ω' => hC_bd i _)
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
      _ ≤ ∫ ω, C^(m - 1) * ∑ i, |A i ω - B i ω| ∂μ :=
          integral_mono_ae (hprodA_int.sub hprodB_int).abs
            ((integrable_finset_sum _ fun i _ => (hAB_diff_int i).abs).const_mul _) h_pointwise
      _ = C^(m - 1) * ∫ ω, ∑ i, |A i ω - B i ω| ∂μ := integral_const_mul _ _
      _ = C^(m - 1) * ∑ i, ∫ ω, |A i ω - B i ω| ∂μ := by
          congr 1; exact integral_finset_sum _ fun i _ => (hAB_diff_int i).abs
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
private lemma measure_map_reindexBlock_eq_of_contractable
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
  have hk_mono : StrictMono (fun i : Fin N => blockInjection m n j i.val) :=
    fun i₁ i₂ hi => blockInjection_strictMono m n hn j hi

  -- Apply contractability
  have hMarg := hContract N (fun i : Fin N => blockInjection m n j i.val) hk_mono

  -- hMarg says: map (fun ω i => ω (blockInjection m n j i.val)) μ = map (fun ω i => ω i.val) μ
  -- The RHS is exactly map (prefixProj N) μ, so we're done
  calc Measure.map (fun ω (i : Fin N) => ω (blockInjection m n j i.val)) μ S
    _ = Measure.map (fun ω (i : Fin N) => ω i.val) μ S := by rw [hMarg]
    _ = Measure.map (prefixProj (α := α) N) μ S := rfl

omit [IsProbabilityMeasure μ] in
/-- Set integral equality from measure invariance and set invariance.

If the measure is invariant under reindexing (μ = μ ∘ reindexBlock⁻¹) and the set is invariant
under reindexing (s = reindexBlock⁻¹(s)), then ∫_s f ∘ reindexBlock = ∫_s f.

This is the key lemma that replaces "conditional contractability". -/
private lemma setIntegral_comp_reindexBlock_eq
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

  -- Uniform positive bound on all fs i, used by every integrability subproof below.
  obtain ⟨C, hC_pos, hC_bd⟩ := exists_uniform_pos_bound_fin (Nat.pos_of_ne_zero hm) hfs_bd

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
    -- Each CE is bounded by C
    have hCE_bd : ∀ᵐ ω ∂μ, ∀ i, |μ[(fun ω' => fs i (ω' 0)) | mSI] ω| ≤ C := by
      rw [ae_all_iff]
      intro i
      let R : NNReal := Real.toNNReal C
      have hR_eq : (R : ℝ) = C := Real.coe_toNNReal C (le_of_lt hC_pos)
      have h_fs_bdd : ∀ᵐ ω' ∂μ, |fs i (ω' 0)| ≤ (R : ℝ) :=
        hR_eq.symm ▸ Eventually.of_forall (fun ω' => hC_bd i _)
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
        -- Note: reindexBlock m n j = fun ω => ω ∘ blockInjection m n j definitionally
        have hs_reindex_inv : reindexBlock m (n + 1) j ⁻¹' s = s :=
          reindex_blockInjection_preimage_shiftInvariant hn1_pos j s hs_inv
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

      -- The RHS simplifies to the same as LHS
      -- ∫_s (1/(n+1)^m * ∑_j ...) = (1/(n+1)^m) * ∫_s (∑_j ...) = (1/(n+1)^m) * ∑_j ∫_s ...
      -- Each ∫_s ... = ∫_s f by h_each_j_setIntegral
      -- So RHS = (1/(n+1)^m) * (n+1)^m * ∫_s f = ∫_s f = LHS

      -- Convert to simpler form
      have h_rhs_eq : ∫ ω in s, (1 / ((n + 1) : ℝ)^m) * ∑ j : Fin m → Fin (n + 1),
            ∏ i : Fin m, fs i (ω (i.val * (n + 1) + (j i).val)) ∂μ =
          (1 / ((n + 1) : ℝ)^m) * ∫ ω in s, ∑ j : Fin m → Fin (n + 1),
            ∏ i : Fin m, fs i (ω (i.val * (n + 1) + (j i).val)) ∂μ := by
        rw [integral_const_mul]

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
          simp [Fintype.card_fin]
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
      -- Integrability of blockAvgProd n
      have h_int_blockAvg : Integrable (blockAvgProd n) μ := by
        have h_meas_n : Measurable (blockAvgProd n) :=
          Finset.measurable_prod _ (fun i _ => measurable_blockAvg i (hfs_meas i))
        apply Integrable.of_bound h_meas_n.aestronglyMeasurable (C^(Fintype.card (Fin m)))
        filter_upwards with ω
        rw [Real.norm_eq_abs, Finset.abs_prod]
        have : ∏ i : Fin m, |blockAvg m (n + 1) i (fs i) ω| ≤ ∏ _i : Fin m, C :=
          Finset.prod_le_prod (fun i _ => abs_nonneg _) fun i _ =>
            blockAvg_abs_le i (le_of_lt hC_pos) (fun x => hC_bd i x) ω
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
                    ∏ i : Fin m, μ[(fun ω' => fs i (ω' 0)) | mSI] ω|) :=
        funext fun ω => congrArg (|·|) (congrArg (blockAvgProd n ω - ·) (hg_apply ω))
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
  have hg_int_finite : ∀ s, MeasurableSet[mSI] s → μ s < ⊤ → IntegrableOn g s μ :=
    fun _ _ _ => hg_int.integrableOn

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

/-! ### Bridge to CommonEnding

The CE-based factorization above feeds `indicator_product_bridge_contractable`
(in `Exchangeability/DeFinetti/BridgeProperty.lean`), which converts it into the
shape consumed by `CommonEnding.conditional_iid_from_directing_measure`. The
construction is: for injective `k`, sort to obtain a strictly-monotone `ρ` with
permutation `σ` such that `k = ρ ∘ σ`, apply contractability to get integral
equality, and combine with the CE factorization via the `ν` ↔ conditional
expectation identification.
-/

end Exchangeability.DeFinetti.ViaKoopman
