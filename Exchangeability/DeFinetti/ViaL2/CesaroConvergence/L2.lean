/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Exchangeability.DeFinetti.ViaL2.CesaroConvergence.Cauchy
import Exchangeability.DeFinetti.ViaL2.BlockAverages
import Exchangeability.Tail.TailSigma
import Exchangeability.Tail.ShiftInvariantMeasure
import Exchangeability.Probability.SigmaAlgebraHelpers

/-!
# Cesàro L² Convergence: `cesaro_to_condexp_L2`

L² convergence of block Cesàro averages to the conditional expectation given the
tail σ-algebra. Combines the Cauchy property from
`CesaroConvergence/Cauchy.lean` with tail-measurability of the limit.

## Main results

* `cesaro_to_condexp_L2`: L² convergence to the tail conditional expectation
* `blockAvg_measurable_tailFamily`: block averages are measurable w.r.t. tail σ-algebras

## References

* Kallenberg (2005), *Probabilistic Symmetries and Invariance Principles*,
  Chapter 1, "Second proof of Theorem 1.1"
-/

noncomputable section

namespace Exchangeability.DeFinetti.ViaL2

open MeasureTheory ProbabilityTheory BigOperators Filter Topology
open Exchangeability
open Exchangeability.DeFinetti.L2Helpers
open Exchangeability.Probability.CenteredVariables

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

open scoped BigOperators

lemma blockAvg_measurable_tailFamily
    {Ω : Type*} [MeasurableSpace Ω]
    {f : ℝ → ℝ} (hf : Measurable f)
    {X : ℕ → Ω → ℝ}
    (m n : ℕ) :
    Measurable[Exchangeability.Tail.tailFamily X m] (blockAvg f X m n) := by
  -- blockAvg f X m n = (n⁻¹) * ∑_{k<n} f(X_{m+k})
  unfold blockAvg
  -- Each X (m + k) is measurable w.r.t. tailFamily X m by definition
  -- tailFamily X m = iSup (fun j => comap (X (m + j)) m_ℝ)
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro k _
  -- f ∘ X (m + k) is measurable w.r.t. tailFamily X m
  apply hf.comp
  -- X (m + k) is measurable w.r.t. tailFamily X m
  -- tailFamily X m = iSup (fun j => comap (X (m + j)))
  -- X (m + k) ω = (fun j => X (m + j) ω) k, so it's the k-th coordinate
  -- of the shifted sequence, which is measurable by comap construction
  show Measurable[iSup (fun j : ℕ => MeasurableSpace.comap (fun ω => X (m + j) ω) inferInstance)] _
  apply Measurable.of_comap_le
  exact le_iSup (fun j => MeasurableSpace.comap (fun ω => X (m + j) ω) inferInstance) k

private lemma blockAvg_shift_tendsto
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ}
    (f : ℝ → ℝ) (hf_meas : Measurable f) (hf_bdd : ∀ x, |f x| ≤ 1)
    (hX_meas : ∀ i, Measurable (X i))
    (α_f : Ω → ℝ) (hα_memLp : MemLp α_f 2 μ)
    (hα_limit : Tendsto (fun n => eLpNorm (blockAvg f X 0 n - α_f) 2 μ) atTop (𝓝 0))
    (N : ℕ) :
    Tendsto (fun m => eLpNorm (blockAvg f X N m - α_f) 2 μ) atTop (𝓝 0) := by
  -- Case N = 0: trivial, just use the hypothesis
  rcases eq_or_ne N 0 with rfl | hN
  · exact hα_limit
  -- Case N > 0: Use algebraic decomposition and squeeze theorem

  -- Step 1: The shifted hypothesis: eLpNorm (blockAvg f X 0 (N + m) - α_f) 2 μ → 0 as m → ∞
  have hα_limit_shifted : Tendsto (fun m => eLpNorm (blockAvg f X 0 (N + m) - α_f) 2 μ) atTop (𝓝 0) := by
    have h := Filter.tendsto_add_atTop_iff_nat (l := 𝓝 0) (f := fun n => eLpNorm (blockAvg f X 0 n - α_f) 2 μ) N
    simp only [add_comm] at h
    exact h.mpr hα_limit

  -- Step 2: The constant term C_N = eLpNorm (blockAvg f X 0 N - α_f) 2 μ
  let C_N := eLpNorm (blockAvg f X 0 N - α_f) 2 μ

  -- Step 3: We need MemLp for blockAvg - α_f to use eLpNorm_add_le
  have hBlockAvg_memLp : ∀ n, MemLp (blockAvg f X 0 n) 2 μ := fun n =>
    blockAvg_memLp_two_of_abs_le_one f X hf_meas hX_meas hf_bdd 0 n

  have hDiff_memLp : ∀ n, MemLp (blockAvg f X 0 n - α_f) 2 μ :=
    fun n => (hBlockAvg_memLp n).sub hα_memLp

  -- Upper bound sequence
  let upper : ℕ → ENNReal := fun m =>
    if hm : m = 0 then ⊤
    else ENNReal.ofReal ((N + m : ℝ) / m) * eLpNorm (blockAvg f X 0 (N + m) - α_f) 2 μ
         + ENNReal.ofReal ((N : ℝ) / m) * C_N

  -- Show upper bound tends to 0
  have hUpper_tendsto : Tendsto upper atTop (𝓝 0) := by
    have h_coeff1 : Tendsto (fun (m : ℕ) => ENNReal.ofReal (((N : ℝ) + m) / m)) atTop (𝓝 1) := by
      have : Tendsto (fun m : ℕ => (N + m : ℝ) / m) atTop (𝓝 1) := by
        -- For m ≠ 0: (N + m) / m = 1 + N / m
        have hN_div : Tendsto (fun m : ℕ => (N : ℝ) / m) atTop (𝓝 0) :=
          tendsto_const_div_atTop_nhds_zero_nat (N : ℝ)
        have h_sum : Tendsto (fun m : ℕ => (1 : ℝ) + (N : ℝ) / m) atTop (𝓝 1) := by
          convert hN_div.const_add 1; ring
        apply Filter.Tendsto.congr' _ h_sum
        filter_upwards [Filter.eventually_gt_atTop 0] with m hm
        have hm_ne : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hm)
        field_simp [hm_ne]
        ring
      convert ENNReal.tendsto_ofReal this
      simp [ENNReal.ofReal_one]

    have h_coeff2 : Tendsto (fun (m : ℕ) => ENNReal.ofReal ((N : ℝ) / m)) atTop (𝓝 0) := by
      have : Tendsto (fun m : ℕ => (N : ℝ) / m) atTop (𝓝 0) :=
        tendsto_const_div_atTop_nhds_zero_nat (N : ℝ)
      convert ENNReal.tendsto_ofReal this
      simp [ENNReal.ofReal_zero]

    -- Term 1: bounded * 0 → 0
    have hTerm1 : Tendsto (fun (m : ℕ) => ENNReal.ofReal (((N : ℝ) + m) / m) *
        eLpNorm (blockAvg f X 0 (N + m) - α_f) 2 μ) atTop (𝓝 0) := by
      have h1 : Tendsto (fun (m : ℕ) => ENNReal.ofReal (((N : ℝ) + m) / m)) atTop (𝓝 1) := h_coeff1
      have h2 : Tendsto (fun (m : ℕ) => eLpNorm (blockAvg f X 0 (N + m) - α_f) 2 μ) atTop (𝓝 0) :=
        hα_limit_shifted
      -- ENNReal.Tendsto.mul needs: (a ≠ 0 ∨ b ≠ ∞) and (b ≠ 0 ∨ a ≠ ∞) where a=1, b=0
      have := ENNReal.Tendsto.mul h1 (Or.inl one_ne_zero) h2 (Or.inr ENNReal.one_ne_top)
      simp only [mul_zero] at this
      exact this

    -- Term 2: 0 * constant → 0
    have hTerm2 : Tendsto (fun (m : ℕ) => ENNReal.ofReal ((N : ℝ) / m) * C_N) atTop (𝓝 0) := by
      have h1 : Tendsto (fun (m : ℕ) => ENNReal.ofReal ((N : ℝ) / m)) atTop (𝓝 0) := h_coeff2
      have hC_N_ne_top : C_N ≠ ⊤ := (hDiff_memLp N).eLpNorm_ne_top
      -- ENNReal.Tendsto.mul needs: (a ≠ 0 ∨ b ≠ ∞) and (b ≠ 0 ∨ a ≠ ∞) where a=0, b=C_N
      have := ENNReal.Tendsto.mul h1 (Or.inr hC_N_ne_top) tendsto_const_nhds (Or.inr ENNReal.zero_ne_top)
      simp only [zero_mul] at this
      exact this

    -- Combine
    rw [ENNReal.tendsto_atTop_zero]
    intro ε hε
    have hε2 : (0 : ENNReal) < ε / 2 := ENNReal.div_pos hε.ne' (by norm_num : (2 : ENNReal) ≠ ⊤)
    rw [ENNReal.tendsto_atTop_zero] at hTerm1 hTerm2
    obtain ⟨M₁, hM₁⟩ := hTerm1 (ε / 2) hε2
    obtain ⟨M₂, hM₂⟩ := hTerm2 (ε / 2) hε2
    use max (max M₁ M₂) 1
    intro m hm
    have hm1 : m ≥ M₁ := le_trans (le_max_left M₁ M₂) (le_trans (le_max_left _ _) hm)
    have hm2 : m ≥ M₂ := le_trans (le_max_right M₁ M₂) (le_trans (le_max_left _ _) hm)
    have hm_pos : m ≥ 1 := le_trans (le_max_right _ _) hm
    have hm_ne : m ≠ 0 := Nat.one_le_iff_ne_zero.mp hm_pos
    simp only [upper, dif_neg hm_ne]
    -- The goal and hM₁/hM₂ match after simp expands upper
    calc ENNReal.ofReal ((↑N + ↑m) / ↑m) * eLpNorm (blockAvg f X 0 (N + m) - α_f) 2 μ
           + ENNReal.ofReal (↑N / ↑m) * C_N
        ≤ ε / 2 + ε / 2 := add_le_add (hM₁ m hm1) (hM₂ m hm2)
      _ = ε := ENNReal.add_halves ε

  -- Step 5: Use squeeze theorem
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hUpper_tendsto
  · exact Eventually.of_forall (fun _ => zero_le _)
  · rw [Filter.eventually_atTop]
    use 1
    intro m hm_pos
    have hm_ne : m ≠ 0 := Nat.one_le_iff_ne_zero.mp hm_pos
    -- Expand upper and show the eLpNorm bound
    -- The goal after simp: eLpNorm(blockAvg f X N m - α_f) ≤ upper m
    -- which expands to the algebraic bound via triangle inequality
    simp only [upper, dif_neg hm_ne]

    -- Algebraic identity (pointwise)
    have hAlg : ∀ ω, blockAvg f X N m ω - α_f ω =
        ((N + m : ℝ) / m) * (blockAvg f X 0 (N + m) ω - α_f ω)
        - (N / m) * (blockAvg f X 0 N ω - α_f ω) := by
      intro ω
      simp only [blockAvg]
      have hm_real_ne : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm_ne
      have hNm_real_ne : (N + m : ℝ) ≠ 0 := by positivity
      have hN_real_ne : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
      -- Introduce abbreviations for sums
      set S_m := (Finset.range m).sum (fun k => f (X (N + k) ω)) with hS_m_def
      set S_N := (Finset.range N).sum (fun k => f (X k ω)) with hS_N_def
      set S_Nm := (Finset.range (N + m)).sum (fun k => f (X (0 + k) ω)) with hS_Nm_def
      have hSum : S_Nm = S_N + S_m := by
        simp only [hS_Nm_def, hS_N_def, hS_m_def]
        rw [Finset.sum_range_add]
        simp only [zero_add]
      -- The goal is: (1/m) * S_m - α = ((N+m)/m) * ((1/(N+m)) * S_Nm - α) - (N/m) * ((1/N) * S_N - α)
      rw [hSum]
      field_simp
      -- After field_simp, some occurrences of S_N get expanded back to the sum
      -- The sum has `0 + k` which needs to simplify to `k`
      simp only [zero_add]
      conv_rhs => rw [← hS_N_def]
      -- Normalize casts: ↑(N + m) = ↑N + ↑m
      simp only [Nat.cast_add]
      ring

    -- Apply eLpNorm bounds with triangle inequality
    calc eLpNorm (blockAvg f X N m - α_f) 2 μ
        = eLpNorm (fun ω => ((N + m : ℝ) / m) * (blockAvg f X 0 (N + m) ω - α_f ω)
                           - (N / m) * (blockAvg f X 0 N ω - α_f ω)) 2 μ := by
            congr 1; ext ω; exact hAlg ω
      _ ≤ eLpNorm (fun ω => ((N + m : ℝ) / m) * (blockAvg f X 0 (N + m) ω - α_f ω)) 2 μ
          + eLpNorm (fun ω => (N / m) * (blockAvg f X 0 N ω - α_f ω)) 2 μ := by
            apply eLpNorm_sub_le
            · exact (hDiff_memLp (N + m)).aestronglyMeasurable.const_mul _
            · exact (hDiff_memLp N).aestronglyMeasurable.const_mul _
            · norm_num
      _ = eLpNorm (((N + m : ℝ) / m) • (blockAvg f X 0 (N + m) - α_f)) 2 μ
          + eLpNorm ((N / m : ℝ) • (blockAvg f X 0 N - α_f)) 2 μ := by
            rfl
      _ = ‖((N + m : ℝ) / m)‖ₑ * eLpNorm (blockAvg f X 0 (N + m) - α_f) 2 μ
          + ‖(N / m : ℝ)‖ₑ * eLpNorm (blockAvg f X 0 N - α_f) 2 μ := by
            rw [eLpNorm_const_smul, eLpNorm_const_smul]
      _ = ENNReal.ofReal |((N + m : ℝ) / m)| * eLpNorm (blockAvg f X 0 (N + m) - α_f) 2 μ
          + ENNReal.ofReal |(N / m : ℝ)| * C_N := by
            simp only [Real.enorm_eq_ofReal_abs]; rfl
      _ = ENNReal.ofReal ((↑N + ↑m) / ↑m) * eLpNorm (blockAvg f X 0 (N + m) - α_f) 2 μ
          + ENNReal.ofReal (↑N / ↑m) * C_N := by
            congr 1
            · congr 1
              rw [abs_of_nonneg]
              positivity
            · congr 1; rw [abs_of_nonneg]; positivity

/-- Helper lemma: tail-measurability of L² limit of block averages.

Given an L² limit α_f of block averages, if the block averages are measurable
with respect to the tail σ-algebra for large N, then α_f is tail-measurable. -/
private lemma tail_measurability_of_blockAvg
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ}
    (f : ℝ → ℝ) (hf_meas : Measurable f) (hf_bdd : ∀ x, |f x| ≤ 1)
    (hX_meas : ∀ i, Measurable (X i))
    (α_f : Ω → ℝ) (hα_memLp : MemLp α_f 2 μ)
    (hα_limit : Tendsto (fun n => eLpNorm (blockAvg f X 0 n - α_f) 2 μ) atTop (𝓝 0)) :
    AEStronglyMeasurable[Exchangeability.Tail.tailProcess X] α_f μ := by
  -- PROOF STRATEGY:
  -- 1. For each N, show α_f is AEStronglyMeasurable[tailFamily X N]
  --    (using closedness of L² measurable functions and blockAvg_shift_tendsto)
  -- 2. Apply aestronglyMeasurable_iInf_antitone to descend to the infimum
  --
  -- The key insight: tailFamily X forms an antitone (decreasing) sequence,
  -- and tailSigma X = ⨅ N, tailFamily X N by definition.

  -- Step 1: Show α_f is AEStronglyMeasurable[tailFamily X N] for each N
  have h_aesm_each : ∀ N, AEStronglyMeasurable[Exchangeability.Tail.tailFamily X N] α_f μ := by
    intro N
    -- The block averages starting at N converge to α_f in L²
    -- Each blockAvg f X N m is Measurable[tailFamily X N]
    -- By closedness of L²(tailFamily X N), the limit α_f is also in it

    -- Step 1a: blockAvg f X N m is Measurable[tailFamily X N] for all m
    have h_block_meas : ∀ m, @Measurable Ω ℝ (Exchangeability.Tail.tailFamily X N) _ (blockAvg f X N m) :=
      fun m => blockAvg_measurable_tailFamily hf_meas N m

    -- Step 1b: blockAvg f X N m → α_f in L² (by blockAvg_shift_tendsto)
    have h_L2_conv := blockAvg_shift_tendsto f hf_meas hf_bdd hX_meas α_f hα_memLp hα_limit N

    -- Step 1c: tailFamily X N ≤ ambient σ-algebra (for measure compatibility)
    have h_tf_le : Exchangeability.Tail.tailFamily X N ≤ (inferInstance : MeasurableSpace Ω) := by
      refine iSup_le (fun k => ?_)
      exact MeasurableSpace.comap_le_iff_le_map.mpr (hX_meas (N + k))

    -- Step 1d: Convert L² convergence to convergence in measure
    -- Note: α_f is AEStronglyMeasurable wrt ambient from MemLp
    have h_α_aesm : AEStronglyMeasurable α_f μ := hα_memLp.aestronglyMeasurable
    have h_block_aesm : ∀ m, AEStronglyMeasurable (blockAvg f X N m) μ :=
      fun m => (blockAvg_measurable_tailFamily hf_meas N m).aestronglyMeasurable.mono h_tf_le
    have h_in_measure : TendstoInMeasure μ (blockAvg f X N) atTop α_f :=
      tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) h_block_aesm h_α_aesm h_L2_conv

    -- Step 1e: Extract a.e.-convergent subsequence
    obtain ⟨ns, hns_mono, h_ae_conv⟩ := h_in_measure.exists_seq_tendsto_ae

    -- Step 1f: Apply the sub-σ-algebra measurability lemma
    -- The subsequence blockAvg f X N (ns k) are all Measurable[tailFamily X N]
    -- and converge a.e. to α_f, so α_f is AEStronglyMeasurable[tailFamily X N]
    exact aestronglyMeasurable_sub_of_tendsto_ae h_tf_le (fun k => h_block_meas (ns k)) h_ae_conv

  -- Step 2: Apply the axiom to descend to the infimum
  have h_anti : Antitone (Exchangeability.Tail.tailFamily X) := Exchangeability.Tail.tailFamily_antitone X

  -- Each tailFamily X N ≤ ambient measurable space
  -- This follows from: tailFamily X N = ⨆ k, comap (X (N+k)) _
  -- and comap f ≤ ambient when f is measurable
  have h_le : ∀ N, Exchangeability.Tail.tailFamily X N ≤ (inferInstance : MeasurableSpace Ω) := by
    intro N
    -- tailFamily X N consists of sets measurable wrt X_{N+k} for k ∈ ℕ
    -- Each such set is in the ambient σ-algebra when X_k are measurable
    refine iSup_le (fun k => ?_)
    exact MeasurableSpace.comap_le_iff_le_map.mpr (hX_meas (N + k))

  -- tailSigma X = ⨅ N, tailFamily X N (by definition in TailSigma module)
  have h_eq : Exchangeability.Tail.tailProcess X = ⨅ N, Exchangeability.Tail.tailFamily X N := rfl

  rw [h_eq]
  exact aestronglyMeasurable_iInf_antitone h_anti h_le α_f h_aesm_each

/-- L² convergence implies set integral convergence on probability spaces.
Proof: L² → L¹ on probability spaces (via eLpNorm_le_eLpNorm_of_exponent_le),
then use tendsto_setIntegral_of_L1'. -/
private lemma tendsto_setIntegral_of_L2_tendsto
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {A : Set Ω} (_hA : MeasurableSet A)
    {fn : ℕ → Ω → ℝ} {f : Ω → ℝ}
    (hfn : ∀ n, MemLp (fn n) 2 μ) (hf : MemLp f 2 μ)
    (hL2 : Tendsto (fun n => eLpNorm (fn n - f) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω in A, fn n ω ∂μ) atTop (𝓝 (∫ ω in A, f ω ∂μ)) := by
  -- Step 1: L² → L¹ convergence on probability spaces (‖g‖₁ ≤ ‖g‖₂)
  have h1 : Tendsto (fun n => eLpNorm (fn n - f) 1 μ) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hL2
    · intro n; exact zero_le _
    · intro n
      exact eLpNorm_le_eLpNorm_of_exponent_le one_le_two ((hfn n).sub hf).aestronglyMeasurable
  -- Step 2: Show each fn is integrable
  have hfn_int : ∀ n, Integrable (fn n) μ := fun n => (hfn n).integrable one_le_two
  -- Step 3: Apply tendsto_setIntegral_of_L1'
  exact tendsto_setIntegral_of_L1' f (hf.integrable one_le_two)
    (Filter.univ_mem' hfn_int) h1 A


/-- **Cesàro averages converge in L² to a tail-measurable limit.**

This is the elementary L² route to de Finetti (Kallenberg's "second proof"):
1. L² contractability bound → Cesàro averages are Cauchy in L²
2. Completeness of L² → limit α_f exists
3. Block averages A_{N,n} are σ(X_{>N})-measurable → α_f is tail-measurable
4. Tail measurability + L² limit → α_f = E[f(X_1) | tail σ-algebra]

**No Mean Ergodic Theorem, no martingales** - just elementary L² space theory! -/
lemma cesaro_to_condexp_L2
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} (hX_contract : Exchangeability.Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (f : ℝ → ℝ) (hf_meas : Measurable f) (hf_bdd : ∀ x, |f x| ≤ 1) :
    ∃ (α_f : Ω → ℝ), MemLp α_f 2 μ ∧
      AEStronglyMeasurable[Exchangeability.Tail.tailProcess X] α_f μ ∧
      Tendsto (fun n => eLpNorm (blockAvg f X 0 n - α_f) 2 μ) atTop (𝓝 0) ∧
      α_f =ᵐ[μ] μ[(f ∘ X 0) | Exchangeability.Tail.tailProcess X] := by
  -- Step 1: Show block averages form a Cauchy sequence in L² (via `Cauchy.lean`).
  have hCauchy := blockAvg_cauchy_in_L2 hX_contract hX_meas f hf_meas hf_bdd

  -- Step 2: Extract L² limit using completeness of Hilbert space
  -- Lp(2, μ) is complete (Hilbert space), so Cauchy sequence converges
  have ⟨α_f, hα_memLp, hα_limit⟩ : ∃ α_f, MemLp α_f 2 μ ∧
      Tendsto (fun n => eLpNorm (blockAvg f X 0 n - α_f) 2 μ) atTop (𝓝 0) := by
    -- Apply cauchy_complete_eLpNorm to get L² limit

    -- Step 1: Show each blockAvg is in L²
    have hblockAvg_memLp_all : ∀ n, MemLp (blockAvg f X 0 n) 2 μ := fun n =>
      blockAvg_memLp_two_of_abs_le_one f X hf_meas hX_meas hf_bdd 0 n
    have hblockAvg_memLp : ∀ n, n > 0 → MemLp (blockAvg f X 0 n) 2 μ :=
      fun n _ => hblockAvg_memLp_all n

    -- Extract L² limit from the Cauchy sequence by completeness of `Lp ℝ 2 μ`.

    -- Step 1: Define sequence in L² space
    let u : ℕ → Lp ℝ 2 μ := fun n =>
      if hn : n > 0 then
        (hblockAvg_memLp n hn).toLp (blockAvg f X 0 n)
      else
        0  -- n = 0 case

    -- Step 2: Prove sequence is Cauchy
    -- Use the simpler approach: dist = norm = eLpNorm.toReal
    have hCauchySeq : CauchySeq u := by
      rw [Metric.cauchySeq_iff]
      intro ε hε
      obtain ⟨N, hN⟩ := hCauchy (ENNReal.ofReal ε) (by simp [hε])
      use max N 1  -- Ensure N is at least 1
      intro n hn m hm
      -- For n, m ≥ max N 1, both are > 0, so we can unfold u
      have hn_pos : n > 0 := Nat.lt_of_lt_of_le (Nat.zero_lt_one) (Nat.le_trans (Nat.le_max_right N 1) hn)
      have hm_pos : m > 0 := Nat.lt_of_lt_of_le (Nat.zero_lt_one) (Nat.le_trans (Nat.le_max_right N 1) hm)
      have hn' : n ≥ N := Nat.le_trans (Nat.le_max_left N 1) hn
      have hm' : m ≥ N := Nat.le_trans (Nat.le_max_left N 1) hm
      simp only [u, dif_pos hn_pos, dif_pos hm_pos]
      -- Use dist = (eLpNorm ...).toReal and the fact that toLp preserves eLpNorm
      rw [dist_comm, dist_eq_norm, Lp.norm_def]
      -- Now goal is: eLpNorm (toLp m - toLp n) 2 μ).toReal < ε
      -- Use MemLp.toLp_sub to rewrite the difference
      rw [← (hblockAvg_memLp m hm_pos).toLp_sub (hblockAvg_memLp n hn_pos)]
      -- Now: (eLpNorm (coeFn (toLp (blockAvg m - blockAvg n))) 2 μ).toReal < ε
      -- coeFn of toLp is ae-equal to original, so eLpNorms are equal
      rw [eLpNorm_congr_ae (((hblockAvg_memLp m hm_pos).sub (hblockAvg_memLp n hn_pos)).coeFn_toLp)]
      -- Now: (eLpNorm (blockAvg m - blockAvg n) 2 μ).toReal < ε
      -- Use toReal_lt_of_lt_ofReal: if a < ofReal b then a.toReal < b
      exact ENNReal.toReal_lt_of_lt_ofReal (hN hm' hn')

    -- Step 3: Extract limit from completeness
    haveI : CompleteSpace (Lp ℝ 2 μ) := by infer_instance
    obtain ⟨α_L2, h_tendsto⟩ := cauchySeq_tendsto_of_complete hCauchySeq

    -- Step 4: Extract representative function
    -- α_L2 : Lp ℝ 2 μ is an ae-equivalence class
    -- In Lean 4, Lp coerces to a function type automatically
    let α_f : Ω → ℝ := α_L2

    -- Properties of α_f (using theorems, not fields)
    have hα_meas : StronglyMeasurable α_f := Lp.stronglyMeasurable α_L2
    have hα_memLp : MemLp α_f 2 μ := Lp.memLp α_L2

    have hα_limit : Tendsto (fun n => eLpNorm (blockAvg f X 0 n - α_f) 2 μ) atTop (𝓝 0) := by
      -- Use Lp.tendsto_Lp_iff_tendsto_eLpNorm': Tendsto f (𝓝 f_lim) ↔ Tendsto (eLpNorm (f - f_lim)) (𝓝 0)
      -- h_tendsto : Tendsto u atTop (𝓝 α_L2)
      rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'] at h_tendsto
      -- h_tendsto : Tendsto (fun n => eLpNorm (↑(u n) - ↑α_L2) 2 μ) atTop (𝓝 0)
      -- Need to show this equals eLpNorm (blockAvg n - α_f) eventually
      refine h_tendsto.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hn_pos : n > 0 := Nat.zero_lt_of_lt hn
      simp only [u, dif_pos hn_pos, α_f]
      -- Show: eLpNorm (↑(toLp (blockAvg n)) - ↑α_L2) 2 μ = eLpNorm (blockAvg n - ↑↑α_L2) 2 μ
      refine eLpNorm_congr_ae ?_
      filter_upwards [(hblockAvg_memLp n hn_pos).coeFn_toLp] with ω hω
      simp only [Pi.sub_apply, hω]

    -- Close the existential proof
    use α_f, hα_memLp, hα_limit

  -- Now α_f, hα_memLp, and hα_limit are in scope from the pattern match
  -- Provide the witness and the 4-tuple of proofs
  use α_f
  refine ⟨hα_memLp, ?_, hα_limit, ?_⟩

  -- Step 3: Show α_f is tail-measurable
  -- Use condexpL2 projection approach: α_L2 is fixed by projection ⟹ tail-measurable
  · -- Tail measurability via continuous projection — see
    -- `tail_measurability_of_blockAvg` above for the closed-subspace argument.
    exact tail_measurability_of_blockAvg f hf_meas hf_bdd hX_meas α_f hα_memLp hα_limit

  -- Step 4: Identify α_f = E[f(X_1)|tail] using tail-event integrals
  -- For any tail event A:
  --   E[f(X_1) 1_A] = E[f(X_j) 1_A] for any j (by exchangeability + tail invariance)
  --                 = lim_{n→∞} (1/n) ∑ E[f(X_j) 1_A] (average over large block)
  --                 = lim_{n→∞} E[A_{0,n} 1_A] (by linearity)
  --                 = E[α_f 1_A] (by L² convergence)
  -- Therefore α_f is the conditional expectation
  · -- Identification as conditional expectation
    -- The key relationship: Exchangeability.Tail.tailProcess X = tailProcess X
    -- This follows from the re-export in BlockAverages.lean

    -- Step 1: Sub-σ-algebra condition
    have hm : Exchangeability.Tail.tailProcess X ≤ (inferInstance : MeasurableSpace Ω) :=
      Exchangeability.Tail.tailProcess_le_ambient X hX_meas

    -- Step 2: SigmaFinite for trimmed measure (automatic for probability measures)
    haveI h_finite : IsFiniteMeasure (μ.trim hm) := by
      constructor
      rw [trim_measurableSet_eq hm MeasurableSet.univ]
      exact measure_lt_top μ Set.univ
    haveI : SigmaFinite (μ.trim hm) := @IsFiniteMeasure.toSigmaFinite _ _ _ h_finite

    -- Step 3: Integrability of f ∘ X 0 (bounded function on probability space)
    have hfX0_int : Integrable (f ∘ X 0) μ := by
      -- Bounded functions on probability spaces are integrable
      have h_memLp2 : MemLp (f ∘ X 0) 2 μ := by
        apply MemLp.of_bound (hf_meas.comp (hX_meas 0)).aestronglyMeasurable 1
        filter_upwards with ω
        simp only [Real.norm_eq_abs, Function.comp_apply]
        exact hf_bdd (X 0 ω)
      -- MemLp 2 → MemLp 1 on probability spaces (since 1 ≤ 2)
      have h_memLp1 : MemLp (f ∘ X 0) 1 μ := h_memLp2.mono_exponent one_le_two
      exact memLp_one_iff_integrable.mp h_memLp1

    -- Apply uniqueness lemma: ae_eq_condExp_of_forall_setIntegral_eq
    -- This shows α_f = condExp if they have equal set integrals and α_f is tail-measurable
    apply ae_eq_condExp_of_forall_setIntegral_eq hm hfX0_int

    -- Condition 1: α_f is integrable on finite-measure tail sets
    · intro s hs hμs
      exact (hα_memLp.integrable one_le_two).integrableOn

    -- Condition 2: Set integrals are equal
    · intro A hA hμA
      -- Convert MeasurableSet from Exchangeability.Tail.tailProcess to tailProcess
      -- (They are definitionally equal via the re-export in BlockAverages.lean)
      have hA_tail : MeasurableSet[Exchangeability.Tail.tailProcess X] A := hA

      -- Step (a): Show ∫_A f(X k) = ∫_A f(X 0) for all k using setIntegral_comp_shift_eq
      have h_shift_eq : ∀ k, ∫ ω in A, f (X k ω) ∂μ = ∫ ω in A, f (X 0 ω) ∂μ :=
        fun k => Exchangeability.Tail.ShiftInvariance.setIntegral_comp_shift_eq X hX_contract hX_meas f hf_meas hA_tail hfX0_int k

      -- Step (b): Show ∫_A blockAvg n = ∫_A f(X 0) for all n > 0
      -- blockAvg f X 0 n ω = (1/n) * ∑ k : Fin n, f (X k ω)
      -- By linearity: ∫_A (1/n * ∑ f(X k)) = (1/n) * ∑ ∫_A f(X k) = (1/n) * n * ∫_A f(X 0) = ∫_A f(X 0)
      have h_blockAvg_eq : ∀ n > 0, ∫ ω in A, blockAvg f X 0 n ω ∂μ = ∫ ω in A, f (X 0 ω) ∂μ := by
        intro n hn
        -- Each f ∘ X k is integrable (bounded function on probability space)
        have hfXk_int : ∀ k, Integrable (fun ω => f (X k ω)) μ := fun k => by
          have h_memLp2 : MemLp (fun ω => f (X k ω)) 2 μ := by
            apply MemLp.of_bound (hf_meas.comp (hX_meas k)).aestronglyMeasurable 1
            filter_upwards with ω
            simp only [Real.norm_eq_abs]
            exact hf_bdd (X k ω)
          exact (h_memLp2.mono_exponent one_le_two).integrable le_rfl
        -- Unfold blockAvg: blockAvg f X 0 n ω = (n:ℝ)⁻¹ * ∑_{k∈range n} f(X (0+k) ω)
        -- For m = 0, this is (n:ℝ)⁻¹ * ∑_{k∈range n} f(X k ω)
        simp only [blockAvg, zero_add]
        -- Rewrite using scalar multiplication
        have h_scalar : ∫ ω in A, (↑n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, f (X k ω) ∂μ =
            (↑n : ℝ)⁻¹ * ∫ ω in A, ∑ k ∈ Finset.range n, f (X k ω) ∂μ := by
          simp_rw [← smul_eq_mul]
          exact MeasureTheory.integral_smul _ _
        rw [h_scalar]
        -- Sum pullout: ∫_A (∑ ...) = ∑ ∫_A ...
        rw [MeasureTheory.integral_finset_sum _ (fun k _ => (hfXk_int k).integrableOn.integrable)]
        -- Apply shift invariance: ∑ ∫_A f(X k) = ∑ ∫_A f(X 0) = n * ∫_A f(X 0)
        simp_rw [h_shift_eq]
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        -- Simplify: n⁻¹ * (n * ∫_A f(X 0)) = ∫_A f(X 0) (since n > 0)
        field_simp

      -- Step (c): Show ∫_A blockAvg n → ∫_A α_f using L² convergence
      -- Use Hölder: |∫_A (g - h)| ≤ μ(A)^(1/2) * ‖g - h‖₂
      -- L² convergence + bounded measure gives set integral convergence
      have h_setInt_tendsto : Tendsto (fun n => ∫ ω in A, blockAvg f X 0 n ω ∂μ)
          atTop (𝓝 (∫ ω in A, α_f ω ∂μ)) := by
        have h_blockAvg_memLp : ∀ n, MemLp (blockAvg f X 0 n) 2 μ := fun n =>
          blockAvg_memLp_two_of_abs_le_one f X hf_meas hX_meas hf_bdd 0 n
        have hA_meas : MeasurableSet A := hm A hA
        exact tendsto_setIntegral_of_L2_tendsto hA_meas h_blockAvg_memLp hα_memLp hα_limit

      -- Step (d): Combine: constant sequence converges to unique limit
      -- From (b): the sequence ∫_A blockAvg n is eventually constant at ∫_A f(X 0)
      -- From (c): it converges to ∫_A α_f
      -- Therefore ∫_A α_f = ∫_A f(X 0)
      have h_const : ∀ᶠ n in atTop, ∫ ω in A, blockAvg f X 0 n ω ∂μ = ∫ ω in A, f (X 0 ω) ∂μ := by
        filter_upwards [eventually_gt_atTop 0] with n hn
        exact h_blockAvg_eq n hn
      -- The limit of an eventually constant sequence equals that constant
      have h_lim_eq_const : Tendsto (fun n => ∫ ω in A, blockAvg f X 0 n ω ∂μ)
          atTop (𝓝 (∫ ω in A, f (X 0 ω) ∂μ)) := by
        apply tendsto_const_nhds.congr'
        filter_upwards [h_const] with n hn
        exact hn.symm
      exact tendsto_nhds_unique h_setInt_tendsto h_lim_eq_const

    -- Condition 3: α_f is tail-measurable
    · exact tail_measurability_of_blockAvg f hf_meas hf_bdd hX_meas α_f hα_memLp hα_limit

end Exchangeability.DeFinetti.ViaL2
