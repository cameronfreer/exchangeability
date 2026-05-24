/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Exchangeability.DeFinetti.ViaL2.AlphaIicCE
import Exchangeability.DeFinetti.ViaL2.CesaroConvergence.L1

/-!
# Identification of `alphaIic` with `alphaIicCE`

`alphaIic` (the raw existential L¹ limit) and `alphaIicCE` (the canonical
`condExp`-based form) are almost everywhere equal. Both are L¹ limits of the
same Cesàro averages, so uniqueness of L¹ limits gives a.e. equality.

## Main result

* `alphaIic_ae_eq_alphaIicCE`: `alphaIic =ᵐ[μ] alphaIicCE`.

## References

* Kallenberg (2005), *Probabilistic Symmetries and Invariance Principles*,
  Chapter 1, "Second proof of Theorem 1.1"
-/

noncomputable section

namespace Exchangeability.DeFinetti.ViaL2

open MeasureTheory ProbabilityTheory BigOperators Filter Topology
open Exchangeability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- **Identification lemma**: alphaIic equals alphaIicCE almost everywhere.

**Proof strategy:**
Both are L¹ limits of the same Cesàro averages `(1/m) ∑ᵢ (indIic t) ∘ X_{n+i}`:
- `alphaIic` is defined as the L¹ limit from `weighted_sums_converge_L1`
- `alphaIicCE` is the conditional expectation `μ[(indIic t) ∘ X_0 | tailSigma X]`

By the reverse martingale convergence theorem (or direct L² analysis), the Cesàro averages
converge in L² (hence L¹) to the conditional expectation. Since L¹ limits are unique up
to a.e. equality, we get `alphaIic =ᵐ alphaIicCE`.

Note: Uses reverse martingale convergence or L² projection argument. -/
lemma alphaIic_ae_eq_alphaIicCE
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ)
    (t : ℝ) :
    alphaIic X hX_contract hX_meas hX_L2 t
      =ᵐ[μ] alphaIicCE X hX_contract hX_meas hX_L2 t := by
  -- Proof strategy: Both are L¹ limits of the same Cesàro averages, so they're equal a.e.

  -- Define the Cesàro averages
  let A : ℕ → ℕ → Ω → ℝ := fun n m ω =>
    (1 / (m : ℝ)) * ∑ k : Fin m, indIic t (X (n + k.val + 1) ω)

  -- Step 1: alphaIic is (essentially) the L¹ limit of these averages by construction
  have h_alphaIic_is_limit : ∀ n, ∀ ε > 0, ∃ M : ℕ, ∀ m ≥ M,
      ∫ ω, |A n m ω - alphaIic X hX_contract hX_meas hX_L2 t ω| ∂μ < ε := by
    intro n ε hε
    -- By definition, alphaIic is max 0 (min 1 (witness from weighted_sums_converge_L1))
    -- The witness satisfies the L¹ convergence property
    unfold alphaIic

    -- Get the witness alpha from weighted_sums_converge_L1
    let alpha := (weighted_sums_converge_L1 X hX_contract hX_meas hX_L2
                    (indIic t) (indIic_measurable t) ⟨1, indIic_bdd t⟩).choose
    have h_alpha_conv := (weighted_sums_converge_L1 X hX_contract hX_meas hX_L2
                    (indIic t) (indIic_measurable t) ⟨1, indIic_bdd t⟩).choose_spec.2.2

    -- Use L¹ convergence of A n m to alpha
    obtain ⟨M, hM⟩ := h_alpha_conv n ε hε
    use M
    intro m hm

    -- Strategy: Show A n m is already in [0,1], so clipping doesn't change it
    -- A n m = (1/m) * ∑ indIic, and each indIic ∈ {0,1}, so A n m ∈ [0,1]
    have hA_in_01 : ∀ ω, 0 ≤ A n m ω ∧ A n m ω ≤ 1 := by
      intro ω
      unfold A
      constructor
      · -- 0 ≤ A
        apply mul_nonneg
        · positivity
        · apply Finset.sum_nonneg
          intro k _
          unfold indIic
          simp [Set.indicator]
          split_ifs <;> norm_num
      · -- A ≤ 1
        by_cases hm_pos : m = 0
        · simp [hm_pos]
        · have hm_cast : 0 < (m : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm_pos)
          calc (1 / (m : ℝ)) * ∑ k : Fin m, indIic t (X (n + ↑k + 1) ω)
              ≤ (1 / (m : ℝ)) * ∑ k : Fin m, (1 : ℝ) := by
                apply mul_le_mul_of_nonneg_left _ (by positivity)
                apply Finset.sum_le_sum
                intro k _
                unfold indIic
                simp [Set.indicator]
                split_ifs <;> norm_num
            _ = (1 / (m : ℝ)) * m := by simp
            _ = 1 := by field_simp [hm_cast.ne']

    -- Since A n m ∈ [0,1], we have max 0 (min 1 (A n m)) = A n m
    have hA_clip_eq : ∀ ω, max 0 (min 1 (A n m ω)) = A n m ω := by
      intro ω
      obtain ⟨h0, h1⟩ := hA_in_01 ω
      rw [min_comm, min_eq_left h1, max_eq_right h0]

    -- Use the fact that clipping can only make things closer when A n m ∈ [0,1]
    -- Since A n m ∈ [0,1], we have |A - clip(alpha)| ≤ |A - alpha| for all alpha
    have h_clip_le : ∀ ω, |A n m ω - max 0 (min 1 (alpha ω))| ≤ |A n m ω - alpha ω| := by
      intro ω
      obtain ⟨hA0, hA1⟩ := hA_in_01 ω
      by_cases halpha : alpha ω < 0
      · calc |A n m ω - max 0 (min 1 (alpha ω))|
            = |A n m ω - max 0 (alpha ω)| := by rw [min_eq_right (by linarith : alpha ω ≤ 1)]
          _ = |A n m ω - 0| := by rw [max_eq_left (by linarith : 0 ≥ alpha ω)]
          _ = A n m ω := by rw [sub_zero, abs_of_nonneg hA0]
          _ ≤ A n m ω - alpha ω := by linarith
          _ ≤ |A n m ω - alpha ω| := le_abs_self _
      · by_cases halpha1 : 1 < alpha ω
        · calc |A n m ω - max 0 (min 1 (alpha ω))|
              = |A n m ω - max 0 1| := by rw [min_eq_left (by linarith : 1 ≤ alpha ω)]
            _ = |A n m ω - 1| := by rw [max_eq_right (by linarith : (0 : ℝ) ≤ 1)]
            _ = 1 - A n m ω := by
                rw [abs_of_nonpos (by linarith : A n m ω - 1 ≤ 0)]
                ring
            _ ≤ alpha ω - A n m ω := by linarith
            _ ≤ |A n m ω - alpha ω| := by rw [abs_sub_comm]; exact le_abs_self _
        · -- alpha ∈ [0,1], so clipping does nothing
          push Not at halpha halpha1
          rw [min_comm, min_eq_left halpha1, max_eq_right halpha]

    -- Prove integrability of A n m
    have hA_int : Integrable (A n m) μ := by
      have hA_meas_nm : Measurable (A n m) := by fun_prop
      refine Integrable.of_bound hA_meas_nm.aestronglyMeasurable 1 ?_
      filter_upwards with ω
      unfold A
      simp only [Real.norm_eq_abs]
      by_cases hm : m = 0
      · simp [hm]
      · have hm_pos : 0 < (m : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm)
        calc |(1/(m:ℝ)) * ∑ k : Fin m, indIic t (X (n + k.val + 1) ω)|
            = (1/(m:ℝ)) * |∑ k : Fin m, indIic t (X (n + k.val + 1) ω)| := by
                rw [abs_mul, abs_of_pos (one_div_pos.mpr hm_pos)]
          _ ≤ (1/(m:ℝ)) * ∑ k : Fin m, |indIic t (X (n + k.val + 1) ω)| := by
                gcongr; exact Finset.abs_sum_le_sum_abs _ _
          _ ≤ (1/(m:ℝ)) * ∑ k : Fin m, (1 : ℝ) := by
                gcongr with k
                unfold indIic; simp [Set.indicator]; split_ifs <;> norm_num
          _ = (1/(m:ℝ)) * m := by simp [Finset.sum_const]
          _ = 1 := by field_simp [hm]

    -- Prove integrability of alpha (from weighted_sums_converge_L1)
    have halpha_meas : Measurable alpha :=
      (weighted_sums_converge_L1 X hX_contract hX_meas hX_L2
        (indIic t) (indIic_measurable t) ⟨1, indIic_bdd t⟩).choose_spec.1
    have h_alpha_memLp : MemLp alpha 1 μ :=
      (weighted_sums_converge_L1 X hX_contract hX_meas hX_L2
        (indIic t) (indIic_measurable t) ⟨1, indIic_bdd t⟩).choose_spec.2.1
    have halpha_int : Integrable alpha μ := memLp_one_iff_integrable.mp h_alpha_memLp

    calc ∫ ω, |A n m ω - max 0 (min 1 (alpha ω))| ∂μ
        ≤ ∫ ω, |A n m ω - alpha ω| ∂μ := by
          apply integral_mono_ae
          · apply Integrable.abs
            apply Integrable.sub hA_int
            have : Measurable (fun ω => max 0 (min 1 (alpha ω))) :=
              Measurable.max measurable_const (Measurable.min measurable_const halpha_meas)
            apply Integrable.of_bound this.aestronglyMeasurable 1
            filter_upwards with ω
            simp [Real.norm_eq_abs]
            -- max 0 (min 1 x) is always in [0,1]
            by_cases h : alpha ω ≤ 0
            · rw [min_eq_right (by linarith : alpha ω ≤ 1), max_eq_left h, abs_zero]
              norm_num
            · by_cases h1 : 1 ≤ alpha ω
              · rw [min_eq_left h1, max_eq_right (by linarith : 0 ≤ (1:ℝ)), abs_of_nonneg (by linarith : 0 ≤ (1:ℝ))]
              · push Not at h h1
                rw [min_eq_right (le_of_lt h1), max_eq_right (le_of_lt h)]
                exact abs_of_pos h |>.trans_le (le_of_lt h1)
          · exact (hA_int.sub halpha_int).abs
          · filter_upwards with ω; exact h_clip_le ω
      _ < ε := hM m hm

  -- Step 2: alphaIicCE is also the L¹ limit of the same averages (at n=0)
  -- This is the reverse martingale convergence theorem / ergodic theorem
  -- Note: We only need n=0 for the uniqueness argument below
  have h_alphaIicCE_is_limit : ∀ ε > 0, ∃ M : ℕ, ∀ m ≥ M,
      ∫ ω, |A 0 m ω - alphaIicCE X hX_contract hX_meas hX_L2 t ω| ∂μ < ε := by
    intro ε hε

    -- Strategy: Use asymptotic negligibility
    -- A 0 m uses X(k+1) for k ∈ {0,...,m-1}, i.e., X_1,...,X_m
    -- cesaro_to_condexp_L1 uses X(k) for k ∈ {0,...,m-1}, i.e., X_0,...,X_{m-1}

    unfold A alphaIicCE
    simp only [zero_add]

    -- Define the "standard" Cesàro average (matching axiom indexing)
    let B : ℕ → Ω → ℝ := fun m ω => (1 / (m : ℝ)) * ∑ i : Fin m, indIic t (X i ω)

    -- Apply cesaro_to_condexp_L1 for B
    have hε_half : ε/2 > 0 := by linarith
    have h_axiom : ∃ (M : ℕ), ∀ (m : ℕ), m ≥ M →
        ∫ ω, |(1 / (m : ℝ)) * ∑ i : Fin m, indIic t (X i ω) -
              (μ[(indIic t ∘ X 0) | TailSigma.tailSigma X] ω)| ∂μ < ε/2 :=
      cesaro_to_condexp_L1 hX_contract hX_meas (indIic t) (indIic_measurable t) (indIic_bdd t) (ε/2) hε_half
    obtain ⟨M₁, hM₁⟩ := h_axiom

    -- The difference between A 0 m and B m is O(1/m)
    -- A 0 m = (1/m)[f(X₁) + ... + f(Xₘ)]
    -- B m   = (1/m)[f(X₀) + ... + f(X_{m-1})]
    -- Diff  = (1/m)[f(Xₘ) - f(X₀)]

    have h_diff_small : ∀ m : ℕ, m > 0 →
        ∫ ω, |(1/(m:ℝ)) * ∑ k : Fin m, indIic t (X (k.val + 1) ω) - B m ω| ∂μ ≤ 2/(m:ℝ) := by
      intro m hm_pos
      -- Unfold B and simplify
      simp only [B]

      -- The difference telescopes: (1/m)[∑ f(X(k+1)) - ∑ f(X(k))] = (1/m)[f(Xₘ) - f(X₀)]
      -- We'll bound this by (1/m)[|f(Xₘ)| + |f(X₀)|] ≤ 2/m

      have h_telescope : ∀ ω,
          |(1/(m:ℝ)) * ∑ k : Fin m, indIic t (X (k.val + 1) ω) -
           (1/(m:ℝ)) * ∑ i : Fin m, indIic t (X i ω)|
          = |(1/(m:ℝ)) * (indIic t (X m ω) - indIic t (X 0 ω))| := by
        intro ω
        congr 1
        -- After congr 1, goal is the argument to | · |
        rw [←mul_sub]
        congr 1
        -- Now goal is: ∑ k, f(k+1) - ∑ i, f(i) = f(m) - f(0)

        -- The key telescoping identity:
        -- ∑_{k<m} f(X(k+1)) - ∑_{i<m} f(X i) = f(Xₘ) - f(X₀)
        --
        -- Proof: Left sum  = f(X₁) + f(X₂) + ... + f(Xₘ)
        --        Right sum = f(X₀) + f(X₁) + ... + f(X_{m-1})
        --        Middle terms cancel, leaving f(Xₘ) - f(X₀)

        -- First convert Fin m sums to range sums for easier manipulation
        -- Use Fin.sum_univ_eq_sum_range: ∑ i : Fin m, f ↑i = ∑ i ∈ range m, f i
        -- Note: k.val and ↑k are definitionally equal for Fin
        have h_left : ∑ k : Fin m, indIic t (X (k.val + 1) ω) =
                      (Finset.range m).sum (fun k => indIic t (X (k + 1) ω)) :=
          Fin.sum_univ_eq_sum_range (fun k => indIic t (X (k + 1) ω)) m
        have h_right : ∑ i : Fin m, indIic t (X i ω) =
                       (Finset.range m).sum (fun i => indIic t (X i ω)) :=
          Fin.sum_univ_eq_sum_range (fun i => indIic t (X i ω)) m

        -- Prove telescoping: ∑_{k<m} f(k+1) - ∑_{i<m} f(i) = f(m) - f(0)
        have h_telescope_sum : (Finset.range m).sum (fun k => indIic t (X (k + 1) ω)) -
                                (Finset.range m).sum (fun i => indIic t (X i ω)) =
                                indIic t (X m ω) - indIic t (X 0 ω) := by
          clear h_left h_right hm_pos -- Don't use outer context
          induction m with
          | zero => simp
          | succ m' ih =>
              rw [Finset.sum_range_succ (f := fun k => indIic t (X (k + 1) ω))]
              rw [Finset.sum_range_succ (f := fun i => indIic t (X i ω))]
              --  Goal: (∑ x < m', f(x+1)) + f(m'+1) - ((∑ x < m', f(x)) + f(m')) = f(m'+1) - f(0)
              -- Simplify LHS algebraically to expose the IH pattern
              have : (∑ x ∈ Finset.range m', indIic t (X (x + 1) ω)) + indIic t (X (m' + 1) ω) -
                     ((∑ x ∈ Finset.range m', indIic t (X x ω)) + indIic t (X m' ω))
                   = (∑ x ∈ Finset.range m', indIic t (X (x + 1) ω)) - (∑ x ∈ Finset.range m', indIic t (X x ω))
                     + (indIic t (X (m' + 1) ω) - indIic t (X m' ω)) := by ring
              rw [this, ih]
              ring

        -- Now apply to our goal: ∑ k : Fin m, f(k+1) - ∑ i : Fin m, f(i) = f(m) - f(0)
        -- Use h_left and h_right to convert Fin sums to range sums, then apply h_telescope_sum
        rw [h_left, h_right]
        exact h_telescope_sum

      -- Integrability facts needed throughout the calc chain
      have hf_int : Integrable (indIic t ∘ X m) μ := by
        apply Integrable.of_bound ((indIic_measurable t).comp (hX_meas m) |>.aestronglyMeasurable) 1
        filter_upwards with x; unfold indIic; simp [Set.indicator]; split_ifs <;> norm_num
      have hg_int : Integrable (indIic t ∘ X 0) μ := by
        apply Integrable.of_bound ((indIic_measurable t).comp (hX_meas 0) |>.aestronglyMeasurable) 1
        filter_upwards with x; unfold indIic; simp [Set.indicator]; split_ifs <;> norm_num

      calc ∫ ω, |(1/(m:ℝ)) * ∑ k : Fin m, indIic t (X (k.val + 1) ω) -
                 (1/(m:ℝ)) * ∑ i : Fin m, indIic t (X i ω)| ∂μ
          = ∫ ω, |(1/(m:ℝ)) * (indIic t (X m ω) - indIic t (X 0 ω))| ∂μ := by
              congr 1; ext ω; exact h_telescope ω
        _ = ∫ ω, (1/(m:ℝ)) * |indIic t (X m ω) - indIic t (X 0 ω)| ∂μ := by
              congr 1; ext ω
              have hm_pos' : 0 < (m : ℝ) := Nat.cast_pos.mpr hm_pos
              rw [abs_mul, abs_of_pos (one_div_pos.mpr hm_pos')]
        _ = (1/(m:ℝ)) * ∫ ω, |indIic t (X m ω) - indIic t (X 0 ω)| ∂μ := by
              rw [integral_const_mul]
        _ ≤ (1/(m:ℝ)) * ∫ ω, |indIic t (X m ω)| + |indIic t (X 0 ω)| ∂μ := by
              gcongr
              -- gcongr creates 3 goals: integrability of LHS, RHS, and pointwise inequality
              · -- Integrable (fun x => |f x - g x|)
                exact Integrable.abs (Integrable.sub hf_int hg_int)
              · -- Integrable (fun x => |f x| + |g x|)
                exact Integrable.add (Integrable.abs hf_int) (Integrable.abs hg_int)
              · -- Pointwise: |f x - g x| ≤ |f x| + |g x|
                intro ω
                exact abs_sub (indIic t (X m ω)) (indIic t (X 0 ω))
        _ = (1/(m:ℝ)) * (∫ ω, |indIic t (X m ω)| ∂μ + ∫ ω, |indIic t (X 0 ω)| ∂μ) := by
              congr 1
              exact integral_add (Integrable.abs hf_int) (Integrable.abs hg_int)
        _ ≤ (1/(m:ℝ)) * (1 + 1) := by
              gcongr
              · -- ∫ |indIic t (X m)| ≤ 1
                have : ∫ ω, |indIic t (X m ω)| ∂μ ≤ ∫ ω, (1 : ℝ) ∂μ := by
                  refine integral_mono (Integrable.abs hf_int) (integrable_const 1) ?_
                  intro ω
                  unfold indIic; simp [Set.indicator]; split_ifs <;> norm_num
                calc ∫ ω, |indIic t (X m ω)| ∂μ
                    ≤ ∫ ω, (1 : ℝ) ∂μ := this
                  _ = 1 := by simp
              · -- ∫ |indIic t (X 0)| ≤ 1
                have : ∫ ω, |indIic t (X 0 ω)| ∂μ ≤ ∫ ω, (1 : ℝ) ∂μ := by
                  refine integral_mono (Integrable.abs hg_int) (integrable_const 1) ?_
                  intro ω
                  unfold indIic; simp [Set.indicator]; split_ifs <;> norm_num
                calc ∫ ω, |indIic t (X 0 ω)| ∂μ
                    ≤ ∫ ω, (1 : ℝ) ∂μ := this
                  _ = 1 := by simp
        _ = 2/(m:ℝ) := by ring

    -- Choose M large enough for both axiom and negligibility
    -- M₁: ensures ∫ |B m - target| < ε/2 (from axiom)
    -- ⌈4/ε⌉: ensures 2/m ≤ ε/2 (from negligibility)
    use max M₁ (Nat.ceil (4/ε))
    intro m hm

    -- Triangle inequality: ∫ |A 0 m - target| ≤ ∫ |A 0 m - B m| + ∫ |B m - target|
    -- We need to show: ∫ |A 0 m - μ[indIic t ∘ X 0|tail]| < ε
    -- We have:
    --   1. ∫ |A 0 m - B m| ≤ 2/m (from h_diff_small)
    --   2. ∫ |B m - μ[indIic t ∘ X 0|tail]| < ε/2 (from h_axiom/hM₁)

    have h1 : (m : ℝ) ≥ M₁ := by
      calc (m : ℝ)
          ≥ max M₁ (Nat.ceil (4/ε)) := Nat.cast_le.mpr hm
        _ ≥ M₁ := by
            have : max (M₁ : ℝ) (Nat.ceil (4/ε) : ℝ) ≥ M₁ := le_max_left _ _
            simp [Nat.cast_max]

    have h2 : (m : ℝ) ≥ Nat.ceil (4/ε) := by
      calc (m : ℝ)
          ≥ max M₁ (Nat.ceil (4/ε)) := Nat.cast_le.mpr hm
        _ ≥ Nat.ceil (4/ε) := by
            have : max (M₁ : ℝ) (Nat.ceil (4/ε) : ℝ) ≥ Nat.ceil (4/ε) := le_max_right _ _
            simp [Nat.cast_max]

    -- From h2, we get 2/m ≤ ε/2
    have h_small : 2/(m:ℝ) ≤ ε/2 := by
      have hm_pos'' : 0 < (m : ℝ) := by
        calc (m : ℝ)
            ≥ Nat.ceil (4/ε) := h2
          _ > 0 := Nat.cast_pos.mpr (Nat.ceil_pos.mpr (by positivity))
      have : (m : ℝ) ≥ 4/ε := by
        calc (m : ℝ)
            ≥ Nat.ceil (4/ε) := h2
          _ ≥ 4/ε := Nat.le_ceil _
      calc 2/(m:ℝ)
          ≤ 2/(4/ε) := by gcongr
        _ = ε/2 := by field_simp; ring

    -- Apply the axiom
    have hB_conv : ∫ ω, |B m ω - μ[indIic t ∘ X 0|TailSigma.tailSigma X] ω| ∂μ < ε/2 := by
      convert hM₁ m (Nat.cast_le.mp h1) using 2

    -- Apply h_diff_small
    have hm_pos' : m > 0 := Nat.pos_of_ne_zero (by
      intro h
      simp [h] at h2
      have : (4 : ℝ) / ε > 0 := by positivity
      linarith)
    have hAB_diff : ∫ ω, |(1/(m:ℝ)) * ∑ k : Fin m, indIic t (X (k.val + 1) ω) - B m ω| ∂μ ≤ 2/(m:ℝ) :=
      h_diff_small m hm_pos'

    -- Factor out the integrability of the shifted Cesàro average (used 3× below).
    have hA_int :
        Integrable (fun ω => (1/(m:ℝ)) * ∑ k : Fin m, indIic t (X (k.val + 1) ω)) μ := by
      have h_meas : Measurable (fun ω => (1/(m:ℝ)) * ∑ k : Fin m, indIic t (X (k.val + 1) ω)) :=
        Measurable.const_mul (Finset.measurable_sum _ (fun k _ =>
          ((indIic_measurable t).comp (hX_meas _)))) _
      apply Integrable.of_bound h_meas.aestronglyMeasurable 1
      filter_upwards with ω
      simp [Real.norm_eq_abs]
      calc (m:ℝ)⁻¹ * |∑ k : Fin m, indIic t (X (k.val + 1) ω)|
        _ ≤ (m:ℝ)⁻¹ * ∑ k : Fin m, |indIic t (X (k.val + 1) ω)| := by
              gcongr; exact Finset.abs_sum_le_sum_abs _ _
        _ ≤ (m:ℝ)⁻¹ * ∑ k : Fin m, (1 : ℝ) := by
              gcongr with k
              unfold indIic; simp [Set.indicator]; split_ifs <;> norm_num
        _ = (1/(m:ℝ)) * m := by
              rw [← one_div]; simp [Finset.sum_const]
        _ = 1 := by field_simp

    -- Factor out the integrability of B m (used 4× below).
    have hB_int : Integrable (B m) μ := by
      simp only [B]
      have h_meas : Measurable (fun ω => (1/(m:ℝ)) * ∑ i : Fin m, indIic t (X i ω)) :=
        Measurable.const_mul (Finset.measurable_sum _ (fun i _ =>
          ((indIic_measurable t).comp (hX_meas _)))) _
      apply Integrable.of_bound h_meas.aestronglyMeasurable 1
      filter_upwards with ω; simp [Real.norm_eq_abs]
      calc (m:ℝ)⁻¹ * |∑ i : Fin m, indIic t (X i ω)|
        _ ≤ (m:ℝ)⁻¹ * ∑ i : Fin m, |indIic t (X i ω)| := by
              gcongr; exact Finset.abs_sum_le_sum_abs _ _
        _ ≤ (m:ℝ)⁻¹ * ∑ i : Fin m, (1 : ℝ) := by
              gcongr with i
              unfold indIic; simp [Set.indicator]; split_ifs <;> norm_num
        _ = (m:ℝ)⁻¹ * m := by simp [Finset.sum_const]
        _ = 1 := by field_simp

    -- Triangle inequality for integrals
    calc ∫ ω, |(1/(m:ℝ)) * ∑ k : Fin m, indIic t (X (k.val + 1) ω) -
               μ[indIic t ∘ X 0|TailSigma.tailSigma X] ω| ∂μ
        ≤ ∫ ω, |(1/(m:ℝ)) * ∑ k : Fin m, indIic t (X (k.val + 1) ω) - B m ω| ∂μ +
          ∫ ω, |B m ω - μ[indIic t ∘ X 0|TailSigma.tailSigma X] ω| ∂μ := by
            -- Use pointwise triangle inequality: |a - c| ≤ |a - b| + |b - c|
            rw [← integral_add]
            · apply integral_mono
              · -- Integrability of |A - target|
                exact (hA_int.sub integrable_condExp).abs
              · -- Integrability of |A - B| + |B - target|
                exact ((hA_int.sub hB_int).abs).add ((hB_int.sub integrable_condExp).abs)
              · -- Pointwise bound: |a - c| ≤ |a - b| + |b - c|
                intro ω
                exact abs_sub_le _ _ _
            · -- Integrability of |A - B|
              apply Integrable.abs
              apply Integrable.sub
              · exact hA_int
              · exact hB_int
            · -- Integrability of |B - target|
              apply Integrable.abs
              apply Integrable.sub
              · exact hB_int
              · exact integrable_condExp
      _ < 2/(m:ℝ) + ε/2 := by linarith [hAB_diff, hB_conv]
      _ ≤ ε/2 + ε/2 := by linarith [h_small]
      _ = ε := by ring

  -- Measurability of Cesàro averages
  have hA_meas : ∀ n m, AEStronglyMeasurable (A n m) μ := by
    intro n m
    -- A n m is a Cesàro average of indIic ∘ X, which are measurable
    -- Each indIic ∘ X_i is measurable, sum is measurable, scalar mult is measurable
    refine Measurable.aestronglyMeasurable ?_
    fun_prop

  -- Step 3: Use uniqueness of L¹ limits to conclude a.e. equality
  -- If both f and g are L¹ limits of the same sequence, then f =ᵐ g
  have h_L1_uniqueness : ∀ (f g : Ω → ℝ),
      AEStronglyMeasurable f μ → AEStronglyMeasurable g μ →
      (∀ᵐ ω ∂μ, ‖f ω‖ ≤ 1) → (∀ᵐ ω ∂μ, ‖g ω‖ ≤ 1) →
      (∀ ε > 0, ∃ M : ℕ, ∀ m ≥ M, ∫ ω, |A 0 m ω - f ω| ∂μ < ε) →
      (∀ ε > 0, ∃ M : ℕ, ∀ m ≥ M, ∫ ω, |A 0 m ω - g ω| ∂μ < ε) →
      f =ᵐ[μ] g := by
    intro f g hf_meas hg_meas hf_bdd hg_bdd hf_lim hg_lim
    -- Strategy: L¹ convergence implies a.e. convergent subsequence, and a.e. limits are unique
    -- Convert L¹ convergence hypothesis to Tendsto format
    have hf_tendsto : Tendsto (fun m => ∫ ω, |A 0 m ω - f ω| ∂μ) atTop (𝓝 0) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨M, hM⟩ := hf_lim ε hε
      use M
      intro m hm
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg (fun ω => abs_nonneg _))]
      exact hM m hm
    have hg_tendsto : Tendsto (fun m => ∫ ω, |A 0 m ω - g ω| ∂μ) atTop (𝓝 0) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨M, hM⟩ := hg_lim ε hε
      use M
      intro m hm
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg (fun ω => abs_nonneg _))]
      exact hM m hm
    -- Complete the proof using the mathlib convergence chain:
    -- 1. Convert L¹ convergence to eLpNorm convergence
    -- 2. Apply tendstoInMeasure_of_tendsto_eLpNorm
    -- 3. Use tendstoInMeasure_ae_unique

    -- Step 1a: Show A m - f is integrable for all m (needed for eLpNorm_one_eq_integral_abs)
    have hAf_integrable : ∀ m, Integrable (fun ω => A 0 m ω - f ω) μ := by
      intro m
      refine Integrable.sub ?_ ?_
      · -- A is a Cesàro average of indicators, bounded by 1
        refine Integrable.of_bound (hA_meas 0 m) 1 ?_
        filter_upwards with ω
        -- A n m ω = (1/m) * ∑_{k<m} indIic t (X (n+k+1) ω)
        -- Each indIic t x ∈ {0, 1}, so the sum is in [0, m]
        -- Therefore A n m ω ∈ [0, 1]
        unfold A
        simp only [Real.norm_eq_abs, zero_add]
        by_cases hm : m = 0
        · simp [hm]
        · calc |1 / (m:ℝ) * ∑ k : Fin m, indIic t (X (k.val + 1) ω)|
                = (m:ℝ)⁻¹ * |∑ k : Fin m, indIic t (X (k.val + 1) ω)| := by
                      rw [one_div, abs_mul, abs_of_pos]; positivity
              _ ≤ (m:ℝ)⁻¹ * ∑ k : Fin m, |indIic t (X (k.val + 1) ω)| := by
                    gcongr; exact Finset.abs_sum_le_sum_abs _ _
              _ ≤ (m:ℝ)⁻¹ * ∑ k : Fin m, (1 : ℝ) := by
                    gcongr with k
                    unfold indIic; simp [Set.indicator]; split_ifs <;> norm_num
              _ = (m:ℝ)⁻¹ * m := by simp [Finset.sum_const]
              _ = 1 := by field_simp [hm]
      · -- f is bounded by hypothesis hf_bdd
        exact Integrable.of_bound hf_meas 1 hf_bdd

    have hAg_integrable : ∀ m, Integrable (fun ω => A 0 m ω - g ω) μ := by
      intro m
      refine Integrable.sub ?_ ?_
      · -- A is a Cesàro average of indicators, bounded by 1 (same proof as above)
        refine Integrable.of_bound (hA_meas 0 m) 1 ?_
        filter_upwards with ω
        unfold A
        simp only [Real.norm_eq_abs, zero_add]
        by_cases hm : m = 0
        · simp [hm]
        · calc |1 / (m:ℝ) * ∑ k : Fin m, indIic t (X (k.val + 1) ω)|
                = (m:ℝ)⁻¹ * |∑ k : Fin m, indIic t (X (k.val + 1) ω)| := by
                      rw [one_div, abs_mul, abs_of_pos]; positivity
              _ ≤ (m:ℝ)⁻¹ * ∑ k : Fin m, |indIic t (X (k.val + 1) ω)| := by
                    gcongr; exact Finset.abs_sum_le_sum_abs _ _
              _ ≤ (m:ℝ)⁻¹ * ∑ k : Fin m, (1 : ℝ) := by
                    gcongr with k
                    unfold indIic; simp [Set.indicator]; split_ifs <;> norm_num
              _ = (m:ℝ)⁻¹ * m := by simp [Finset.sum_const]
              _ = 1 := by field_simp [hm]
      · -- g is bounded by hypothesis hg_bdd
        exact Integrable.of_bound hg_meas 1 hg_bdd

    -- Step 1b: Convert L¹ to eLpNorm using IntegrationHelpers.eLpNorm_one_eq_integral_abs
    have hf_eLpNorm : Tendsto (fun m => eLpNorm (fun ω => A 0 m ω - f ω) 1 μ) atTop (𝓝 0) := by
      rw [ENNReal.tendsto_nhds_zero]
      intro ε hε
      rw [Metric.tendsto_atTop] at hf_tendsto
      by_cases h_top : ε = ⊤
      · simp [h_top]
      · have ε_pos : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' h_top
        obtain ⟨M, hM⟩ := hf_tendsto ε.toReal ε_pos
        refine Filter.eventually_atTop.mpr ⟨M, fun m hm => ?_⟩
        rw [Exchangeability.Probability.IntegrationHelpers.eLpNorm_one_eq_integral_abs (hAf_integrable m)]
        -- Goal: ENNReal.ofReal (∫ |...|) ≤ ε
        rw [← ENNReal.ofReal_toReal h_top]
        -- Goal: ENNReal.ofReal (∫ |...|) ≤ ENNReal.ofReal ε.toReal
        rw [ENNReal.ofReal_le_ofReal_iff ε_pos.le]
        -- Goal: ∫ |...| ≤ ε.toReal
        have := hM m hm
        rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg (fun ω => abs_nonneg _))] at this
        exact this.le

    have hg_eLpNorm : Tendsto (fun m => eLpNorm (fun ω => A 0 m ω - g ω) 1 μ) atTop (𝓝 0) := by
      rw [ENNReal.tendsto_nhds_zero]
      intro ε hε
      rw [Metric.tendsto_atTop] at hg_tendsto
      by_cases h_top : ε = ⊤
      · simp [h_top]
      · have ε_pos : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' h_top
        obtain ⟨M, hM⟩ := hg_tendsto ε.toReal ε_pos
        refine Filter.eventually_atTop.mpr ⟨M, fun m hm => ?_⟩
        rw [Exchangeability.Probability.IntegrationHelpers.eLpNorm_one_eq_integral_abs (hAg_integrable m)]
        -- Goal: ENNReal.ofReal (∫ |...|) ≤ ε
        rw [← ENNReal.ofReal_toReal h_top]
        -- Goal: ENNReal.ofReal (∫ |...|) ≤ ENNReal.ofReal ε.toReal
        rw [ENNReal.ofReal_le_ofReal_iff ε_pos.le]
        -- Goal: ∫ |...| ≤ ε.toReal
        have := hM m hm
        rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg (fun ω => abs_nonneg _))] at this
        exact this.le

    -- Step 2: Apply tendstoInMeasure
    have hf_meas_conv : TendstoInMeasure μ (A 0) atTop f := by
      apply tendstoInMeasure_of_tendsto_eLpNorm (p := 1) one_ne_zero
      · intro m; exact hA_meas 0 m
      · exact hf_meas
      · exact hf_eLpNorm

    have hg_meas_conv : TendstoInMeasure μ (A 0) atTop g := by
      apply tendstoInMeasure_of_tendsto_eLpNorm (p := 1) one_ne_zero
      · intro m; exact hA_meas 0 m
      · exact hg_meas
      · exact hg_eLpNorm

    -- Step 3: Apply uniqueness
    exact tendstoInMeasure_ae_unique hf_meas_conv hg_meas_conv

  -- Apply uniqueness with f = alphaIic, g = alphaIicCE
  apply h_L1_uniqueness
  · -- alphaIic is ae strongly measurable
    exact (alphaIic_measurable X hX_contract hX_meas hX_L2 t).aestronglyMeasurable
  · -- alphaIicCE is ae strongly measurable
    exact (alphaIicCE_measurable X hX_contract hX_meas hX_L2 t).aestronglyMeasurable
  · -- alphaIic is bounded by 1
    filter_upwards with ω
    simp only [Real.norm_eq_abs]
    rw [abs_le_one_iff_mul_self_le_one]
    have ⟨h0, h1⟩ := alphaIic_bound X hX_contract hX_meas hX_L2 t ω
    nlinarith [sq_nonneg (alphaIic X hX_contract hX_meas hX_L2 t ω)]
  · -- alphaIicCE is bounded by 1 (using alphaIicCE_nonneg_le_one)
    have := alphaIicCE_nonneg_le_one X hX_contract hX_meas hX_L2 t
    filter_upwards [this] with ω ⟨h0, h1⟩
    simp only [Real.norm_eq_abs]
    rw [abs_le_one_iff_mul_self_le_one]
    nlinarith [sq_nonneg (alphaIicCE X hX_contract hX_meas hX_L2 t ω)]
  · exact h_alphaIic_is_limit 0
  · exact h_alphaIicCE_is_limit


end Exchangeability.DeFinetti.ViaL2
