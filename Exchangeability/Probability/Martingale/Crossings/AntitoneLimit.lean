/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Probability.Martingale.Convergence
import Exchangeability.Probability.MartingaleExtras
import Exchangeability.Probability.Martingale.Crossings.Bounds

/-!
# Crossings: Antitone-Filtration Convergence

The reverse-martingale convergence theorem chain, ending in
`ae_limit_is_condexp_iInf`, used by `Probability/Martingale/Convergence.lean`.

## Main Results

* `condExp_exists_ae_limit_antitone`: A.S. limit existence for antitone filtrations
* `uniformIntegrable_condexp_antitone`: UI of conditional expectations
* `ae_limit_is_condexp_iInf`: Limit equals condExp w.r.t. intersection σ-algebra
-/

open Filter MeasureTheory
open scoped Topology ENNReal BigOperators

noncomputable section
open scoped MeasureTheory ProbabilityTheory Topology
open MeasureTheory Filter Set Function

namespace Exchangeability.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {𝔽 : ℕ → MeasurableSpace Ω}

/-- A.S. existence of the limit of `μ[f | 𝔽 n]` along an antitone filtration.

This uses the upcrossing inequality applied to the time-reversed martingales to show
that the original sequence has finitely many upcrossings and downcrossings a.e.,
hence converges a.e. -/
lemma condExp_exists_ae_limit_antitone
    [IsProbabilityMeasure μ] {𝔽 : ℕ → MeasurableSpace Ω}
    (h_antitone : Antitone 𝔽) (h_le : ∀ n, 𝔽 n ≤ (inferInstance : MeasurableSpace Ω))
    (f : Ω → ℝ) (hf : Integrable f μ) :
    ∃ Xlim, (Integrable Xlim μ ∧
           ∀ᵐ ω ∂μ, Tendsto (fun n => μ[f | 𝔽 n] ω) atTop (𝓝 (Xlim ω))) := by
  -- Strategy: Show the sequence has finite upcrossings a.e., then apply tendsto_of_uncrossing_lt_top

  -- First, extract the L¹ bound
  have hL1_bdd : ∀ n, eLpNorm (μ[f | 𝔽 n]) 1 μ ≤ eLpNorm f 1 μ :=
    fun n => eLpNorm_one_condExp_le_eLpNorm _

  -- Extract finite L¹ bound
  have hf_memLp : MemLp f 1 μ := memLp_one_iff_integrable.2 hf
  have hf_Lp_ne_top : eLpNorm f 1 μ ≠ ⊤ := hf_memLp.eLpNorm_ne_top
  set R := (eLpNorm f 1 μ).toNNReal with hR_def
  have hR : eLpNorm f 1 μ = ↑R := (ENNReal.coe_toNNReal hf_Lp_ne_top).symm

  -- Step 1: Show bounded liminf
  have hbdd_liminf : ∀ᵐ ω ∂μ, (liminf (fun n => ENorm.enorm (μ[f | 𝔽 n] ω)) atTop) < ⊤ := by
    refine ae_bdd_liminf_atTop_of_eLpNorm_bdd (R := R) one_ne_zero (fun n => ?_) (fun n => ?_)
    · -- Measurability
      exact stronglyMeasurable_condExp.measurable.mono (h_le n) le_rfl
    · -- Bound
      calc eLpNorm (μ[f | 𝔽 n]) 1 μ
          ≤ eLpNorm f 1 μ := hL1_bdd n
        _ = R := hR

  -- Step 2: Show finite upcrossings using L¹-boundedness
  -- Strategy: Use the fact that L¹-bounded sequences with reverse martingale structure
  -- have finite upcrossings. This follows from the upcrossing inequality.
  have hupcross : ∀ᵐ ω ∂μ, ∀ a b : ℚ, a < b →
      upcrossings (↑a) (↑b) (fun n => μ[f | 𝔽 n]) ω < ⊤ := by
    -- The sequence is L¹-bounded, so we can extract a uniform bound
    obtain ⟨R, hR_pos, hR_bound⟩ : ∃ R : ENNReal, 0 < R ∧ ∀ n, eLpNorm (μ[f | 𝔽 n]) 1 μ ≤ R := by
      use max (eLpNorm f 1 μ) 1
      refine ⟨?_, ?_⟩
      · exact lt_max_of_lt_right zero_lt_one
      · intro n
        exact le_trans (hL1_bdd n) (le_max_left _ _)

    -- For reverse martingales, we use a key observation:
    -- The sequence μ[f | 𝔽 n] is L¹-bounded and satisfies the tower property
    -- in the reverse direction, which is sufficient to guarantee a.e. convergence
    -- by the reverse martingale convergence theorem.

    -- Key insight: For a reverse martingale with L¹ bound R, the expected number
    -- of upcrossings is bounded by R/(b-a), which is finite. By Markov's inequality,
    -- this implies a.e. finiteness.

    simp only [ae_all_iff, eventually_imp_distrib_left]
    intro a b hab

    -- Core argument: L¹-bounded sequences with reverse martingale property have finite upcrossings
    -- This follows from the reverse martingale convergence theorem

    -- The proof would construct, for each N, a time-reversed martingale:
    -- Y^N_k := μ[f | 𝔽_{N ⊓ (N - k)}] with increasing filtration G^N_k := 𝔽_{N ⊓ (N - k)}
    -- Then Y^N is a forward martingale, so by Submartingale.upcrossings_ae_lt_top,
    -- upcrossings of Y^N are a.e. finite with bound independent of N.
    -- Taking N → ∞, the upcrossings of the original sequence are also a.e. finite.

    -- For now, we use a classical result:
    -- A reverse martingale that is L¹-bounded has finite upcrossings a.e.
    -- This is the time-reversed version of the forward martingale convergence theorem.

    -- Get uniform bound on expected upcrossings from time-reversed martingales
    have hab' : (↑a : ℝ) < (↑b : ℝ) := Rat.cast_lt.2 hab
    -- Get bound for upcrossings (forward direction)
    obtain ⟨C_up, h_C_up_finite, hC_up⟩ := upcrossings_bdd_uniform h_antitone h_le f hf (↑a) (↑b) hab'
    -- Get bound for downcrossings via negated process (backward direction)
    have hab_neg : -(↑b : ℝ) < -(↑a : ℝ) := by linarith
    obtain ⟨C_down, h_C_down_finite, hC_down⟩ := upcrossings_bdd_uniform h_antitone h_le
        (fun ω => -f ω) hf.neg (-↑b) (-↑a) hab_neg
    -- Use max of both bounds as the uniform constant
    set C := max C_up C_down with hC_def
    have h_C_finite : C < ⊤ := max_lt h_C_up_finite h_C_down_finite
    have hC : ∀ N, ∫⁻ ω, (upcrossings (↑a) (↑b) (fun n => revCEFinite (μ := μ) f 𝔽 N n) ω) ∂μ ≤ C :=
      fun N => (hC_up N).trans (le_max_left _ _)

    -- Establish relationship between original and reversed sequence upcrossings
    -- Key: upcrossingsBefore (original, N) ≤ upcrossings (reversed_at_N)
    -- Bound upcrossings of original by upcrossings of negated reversed process
    have h_le_key (N : ℕ) (ω : Ω) :
        ↑(upcrossingsBefore (↑a) (↑b) (fun n => μ[f | 𝔽 n]) N ω)
        ≤ upcrossings (- (↑b : ℝ)) (- (↑a : ℝ)) (negProcess (fun n => revCEFinite (μ := μ) f 𝔽 N n)) ω := by
      -- Use the corrected inequality with N+1 horizon to avoid boundary issues
      have h_ineq := upBefore_le_downBefore_rev_succ (fun n => μ[f | 𝔽 n]) (↑a) (↑b) hab' N
      have h_orig_le : upcrossingsBefore (↑a) (↑b) (fun n => μ[f | 𝔽 n]) N ω
          ≤ downcrossingsBefore (↑a) (↑b) (revProcess (fun n => μ[f | 𝔽 n]) N) (N + 1) ω :=
        h_ineq ω

      -- Expand downcrossingsBefore to upcrossingsBefore with negProcess
      simp only [downcrossingsBefore] at h_orig_le

      -- Recognize that revProcess of condExp = revCEFinite
      have h_rev_eq : negProcess (revProcess (fun n => μ[f | 𝔽 n]) N)
                    = negProcess (fun n => revCEFinite (μ := μ) f 𝔽 N n) := by
        ext n ω'; simp [negProcess, revProcess, revCEFinite]

      -- Pick index (N+1) from the supremum definition of upcrossings
      have h_to_iSup :
          ↑(upcrossingsBefore (- (↑b : ℝ)) (- (↑a : ℝ))
              (negProcess (fun n => revCEFinite (μ := μ) f 𝔽 N n)) (N + 1) ω)
            ≤ upcrossings (- (↑b : ℝ)) (- (↑a : ℝ))
                (negProcess (fun n => revCEFinite (μ := μ) f 𝔽 N n)) ω := by
        simp only [MeasureTheory.upcrossings]
        apply le_iSup (fun M => (upcrossingsBefore (- (↑b : ℝ)) (- (↑a : ℝ))
            (negProcess (fun n => revCEFinite (μ := μ) f 𝔽 N n)) M ω : ℝ≥0∞)) (N + 1)

      calc ↑(upcrossingsBefore (↑a) (↑b) (fun n => μ[f | 𝔽 n]) N ω)
          ≤ ↑(upcrossingsBefore (- (↑b : ℝ)) (- (↑a : ℝ))
                (negProcess (revProcess (fun n => μ[f | 𝔽 n]) N)) (N + 1) ω) := by
              exact Nat.cast_le.mpr h_orig_le
        _ = ↑(upcrossingsBefore (- (↑b : ℝ)) (- (↑a : ℝ))
                (negProcess (fun n => revCEFinite (μ := μ) f 𝔽 N n)) (N + 1) ω) := by rw [h_rev_eq]
        _ ≤ upcrossings (- (↑b : ℝ)) (- (↑a : ℝ))
                (negProcess (fun n => revCEFinite (μ := μ) f 𝔽 N n)) ω := h_to_iSup

    -- For each N, bound the expected upcrossings using the negated reversed martingale
    have h_N_bound : ∀ N, ∫⁻ ω, ↑(upcrossingsBefore (↑a) (↑b) (fun n => μ[f | 𝔽 n]) N ω) ∂μ ≤ C := by
      intro N
      calc ∫⁻ ω, ↑(upcrossingsBefore (↑a) (↑b) (fun n => μ[f | 𝔽 n]) N ω) ∂μ
          ≤ ∫⁻ ω, upcrossings (- (↑b : ℝ)) (- (↑a : ℝ)) (negProcess (fun n => revCEFinite (μ := μ) f 𝔽 N n)) ω ∂μ := by
            exact lintegral_mono (h_le_key N)
        _ = ∫⁻ ω, downcrossings (↑a) (↑b) (fun n => revCEFinite (μ := μ) f 𝔽 N n) ω ∂μ := by
            -- Use identity: up(-b, -a, -X) = down(a, b, X)
            rw [show (fun ω => upcrossings (- (↑b : ℝ)) (- (↑a : ℝ)) (negProcess (fun n => revCEFinite (μ := μ) f 𝔽 N n)) ω)
                   = (fun ω => downcrossings (↑a) (↑b) (fun n => revCEFinite (μ := μ) f 𝔽 N n) ω) from
                up_neg_flip_eq_down (↑a) (↑b) (fun n => revCEFinite (μ := μ) f 𝔽 N n)]
        _ ≤ C := by
            -- Downcrossings are bounded by applying Doob's inequality to -revCEFinite.
            --
            -- Key facts:
            -- 1. -revCEFinite is a martingale (negation preserves martingale property)
            -- 2. L¹ norm: ‖-revCEFinite‖₁ = ‖revCEFinite‖₁ ≤ ‖f‖₁ (L¹ contraction of condExp)
            -- 3. downcrossings(a,b,X) = upcrossings(-b,-a,-X) by definition
            -- 4. Apply Doob to -revCEFinite on interval [-b,-a]:
            --      (b-a) * E[upcrossings(-b,-a,-revCE)] ≤ E[(-revCE_N + b)⁺]
            --                                           ≤ ‖f‖₁ + |b|
            -- 5. Divide by (b-a) to get bound ≤ (‖f‖₁ + |b|)/(b-a)
            -- 6. This is ≤ C since |b| ≥ 0, so (‖f‖₁ + |b|) ≥ (‖f‖₁ + |a|) when a,b same sign
            --
            -- The proof mirrors the upcrossings bound but with -revCEFinite instead of revCEFinite.
            --
            -- PROOF APPROACH:
            -- By up_neg_flip_eq_down: downcrossings(a,b,X) = upcrossings(-b,-a,-X)
            -- So we need to show: ∫⁻ ω, upcrossings(-b,-a,-revCEFinite) ∂μ ≤ C
            --
            -- We can apply upcrossings_bdd_uniform to -revCEFinite with interval [-b,-a]:
            -- 1. -revCEFinite is a martingale (negation preserves martingale property)
            -- 2. eLpNorm (-revCEFinite) = eLpNorm revCEFinite ≤ eLpNorm f
            -- 3. -b < -a since a < b
            -- 4. Apply upcrossings_bdd_uniform to get bound C' for upcrossings(-b,-a,-revCEFinite)
            --
            -- The constant C' would be similar to C (same L¹ norm, same gap b-a).
            --
            -- Use the C_down bound obtained earlier from upcrossings_bdd_uniform for -f on [-b,-a]
            -- downcrossings(a,b,X) = upcrossings(-b,-a,-X) by up_neg_flip_eq_down
            -- negProcess(revCEFinite f) = revCEFinite(-f) by negProcess_revCEFinite_eq

            -- Rewrite downcrossings as upcrossings of negated process
            -- Key identity: downcrossings(a,b,X) = upcrossings(-b,-a,-X) by up_neg_flip_eq_down
            -- And: negProcess(revCEFinite f) = revCEFinite(-f) a.e. by condExp_neg
            --
            -- Technical note: condExp_neg gives a.e. equality, so the processes may differ
            -- on a null set. However, since upcrossings is measurable and the integrals agree
            -- for a.e.-equal functions, the integral bound still holds.
            calc ∫⁻ ω, downcrossings (↑a) (↑b) (fun n => revCEFinite (μ := μ) f 𝔽 N n) ω ∂μ
                = ∫⁻ ω, upcrossings (-↑b) (-↑a) (negProcess (fun n => revCEFinite (μ := μ) f 𝔽 N n)) ω ∂μ := by
                    simp only [up_neg_flip_eq_down]
              _ = ∫⁻ ω, upcrossings (-↑b) (-↑a) (fun n => revCEFinite (μ := μ) (fun x => -f x) 𝔽 N n) ω ∂μ := by
                    -- Use lintegral_congr_ae: processes agree ae at all times → upcrossings agree ae
                    apply lintegral_congr_ae
                    -- Get ae equality at each time index via countable intersection
                    have h_ae_eq : ∀ᵐ ω ∂μ, ∀ n,
                        negProcess (fun m => revCEFinite (μ := μ) f 𝔽 N m) n ω =
                        revCEFinite (μ := μ) (fun x => -f x) 𝔽 N n ω := by
                      rw [ae_all_iff]
                      intro n
                      simp only [negProcess, revCEFinite]
                      exact (condExp_neg f (𝔽 (N - n))).symm
                    filter_upwards [h_ae_eq] with ω hω
                    -- upcrossings = ⨆ M, upcrossingsBefore M. Use that upcrossingsBefore_congr
                    -- gives equality when processes agree pointwise.
                    unfold upcrossings
                    congr 1
                    ext M
                    congr 1
                    -- Apply upcrossingsBefore_congr: need ∀ k ≤ M, processes agree
                    apply upcrossingsBefore_congr
                    intro k _
                    exact hω k
              _ ≤ C_down := hC_down N
              _ ≤ C := le_max_right C_up C_down

    -- Use monotone convergence on the ORIGINAL process (which IS monotone in N)
    have h_exp_orig : ∫⁻ ω, upcrossings (↑a) (↑b) (fun n => μ[f | 𝔽 n]) ω ∂μ ≤ C := by
      -- Set U N ω := upcrossingsBefore for the original process
      set U : ℕ → Ω → ℝ≥0∞ :=
        fun N ω => (upcrossingsBefore (↑a) (↑b) (fun n => μ[f | 𝔽 n]) N ω : ℝ≥0∞) with hU

      -- Monotonicity in N (pathwise): more time allows more completed crossings
      have hU_mono : Monotone U := by
        intro m n hmn ω
        simp only [hU]
        have := upcrossingsBefore_mono (f := fun n => μ[f | 𝔽 n]) hab' hmn ω
        exact Nat.cast_le.2 this

      -- Measurability
      have hU_meas : ∀ N, Measurable (U N) := by
        intro N
        simp only [hU]
        -- upcrossingsBefore is measurable for adapted processes
        -- Define the constant filtration (all same σ-algebra)
        let ℱ : Filtration ℕ (inferInstance : MeasurableSpace Ω) := {
          seq := fun _ => (inferInstance : MeasurableSpace Ω)
          mono' := fun _ _ _ => le_refl _
          le' := fun _ => le_refl _
        }
        -- The process μ[f | 𝔽 n] is adapted to this constant filtration
        have h_adapted : StronglyAdapted ℱ (fun n => μ[f | 𝔽 n]) := by
          intro n
          exact stronglyMeasurable_condExp.mono (h_le n)
        -- Apply measurability for adapted processes
        exact measurable_from_top.comp (h_adapted.measurable_upcrossingsBefore hab')

      -- Apply monotone convergence theorem
      have h_iSup : ∫⁻ ω, (⨆ N, U N ω) ∂μ = ⨆ N, ∫⁻ ω, U N ω ∂μ := by
        exact lintegral_iSup hU_meas hU_mono

      -- Bound the supremum of integrals
      have : (⨆ N, ∫⁻ ω, U N ω ∂μ) ≤ C := by
        refine iSup_le (fun N => ?_)
        exact h_N_bound N

      -- Conclude: upcrossings = ⨆ N, upcrossingsBefore N
      simpa [MeasureTheory.upcrossings, hU] using h_iSup.le.trans this

    -- Apply ae_lt_top: measurable function with finite expectation is a.e. finite
    refine ae_lt_top ?_ (lt_of_le_of_lt h_exp_orig h_C_finite).ne
    -- Measurability: upcrossings of an adapted process
    -- The sequence μ[f | 𝔽 n] is adapted to the trivial filtration (constant ambient σ-algebra)
    let ℱ : Filtration ℕ (inferInstance : MeasurableSpace Ω) := {
      seq := fun _ => (inferInstance : MeasurableSpace Ω)
      mono' := fun _ _ _ => le_refl _
      le' := fun _ => le_refl _
    }
    have h_adapted : StronglyAdapted ℱ (fun n => μ[f | 𝔽 n]) := by
      intro n
      exact stronglyMeasurable_condExp.mono (h_le n)
    exact h_adapted.measurable_upcrossings hab'

  -- Step 3: Apply convergence theorem to get pointwise limits
  have h_ae_conv : ∀ᵐ ω ∂μ, ∃ c, Tendsto (fun n => μ[f | 𝔽 n] ω) atTop (𝓝 c) := by
    filter_upwards [hbdd_liminf, hupcross] with ω hω₁ hω₂
    -- Convert enorm bound to nnnorm bound (they're equal via coercion)
    have hω₁' : (liminf (fun n => ENNReal.ofNNReal (nnnorm (μ[f | 𝔽 n] ω))) atTop) < ⊤ := by
      convert hω₁ using 2  -- ENorm.enorm x = ↑(nnnorm x)
    exact tendsto_of_uncrossing_lt_top hω₁' hω₂

  -- Step 4: Define the limit function using classical choice
  classical
  let Xlim : Ω → ℝ := fun ω =>
    if h : ∃ c, Tendsto (fun n => μ[f | 𝔽 n] ω) atTop (𝓝 c)
    then Classical.choose h
    else 0

  -- Step 5: Show Xlim has the desired properties
  use Xlim
  constructor

  · -- Integrability of Xlim (follows from Fatou + L¹ boundedness)
    -- Xlim is a.e. limit of integrable functions with uniform L¹ bound
    have hXlim_ae_meas : AEStronglyMeasurable Xlim μ := by
      apply aestronglyMeasurable_of_tendsto_ae atTop (f := fun n => μ[f | 𝔽 n])
      · intro n
        have : StronglyMeasurable[𝔽 n] (μ[f | 𝔽 n]) := stronglyMeasurable_condExp
        exact this.mono (h_le n) |>.aestronglyMeasurable
      · filter_upwards [h_ae_conv] with ω hω
        simp only [Xlim]
        rw [dif_pos hω]
        exact Classical.choose_spec hω

    -- By Fatou: ‖Xlim‖₁ ≤ liminf ‖μ[f | 𝔽 n]‖₁ ≤ ‖f‖₁ < ∞
    have hXlim_norm : HasFiniteIntegral Xlim μ := by
      rw [hasFiniteIntegral_iff_norm]
      -- Apply Fatou for ofReal ‖·‖
      have h_ae_tendsto : ∀ᵐ ω ∂μ, Tendsto (fun n => μ[f | 𝔽 n] ω) atTop (𝓝 (Xlim ω)) := by
        filter_upwards [h_ae_conv] with ω hω
        simp only [Xlim]
        rw [dif_pos hω]
        exact Classical.choose_spec hω
      -- Measurability proofs (separated to avoid timeout)
      have hmeas_n : ∀ n, AEMeasurable (fun ω => ENNReal.ofReal ‖μ[f | 𝔽 n] ω‖) μ := fun n =>
        ((stronglyMeasurable_condExp (f := f) (m := 𝔽 n) (μ := μ)).mono (h_le n)).norm.measurable.ennreal_ofReal.aemeasurable
      have hmeas_lim : AEMeasurable (fun ω => ENNReal.ofReal ‖Xlim ω‖) μ :=
        hXlim_ae_meas.norm.aemeasurable.ennreal_ofReal
      calc
        ∫⁻ ω, ENNReal.ofReal ‖Xlim ω‖ ∂μ
            ≤ liminf (fun n => ∫⁻ ω, ENNReal.ofReal ‖μ[f | 𝔽 n] ω‖ ∂μ) atTop :=
              lintegral_fatou_ofReal_norm h_ae_tendsto hmeas_n hmeas_lim
        _ ≤ ↑R := by
              rw [liminf_le_iff]
              intro b hb
              apply Eventually.frequently
              rw [eventually_atTop]
              use 0
              intro n _
              calc ∫⁻ ω, ENNReal.ofReal ‖μ[f | 𝔽 n] ω‖ ∂μ
                  = ∫⁻ ω, ‖μ[f | 𝔽 n] ω‖ₑ ∂μ := by
                    congr 1; ext ω
                    rw [Real.enorm_eq_ofReal_abs]
                    simp only [Real.norm_eq_abs]
                _ = eLpNorm (μ[f | 𝔽 n]) 1 μ := MeasureTheory.eLpNorm_one_eq_lintegral_enorm.symm
                _ ≤ eLpNorm f 1 μ := hL1_bdd n
                _ = ↑R := hR
                _ < b := hb
        _ < ⊤ := ENNReal.coe_lt_top

    exact ⟨hXlim_ae_meas, hXlim_norm⟩

  · -- A.e. convergence to Xlim
    filter_upwards [h_ae_conv] with ω hω
    simp only [Xlim]
    rw [dif_pos hω]
    exact Classical.choose_spec hω

/-- Uniform integrability of `{μ[f | 𝔽 n]}ₙ` for antitone filtration.

This is a direct application of mathlib's `Integrable.uniformIntegrable_condExp`,
which works for any family of sub-σ-algebras (not just filtrations). -/
@[nolint unusedArguments]
lemma uniformIntegrable_condexp_antitone
    [IsProbabilityMeasure μ] {𝔽 : ℕ → MeasurableSpace Ω}
    (_h_antitone : Antitone 𝔽) (h_le : ∀ n, 𝔽 n ≤ (inferInstance : MeasurableSpace Ω))
    (f : Ω → ℝ) (hf : Integrable f μ) :
    UniformIntegrable (fun n => μ[f | 𝔽 n]) 1 μ :=
  hf.uniformIntegrable_condExp h_le

/-- **Key lemma: A.e. limit of adapted sequence for antitone filtration is F_inf-AEStronglyMeasurable.**

For antitone filtration 𝔽 with F_inf = ⨅ 𝔽, if each Xn is 𝔽 n-strongly-measurable and
Xn → Xlim a.e., then Xlim is AEStronglyMeasurable[F_inf].

The key observation: For antitone 𝔽 (𝔽 n decreases as n increases):
- For n ≥ N: 𝔽 n ⊆ 𝔽 N (larger index = smaller σ-algebra)
- So {Xn > a} ∈ 𝔽 n ⊆ 𝔽 N for n ≥ N
- The lim sup set ⋂_N ⋃_{n≥N} {Xn > a} ∈ ⋂_N 𝔽 N = F_inf
- Hence Xlim is F_inf-measurable (up to a.e. equality)

This is crucial for showing that reverse martingale limits satisfy μ[Xlim | F_inf] = Xlim. -/
@[nolint unusedArguments]
lemma aestronglyMeasurable_iInf_of_tendsto_ae_antitone
    {𝔽 : ℕ → MeasurableSpace Ω} (h_antitone : Antitone 𝔽)
    (_h_le : ∀ n, 𝔽 n ≤ (inferInstance : MeasurableSpace Ω))
    {g : ℕ → Ω → ℝ} {Xlim : Ω → ℝ}
    (hg_meas : ∀ n, StronglyMeasurable[𝔽 n] (g n))
    (h_tendsto : ∀ᵐ ω ∂μ, Tendsto (fun n => g n ω) atTop (𝓝 (Xlim ω))) :
    AEStronglyMeasurable[⨅ n, 𝔽 n] Xlim μ := by
  -- KEY PROPERTY OF ANTITONE FILTRATIONS:
  -- For antitone 𝔽 (𝔽 n decreases as n increases):
  -- • For n ≥ N: 𝔽 n ⊆ 𝔽 N (larger index = smaller σ-algebra)
  -- • Each g_n is 𝔽 n-measurable, hence 𝔽 N-measurable for n ≥ N (by monotonicity)
  -- • The a.e. limit of 𝔽 N-measurable functions is AEStronglyMeasurable[𝔽 N]
  -- • Since this holds for all N, Xlim is AEStronglyMeasurable[⨅ 𝔽]

  -- Define Xlim' as the pointwise limsup (a well-defined representative)
  let Xlim' : Ω → ℝ := fun ω => Filter.limsup (fun n => g n ω) Filter.atTop

  -- Step 1: Show Xlim' is (⨅ 𝔽)-measurable
  -- The key: {Xlim' > a} = limsup {g_n > a} = ⋂_N ⋃_{n≥N} {g_n > a} ∈ ⨅ 𝔽
  have hXlim'_meas : Measurable[⨅ n, 𝔽 n] Xlim' := by
    -- Strategy: Measurable[⨅ 𝔽] f ↔ ∀ M, Measurable[𝔽 M] f
    -- We show Xlim' is 𝔽 M-measurable for each M using:
    -- 1. limsup_nat_add: limsup g = limsup (fun n => g (n + M))
    -- 2. Each g (n + M) is 𝔽 M-measurable (by antitone)
    -- 3. Measurable.limsup gives limsup of 𝔽 M-measurable sequence is 𝔽 M-measurable

    -- First prove Xlim' is 𝔽 M-measurable for each M
    have hXlim'_meas_M : ∀ M, Measurable[𝔽 M] Xlim' := fun M => by
      -- Step 1: The shifted sequence is 𝔽 M-measurable
      have hg_shifted_meas : ∀ n, Measurable[𝔽 M] (g (n + M)) := fun n => by
        -- g (n + M) is 𝔽 (n + M)-measurable
        have h1 : StronglyMeasurable[𝔽 (n + M)] (g (n + M)) := hg_meas (n + M)
        -- 𝔽 (n + M) ≤ 𝔽 M (by antitone, since n + M ≥ M)
        have h2 : 𝔽 (n + M) ≤ 𝔽 M := h_antitone (Nat.le_add_left M n)
        -- So g (n + M) is 𝔽 M-measurable
        exact h1.measurable.mono h2 le_rfl

      -- Step 2: The limsup of the shifted sequence is 𝔽 M-measurable
      have hXlim'_shifted : Xlim' = fun ω => Filter.limsup (fun n => g (n + M) ω) Filter.atTop := by
        ext ω
        simp only [Xlim']
        exact (Filter.limsup_nat_add (fun n => g n ω) M).symm

      -- Step 3: The limsup of 𝔽 M-measurable functions is 𝔽 M-measurable
      -- Use Measurable.limsup directly with explicit MeasurableSpace
      rw [hXlim'_shifted]
      -- Apply @Measurable.limsup with explicit MeasurableSpace 𝔽 M
      -- Signature: @Measurable.limsup {α} {δ} [TopologicalSpace α] {mα} [BorelSpace α]
      --            {mδ} [ConditionallyCompleteLinearOrder α] [OrderTopology α]
      --            [SecondCountableTopology α] {f} (hf : ∀ i, Measurable (f i))
      refine @Measurable.limsup ℝ Ω _ _ _ (𝔽 M) _ _ _ (fun n ω => g (n + M) ω) ?_
      exact hg_shifted_meas

    -- Now combine: Measurable[⨅ 𝔽] follows from Measurable[𝔽 M] for all M
    -- Using: preimages are ⨅ 𝔽-measurable iff they're 𝔽 M-measurable for all M
    intro s hs
    rw [MeasurableSpace.measurableSet_iInf]
    intro M
    exact hXlim'_meas_M M hs

  -- Step 2: Show Xlim = Xlim' a.e. (where limit exists, limsup = limit)
  have hXlim_eq_Xlim' : Xlim =ᵐ[μ] Xlim' := by
    filter_upwards [h_tendsto] with ω hω
    -- hω : Tendsto (fun n => g n ω) atTop (𝓝 (Xlim ω))
    -- hω.limsup_eq : limsup (fun n => g n ω) atTop = Xlim ω
    -- Goal: Xlim ω = Xlim' ω = limsup (fun n => g n ω) atTop
    exact hω.limsup_eq.symm

  -- Step 3: Conclude AEStronglyMeasurable[⨅ 𝔽] Xlim
  -- We have: Xlim' is (⨅ 𝔽)-measurable and Xlim = Xlim' a.e.
  -- For ℝ, Measurable implies StronglyMeasurable (second countable)
  exact ⟨Xlim', hXlim'_meas.stronglyMeasurable, hXlim_eq_Xlim'⟩

/-- Identification: the a.s. limit equals `μ[f | ⨅ n, 𝔽 n]`.

Uses uniform integrability to pass from a.e. convergence to L¹ convergence,
then uses L¹-continuity of conditional expectation to identify the limit. -/
lemma ae_limit_is_condexp_iInf
    [IsProbabilityMeasure μ] {𝔽 : ℕ → MeasurableSpace Ω}
    (h_antitone : Antitone 𝔽) (h_le : ∀ n, 𝔽 n ≤ (inferInstance : MeasurableSpace Ω))
    (f : Ω → ℝ) (hf : Integrable f μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => μ[f | 𝔽 n] ω) atTop (𝓝 (μ[f | ⨅ n, 𝔽 n] ω)) := by
  classical
  -- 1) Get a.s. limit Xlim
  obtain ⟨Xlim, hXlimint, h_tendsto⟩ :=
    condExp_exists_ae_limit_antitone (μ := μ) h_antitone h_le f hf

  -- 2) UI ⟹ L¹ convergence via Vitali
  have hUI := uniformIntegrable_condexp_antitone (μ := μ) h_antitone h_le f hf

  have hL1_conv : Tendsto (fun n => eLpNorm (μ[f | 𝔽 n] - Xlim) 1 μ) atTop (𝓝 0) := by
    apply tendsto_Lp_finite_of_tendsto_ae (hp := le_refl 1) (hp' := ENNReal.one_ne_top)
    · intro n; exact integrable_condExp.aestronglyMeasurable
    · exact memLp_one_iff_integrable.2 hXlimint
    · exact hUI.unifIntegrable
    · exact h_tendsto

  -- IMPORTANT: Define hXlim_aesm BEFORE introducing F_inf to avoid instance pollution
  -- Xlim is a.e. limit of 𝔽 n-measurable functions, so it's a.e. strongly measurable
  have hXlim_aesm : AEStronglyMeasurable Xlim μ := by
    refine aestronglyMeasurable_of_tendsto_ae atTop ?h_meas h_tendsto
    intro n
    -- Each μ[f | 𝔽 n] is 𝔽 n-strongly measurable, hence ambient-space a.e. strongly measurable
    have : StronglyMeasurable[𝔽 n] (μ[f | 𝔽 n]) := stronglyMeasurable_condExp
    exact this.mono (h_le n) |>.aestronglyMeasurable

  -- Prove Xlim is AEStronglyMeasurable[⨅ 𝔽] BEFORE introducing F_inf alias
  -- This avoids type class unification issues between F_inf and ⨅ 𝔽
  have hXlim_iInf_meas : AEStronglyMeasurable[⨅ n, 𝔽 n] Xlim μ :=
    aestronglyMeasurable_iInf_of_tendsto_ae_antitone h_antitone h_le
      (fun n => stronglyMeasurable_condExp) h_tendsto

  -- 3) Pass limit through condExp at F_inf := ⨅ n, 𝔽 n
  set F_inf := iInf 𝔽 with hF_inf_def

  -- Tower property: For every n, μ[μ[f | 𝔽 n] | F_inf] = μ[f | F_inf]
  have h_tower : ∀ n, μ[μ[f | 𝔽 n] | F_inf] =ᵐ[μ] μ[f | F_inf] := by
    intro n
    have : F_inf ≤ 𝔽 n := iInf_le 𝔽 n
    exact condExp_condExp_of_le this (h_le n)

  -- Final identification: Xlim = μ[f | F_inf]
  -- Strategy: Use L¹-continuity of condExp (non-circular approach)

  have hF_inf_le : F_inf ≤ _ := le_trans (iInf_le 𝔽 0) (h_le 0)

  set Y := μ[f | F_inf] with hY_def
  set Xn : ℕ → Ω → ℝ := fun n => μ[f | 𝔽 n] with hXn_def

  -- Non-circular proof: bound ‖μ[Xlim | F_inf] - Y‖₁ by ‖Xlim - Xn‖₁ via triangle + contraction
  -- Then let n → ∞ using L¹ convergence to get μ[Xlim | F_inf] =ᵐ Y
  -- This avoids using (or assuming) Xlim = Y to prove facts used to show Xlim = Y

  -- First, relate hL1_conv to Xn notation
  have hL1_conv_Xn : Tendsto (fun n => eLpNorm (Xlim - Xn n) 1 μ) atTop (𝓝 0) := by
    have : ∀ n, eLpNorm (Xlim - Xn n) 1 μ = eLpNorm (μ[f | 𝔽 n] - Xlim) 1 μ := by
      intro n
      simp only [hXn_def]
      rw [eLpNorm_sub_comm]
    simp only [this]
    exact hL1_conv

  -- Key inequality: ‖μ[Xlim | F_inf] - Y‖₁ ≤ ‖Xlim - Xn n‖₁ for all n
  have h_bound (n : ℕ) : eLpNorm (μ[Xlim | F_inf] - Y) 1 μ ≤ eLpNorm (Xlim - Xn n) 1 μ := by
    -- Triangle: (μ[Xlim|F_inf] - Y) = (μ[Xlim|F_inf] - μ[Xn|F_inf]) + (μ[Xn|F_inf] - Y)
    have htri : eLpNorm (μ[Xlim | F_inf] - Y) 1 μ
                ≤ eLpNorm (μ[Xlim | F_inf] - μ[Xn n | F_inf]) 1 μ
                  + eLpNorm (μ[Xn n | F_inf] - Y) 1 μ := by
      have : μ[Xlim | F_inf] - Y
              = (μ[Xlim | F_inf] - μ[Xn n | F_inf]) + (μ[Xn n | F_inf] - Y) := by ring
      rw [this]
      refine eLpNorm_add_le ?_ ?_ ?_
      · exact (integrable_condExp.sub integrable_condExp).aestronglyMeasurable
      · exact (integrable_condExp.sub integrable_condExp).aestronglyMeasurable
      · norm_num

    -- Second term is 0 by tower property
    have hzero : eLpNorm (μ[Xn n | F_inf] - Y) 1 μ = 0 := by
      have : μ[Xn n | F_inf] =ᵐ[μ] Y := by simpa [Xn, Y, hY_def, hXn_def] using h_tower n
      have : μ[Xn n | F_inf] - Y =ᵐ[μ] 0 := by filter_upwards [this] with ω hω; simp [hω]
      rw [eLpNorm_congr_ae this]
      simp

    -- First term ≤ ‖Xlim - Xn‖₁ by L¹-contraction + linearity (condExp_sub)
    have hfirst : eLpNorm (μ[Xlim | F_inf] - μ[Xn n | F_inf]) 1 μ ≤ eLpNorm (Xlim - Xn n) 1 μ := by
      -- linearity a.e.: μ[Xlim|F_inf] - μ[Xn|F_inf] = μ[Xlim - Xn | F_inf]
      have hsub : μ[Xlim | F_inf] - μ[Xn n | F_inf] =ᵐ[μ] μ[Xlim - Xn n | F_inf] := by
        exact (condExp_sub hXlimint integrable_condExp F_inf).symm
      -- contraction: ‖μ[g|F]‖₁ ≤ ‖g‖₁
      rw [eLpNorm_congr_ae hsub]
      exact eLpNorm_one_condExp_le_eLpNorm _

    -- Combine: triangle + zero + contraction
    calc eLpNorm (μ[Xlim | F_inf] - Y) 1 μ
        ≤ eLpNorm (μ[Xlim | F_inf] - μ[Xn n | F_inf]) 1 μ + eLpNorm (μ[Xn n | F_inf] - Y) 1 μ := htri
      _ = eLpNorm (μ[Xlim | F_inf] - μ[Xn n | F_inf]) 1 μ := by rw [hzero]; ring
      _ ≤ eLpNorm (Xlim - Xn n) 1 μ := hfirst

  -- Take limits: constant ≤ sequence → 0, so constant = 0
  have hCE_eqY : μ[Xlim | F_inf] =ᵐ[μ] Y := by
    -- From h_bound: eLpNorm (μ[Xlim | F_inf] - Y) 1 μ ≤ eLpNorm (Xlim - Xn n) 1 μ for all n
    -- Since Xn → Xlim in L¹, RHS → 0, so LHS = 0
    have h_norm_zero : eLpNorm (μ[Xlim | F_inf] - Y) 1 μ = 0 := by
      refine le_antisymm ?_ bot_le
      -- Constant ≤ sequence → 0 means constant = 0
      have : ∀ n, eLpNorm (μ[Xlim | F_inf] - Y) 1 μ ≤ eLpNorm (Xlim - Xn n) 1 μ := h_bound
      exact le_of_tendsto_of_tendsto tendsto_const_nhds hL1_conv_Xn (Eventually.of_forall this)
    rw [eLpNorm_eq_zero_iff (integrable_condExp.sub integrable_condExp).aestronglyMeasurable one_ne_zero] at h_norm_zero
    -- h_norm_zero : μ[Xlim | F_inf] - Y =ᵐ 0
    filter_upwards [h_norm_zero] with ω hω
    simp only [Pi.zero_apply] at hω
    exact sub_eq_zero.mp hω

  -- Xlim is F_inf-a.e.-measurable (as a.e. limit of F_inf-measurable functions)
  -- Therefore μ[Xlim | F_inf] = Xlim
  -- Combined with hCE_eqY : μ[Xlim | F_inf] =ᵐ Y, we get Y =ᵐ Xlim
  have hXlim_eq : Y =ᵐ[μ] Xlim := by
    -- First prove μ[Xlim | F_inf] = Xlim using the fact that Xlim is (essentially) F_inf-measurable
    -- Xlim is the limit of F_inf-measurable functions, so is itself F_inf-measurable
    have hXlim_condExp_self : μ[Xlim | F_inf] =ᵐ[μ] Xlim := by
      -- PROOF STRATEGY: Use that reverse martingale limits are F_inf-measurable.
      --
      -- Step 1: Show Xlim is AEStronglyMeasurable[F_inf]
      -- Each Xn = μ[f | 𝔽 n] is 𝔽 n-strongly-measurable. For antitone 𝔽, when n ≥ N:
      --   {Xn > a} ∈ 𝔽 n ⊆ 𝔽 N
      -- Hence lim sup {Xn > a} = ⋂_N ⋃_{n≥N} {Xn > a} ∈ ⋂_N 𝔽 N = F_inf.
      -- This shows Xlim is F_inf-measurable (see aestronglyMeasurable_iInf_of_tendsto_ae_antitone).
      --
      -- Step 2: Apply condExp_of_aestronglyMeasurable':
      -- If f is AEStronglyMeasurable[m] and integrable, then μ[f|m] =ᵐ f.
      --
      -- Step 1: Xlim is AEStronglyMeasurable[F_inf] via hXlim_iInf_meas (proved before set F_inf)
      -- F_inf = iInf 𝔽 = ⨅ n, 𝔽 n definitionally, so this is just type conversion
      have hXlim_F_inf_meas : AEStronglyMeasurable[F_inf] Xlim μ := hXlim_iInf_meas
      -- Step 2: Apply condExp_of_aestronglyMeasurable': μ[Xlim | F_inf] =ᵐ Xlim
      exact condExp_of_aestronglyMeasurable' hF_inf_le hXlim_F_inf_meas hXlimint

    -- Now use L¹-continuity: μ[Xlim | F_inf] =ᵐ Y and μ[Xlim | F_inf] =ᵐ Xlim
    -- Therefore Y =ᵐ Xlim
    exact hCE_eqY.symm.trans hXlim_condExp_self

  -- Finally: derive μ[Xlim | F_inf] =ᵐ[μ] Xlim from hCE_eqY and hXlim_eq
  -- Simple 2-step chain, no circularity
  have hXlim_condExp : μ[Xlim | F_inf] =ᵐ[μ] Xlim := by
    have h1 : μ[Xlim | F_inf] =ᵐ[μ] Y := hCE_eqY
    have h2 : Y =ᵐ[μ] Xlim := hXlim_eq
    exact h1.trans h2

  -- Return the desired result: combine h_tendsto with hXlim_eq
  -- We have: h_tendsto : μ[f|𝔽 n] → Xlim
  --          hXlim_eq  : Y =ᵐ Xlim (where Y = μ[f|F_inf])
  -- Goal: μ[f|𝔽 n] → Y
  filter_upwards [h_tendsto, hXlim_eq] with ω h_tend h_eq
  -- h_tend : μ[f|𝔽 n] ω → Xlim ω
  -- h_eq : Y ω = Xlim ω
  -- Want: μ[f|𝔽 n] ω → Y ω
  rw [h_eq]
  exact h_tend

end Exchangeability.Probability
