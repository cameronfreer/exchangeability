/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Exchangeability.DeFinetti.ViaKoopman.Infrastructure
import Exchangeability.DeFinetti.ViaKoopman.LpCondExpHelpers

/-! # Cesàro Helper Lemmas

Helper lemmas for the L¹ Cesàro convergence framework:
- `condexp_precomp_iterate_eq` - CE of shifted function equals CE of original
- `shift_iterate_apply` - evaluation formula for shift iteration
- `cesaro_ce_eq_condexp` - Cesàro average CE equals point CE
- `condexp_product_eq_at_one` - lag constancy for products
- `product_ce_constant_of_lag_const` - full lag constancy
- `product_ce_constant_of_lag_const_from_one` - tower from lag constancy

These lemmas are used by both the Cesàro convergence section and the
kernel independence framework.
-/

open Filter MeasureTheory

noncomputable section

namespace Exchangeability.DeFinetti.ViaKoopman

open MeasureTheory Filter Topology ProbabilityTheory
open Exchangeability.Ergodic
open Exchangeability.PathSpace
open scoped BigOperators

variable {α : Type*} [MeasurableSpace α]

-- Short notation for shift-invariant σ-algebra (used throughout this file)
local notation "mSI" => shiftInvariantSigma (α := α)


lemma condexp_precomp_iterate_eq
    {μ : Measure (Ω[α])} [IsProbabilityMeasure μ]
    (hσ : MeasurePreserving shift μ μ) {k : ℕ}
    {f : Ω[α] → ℝ} (hf : Integrable f μ) :
    μ[(fun ω => f ((shift (α := α))^[k] ω)) | shiftInvariantSigma (α := α)]
      =ᵐ[μ] μ[f | shiftInvariantSigma (α := α)] := by
  classical
  set shiftk := (shift (α := α))^[k] with hshiftk_def
  have h_shiftk_pres : MeasurePreserving shiftk μ μ := hσ.iterate k
  have h_shiftk_meas : AEMeasurable shiftk μ :=
    (measurable_shift (α := α)).iterate k |>.aemeasurable
  have h_int_shift : Integrable (fun ω => f (shiftk ω)) μ :=
    h_shiftk_pres.integrable_comp_of_integrable hf
  have h_condexp_int : Integrable (μ[f | shiftInvariantSigma (α := α)]) μ :=
    MeasureTheory.integrable_condExp
  refine (MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq
        (μ := μ) (m := shiftInvariantSigma (α := α))
        (hm := shiftInvariantSigma_le (α := α))
        (f := fun ω => f (shiftk ω))
        (g := μ[f | shiftInvariantSigma (α := α)])
        (hf := h_int_shift)
        (hg_int_finite := ?hg_int_finite)
        (hg_eq := ?hg_eq)
        (hgm := (MeasureTheory.stronglyMeasurable_condExp (μ := μ)).aestronglyMeasurable)).symm
  case hg_int_finite =>
    intro s hs _
    exact integrable_condExp.integrableOn
  case hg_eq =>
    intro s hs _
    have ⟨hS_meas, hS_shift⟩ := (mem_shiftInvariantSigma_iff (α := α) (s := s)).1 hs
    have hS_iter : shiftk ⁻¹' s = s := by
      rw [hshiftk_def]
      clear hshiftk_def shiftk h_shiftk_pres h_shiftk_meas h_int_shift h_condexp_int
      induction k with
      | zero => rfl
      | succ k hk =>
        rw [Function.iterate_succ']
        simp only [Set.preimage_comp, hk, hS_shift]
    have h_indicator_int : Integrable (s.indicator f) μ :=
      hf.indicator hS_meas
    have h_indicator_meas :
        AEStronglyMeasurable (s.indicator f) μ :=
      hf.aestronglyMeasurable.indicator hS_meas
    have hfm : AEStronglyMeasurable (s.indicator f) (Measure.map shiftk μ) := by
      simpa [h_shiftk_pres.map_eq] using h_indicator_meas
    have h_indicator_comp :
        ∫ ω, s.indicator f ω ∂μ
          = ∫ ω, s.indicator f (shiftk ω) ∂μ := by
      have :=
        MeasureTheory.integral_map
          (μ := μ) (φ := shiftk)
          (f := s.indicator f)
          (hφ := h_shiftk_meas)
          (hfm := hfm)
      simpa [h_shiftk_pres.map_eq] using this
    have h_mem_equiv : ∀ ω, (shiftk ω ∈ s) ↔ ω ∈ s := by
      intro ω
      constructor
      · intro hmem
        have : ω ∈ shiftk ⁻¹' s := by simpa [Set.mem_preimage] using hmem
        simpa [hS_iter] using this
      · intro hω
        have : ω ∈ shiftk ⁻¹' s := by simpa [hS_iter] using hω
        simpa [Set.mem_preimage] using this
    have h_indicator_comp' :
        ∫ ω, s.indicator f (shiftk ω) ∂μ
          = ∫ ω, s.indicator (fun ω => f (shiftk ω)) ω ∂μ := by
      refine integral_congr_ae (ae_of_all _ ?_)
      intro ω
      by_cases hω : ω ∈ s
      · have h_shiftk_mem : shiftk ω ∈ s := (h_mem_equiv ω).mpr hω
        simp [Set.indicator, hω, h_shiftk_mem]
      · have h_shiftk_mem : shiftk ω ∉ s := by
          intro hcontr
          exact hω ((h_mem_equiv ω).mp hcontr)
        simp [Set.indicator, hω, h_shiftk_mem]
    have h_indicator_eq :
        ∫ ω, s.indicator f ω ∂μ
          = ∫ ω, s.indicator (fun ω => f (shiftk ω)) ω ∂μ :=
      h_indicator_comp.trans h_indicator_comp'
    calc
      ∫ ω in s, μ[f | shiftInvariantSigma (α := α)] ω ∂μ
          = ∫ ω in s, f ω ∂μ :=
            MeasureTheory.setIntegral_condExp
              (μ := μ) (m := shiftInvariantSigma (α := α))
              (hm := shiftInvariantSigma_le (α := α))
              (hf := hf) (hs := hs)
      _ = ∫ ω, s.indicator f ω ∂μ :=
            (MeasureTheory.integral_indicator hS_meas).symm
      _ = ∫ ω, s.indicator (fun ω => f (shiftk ω)) ω ∂μ := h_indicator_eq
      _ = ∫ ω in s, (fun ω => f (shiftk ω)) ω ∂μ :=
            MeasureTheory.integral_indicator hS_meas

lemma shift_iterate_apply (k n : ℕ) (y : Ω[α]) :
    (shift (α := α))^[k] y n = y (n + k) := by
  induction k generalizing n with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply']; simp only [shift, ih]; ring_nf


lemma cesaro_ce_eq_condexp
    {μ : Measure (Ω[α])} [IsProbabilityMeasure μ] [StandardBorelSpace α]
    (hσ : MeasurePreserving shift μ μ)
    (g : α → ℝ)
    (hg_meas : Measurable g) (hg_bd : ∃ Cg, ∀ x, |g x| ≤ Cg)
    (n : ℕ) :
    μ[(fun ω => (1 / ((n + 1) : ℝ)) * (Finset.range (n + 1)).sum (fun j => g (ω j))) | mSI]
      =ᵐ[μ]
    μ[(fun ω => g (ω 0)) | mSI] := by
  classical
  have hmSI := shiftInvariantSigma_le (α := α)
  let A : Ω[α] → ℝ := fun ω => (1 / ((n + 1) : ℝ)) * (Finset.range (n + 1)).sum (fun j => g (ω j))
  set Y : Ω[α] → ℝ := fun ω => μ[(fun ω => g (ω 0)) | mSI] ω

  -- Push CE through the outer scalar
  have h_push :
      μ[A | mSI]
        =ᵐ[μ]
      (fun ω =>
        (1 / (n + 1 : ℝ)) *
          μ[(fun ω =>
              (Finset.range (n + 1)).sum (fun j => g (ω j))) | mSI] ω) := by
    have h_smul := condExp_smul (μ := μ) (m := mSI) (1 / (n + 1 : ℝ))
      (fun ω => (Finset.range (n + 1)).sum (fun j => g (ω j)))
    filter_upwards [h_smul] with ω hω
    simp only [A, Pi.smul_apply, smul_eq_mul] at hω ⊢
    exact hω

  -- Push CE through the finite sum
  have h_sum :
      μ[(fun ω =>
          (Finset.range (n + 1)).sum (fun j => g (ω j))) | mSI]
        =ᵐ[μ]
      (fun ω =>
        (Finset.range (n + 1)).sum (fun j => μ[(fun ω => g (ω j)) | mSI] ω)) := by
    have hint : ∀ j ∈ Finset.range (n + 1), Integrable (fun ω => g (ω j)) μ := fun j _ =>
      hg_bd.elim fun Cg hCg => integrable_of_bounded_measurable
        (hg_meas.comp (measurable_pi_apply j)) Cg (fun ω => hCg (ω j))
    exact condExp_sum_finset (m := mSI) (_hm := hmSI)
      (Finset.range (n + 1)) (fun j ω => g (ω j)) hint

  -- Each term μ[g(ωⱼ)| mSI] =ᵐ μ[g(ω₀)| mSI]
  have h_term : ∀ j, μ[(fun ω => g (ω j)) | mSI] =ᵐ[μ] μ[(fun ω => g (ω 0)) | mSI] := fun j => by
    have hg_0_int : Integrable (fun ω => g (ω 0)) μ :=
      hg_bd.elim fun Cg hCg => integrable_of_bounded_measurable
        (hg_meas.comp (measurable_pi_apply 0)) Cg (fun ω => hCg (ω 0))
    have h_shift : (fun ω => g (shift^[j] ω 0)) = (fun ω => g (ω j)) := by
      ext ω; simp only [shift_iterate_apply, zero_add]
    rw [← h_shift]; exact condexp_precomp_iterate_eq hσ hg_0_int

  -- Sum of identical a.e.-terms = (n+1) · that term
  have h_sum_const :
      (fun ω =>
        (Finset.range (n + 1)).sum (fun j => μ[(fun ω => g (ω j)) | mSI] ω))
        =ᵐ[μ]
      (fun ω =>
        (n + 1 : ℝ) * Y ω) := by
    have h' : ∀ s : Finset ℕ,
        (fun ω =>
          s.sum (fun j => μ[(fun ω => g (ω j)) | mSI] ω))
          =ᵐ[μ]
        (fun ω =>
          (s.card : ℝ) * Y ω) := by
      refine Finset.induction ?base ?step
      · exact ae_of_all μ (fun ω => by simp)
      · intro j s hj hInd
        have hj' :
            (fun ω => μ[(fun ω => g (ω j)) | mSI] ω)
              =ᵐ[μ]
            (fun ω => Y ω) := h_term j
        have h_eq : (fun ω => ∑ j ∈ insert j s, μ[fun ω => g (ω j)| mSI] ω)
                  = ((fun ω => ∑ j ∈ s, μ[fun ω => g (ω j)| mSI] ω) + (fun ω => μ[fun ω => g (ω j)| mSI] ω)) := by
          ext ω; simp [Finset.sum_insert hj, add_comm]
        rw [h_eq]
        calc (fun ω => ∑ j ∈ s, μ[fun ω => g (ω j)| mSI] ω) + (fun ω => μ[fun ω => g (ω j)| mSI] ω)
            =ᵐ[μ] (fun ω => ↑s.card * Y ω) + (fun ω => Y ω) := hInd.add hj'
          _ =ᵐ[μ] (fun ω => ↑(insert j s).card * Y ω) := by
              refine ae_of_all μ (fun ω => ?_)
              simp only [Pi.add_apply]
              rw [Finset.card_insert_of_notMem hj]
              simp only [Nat.cast_add, Nat.cast_one]
              ring
    simpa [Finset.card_range] using h' (Finset.range (n + 1))

  -- Assemble: push → sum → collapse → cancel (1/(n+1))·(n+1)
  have hne : ((n + 1) : ℝ) ≠ 0 := by positivity
  refine h_push.trans ?_
  have h2 :
      (fun ω =>
        (1 / (n + 1 : ℝ)) *
          μ[(fun ω =>
              (Finset.range (n + 1)).sum (fun j => g (ω j))) | mSI] ω)
        =ᵐ[μ]
      (fun ω =>
        (1 / (n + 1 : ℝ)) *
          (Finset.range (n + 1)).sum
            (fun j => μ[(fun ω => g (ω j)) | mSI] ω)) := by
    refine h_sum.mono ?_
    intro ω hω; simp [hω]
  refine h2.trans ?_
  have h3 :
      (fun ω =>
        (1 / (n + 1 : ℝ)) *
          (Finset.range (n + 1)).sum
            (fun j => μ[(fun ω => g (ω j)) | mSI] ω))
        =ᵐ[μ]
      (fun ω =>
        (1 / (n + 1 : ℝ)) *
          ((n + 1 : ℝ) * Y ω)) := by
    refine h_sum_const.mono ?_
    intro ω hω; simp [hω]
  refine h3.trans ?_
  exact ae_of_all μ (fun ω => by
    simp [Y]
    field_simp [one_div, hne, mul_comm, mul_left_comm, mul_assoc])

/-- **Lag constancy chain for j ≥ 1**: CE[f(ω₀)·g(ω_j)|ℐ] = CE[f(ω₀)·g(ω₁)|ℐ] for j ≥ 1.

This uses only k ≥ 1 lag constancy (avoiding the false k=0 case).
The induction has base case j=1 (reflexivity) and step uses k = j-1 ≥ 1. -/
lemma condexp_product_eq_at_one
    {μ : Measure (Ω[α])} [IsProbabilityMeasure μ] [StandardBorelSpace α]
    (hExch : ∀ π : Equiv.Perm ℕ, Measure.map (Exchangeability.reindex π) μ = μ)
    (f g : α → ℝ)
    (hf_meas : Measurable f) (hf_bd : ∃ Cf, ∀ x, |f x| ≤ Cf)
    (hg_meas : Measurable g) (hg_bd : ∃ Cg, ∀ x, |g x| ≤ Cg)
    (j : ℕ) (hj : 1 ≤ j) :
    μ[(fun ω => f (ω 0) * g (ω j)) | mSI]
      =ᵐ[μ]
    μ[(fun ω => f (ω 0) * g (ω 1)) | mSI] := by
  -- Strong induction: show for all j ≥ 1
  -- Base: j = 1 is reflexivity
  -- Step: j + 1 > 1 → use lag_const at k = j ≥ 1, then reduce to j
  match j with
  | 0 => omega  -- contradicts hj
  | 1 => rfl  -- CE[f·g_1] = CE[f·g_1]
  | k + 2 =>
    -- k + 2 ≥ 2, so k + 1 ≥ 1
    -- Use lag constancy at k + 1 ≥ 1: CE[f·g_{k+2}] = CE[f·g_{k+1}]
    have hk1_pos : 0 < k + 1 := Nat.succ_pos k
    have lag := condexp_lag_constant_from_exchangeability hExch f g
                  hf_meas hf_bd hg_meas hg_bd (k + 1) hk1_pos
    -- Recursive call: CE[f·g_{k+1}] = CE[f·g_1]
    have ih := condexp_product_eq_at_one hExch f g hf_meas hf_bd hg_meas hg_bd (k + 1) (Nat.succ_pos k)
    exact lag.trans ih


/-- **Section 2 helper**: Product CE is constant in n under lag-constancy.

Given lag-constancy (CE[f·g_{k+1}] = CE[f·g_k] for all k), proves that
`CE[f·A_n | mSI] = CE[f·g₀ | mSI]` for all n, where A_n is the Cesàro average.

This uses the lag-constancy hypothesis to collapse the sum termwise. -/
lemma product_ce_constant_of_lag_const
    {μ : Measure (Ω[α])} [IsProbabilityMeasure μ] [StandardBorelSpace α]
    (f g : α → ℝ)
    (hf_meas : Measurable f) (hf_bd : ∃ Cf, ∀ x, |f x| ≤ Cf)
    (hg_meas : Measurable g) (hg_bd : ∃ Cg, ∀ x, |g x| ≤ Cg)
    (lag_const :
      ∀ k : ℕ,
        μ[(fun ω => f (ω 0) * g (ω (k+1))) | shiftInvariantSigma (α := α)]
          =ᵐ[μ]
        μ[(fun ω => f (ω 0) * g (ω k)) | shiftInvariantSigma (α := α)])
    (n : ℕ) :
    let A := fun ω => (1 / ((n + 1) : ℝ)) * (Finset.range (n + 1)).sum (fun j => g (ω j))
    μ[(fun ω => f (ω 0) * A ω) | mSI]
      =ᵐ[μ]
    μ[(fun ω => f (ω 0) * g (ω 0)) | mSI] := by
  classical
  intro A
  -- Push CE through scalar
  have h_push :
      μ[(fun ω => f (ω 0) * A ω) | mSI]
        =ᵐ[μ]
      (fun ω =>
        (1 / ((n + 1) : ℝ)) *
          μ[(fun ω =>
              (Finset.range (n + 1)).sum
                (fun j => f (ω 0) * g (ω j))) | mSI] ω) := by
    have : (fun ω => f (ω 0) * A ω)
         = (fun ω => (1 / ((n + 1) : ℝ)) * (Finset.range (n + 1)).sum (fun j => f (ω 0) * g (ω j))) := by
      funext ω; simp [A, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]
    rw [this]
    exact condExp_const_mul (shiftInvariantSigma_le (α := α))
      (1 / ((n + 1) : ℝ)) (fun ω => (Finset.range (n + 1)).sum (fun j => f (ω 0) * g (ω j)))

  -- Push CE through the finite sum
  have h_sum :
      μ[(fun ω =>
          (Finset.range (n + 1)).sum (fun j => f (ω 0) * g (ω j))) | mSI]
        =ᵐ[μ]
      (fun ω =>
        (Finset.range (n + 1)).sum
          (fun j => μ[(fun ω => f (ω 0) * g (ω j)) | mSI] ω)) := by
    have hint : ∀ j ∈ Finset.range (n + 1), Integrable (fun ω => f (ω 0) * g (ω j)) μ := by
      intro j _
      obtain ⟨Cf, hCf⟩ := hf_bd
      obtain ⟨Cg, hCg⟩ := hg_bd
      exact integrable_of_bounded_measurable
        (hf_meas.comp (measurable_pi_apply 0) |>.mul (hg_meas.comp (measurable_pi_apply j)))
        (Cf * Cg)
        (fun ω => by simpa [abs_mul] using mul_le_mul (hCf (ω 0)) (hCg (ω j)) (abs_nonneg _) (le_trans (abs_nonneg _) (hCf (ω 0))))
    exact condExp_sum_finset (shiftInvariantSigma_le (α := α))
      (Finset.range (n + 1)) (fun j => fun ω => f (ω 0) * g (ω j)) hint

  -- From lag_const: every term is a.e.-equal to the j=0 term
  have h_term_const : ∀ j,
      μ[(fun ω => f (ω 0) * g (ω j)) | mSI]
        =ᵐ[μ]
      μ[(fun ω => f (ω 0) * g (ω 0)) | mSI] := by
    refine Nat.rec ?h0 ?hstep
    · rfl
    · intro k hk
      exact (lag_const k).trans hk

  -- Sum collapses to (n+1)·CE[f·g₀| mSI]
  have h_sum_const :
      (fun ω =>
        (Finset.range (n + 1)).sum
          (fun j => μ[(fun ω => f (ω 0) * g (ω j)) | mSI] ω))
        =ᵐ[μ]
      (fun ω =>
        ((n + 1) : ℝ) *
          μ[(fun ω => f (ω 0) * g (ω 0)) | mSI] ω) := by
    have h' : ∀ s : Finset ℕ,
        (fun ω =>
          s.sum (fun j => μ[(fun ω => f (ω 0) * g (ω j)) | mSI] ω))
          =ᵐ[μ]
        (fun ω =>
          (s.card : ℝ) *
            μ[(fun ω => f (ω 0) * g (ω 0)) | mSI] ω) := by
      apply Finset.induction
      · exact ae_of_all μ (fun ω => by simp)
      · intro j s hj hInd
        have hj' :
            (fun ω => μ[(fun ω => f (ω 0) * g (ω j)) | mSI] ω)
              =ᵐ[μ]
            (fun ω =>
              μ[(fun ω => f (ω 0) * g (ω 0)) | mSI] ω) := h_term_const j
        have h_eq : (fun ω => ∑ j ∈ insert j s, μ[(fun ω => f (ω 0) * g (ω j)) | mSI] ω)
                  = ((fun ω => ∑ j ∈ s, μ[(fun ω => f (ω 0) * g (ω j)) | mSI] ω) +
                     (fun ω => μ[(fun ω => f (ω 0) * g (ω j)) | mSI] ω)) := by
          ext ω; simp [Finset.sum_insert hj, add_comm]
        rw [h_eq]
        calc (fun ω => ∑ j ∈ s, μ[(fun ω => f (ω 0) * g (ω j)) | mSI] ω) +
               (fun ω => μ[(fun ω => f (ω 0) * g (ω j)) | mSI] ω)
            =ᵐ[μ] (fun ω => ↑s.card * μ[(fun ω => f (ω 0) * g (ω 0)) | mSI] ω) +
                   (fun ω => μ[(fun ω => f (ω 0) * g (ω 0)) | mSI] ω) := hInd.add hj'
          _ =ᵐ[μ] (fun ω => ↑(insert j s).card * μ[(fun ω => f (ω 0) * g (ω 0)) | mSI] ω) := by
              refine ae_of_all μ (fun ω => ?_)
              simp only [Pi.add_apply]
              rw [Finset.card_insert_of_notMem hj]
              simp only [Nat.cast_add, Nat.cast_one]
              ring
    simpa [Finset.card_range] using h' (Finset.range (n + 1))

  -- Assemble and cancel the average
  have hne : ((n + 1) : ℝ) ≠ 0 := by positivity
  refine h_push.trans ?_
  have h2 :
      (fun ω =>
        (1 / ((n + 1) : ℝ)) *
          μ[(fun ω =>
              (Finset.range (n + 1)).sum (fun j => f (ω 0) * g (ω j))) | mSI] ω)
        =ᵐ[μ]
      (fun ω =>
        (1 / ((n + 1) : ℝ)) *
          (Finset.range (n + 1)).sum
            (fun j => μ[(fun ω => f (ω 0) * g (ω j)) | mSI] ω)) := by
    refine h_sum.mono ?_
    intro ω hω; simp [hω]
  refine h2.trans ?_
  have h3 :
      (fun ω =>
        (1 / ((n + 1) : ℝ)) *
          (Finset.range (n + 1)).sum
            (fun j => μ[(fun ω => f (ω 0) * g (ω j)) | mSI] ω))
        =ᵐ[μ]
      (fun ω =>
        (1 / ((n + 1) : ℝ)) *
          (((n + 1) : ℝ) *
            μ[(fun ω => f (ω 0) * g (ω 0)) | mSI] ω)) := by
    refine h_sum_const.mono ?_
    intro ω hω; simp [hω]
  refine h3.trans ?_
  exact ae_of_all μ (fun ω => by
    field_simp [one_div, hne, mul_comm, mul_left_comm, mul_assoc])



/-- **Product CE constant from index 1**: CE[f·A'_n | mSI] = CE[f·g₁ | mSI]
where A'_n = (1/n)·Σ_{j=1}^n g(ω_j) is the Cesàro average starting from index 1.

This avoids the false k=0 lag constancy by only using k ≥ 1.
Each term CE[f·g_{j+1}] = CE[f·g₁] for j ∈ range n (so j+1 ≥ 1). -/
lemma product_ce_constant_of_lag_const_from_one
    {μ : Measure (Ω[α])} [IsProbabilityMeasure μ] [StandardBorelSpace α]
    (hExch : ∀ π : Equiv.Perm ℕ, Measure.map (Exchangeability.reindex π) μ = μ)
    (f g : α → ℝ)
    (hf_meas : Measurable f) (hf_bd : ∃ Cf, ∀ x, |f x| ≤ Cf)
    (hg_meas : Measurable g) (hg_bd : ∃ Cg, ∀ x, |g x| ≤ Cg)
    (n : ℕ) (hn : 0 < n) :
    -- A'_n = (1/n) * Σ_{j ∈ range n} g(ω_{j+1}) = (1/n) * Σ_{j=1}^n g(ω_j)
    let A' := fun ω => (1 / (n : ℝ)) * (Finset.range n).sum (fun j => g (ω (j + 1)))
    μ[(fun ω => f (ω 0) * A' ω) | mSI]
      =ᵐ[μ]
    μ[(fun ω => f (ω 0) * g (ω 1)) | mSI] := by
  classical
  intro A'
  -- Push CE through scalar
  have h_push :
      μ[(fun ω => f (ω 0) * A' ω) | mSI]
        =ᵐ[μ]
      (fun ω =>
        (1 / (n : ℝ)) *
          μ[(fun ω =>
              (Finset.range n).sum
                (fun j => f (ω 0) * g (ω (j + 1)))) | mSI] ω) := by
    have : (fun ω => f (ω 0) * A' ω)
         = (fun ω => (1 / (n : ℝ)) * (Finset.range n).sum (fun j => f (ω 0) * g (ω (j + 1)))) := by
      funext ω; simp [A', Finset.mul_sum, mul_left_comm]
    rw [this]
    exact condExp_const_mul (shiftInvariantSigma_le (α := α))
      (1 / (n : ℝ)) (fun ω => (Finset.range n).sum (fun j => f (ω 0) * g (ω (j + 1))))

  -- Push CE through the finite sum
  have h_sum :
      μ[(fun ω =>
          (Finset.range n).sum (fun j => f (ω 0) * g (ω (j + 1)))) | mSI]
        =ᵐ[μ]
      (fun ω =>
        (Finset.range n).sum
          (fun j => μ[(fun ω => f (ω 0) * g (ω (j + 1))) | mSI] ω)) := by
    have hint : ∀ j ∈ Finset.range n, Integrable (fun ω => f (ω 0) * g (ω (j + 1))) μ := by
      intro j _
      obtain ⟨Cf, hCf⟩ := hf_bd
      obtain ⟨Cg, hCg⟩ := hg_bd
      exact integrable_of_bounded_measurable
        (hf_meas.comp (measurable_pi_apply 0) |>.mul (hg_meas.comp (measurable_pi_apply (j + 1))))
        (Cf * Cg)
        (fun ω => by simpa [abs_mul] using mul_le_mul (hCf (ω 0)) (hCg (ω (j + 1))) (abs_nonneg _) (le_trans (abs_nonneg _) (hCf (ω 0))))
    exact condExp_sum_finset (shiftInvariantSigma_le (α := α))
      (Finset.range n) (fun j => fun ω => f (ω 0) * g (ω (j + 1))) hint

  -- From condexp_product_eq_at_one: every term is a.e.-equal to the j=1 term
  -- For j ∈ range n, we have j + 1 ≥ 1, so condexp_product_eq_at_one applies
  have h_term_const : ∀ j,
      μ[(fun ω => f (ω 0) * g (ω (j + 1))) | mSI]
        =ᵐ[μ]
      μ[(fun ω => f (ω 0) * g (ω 1)) | mSI] := by
    intro j
    exact condexp_product_eq_at_one hExch f g hf_meas hf_bd hg_meas hg_bd (j + 1) (Nat.one_le_of_lt (Nat.succ_pos j))

  -- Sum collapses to n·CE[f·g₁| mSI]
  have h_sum_const :
      (fun ω =>
        (Finset.range n).sum
          (fun j => μ[(fun ω => f (ω 0) * g (ω (j + 1))) | mSI] ω))
        =ᵐ[μ]
      (fun ω =>
        (n : ℝ) *
          μ[(fun ω => f (ω 0) * g (ω 1)) | mSI] ω) := by
    have h' : ∀ s : Finset ℕ,
        (fun ω =>
          s.sum (fun j => μ[(fun ω => f (ω 0) * g (ω (j + 1))) | mSI] ω))
          =ᵐ[μ]
        (fun ω =>
          (s.card : ℝ) *
            μ[(fun ω => f (ω 0) * g (ω 1)) | mSI] ω) := by
      apply Finset.induction
      · exact ae_of_all μ (fun ω => by simp)
      · intro j s hj hInd
        have hj' :
            (fun ω => μ[(fun ω => f (ω 0) * g (ω (j + 1))) | mSI] ω)
              =ᵐ[μ]
            (fun ω =>
              μ[(fun ω => f (ω 0) * g (ω 1)) | mSI] ω) := h_term_const j
        have h_eq : (fun ω => ∑ k ∈ insert j s, μ[(fun ω => f (ω 0) * g (ω (k + 1))) | mSI] ω)
                  = ((fun ω => ∑ k ∈ s, μ[(fun ω => f (ω 0) * g (ω (k + 1))) | mSI] ω) +
                     (fun ω => μ[(fun ω => f (ω 0) * g (ω (j + 1))) | mSI] ω)) := by
            ext ω; simp [Finset.sum_insert hj, add_comm]
        rw [h_eq]
        calc (fun ω => ∑ k ∈ s, μ[(fun ω => f (ω 0) * g (ω (k + 1))) | mSI] ω) +
               (fun ω => μ[(fun ω => f (ω 0) * g (ω (j + 1))) | mSI] ω)
            =ᵐ[μ] (fun ω => ↑s.card * μ[(fun ω => f (ω 0) * g (ω 1)) | mSI] ω) +
                   (fun ω => μ[(fun ω => f (ω 0) * g (ω 1)) | mSI] ω) := hInd.add hj'
          _ =ᵐ[μ] (fun ω => ↑(insert j s).card * μ[(fun ω => f (ω 0) * g (ω 1)) | mSI] ω) := by
              refine ae_of_all μ (fun ω => ?_)
              simp only [Pi.add_apply]
              rw [Finset.card_insert_of_notMem hj]
              simp only [Nat.cast_add, Nat.cast_one]
              ring
    simpa [Finset.card_range] using h' (Finset.range n)

  -- Assemble and cancel the average
  have hne : (n : ℝ) ≠ 0 := by positivity
  refine h_push.trans ?_
  have h2 :
      (fun ω =>
        (1 / (n : ℝ)) *
          μ[(fun ω =>
              (Finset.range n).sum (fun j => f (ω 0) * g (ω (j + 1)))) | mSI] ω)
        =ᵐ[μ]
      (fun ω =>
        (1 / (n : ℝ)) *
          (Finset.range n).sum
            (fun j => μ[(fun ω => f (ω 0) * g (ω (j + 1))) | mSI] ω)) := by
    refine h_sum.mono ?_
    intro ω hω; simp [hω]
  refine h2.trans ?_
  have h3 :
      (fun ω =>
        (1 / (n : ℝ)) *
          (Finset.range n).sum
            (fun j => μ[(fun ω => f (ω 0) * g (ω (j + 1))) | mSI] ω))
        =ᵐ[μ]
      (fun ω =>
        (1 / (n : ℝ)) *
          ((n : ℝ) *
            μ[(fun ω => f (ω 0) * g (ω 1)) | mSI] ω)) := by
    refine h_sum_const.mono ?_
    intro ω hω; simp [hω]
  refine h3.trans ?_
  exact ae_of_all μ (fun ω => by
    field_simp [one_div, hne, mul_comm, mul_left_comm, mul_assoc])


end Exchangeability.DeFinetti.ViaKoopman
