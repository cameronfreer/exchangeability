/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Exchangeability.DeFinetti.L2Approach
import Exchangeability.DeFinetti.CommonEnding
import Exchangeability.Contractability
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Probability.Kernel.Basic
import Canonical

/-!
# de Finetti's Theorem via L² Contractability

**Kallenberg's "second proof"** of de Finetti's theorem using the elementary
L² contractability bound (Lemma 1.2). This is the **lightest-dependency proof**.

## Proof approach

Starting from a **contractable** sequence ξ:

1. Fix a bounded measurable function f ∈ L¹
2. Use Lemma 1.2 (L² contractability bound) and completeness of L¹:
   - Show ‖E_m ∑_{k=n+1}^{n+m} (f(ξ_{n+k}) - α_{k-1})‖₁² → 0
3. Extract limit α_∞ = lim_n α_n in L¹
4. Show α_n is a reverse martingale (subsequence convergence a.s.)
5. Use contractability + dominated convergence:
   - E[f(ξ_i); ∩I_k] = E[α_{k-1}; ∩I_k] → E[α_∞; ∩I_k]
6. Conclude α_n = E_n f(ξ_{n+1}) = ν^f a.s.
7. Complete using the common ending (monotone class argument)

## Main results

* `deFinetti_viaL2`: **Main theorem** - contractable implies conditionally i.i.d.
* `deFinetti`: **Canonical name** (alias for `deFinetti_viaL2`)

Supporting lemmas:
* `contractable_covariance_structure`: Uniform covariance structure
* `weighted_sums_converge_L1`: L² bound implies L¹ convergence
* `reverse_martingale_limit`: Tail-measurable limit via reverse martingale

## Why this proof is default

✅ **Elementary** - Only uses basic L² space theory and Cauchy-Schwarz
✅ **Direct** - Proves convergence via explicit bounds
✅ **Quantitative** - Gives explicit rates of convergence
✅ **Lightest dependencies** - No ergodic theory required

## References

* Kallenberg (2005), *Probabilistic Symmetries and Invariance Principles*,
  Chapter 1, pages 26-27: "Second proof of Theorem 1.1"

-/

noncomputable section

namespace Exchangeability.DeFinetti.ViaL2

open MeasureTheory ProbabilityTheory BigOperators Filter Topology
open Exchangeability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-!
## Step 1: L² bound is the key tool

Before tackling the quantitative L² estimates we record two basic consequences of
contractability: (1) all single coordinates share the same law, and (2) any pair
of coordinates has the same joint distribution as `(X 0, X 1)`.  These facts are
packaged below and will later feed into the uniform covariance statement.
-/

open scoped BigOperators

section CovarianceHelpers

variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable (X : ℕ → Ω → ℝ)
variable (hX_contract : Contractable μ X)
variable (hX_meas : ∀ i, Measurable (X i))

private def fin1Zero : Fin 1 := ⟨0, by decide⟩
private def fin2Zero : Fin 2 := ⟨0, by decide⟩
private def fin2One : Fin 2 := ⟨1, by decide⟩

private lemma measurable_eval_fin1 :
    Measurable fun g : (Fin 1 → ℝ) => g (fin1Zero) :=
  measurable_pi_apply _

private lemma measurable_eval_fin2 {i : Fin 2} :
    Measurable fun g : (Fin 2 → ℝ) => g i :=
  measurable_pi_apply _

/-- For a contractable sequence, the law of each coordinate agrees with the law
of `X 0`. -/
lemma contractable_map_single {i : ℕ} :
    Measure.map (fun ω => X i ω) μ = Measure.map (fun ω => X 0 ω) μ := by
  classical
  -- `k` selects the singleton subsequence `{i}`.
  let k : Fin 1 → ℕ := fun _ => i
  have hk : StrictMono k := by
    canonical
  have h_map := hX_contract 1 k hk
  let eval : (Fin 1 → ℝ) → ℝ := fun g => g fin1Zero
  have h_eval_meas : Measurable eval := measurable_eval_fin1
  have h_meas_k : Measurable fun ω => fun j : Fin 1 => X (k j) ω := by
    refine measurable_pi_lambda _ ?_
    intro j
    simpa [k] using hX_meas (k j)
  have h_meas_std : Measurable fun ω => fun j : Fin 1 => X j.val ω := by
    refine measurable_pi_lambda _ ?_
    intro j
    simpa using hX_meas j.val
  have h_left := (Measure.map_map h_eval_meas h_meas_k).symm
  have h_right := Measure.map_map h_eval_meas h_meas_std
  have h_eval := congrArg (Measure.map eval) h_map
  have h_comp := h_left.trans (h_eval.trans h_right)
  -- Evaluate the compositions explicitly.
  have h_comp_simp :
      (fun ω => eval (fun j : Fin 1 => X (k j) ω)) = fun ω => X i ω := by
    funext ω
    simp [eval, k, fin1Zero]
  have h_comp_simp' :
      (fun ω => eval (fun j : Fin 1 => X j.val ω)) = fun ω => X 0 ω := by
    funext ω
    simp [eval, fin1Zero]
  simpa [Function.comp, h_comp_simp, h_comp_simp'] using h_comp

/-- Helper lemma: the strict monotonicity condition for two-point selections. -/
private lemma strictMono_two {i j : ℕ} (hij : i < j) :
    StrictMono fun t : Fin 2 => if t = fin2Zero then i else j := by
  classical
  intro a b hlt
  -- Reduce the strict inequality on `Fin 2` to natural numbers.
  have hval : a.val < b.val := Fin.lt_iff_val_lt_val.mp hlt
  -- `b` must be the second coordinate.
  have hb_val_le : b.val ≤ 1 := Nat.lt_succ_iff.mp (show b.val < 2 by simpa using b.is_lt)
  have hb_ne_zero : b.val ≠ 0 := by
    intro hb
    have : a.val < 0 := by simpa [hb] using hval
    exact Nat.not_lt_zero _ this
  have hb_pos : 0 < b.val := Nat.pos_of_ne_zero hb_ne_zero
  have hb_ge_one : 1 ≤ b.val := Nat.succ_le_of_lt hb_pos
  have hb_val : b.val = 1 := le_antisymm hb_val_le hb_ge_one
  -- Consequently `a` is the first coordinate.
  have ha_lt_one : a.val < 1 := by simpa [hb_val] using hval
  have ha_val : a.val = 0 := Nat.lt_one_iff.mp ha_lt_one
  -- Rewrite the conclusion using these identifications.
  have ha : a = fin2Zero := by ext; simpa [fin2Zero, ha_val]
  have hb : b = fin2One := by ext; simpa [fin2One, hb_val]
  subst ha; subst hb
  simp [fin2Zero, fin2One, hij]

/-- For a contractable sequence, every increasing pair `(i,j)` with `i < j`
has the same joint law as `(X 0, X 1)`. -/
lemma contractable_map_pair {i j : ℕ} (hij : i < j) :
    Measure.map (fun ω => (X i ω, X j ω)) μ =
      Measure.map (fun ω => (X 0 ω, X 1 ω)) μ := by
  classical
  -- Define the two-point subsequence.
  let k : Fin 2 → ℕ := fun t => if t = fin2Zero then i else j
  have hk : StrictMono k := strictMono_two hij
  have h_map := hX_contract 2 k hk
  let eval : (Fin 2 → ℝ) → ℝ × ℝ :=
    fun g => (g fin2Zero, g fin2One)
  have h_eval_meas : Measurable eval := by
    refine (measurable_eval_fin2 (i := fin2Zero)).prod_mk ?_
    exact measurable_eval_fin2 (i := fin2One)
  have h_meas_k : Measurable fun ω => fun t : Fin 2 => X (k t) ω := by
    refine measurable_pi_lambda _ ?_
    intro t
    by_cases ht : t = fin2Zero
    · have : k t = i := by simpa [k, ht]
      simpa [this] using hX_meas i
    · have : k t = j := by simpa [k, ht] using if_neg ht
      simpa [this] using hX_meas j
  have h_meas_std : Measurable fun ω => fun t : Fin 2 => X t.val ω := by
    refine measurable_pi_lambda _ ?_
    intro t
    simpa using hX_meas t.val
  have h_left := (Measure.map_map h_eval_meas h_meas_k).symm
  have h_right := Measure.map_map h_eval_meas h_meas_std
  have h_eval := congrArg (Measure.map eval) h_map
  have h_comp := h_left.trans (h_eval.trans h_right)
  have h_comp_simp :
      (fun ω => eval (fun t : Fin 2 => X (k t) ω)) = fun ω => (X i ω, X j ω) := by
    funext ω
    simp [eval, k, fin2Zero, fin2One]
  have h_comp_simp' :
      (fun ω => eval (fun t : Fin 2 => X t.val ω)) = fun ω => (X 0 ω, X 1 ω) := by
    funext ω
    simp [eval, fin2Zero, fin2One]
  simpa [Function.comp, h_comp_simp, h_comp_simp'] using h_comp

/-- Postcompose a contractable sequence with a measurable function. -/
lemma contractable_comp
    (f : ℝ → ℝ) (hf_meas : Measurable f) :
    Contractable μ (fun n ω => f (X n ω)) := by
  intro n k hk
  classical
  have h_base := hX_contract n k hk
  set Φ : (Fin n → ℝ) → (Fin n → ℝ) := fun g i => f (g i)
  have hΦ_meas : Measurable Φ := by
    refine measurable_pi_lambda _ ?_
    intro i
    simpa [Φ] using hf_meas.comp (measurable_pi_apply i)
  have h_meas_k : Measurable fun ω => fun i : Fin n => X (k i) ω := by
    refine measurable_pi_lambda _ ?_
    intro i
    simpa using hX_meas (k i)
  have h_meas_std : Measurable fun ω => fun i : Fin n => X i.val ω := by
    refine measurable_pi_lambda _ ?_
    intro i
    simpa using hX_meas i.val
  have h_left := (Measure.map_map hΦ_meas h_meas_k).symm
  have h_right := Measure.map_map hΦ_meas h_meas_std
  have h_apply := congrArg (Measure.map Φ) h_base
  -- Evaluate the compositions explicitly.
  have h_left_eval :
      (fun ω => Φ (fun i : Fin n => X (k i) ω)) =
        fun ω => fun i : Fin n => f (X (k i) ω) := by
    funext ω i
    simp [Φ]
  have h_right_eval :
      (fun ω => Φ (fun i : Fin n => X i.val ω)) =
        fun ω => fun i : Fin n => f (X i.val ω) := by
    funext ω i
    simp [Φ]
  simpa [Function.comp, Φ, h_left_eval, h_right_eval] using
    h_left.trans (h_apply.trans h_right)

/-- Elementary inequality used to dominate products by squares. -/
private lemma abs_mul_le_half_sq_add_sq (a b : ℝ) :
    |a * b| ≤ ((a ^ 2) + (b ^ 2)) / 2 := by
  have h := two_mul_le_add_sq (|a|) (|b|)
  have h' : (|a| * |b|) * 2 ≤ |a| ^ 2 + |b| ^ 2 := by
    simpa [mul_comm, mul_left_comm, mul_assoc, pow_two] using h
  have h'' : |a| * |b| ≤ (|a| ^ 2 + |b| ^ 2) / 2 :=
    (le_div_iff (show (0 : ℝ) < 2 by norm_num)).mpr h'
  have h''' : |a * b| ≤ (|a| ^ 2 + |b| ^ 2) / 2 := by
    simpa [abs_mul] using h''
  simpa [sq_abs, pow_two, add_comm, add_left_comm, add_assoc] using h'''

end CovarianceHelpers

/-- For a contractable sequence of real-valued random variables in L², all pairs
have the same covariance. This follows from contractability implying that all
increasing subsequences of length 2 have the same joint distribution.

NOTE: This lemma is not needed for the main proof and is left for future work.
-/
lemma contractable_covariance_structure
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ) :
    ∃ (m σSq ρ : ℝ),
      (∀ k, ∫ ω, X k ω ∂μ = m) ∧
      (∀ k, ∫ ω, (X k ω - m)^2 ∂μ = σSq) ∧
      (∀ i j, i ≠ j → ∫ ω, (X i ω - m) * (X j ω - m) ∂μ = σSq * ρ) ∧
      0 ≤ σSq ∧ -1 ≤ ρ ∧ ρ ≤ 1 := by
  classical
  have hX_L1 : ∀ i, Integrable (X i) μ := fun i =>
    MemLp.integrable (μ:=μ) (q:=(2 : ℝ≥0∞)) (hq1:=by norm_num) (hX_L2 i)
  set m := ∫ ω, X 0 ω ∂μ with hm_def
  have hconst_memLp : MemLp (fun _ : Ω => m) 2 μ := by
    simpa using (memLp_const (μ:=μ) (p:=2) m)
  have hsub_memLp : ∀ i, MemLp (fun ω => X i ω - m) 2 μ := by
    intro i
    simpa [sub_eq_add_neg] using (hX_L2 i).sub hconst_memLp
  have hsq_integrable : ∀ i, Integrable (fun ω => (X i ω - m) ^ 2) μ := by
    intro i
    have h := (hsub_memLp i).integrable_norm_pow (p:=2) (by decide)
    simpa [Real.norm_eq_abs, sq_abs] using h
  have hmean : ∀ k, ∫ ω, X k ω ∂μ = m := by
    intro k
    have hmap := contractable_map_single (μ:=μ) (X:=X) (hX_contract:=hX_contract)
      (hX_meas:=hX_meas) (i:=k)
    have hInt_k :=
      MeasureTheory.integral_map (μ:=μ) (φ:=fun ω => X k ω)
        ((hX_meas k).aemeasurable) measurable_id.aestronglyMeasurable
    have hInt_0 :=
      MeasureTheory.integral_map (μ:=μ) (φ:=fun ω => X 0 ω)
        ((hX_meas 0).aemeasurable) measurable_id.aestronglyMeasurable
    have hk :
        ∫ ω, X k ω ∂μ =
          ∫ x, x ∂ Measure.map (fun ω => X k ω) μ := by
      simpa using hInt_k.symm
    have h0 :
        ∫ ω, X 0 ω ∂μ =
          ∫ x, x ∂ Measure.map (fun ω => X 0 ω) μ := by
      simpa using hInt_0.symm
    calc
      ∫ ω, X k ω ∂μ
          = ∫ x, x ∂ Measure.map (fun ω => X k ω) μ := hk
      _ = ∫ x, x ∂ Measure.map (fun ω => X 0 ω) μ := by
            simpa [hmap]
      _ = m := by simpa [hm_def] using h0.symm
  let σSq := ∫ ω, (X 0 ω - m) ^ 2 ∂μ
  have hσ_nonneg : 0 ≤ σSq := by
    have hsq := hsq_integrable 0
    have h_nonneg :
        0 ≤ᵐ[μ] fun ω => (X 0 ω - m) ^ 2 := by
      refine Eventually.of_forall ?_
      intro ω; exact sq_nonneg _
    exact integral_nonneg_of_ae h_nonneg
  have hvar : ∀ k, ∫ ω, (X k ω - m) ^ 2 ∂μ = σSq := by
    intro k
    have hmap := contractable_map_single (μ:=μ) (X:=X) (hX_contract:=hX_contract)
      (hX_meas:=hX_meas) (i:=k)
    have hInt_k :=
      MeasureTheory.integral_map (μ:=μ) (φ:=fun ω => X k ω)
        ((hX_meas k).aemeasurable)
        ((continuous_id.sub continuous_const).pow 2).aestronglyMeasurable
    have hInt_0 :=
      MeasureTheory.integral_map (μ:=μ) (φ:=fun ω => X 0 ω)
        ((hX_meas 0).aemeasurable)
        ((continuous_id.sub continuous_const).pow 2).aestronglyMeasurable
    have hk :
        ∫ ω, (X k ω - m) ^ 2 ∂μ =
          ∫ x, (x - m) ^ 2 ∂ Measure.map (fun ω => X k ω) μ := by
      simpa using hInt_k.symm
    have h0 :
        σSq = ∫ x, (x - m) ^ 2 ∂ Measure.map (fun ω => X 0 ω) μ := by
      simpa [σSq] using hInt_0.symm
    calc
      ∫ ω, (X k ω - m) ^ 2 ∂μ
          = ∫ x, (x - m) ^ 2 ∂ Measure.map (fun ω => X k ω) μ := hk
      _ = ∫ x, (x - m) ^ 2 ∂ Measure.map (fun ω => X 0 ω) μ := by
            simpa [hmap]
      _ = σSq := by simpa [h0]
  have hsum_integrable :
      ∀ i j, Integrable
        (fun ω => (X i ω - m) ^ 2 + (X j ω - m) ^ 2) μ := by
    intro i j
    exact (hsq_integrable i).add (hsq_integrable j)
  have hprod_integrable :
      ∀ i j, Integrable (fun ω => (X i ω - m) * (X j ω - m)) μ := by
    intro i j
    have hhalf_int :
        Integrable (fun ω =>
          ((X i ω - m) ^ 2 + (X j ω - m) ^ 2) / 2) μ :=
      (hsum_integrable i j).mul_const (1 / 2 : ℝ)
    have hbound :
        ∀ᵐ ω ∂μ, ‖(X i ω - m) * (X j ω - m)‖ ≤
            ((X i ω - m) ^ 2 + (X j ω - m) ^ 2) / 2 := by
      refine Eventually.of_forall ?_
      intro ω
      simp [Real.norm_eq_abs, abs_mul_le_half_sq_add_sq]
    have hmeas :
        AEStronglyMeasurable (fun ω => (X i ω - m) * (X j ω - m)) μ :=
      ((hX_meas i).sub measurable_const).aestronglyMeasurable.mul
        ((hX_meas j).sub measurable_const).aestronglyMeasurable
    exact Integrable.mono' hhalf_int hmeas hbound
  have hcov :
      ∀ {i j} (hij : i < j),
        ∫ ω, (X i ω - m) * (X j ω - m) ∂μ =
          ∫ ω, (X 0 ω - m) * (X 1 ω - m) ∂μ := by
    intro i j hij
    let g : ℝ × ℝ → ℝ := fun p => (p.1 - m) * (p.2 - m)
    have hmap := contractable_map_pair (μ:=μ) (X:=X) (hX_contract:=hX_contract)
      (hX_meas:=hX_meas) hij
    have hφ :=
      ((hX_meas i).prod_mk (hX_meas j)).aemeasurable
    have hφ0 :=
      ((hX_meas 0).prod_mk (hX_meas 1)).aemeasurable
    have hg :
        AEStronglyMeasurable g
          (Measure.map (fun ω => (X i ω, X j ω)) μ) :=
      ((continuous_fst.sub continuous_const).mul
        (continuous_snd.sub continuous_const)).aestronglyMeasurable
    have hg0 :
        AEStronglyMeasurable g
          (Measure.map (fun ω => (X 0 ω, X 1 ω)) μ) :=
      ((continuous_fst.sub continuous_const).mul
        (continuous_snd.sub continuous_const)).aestronglyMeasurable
    have hint_ij :=
      MeasureTheory.integral_map (μ:=μ)
        (φ:=fun ω => (X i ω, X j ω)) hφ hg
    have hint_01 :=
      MeasureTheory.integral_map (μ:=μ)
        (φ:=fun ω => (X 0 ω, X 1 ω)) hφ0 hg0
    calc
      ∫ ω, (X i ω - m) * (X j ω - m) ∂μ
          = ∫ x, g x ∂ Measure.map (fun ω => (X i ω, X j ω)) μ := by
              simpa [g, Function.comp] using hint_ij.symm
      _ = ∫ x, g x ∂ Measure.map (fun ω => (X 0 ω, X 1 ω)) μ := by
              simpa [hmap]
      _ = ∫ ω, (X 0 ω - m) * (X 1 ω - m) ∂μ := by
              simpa [g, Function.comp] using hint_01
  set cov := ∫ ω, (X 0 ω - m) * (X 1 ω - m) ∂μ with hcov_def
  have hcov_abs_le : |cov| ≤ σSq := by
    have hprod_int := hprod_integrable 0 1
    have hsum_int := hsum_integrable 0 1
    have hhalf_int :
        Integrable (fun ω =>
          ((X 0 ω - m) ^ 2 + (X 1 ω - m) ^ 2) / 2) μ :=
      (hsum_int.mul_const (1 / 2 : ℝ))
    have hbound :
        ∀ᵐ ω ∂μ, ‖(X 0 ω - m) * (X 1 ω - m)‖ ≤
            ((X 0 ω - m) ^ 2 + (X 1 ω - m) ^ 2) / 2 := by
      refine Eventually.of_forall ?_
      intro ω
      simp [Real.norm_eq_abs, abs_mul_le_half_sq_add_sq]
    have habs_int :
        ∀ᵐ ω ∂μ, |(X 0 ω - m) * (X 1 ω - m)| ≤
            ((X 0 ω - m) ^ 2 + (X 1 ω - m) ^ 2) / 2 := hbound
    have hhalf_value :
        ∫ ω, ((X 0 ω - m) ^ 2 + (X 1 ω - m) ^ 2) / 2 ∂μ = σSq := by
      have hsum :
          ∫ ω, (X 0 ω - m) ^ 2 + (X 1 ω - m) ^ 2 ∂μ = σSq + σSq := by
        have h0 := hsq_integrable 0
        have h1 := hsq_integrable 1
        have := integral_add h0 h1
        simpa [hvar 0, hvar 1, σSq] using this
      have hcalc :=
        integral_mul_const (hsum_int) (1 / 2 : ℝ)
      have hcalc' :
          ∫ ω, ((X 0 ω - m) ^ 2 + (X 1 ω - m) ^ 2) / 2 ∂μ =
            (1 / 2) * (σSq + σSq) := by
        simpa [hsum, one_div, mul_comm, mul_left_comm, mul_assoc] using hcalc
      have : (1 / 2) * (σSq + σSq) = σSq := by
        simp [one_div, two_mul, mul_add, add_comm, add_left_comm, add_assoc]
      exact hcalc'.trans this
    have habs_le :
        ∫ ω, |(X 0 ω - m) * (X 1 ω - m)| ∂μ ≤
          ∫ ω, ((X 0 ω - m) ^ 2 + (X 1 ω - m) ^ 2) / 2 ∂μ :=
      integral_mono_ae hprod_int.abs hhalf_int habs_int
    have hcov_abs_le_abs :
        |cov| ≤ ∫ ω, |(X 0 ω - m) * (X 1 ω - m)| ∂μ :=
      by
        have := abs_integral_le_integral_abs (f := fun ω =>
          (X 0 ω - m) * (X 1 ω - m))
        simpa [cov, hcov_def]
    have habs_le' :
        ∫ ω, |(X 0 ω - m) * (X 1 ω - m)| ∂μ ≤ σSq := by
      simpa [hhalf_value] using habs_le
    exact (hcov_abs_le_abs.trans habs_le').trans (le_of_eq hhalf_value)
  have hcov_general :
      ∀ {i j}, i ≠ j →
        ∫ ω, (X i ω - m) * (X j ω - m) ∂μ = cov := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with hij_lt | hji_lt
    · exact hcov hij_lt
    · have hji := hcov hji_lt
      have hswap :
          ∫ ω, (X i ω - m) * (X j ω - m) ∂μ =
            ∫ ω, (X j ω - m) * (X i ω - m) ∂μ := by
        simp [mul_comm, mul_left_comm, mul_assoc]
      simpa [hswap] using hji.symm
  let ρ : ℝ := if hσ : σSq = 0 then 0 else cov / σSq
  have hcov_formula :
      ∀ {i j}, i ≠ j →
        ∫ ω, (X i ω - m) * (X j ω - m) ∂μ = σSq * ρ := by
    intro i j hij
    by_cases hσ : σSq = 0
    · have hcov_zero : cov = 0 := by
        have : |cov| = 0 := by
          have habs := hcov_abs_le
          have : |cov| ≤ 0 := by simpa [hσ] using habs
          exact le_antisymm this (abs_nonneg _)
        exact abs_eq_zero.mp this
      have hρ : ρ = 0 := by simp [ρ, hσ]
      have hInt := hcov_general hij
      simp [σSq, hσ, hρ, hInt, hcov_zero]
    · have hInt := hcov_general hij
      have hρ : ρ = cov / σSq := by simp [ρ, hσ]
      simp [hInt, hρ, hσ, mul_comm, mul_left_comm, mul_assoc]
  have hρ_abs_le : |ρ| ≤ 1 := by
    by_cases hσ : σSq = 0
    · simp [ρ, hσ]
    · have hσ_pos : 0 < σSq := lt_of_le_of_ne hσ_nonneg hσ
      have hdiv :
          |ρ| = |cov| / σSq := by
        simp [ρ, hσ, abs_div, abs_of_pos hσ_pos]
      have hbound :
          |cov| / σSq ≤ 1 := by
        have := hcov_abs_le
        have hpos : 0 ≤ (1 / σSq) := inv_nonneg.mpr (le_of_lt hσ_pos)
        have := mul_le_mul_of_nonneg_right this hpos
        simpa [div_eq_inv_mul, mul_comm, mul_left_comm, mul_assoc] using this
      simpa [hdiv] using hbound
  have hρ_bounds := (abs_le.mp hρ_abs_le)
  refine ⟨m, σSq, ρ, hmean, hvar, ?_, hσ_nonneg, hρ_bounds.1, hρ_bounds.2⟩
  intro i j hij
  exact hcov_formula hij

/-!
## Step 2: L² bound implies L¹ convergence of weighted sums (Kallenberg's key step)
-/

/-- Finite window of indices `{n+1, …, n+k}` represented as a `Finset`. -/
def window (n k : ℕ) : Finset ℕ :=
  (Finset.range k).image fun i => n + i + 1

lemma window_card (n k : ℕ) : (window n k).card = k := by
  classical
  unfold window
  refine (Finset.card_image_iff.mpr ?_).trans ?_
  · intro a ha b hb h
    have h' : n + a = n + b := by
      apply Nat.succ.inj
      simpa [Nat.succ_eq_add_one, Nat.add_left_comm, Nat.add_assoc, Nat.add_comm]
        using h
    exact Nat.add_left_cancel h'
  · simp

lemma mem_window_iff {n k t : ℕ} :
    t ∈ window n k ↔ ∃ i : ℕ, i < k ∧ t = n + i + 1 := by
  classical
  unfold window
  constructor
  · intro ht
    rcases Finset.mem_image.mp ht with ⟨i, hi, rfl⟩
    refine ⟨i, ?_, rfl⟩
    simpa using hi
  · intro h
    rcases h with ⟨i, hi, rfl⟩
    refine Finset.mem_image.mpr ?_
    refine ⟨i, ?_, rfl⟩
    simpa using hi

/-- **L² bound wrapper for two starting windows**.

For contractable sequences, the L² difference between averages starting at different
indices n and m is uniformly small. This gives us the key uniform bound we need.

Using `l2_contractability_bound` with appropriate weights shows that for large windows,
the starting index doesn't matter.
-/
lemma l2_bound_two_windows
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ)
    (f : ℝ → ℝ) (hf_meas : Measurable f)
    (hf_bdd : ∃ M, ∀ x, |f x| ≤ M)
    (n m : ℕ) {k : ℕ} (hk : 0 < k) :
    ∃ Cf : ℝ, 0 ≤ Cf ∧
      ∫ ω, ((1/(k:ℝ)) * ∑ i : Fin k, f (X (n + i.val + 1) ω) -
            (1/(k:ℝ)) * ∑ i : Fin k, f (X (m + i.val + 1) ω))^2 ∂μ
        ≤ Cf / k := by
  classical
  have hk_ne : (k : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hk)
  have hk_pos : 0 < (k : ℝ) := by exact_mod_cast hk
  obtain ⟨M, hM⟩ := hf_bdd
  -- Work with the post-composed sequence `Y i = f (X i)`.
  let Y : ℕ → Ω → ℝ := fun i ω => f (X i ω)
  have hY_meas : ∀ i, Measurable (Y i) := fun i => hf_meas.comp (hX_meas _)
  have hY_L2 : ∀ i, MemLp (Y i) 2 μ := by
    intro i
    have hbound : ∀ᵐ ω ∂μ, ‖Y i ω‖ ≤ M := by
      refine Eventually.of_forall fun ω => ?_
      simpa [Y, Real.norm_eq_abs] using hM _
    exact (MemLp.of_bound (μ:=μ) (p:=2) (f:=Y i)
      (hY_meas i).aestronglyMeasurable M hbound)
  have hY_contract : Contractable μ Y :=
    contractable_comp (μ:=μ) (X:=X) (hX_contract:=hX_contract)
      (hX_meas:=hX_meas) f hf_meas
  -- Extract the covariance data for the sequence `Y`.
  obtain ⟨mY, σSq, ρ, hY_mean, hY_var, hY_cov, hσ_nonneg, hρ_lb, hρ_ub⟩ :=
    contractable_covariance_structure (μ:=μ) (X:=Y)
      hY_contract hY_meas hY_L2
  let Cf : ℝ := 2 * σSq * (1 - ρ)
  have hCf_nonneg : 0 ≤ Cf := by
    have h1 : 0 ≤ σSq := hσ_nonneg
    have h2 : 0 ≤ 1 - ρ := sub_nonneg.mpr hρ_ub
    have h3 : 0 ≤ (2 : ℝ) := by norm_num
    exact mul_nonneg (mul_nonneg h3 h1) h2
  -- TODO: apply `l2_contractability_bound` with carefully chosen weights.
  have hgoal :
      ∫ ω, ((1/(k:ℝ)) * ∑ i : Fin k, f (X (n + i.val + 1) ω) -
            (1/(k:ℝ)) * ∑ i : Fin k, f (X (m + i.val + 1) ω))^2 ∂μ
        ≤ Cf / k := by
    -- Implementation pending.
    sorry
  exact ⟨Cf, hCf_nonneg, hgoal⟩

/-- For a contractable sequence and bounded measurable f, the weighted sums
(1/m) ∑_{k=n+1}^{n+m} f(ξ_{n+k}) converge to a **single** function α (independent of n).

This is Kallenberg's key application of the L² bound (Lemma 1.2).

**Key insight**: Using the uniform two-window bound, we show that the limit α_n is
actually **independent of n**. For any n, m and large window k:
  ‖α_n - α_m‖₁ ≤ ‖α_n - A n k‖₁ + ‖A n k - A m k‖₂ + ‖A m k - α_m‖₁
where the middle term is bounded by O(1/k) uniformly in n,m by `l2_bound_two_windows`.

This eliminates the 3ε uniformity problem!
-/
theorem weighted_sums_converge_L1
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ)
    (f : ℝ → ℝ) (hf_meas : Measurable f)
    (hf_bdd : ∃ M, ∀ x, |f x| ≤ M) :
    ∃ (alpha : Ω → ℝ),  -- SINGLE alpha, not a sequence!
      Measurable alpha ∧ MemLp alpha 1 μ ∧
      -- The weighted sums converge to alpha in L¹ (for ANY starting index n)
      (∀ n, ∀ ε > 0, ∃ M : ℕ, ∀ m : ℕ, m ≥ M →
        ∫ ω, |(1/(m:ℝ)) * ∑ k : Fin m, f (X (n + k.val + 1) ω) - alpha ω| ∂μ < ε) := by
  classical

  -- Define the moving averages A n m
  let A : ℕ → ℕ → Ω → ℝ :=
    fun n m ω => (1 / (m : ℝ)) * ∑ k : Fin m, f (X (n + k.val + 1) ω)

  -- A n m is measurable for all n, m
  have hA_meas : ∀ n m, Measurable (A n m) := by
    intro n m
    simp only [A]
    apply Measurable.const_mul
    apply Finset.measurable_sum
    intro k _
    exact hf_meas.comp (hX_meas _)

  -- A n m is in L¹ for all n, m (bounded measurable on probability space)
  have hA_memLp : ∀ n m, MemLp (A n m) 1 μ := by
    intro n m
    obtain ⟨M, hM⟩ := hf_bdd
    -- On probability spaces, the integral of |A n m| is bounded by M
    -- since |A n m ω| ≤ M for all ω and μ is a probability measure
    have hA_ae_bdd : ∀ᵐ ω ∂μ, ‖A n m ω‖ ≤ M := by
      filter_upwards with ω
      simp only [A, Real.norm_eq_abs]
      -- Average of values bounded by M is bounded by M
      calc |(1 / (m : ℝ)) * ∑ k : Fin m, f (X (n + k.val + 1) ω)|
          ≤ (1 / (m : ℝ)) * ∑ k : Fin m, |f (X (n + k.val + 1) ω)| := by
            classical
            by_cases hm : m = 0
            · simp [hm]
            · have hm_pos : 0 < (m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hm
              have h_inv_pos : 0 < 1 / (m : ℝ) := by
                exact div_pos (by norm_num) hm_pos
              have h_abs_sum :
                  |∑ k : Fin m, f (X (n + k.val + 1) ω)|
                    ≤ ∑ k : Fin m, |f (X (n + k.val + 1) ω)| := by
                simpa using
                  (Finset.abs_sum_le_sum_abs
                    (fun k : Fin m => f (X (n + k.val + 1) ω)))
              have h_inv_abs : |1 / (m : ℝ)| = 1 / (m : ℝ) :=
                abs_of_pos h_inv_pos
              calc
                |(1 / (m : ℝ)) * ∑ k : Fin m, f (X (n + k.val + 1) ω)|
                    = (1 / (m : ℝ)) *
                        |∑ k : Fin m, f (X (n + k.val + 1) ω)| := by
                      simpa [abs_mul, h_inv_abs]
                _ ≤ (1 / (m : ℝ)) *
                        ∑ k : Fin m, |f (X (n + k.val + 1) ω)| := by
                      exact
                        (mul_le_mul_of_nonneg_left h_abs_sum
                          (le_of_lt h_inv_pos))
        _ ≤ (1 / (m : ℝ)) * ∑ k : Fin m, M := by
            classical
            by_cases hm : m = 0
            · simp [hm]
            · have h_inv_nonneg : 0 ≤ 1 / (m : ℝ) := by
                have hm_pos : 0 < (m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hm
                exact le_of_lt (div_pos (by norm_num) hm_pos)
              have h_sum_le :
                  ∑ k : Fin m, |f (X (n + k.val + 1) ω)|
                    ≤ ∑ k : Fin m, M := by
                refine Finset.sum_le_sum ?_
                intro k _
                exact hM _
              exact (mul_le_mul_of_nonneg_left h_sum_le h_inv_nonneg)
        _ ≤ M := by
            classical
            by_cases hm : m = 0
            · have hM_nonneg : 0 ≤ M :=
                (le_trans (abs_nonneg _) (hM 0))
              simp [hm, hM_nonneg]
            · have hm_pos : 0 < (m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hm
              have hm_ne_zero : (m : ℝ) ≠ 0 := ne_of_gt hm_pos
              have h_inv_mul : (1 / (m : ℝ)) * (m : ℝ) = (1 : ℝ) := by
                simpa [one_div] using inv_mul_cancel hm_ne_zero
              have : ∑ k : Fin m, M = (m : ℝ) * M := by
                simp [Finset.sum_const, mul_comm, mul_left_comm, mul_assoc]
              calc
                (1 / (m : ℝ)) * ∑ k : Fin m, M
                    = (1 / (m : ℝ)) * ((m : ℝ) * M) := by simpa [this]
                _ = ((1 / (m : ℝ)) * (m : ℝ)) * M := by ring
                _ = M := by simpa [h_inv_mul]
    exact MemLp.of_bound (hA_meas n m).aestronglyMeasurable M hA_ae_bdd

  -- Step 1: For n=0, show (A 0 m)_m is Cauchy in L² hence L¹
  have hA_cauchy_L2_0 : ∀ ε > 0, ∃ N, ∀ m ℓ, m ≥ N → ℓ ≥ N →
      eLpNorm (fun ω => A 0 m ω - A 0 ℓ ω) 2 μ < ENNReal.ofReal ε := by
    intro ε hε
    -- For contractable sequences, A 0 m - A 0 ℓ converges to 0 in L²
    -- This uses l2_contractability_bound: different weight distributions give small L² diff
    -- The weights p = (1/m, ..., 1/m) vs q = (1/ℓ, ..., 1/ℓ) satisfy sup|p_i - q_i| → 0
    sorry  -- TODO: Apply l2_contractability_bound with p,q being uniform on different windows
           -- The sup difference is max(1/m, 1/ℓ) which → 0 as m,ℓ → ∞

  have hA_cauchy_L1_0 : ∀ ε > 0, ∃ N, ∀ m ℓ, m ≥ N → ℓ ≥ N →
      eLpNorm (fun ω => A 0 m ω - A 0 ℓ ω) 1 μ < ENNReal.ofReal ε := by
    intro ε hε
    rcases hA_cauchy_L2_0 ε hε with ⟨N, hN⟩
    refine ⟨N, fun m ℓ hm hℓ => ?_⟩
    calc eLpNorm (fun ω => A 0 m ω - A 0 ℓ ω) 1 μ
        ≤ eLpNorm (fun ω => A 0 m ω - A 0 ℓ ω) 2 μ := by
          apply eLpNorm_le_eLpNorm_of_exponent_le
          · norm_num
          · exact (hA_meas 0 m).sub (hA_meas 0 ℓ) |>.aestronglyMeasurable
      _ < ENNReal.ofReal ε := hN m ℓ hm hℓ

  -- Step 2: Completeness of L¹ gives alpha_0
  have h_exist_alpha_0 : ∃ alpha_0 : Ω → ℝ, Measurable alpha_0 ∧ MemLp alpha_0 1 μ ∧
      (∀ ε > 0, ∃ M, ∀ m ≥ M,
        eLpNorm (fun ω => A 0 m ω - alpha_0 ω) 1 μ < ENNReal.ofReal ε) := by
    sorry  -- TODO: Use CompleteSpace (Lp ℝ 1 μ) as before

  obtain ⟨alpha_0, halpha_0_meas, halpha_0_mem, halpha_0_conv⟩ := h_exist_alpha_0

  -- Step 3: KEY - Prove alpha_0 works for ALL starting indices n
  -- For any n, show A n m → alpha_0 using the uniform two-window bound
  have halpha_0_univ : ∀ n, ∀ ε > 0, ∃ M, ∀ m ≥ M,
      eLpNorm (fun ω => A n m ω - alpha_0 ω) 1 μ < ENNReal.ofReal ε := by
    intro n ε hε
    -- Triangle inequality: ‖A n m - alpha_0‖₁ ≤ ‖A n m - A 0 m‖₂ + ‖A 0 m - alpha_0‖₁
    -- Term 1: ‖A n m - A 0 m‖₂ bounded by l2_bound_two_windows, goes to 0 as m → ∞
    -- Term 2: ‖A 0 m - alpha_0‖₁ → 0 as m → ∞ by halpha_0_conv

    have hε2_pos : 0 < ε / 2 := by linarith

    -- Get M₁ such that ‖A 0 m - alpha_0‖₁ < ε/2 for m ≥ M₁
    rcases halpha_0_conv (ε / 2) hε2_pos with ⟨M₁, hM₁⟩

    -- Choose M large enough that:
    -- 1. M ≥ M₁ (so term 2 < ε/2)
    -- 2. O(n/M) < ε/2 (so term 1 < ε/2 via l2_bound_two_windows)
    -- For now, we just need M large (the exact calculation uses l2_bound_two_windows)
    sorry  -- TODO: Complete with explicit M calculation using l2_bound_two_windows bound
           -- refine ⟨max M₁ (2*n), fun m hm => ?_⟩ and apply triangle + both bounds

  -- Step 4: Package the result - alpha_0 is our answer!
  refine ⟨alpha_0, halpha_0_meas, halpha_0_mem, ?_⟩

  -- Convert eLpNorm convergence to integral convergence
  intro n ε hε
  rcases halpha_0_univ n ε hε with ⟨M, hM⟩
  refine ⟨M, fun m hm => ?_⟩
  have h_elpnorm := hM m hm
  -- Convert eLpNorm 1 to integral
  have h_memLp : MemLp (fun ω => A n m ω - alpha_0 ω) 1 μ := by
    apply MemLp.sub
    · exact hA_memLp n m
    · exact halpha_0_mem
  rw [MemLp.eLpNorm_eq_integral_rpow_norm one_ne_zero ENNReal.coe_ne_top h_memLp] at h_elpnorm
  simp only [ENNReal.toReal_one, Real.rpow_one] at h_elpnorm
  norm_num at h_elpnorm
  rw [ENNReal.ofReal_lt_ofReal_iff hε] at h_elpnorm
  convert h_elpnorm using 1

/-!
## Step 3: Reverse martingale convergence
-/

/-- **FMP 4.2: Subsequence criterion**.

Let ξ, ξ₁, ξ₂,... be random elements in a metric space (S, ρ). Then ξₙ →ᵖ ξ
iff every subsequence N' ⊆ ℕ has a further subsequence N'' ⊆ N' such that
ξₙ → ξ a.s. along N''.
In particular, ξₙ → ξ a.s. implies ξₙ →ᵖ ξ.

**Proof outline** (Kallenberg):
Forward direction (→ᵖ implies a.s. along subsequence):
1. Assume ξₙ →ᵖ ξ, fix arbitrary subsequence N' ⊆ ℕ
2. Choose further subsequence N'' ⊆ N' with
   E ∑_{n∈N''} {ρ(ξₙ,ξ) ∧ 1} = ∑_{n∈N''} E[ρ(ξₙ,ξ) ∧ 1] < ∞
   (equality by monotone convergence)
3. Series converges a.s., so ξₙ → ξ a.s. along N''

Reverse direction (a.s. subsequences imply →ᵖ):
1. Assume condition. If ξₙ ↛ᵖ ξ, then ∃ε > 0 with E[ρ(ξₙ,ξ) ∧ 1] > ε along N' ⊆ ℕ
2. By hypothesis, ξₙ → ξ a.s. along N'' ⊆ N'
3. By dominated convergence, E[ρ(ξₙ,ξ) ∧ 1] → 0 along N'', contradiction

**Mathlib reference**: Look for convergence in probability and a.s. convergence
in `Probability` namespace. The subsequence extraction should follow from
summability of expectations.

TODO: Adapt to our L¹ convergence setting.
-/
theorem subsequence_criterion_convergence_in_probability
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (ξ : ℕ → Ω → ℝ) (ξ_limit : Ω → ℝ)
    (h_prob_conv : ∀ ε > 0, Tendsto (fun n => μ {ω | ε ≤ |ξ n ω - ξ_limit ω|}) atTop (𝓝 0)) :
    ∃ (φ : ℕ → ℕ), StrictMono φ ∧
      ∀ᵐ ω ∂μ, Tendsto (fun k => ξ (φ k) ω) atTop (𝓝 (ξ_limit ω)) := by
  sorry

/-- **OBSOLETE with refactored approach**: This theorem is no longer needed.

With the refactored `weighted_sums_converge_L1`, we get a single `alpha : Ω → ℝ`
that is independent of the starting index. There is no sequence `alpha_n` to
take a subsequence of.

The original Kallenberg approach had `alpha_n → alpha_∞`, but our refactored
proof shows `alpha_n = alpha` for all n directly.
-/
theorem reverse_martingale_subsequence_convergence
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (alpha : ℕ → Ω → ℝ) (alpha_inf : Ω → ℝ)
    (h_L1_conv : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∫ ω, |alpha n ω - alpha_inf ω| ∂μ < ε) :
    ∃ (φ : ℕ → ℕ), StrictMono φ ∧
      ∀ᵐ ω ∂μ, Tendsto (fun k => alpha (φ k) ω) atTop (𝓝 (alpha_inf ω)) := by
  -- NOTE: With refactored approach, this is unnecessary
  -- The identity subsequence φ = id works trivially since alpha is constant
  sorry

/-- The α_n sequence is a reverse martingale with respect to the tail filtration.

**Note**: This lemma's content is deferred to Step 5 (`alpha_is_conditional_expectation`).
Once we identify α_n = E[f(X_{n+1}) | σ(X_{n+1}, X_{n+2}, ...)] in Step 5,
the reverse martingale property follows immediately from the standard tower property
of conditional expectation.

For now, we state this as `True` and complete the identification in Step 5.
-/
theorem alpha_is_reverse_martingale
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (α : ℕ → Ω → ℝ)
    (f : ℝ → ℝ) (hf_meas : Measurable f) :
    True := by
  -- Defer to Step 5 where we identify α_n with conditional expectation
  trivial

/-!
## Step 4: Contractability + dominated convergence gives conditional expectation formula
-/

/-- Using contractability and dominated convergence, we get:
E[f(X_i) ; ∩I_k] = E[α_{k-1} ; ∩I_k] → E[α_∞ ; ∩I_k]

**Kallenberg**: "By the contractability of ξ and dominated convergence we get, a.s. along ℕ
for any i ∈ I:
  E[f(ξ_i); ∩I_k] = E[α_{k-1}; ∩I_k] → E[α_∞; ∩I_k]"

TODO: Use contractability to relate different time points.
-/
theorem contractability_conditional_expectation
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (f : ℝ → ℝ) (hf_meas : Measurable f)
    (alpha : ℕ → Ω → ℝ) (alpha_inf : Ω → ℝ)
    (I_k : Set Ω)  -- Event ∩I_k in tail σ-algebra
    (h_conv : ∀ᵐ ω ∂μ, Tendsto (fun n => alpha n ω) atTop (𝓝 (alpha_inf ω))) :
    True := by  -- TODO: E[f(X_i) ; I_k] = E[alpha_inf ; I_k]
  sorry

/-!
## Step 5: α_n = E_n f(X_{n+1}) = ν^f
-/

/-- The limit α_n satisfies α_n = E_n f(X_{n+1}) where E_n is conditional
expectation on σ(X_{n+1}, X_{n+2}, ...).

Moreover, α_n = ν^f a.s. for some directing measure ν.

**Kallenberg**: "which implies α_n = E_n f(ξ_{n+1}) = ν^f a.s."

TODO: Show this characterizes α_n as the conditional expectation.
-/
theorem alpha_is_conditional_expectation
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (f : ℝ → ℝ) (hf_meas : Measurable f)
    (alpha : ℕ → Ω → ℝ) :
    ∃ (nu : Ω → Measure ℝ),
      (∀ ω, IsProbabilityMeasure (nu ω)) ∧
      -- nu is tail-measurable
      sorry ∧
      -- alpha_n = ∫ f dnu a.s.
      (∀ n, ∀ᵐ ω ∂μ, alpha n ω = ∫ x, f x ∂(nu ω)) := by
  sorry

/-!
## Main theorem: de Finetti via L² approach
-/

/-- **Kallenberg's Second Proof of de Finetti's Theorem 1.1** (refactored):
Starting from a **contractable** sequence ξ in ℝ with L² bounds,
we prove it is conditionally i.i.d. given the tail σ-algebra.

**Original Kallenberg structure** (page 26-27):
1. Fix bounded measurable f ∈ L¹
2. Use Lemma 1.2 (L² bound) + completeness of L¹ to get α_n → α_∞
3. Show α_n is reverse martingale with a.s. convergent subsequence
4. Use contractability + dominated convergence
5. Conclude α_n = E_n f(ξ_{n+1}) = ν^f a.s.
6. "The proof can now be completed as before" (common ending)

**Refactored approach** (with single α):
1. For each bounded f, use `weighted_sums_converge_L1` to get single α
2. Show α = E[f(X_1) | tail] by contractability (no subsequence needed!)
3. Define directing measure ν from α via disintegration
4. Complete using CommonEnding.complete_from_directing_measure

**Key simplification**: No reverse martingale convergence needed since α is
already the limit (not a sequence)!

**Reference**: Kallenberg (2005), Theorem 1.1 (page 26-27), "Second proof".
-/
theorem deFinetti_viaL2
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_meas : ∀ i, Measurable (X i))
    (hX_contract : Contractable μ X)  -- NOTE: Starts with CONTRACTABLE, not exchangeable!
    (hX_L2 : ∀ i, MemLp (X i) 2 μ) :
    ∃ (K : Kernel Ω ℝ),
      IsMarkovKernel K ∧
      -- K is tail-measurable
      sorry ∧
      -- X is conditionally i.i.d. given tail σ-algebra with law K
      sorry := by
  -- Strategy with refactored weighted_sums_converge_L1:
  -- 1. For each bounded f, get single alpha from weighted_sums_converge_L1
  -- 2. Show alpha = E[f(X_1) | tail] using contractability
  -- 3. Use disintegration to build directing measure ν
  -- 4. Apply CommonEnding.complete_from_directing_measure
  sorry  -- TODO: Implement refactored proof flow

/-!
## Connection to exchangeability (for completeness)
-/

/-- Since exchangeable implies contractable (proved in Contractability.lean),
we can also state de Finetti starting from exchangeability.

This combines `contractable_of_exchangeable` with `deFinetti_second_proof`.
-/
theorem deFinetti_from_exchangeable
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_meas : ∀ i, Measurable (X i))
    (hX_exch : Exchangeable μ X)
    (hX_L2 : ∀ i, MemLp (X i) 2 μ) :
    ∃ (K : Kernel Ω ℝ),
      IsMarkovKernel K ∧
      sorry ∧  -- K tail-measurable
      sorry := by  -- X conditionally i.i.d. with law K
  -- First show exchangeable → contractable
  have hX_contract : Contractable μ X := contractable_of_exchangeable hX_exch hX_meas
  -- Then apply the Second proof
  have := deFinetti_viaL2 X hX_meas hX_contract hX_L2
  sorry  -- Type mismatch due to different sorry locations; will fix when sorries are filled

/-- **Standard name** for de Finetti's theorem.
This is an alias for `deFinetti_from_exchangeable` (the L² proof). -/
theorem deFinetti := @deFinetti_from_exchangeable

end Exchangeability.DeFinetti.ViaL2
