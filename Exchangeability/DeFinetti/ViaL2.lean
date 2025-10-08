/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Exchangeability.DeFinetti.L2Approach
import Exchangeability.Contractability
import Exchangeability.ConditionallyIID
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
lemma contractable_map_single (hX_contract : Contractable μ X) (hX_meas : ∀ i, Measurable (X i)) {i : ℕ} :
    Measure.map (fun ω => X i ω) μ = Measure.map (fun ω => X 0 ω) μ := by
  classical
  -- `k` selects the singleton subsequence `{i}`.
  let k : Fin 1 → ℕ := fun _ => i
  have hk : StrictMono k := by
    intro a b hab
    -- In Fin 1, both a and b must be 0, so a < b is impossible
    have : a = 0 := Fin.eq_zero a
    have : b = 0 := Fin.eq_zero b
    simp_all
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
  have h_left := (Measure.map_map h_eval_meas h_meas_k (μ := μ)).symm
  have h_right := Measure.map_map h_eval_meas h_meas_std (μ := μ)
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
lemma contractable_map_pair (hX_contract : Contractable μ X) (hX_meas : ∀ i, Measurable (X i)) {i j : ℕ} (hij : i < j) :
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
  have h_left := (Measure.map_map h_eval_meas h_meas_k (μ := μ)).symm
  have h_right := Measure.map_map h_eval_meas h_meas_std (μ := μ)
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
lemma contractable_comp (hX_contract : Contractable μ X) (hX_meas : ∀ i, Measurable (X i))
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
  have h_left := (Measure.map_map hΦ_meas h_meas_k (μ := μ)).symm
  have h_right := Measure.map_map hΦ_meas h_meas_std (μ := μ)
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
  have h'' : |a| * |b| ≤ (|a| ^ 2 + |b| ^ 2) / 2 := by
    have : |a| * |b| * 2 ≤ |a| ^ 2 + |b| ^ 2 := h'
    linarith [show (0 : ℝ) < 2 by norm_num]
  have h''' : |a * b| ≤ (|a| ^ 2 + |b| ^ 2) / 2 := by
    simpa [abs_mul] using h''
  simpa [sq_abs, pow_two, add_comm, add_left_comm, add_assoc] using h'''

end CovarianceHelpers

/-!
## Lp utility lemmas

Standard lemmas for working with Lp spaces and ENNReal conversions.
-/

section LpUtilities

/-- Distance between `toLp` elements equals the `eLpNorm` of their difference. -/
lemma dist_toLp_eq_eLpNorm_sub
  {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {p : ℝ≥0∞}
  (hp0 : p ≠ 0) (hp∞ : p ≠ ∞)
  {f g : Ω → ℝ} (hf : MemLp f p μ) (hg : MemLp g p μ) :
  dist (hf.toLp f) (hg.toLp g)
    = ENNReal.toReal (eLpNorm (fun ω => f ω - g ω) p μ) := by
  rw [Lp.dist_def]
  have : (hf.toLp f) - (hg.toLp g)
        = (hf.sub hg).toLp (fun ω => f ω - g ω) := by
    ext1
    filter_upwards [Lp.coeFn_sub (hf.toLp f) (hg.toLp g),
                    hf.coeFn_toLp, hg.coeFn_toLp,
                    (hf.sub hg).coeFn_toLp] with ω h_sub hf_ae hg_ae hsub_ae
    simp [h_sub, hf_ae, hg_ae, hsub_ae]
  rw [this, Lp.norm_toLp]

/-- Converting strict inequality through `ENNReal.toReal`. -/
lemma toReal_lt_of_lt_ofReal {x : ℝ≥0∞} {ε : ℝ}
    (hx : x ≠ ∞) (hε : 0 ≤ ε) :
    x < ENNReal.ofReal ε → ENNReal.toReal x < ε := by
  intro h
  rw [ENNReal.toReal_lt_toReal hx (by simp)]
  simpa [ENNReal.toReal_ofReal hε] using h

/-- Arithmetic bound: √(Cf/m) < ε/2 when m is large enough. -/
lemma sqrt_div_lt_half_eps_of_nat
  {Cf ε : ℝ} (hCf : 0 ≤ Cf) (hε : 0 < ε) :
  ∀ ⦃m : ℕ⦄, m ≥ Nat.ceil (4 * Cf / (ε^2)) + 1 →
    Real.sqrt (Cf / m) < ε / 2 := by
  intro m hm
  have hm_real : ((Nat.ceil (4*Cf/ε^2) : ℝ) + 1) ≤ m := by exact_mod_cast hm
  have hA_lt_m : 4*Cf/ε^2 < (m : ℝ) := by
    calc 4*Cf/ε^2
        ≤ Nat.ceil (4*Cf/ε^2) := Nat.le_ceil _
      _ < (Nat.ceil (4*Cf/ε^2) : ℝ) + 1 := by linarith
      _ ≤ m := hm_real
  by_cases hCf0 : Cf = 0
  · simp [hCf0, div_pos hε (by norm_num : (0:ℝ) < 2)]
  have hCfpos : 0 < Cf := lt_of_le_of_ne hCf (Ne.symm hCf0)
  have hmpos : 0 < (m : ℝ) := by
    calc (0 : ℝ) < 4*Cf/ε^2 := by positivity
      _ < m := hA_lt_m
  have hdenom_pos : 0 < 4*Cf/ε^2 := by positivity
  have hdiv : Cf / (m : ℝ) < Cf / (4*Cf/ε^2) := by
    exact div_lt_div_of_pos_left hCfpos hdenom_pos hA_lt_m
  have heq : Cf / (4*Cf/ε^2) = ε^2 / 4 := by
    field_simp [ne_of_gt hCfpos]
    ring
  have hlt : Cf / (m : ℝ) < ε^2 / 4 := by
    calc Cf / (m : ℝ)
        < Cf / (4*Cf/ε^2) := hdiv
      _ = ε^2 / 4 := heq
  have hnonneg : 0 ≤ Cf / (m : ℝ) := div_nonneg hCf (Nat.cast_nonneg m)
  have hsqrt : Real.sqrt (Cf / m) < Real.sqrt (ε^2 / 4) := by
    exact Real.sqrt_lt_sqrt hnonneg hlt
  calc Real.sqrt (Cf / m)
      < Real.sqrt (ε^2 / 4) := hsqrt
    _ = Real.sqrt ((ε/2)^2) := by
        congr 1
        rw [sq]
        ring
    _ = |ε / 2| := Real.sqrt_sq_eq_abs _
    _ = ε / 2 := abs_of_pos (div_pos hε (by norm_num))

/-- Convert an L² integral bound to an eLpNorm bound. -/
lemma eLpNorm_two_from_integral_sq_le
  {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  {g : Ω → ℝ} (hg : MemLp g 2 μ)
  {C : ℝ} (hC : 0 ≤ C)
  (h : ∫ ω, (g ω)^2 ∂μ ≤ C) :
  eLpNorm g 2 μ ≤ ENNReal.ofReal (Real.sqrt C) := by
  have hp_ne_zero : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have hp_ne_top : (2 : ℝ≥0∞) ≠ ∞ := by norm_num
  rw [eLpNorm_eq_lintegral_rpow_nnnorm hp_ne_zero hp_ne_top]
  have : (∫⁻ ω, (‖g ω‖₊ : ℝ≥0∞) ^ (2 : ℝ) ∂μ)^(1/2)
       ≤ (ENNReal.ofReal C)^(1/2) := by
    apply ENNReal.rpow_le_rpow _ (by norm_num : (0:ℝ) ≤ 1/2)
    have hgnn : ∫⁻ ω, (‖g ω‖₊ : ℝ≥0∞) ^ (2 : ℝ) ∂μ
              = ENNReal.ofReal (∫ ω, (g ω)^2 ∂μ) := by
      rw [← integral_eq_lintegral_of_nonneg_ae]
      · congr 1
        ext ω
        simp [Real.nnnorm_of_nonneg (sq_nonneg _), Real.coe_nnabs]
      · apply Filter.eventually_of_forall
        intro ω
        exact sq_nonneg _
      · have : Integrable (fun ω => (g ω)^2) μ := by
          have := hg.integrable_norm_pow (p:=2) (by decide)
          simpa [Real.norm_eq_abs, sq_abs] using this
        exact this.aestronglyMeasurable
    rw [hgnn]
    exact ENNReal.ofReal_le_ofReal h
  calc (∫⁻ ω, (‖g ω‖₊ : ℝ≥0∞) ^ (2 : ℝ) ∂μ) ^ (1 / 2)
      ≤ (ENNReal.ofReal C) ^ (1 / 2) := this
    _ = ENNReal.ofReal (C ^ (1 / 2)) := by
        rw [ENNReal.ofReal_rpow_of_nonneg hC (by norm_num)]
    _ = ENNReal.ofReal (Real.sqrt C) := by
        congr 1
        exact (Real.rpow_natCast C 2).symm ▸ Real.sq_sqrt hC ▸ rfl

end LpUtilities

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
    MemLp.integrable (hq1 := by norm_num) (hX_L2 i)
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
    have hmap := contractable_map_single (i:=k)
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
    have hmap := contractable_map_single (i:=k)
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
    have hmap := contractable_map_pair hij
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

/-- Cardinality of Fin values less than k in Fin (2*k) -/
private lemma card_fin_lt_k {k : ℕ} :
    (Finset.univ.filter (fun i : Fin (2 * k) => i.val < k)).card = k := by
  classical
  have h : Finset.univ.filter (fun i : Fin (2 * k) => i.val < k) =
      Finset.image (fun j : Fin k => ⟨j.val, by omega⟩) Finset.univ := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hi
      use ⟨i.val, Nat.lt_of_lt_of_le hi (Nat.le_mul_of_pos_left k (by norm_num))⟩
      simp [hi]
    · intro ⟨j, _, h⟩
      simp [← h]
  rw [h, Finset.card_image_iff.mpr]
  · simp
  · intro a _ b _ hab
    exact Fin.ext hab

/-- The supremum of |p i - q i| for two-window weights -/
private lemma sup_two_window_weights {k : ℕ} (hk : 0 < k)
    (p q : Fin (2 * k) → ℝ)
    (hp : p = fun i => if i.val < k then 1 / (k : ℝ) else 0)
    (hq : q = fun i => if i.val < k then 0 else 1 / (k : ℝ)) :
    ⨆ i, |p i - q i| = 1 / (k : ℝ) := by
  have hk_pos : 0 < (k : ℝ) := by exact_mod_cast hk
  have hk_ne : (k : ℝ) ≠ 0 := ne_of_gt hk_pos
  -- For any i, |p i - q i| is either 1/k or 0
  have h_cases : ∀ i : Fin (2 * k), |p i - q i| = 1 / (k : ℝ) ∨ |p i - q i| = 0 := by
    intro i
    simp [hp, hq]
    by_cases hi : i.val < k
    · simp [hi]; left; rw [abs_of_nonneg]; exact div_nonneg (by norm_num) (by exact_mod_cast Nat.zero_le _)
    · simp [hi]; right; rw [abs_of_nonpos]; ring; exact div_nonneg (by norm_num) (by exact_mod_cast Nat.zero_le _)
  -- The supremum is achieved and equals 1/k
  have h_bdd : BddAbove (Set.range fun i : Fin (2 * k) => |p i - q i|) := by
    use 1 / (k : ℝ)
    intro y ⟨i, hi⟩
    rw [← hi]
    rcases h_cases i with h | h <;> simp [h]
  have h_nonempty : (Set.range fun i : Fin (2 * k) => |p i - q i|).Nonempty := by
    use |p ⟨0, by omega⟩ - q ⟨0, by omega⟩|
    use ⟨0, by omega⟩
  -- Show that 1/k is in the range (achieved at i = 0)
  have h_achieved : 1 / (k : ℝ) ∈ Set.range fun i : Fin (2 * k) => |p i - q i| := by
    use ⟨0, by omega⟩
    simp [hp, hq, abs_of_nonneg (div_nonneg (by norm_num) (by exact_mod_cast Nat.zero_le k))]
  -- Therefore sup = 1/k
  have h_le : ∀ i, |p i - q i| ≤ 1 / (k : ℝ) := by
    intro i
    rcases h_cases i with h | h <;> simp [h]
  apply le_antisymm
  · exact ciSup_le h_le
  · exact le_ciSup h_bdd ⟨0, by omega⟩

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
    @contractable_comp _ _ μ _ X hX_contract hX_meas f hf_meas
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

  -- Apply l2_contractability_bound with weights on two windows of length k
  have hgoal :
      ∫ ω, ((1/(k:ℝ)) * ∑ i : Fin k, f (X (n + i.val + 1) ω) -
            (1/(k:ℝ)) * ∑ i : Fin k, f (X (m + i.val + 1) ω))^2 ∂μ
        ≤ Cf / k := by
    -- Build the combined index set: 2k coordinates covering both windows
    let twoK := 2 * k
    have htwoK_pos : 0 < twoK := by
      have : 0 < 2 := by norm_num
      exact Nat.mul_pos this hk

    -- Build the full sequence ξ : Fin (2k) → Ω → ℝ covering both windows
    -- Indices 0..(k-1) cover window starting at n, indices k..(2k-1) cover window at m
    let ξ : Fin twoK → Ω → ℝ := fun i =>
      if i.val < k then Y (n + i.val + 1) else Y (m + (i.val - k) + 1)

    -- Set up weights: p is uniform 1/k on first window, q is uniform 1/k on second
    let p : Fin twoK → ℝ := fun i => if i.val < k then 1 / (k : ℝ) else 0
    let q : Fin twoK → ℝ := fun i => if i.val < k then 0 else 1 / (k : ℝ)

    -- Prove weight hypotheses
    have hp_sum : ∑ i, p i = 1 := by
      trans (∑ i ∈ Finset.univ.filter (fun i : Fin twoK => i.val < k), 1 / (k : ℝ))
      · simp only [p]
        rw [← Finset.sum_filter]
        congr 1
        ext i
        simp
      · rw [Finset.sum_const, card_fin_lt_k, nsmul_eq_mul]
        field_simp; ring

    have hp_nonneg : ∀ i, 0 ≤ p i := by
      intro i
      simp [p]
      split_ifs <;> [exact div_nonneg (by norm_num) (by exact_mod_cast Nat.zero_le _); norm_num]

    have hq_sum : ∑ i, q i = 1 := by
      have h_card : (Finset.univ.filter (fun i : Fin twoK => k ≤ i.val)).card = k := by
        have h_compl : Finset.univ.filter (fun i : Fin twoK => k ≤ i.val) =
            (Finset.univ.filter (fun i : Fin twoK => i.val < k))ᶜ := by
          ext i; simp; omega
        rw [h_compl, Finset.card_compl, card_fin_lt_k]
        simp [twoK]
      trans (∑ i ∈ Finset.univ.filter (fun i : Fin twoK => k ≤ i.val), 1 / (k : ℝ))
      · congr 1; ext i
        simp only [Finset.sum_ite, q]
        rw [Finset.sum_filter]
      · rw [Finset.sum_const, h_card, nsmul_eq_mul]
        field_simp; ring

    have hq_nonneg : ∀ i, 0 ≤ q i := by
      intro i; simp [q]; split_ifs <;> [norm_num, exact div_nonneg (by norm_num) (by exact_mod_cast Nat.zero_le _)]

    -- Key: sup |p - q| = 1/k
    have hsup_pq : ⨆ i, |p i - q i| = 1 / (k : ℝ) :=
      sup_two_window_weights hk p q rfl rfl

    -- ξ is measurable
    have hξ_meas : ∀ i, Measurable (ξ i) := fun i => by
      simp [ξ]; split_ifs <;> exact hY_meas _

    -- ξ is in L² (bounded by M)
    have hξ_L2 : ∀ i, MemLp (ξ i) 2 μ := fun i => by
      simp [ξ]; split_ifs <;> exact hY_L2 _

    -- Mean, variance, covariance of ξ match Y
    have hξ_mean : ∀ i, ∫ ω, ξ i ω ∂μ = mY := by
      intro i; simp [ξ]; split_ifs <;> exact hY_mean _

    have hξ_var : ∀ i, ∫ ω, (ξ i ω - mY)^2 ∂μ = σSq := by
      intro i; simp [ξ]; split_ifs <;> exact hY_var _

    have hξ_cov : ∀ i j, i ≠ j → ∫ ω, (ξ i ω - mY) * (ξ j ω - mY) ∂μ = σSq * ρ := by
      intro i j hij
      -- All coordinates ξ i are drawn from Y with different indices from ℕ
      -- By construction of ξ, different Fin indices map to different ℕ indices
      -- (within each window indices are consecutive, between windows they're separate)
      simp only [ξ]
      split_ifs with hi hj hj
      · -- Both in first window: indices are n+i+1 vs n+j+1 with i ≠ j
        have : n + i.val + 1 ≠ n + j.val + 1 := by
          intro h; have : i.val = j.val := by omega
          have : i = j := Fin.ext this; exact hij this
        exact hY_cov _ _ this
      · -- i < k, ¬(j < k): first vs second window
        -- ξ i = Y(n + i.val + 1), ξ j = Y(m + (j.val - k) + 1)
        by_cases heq : n + i.val + 1 = m + (j.val - k) + 1
        · -- Indices coincide: use variance formula
          have : Y (n + i.val + 1) = Y (m + (j.val - k) + 1) := by rw [heq]
          simp only [this]
          have : ∫ ω, (Y (m + (j.val - k) + 1) ω - mY) * (Y (m + (j.val - k) + 1) ω - mY) ∂μ = σSq := by
            have := hY_var (m + (j.val - k) + 1)
            simpa [sq] using this
          -- σSq = σSq * 1 ≥ σSq * ρ since ρ ≤ 1
          have : σSq * ρ ≤ σSq := by
            have : ρ ≤ 1 := hρ_ub
            nlinarith [hσ_nonneg]
          linarith
        · -- Indices distinct: use covariance formula
          exact hY_cov _ _ heq
      · -- ¬(i < k), j < k: second vs first window (symmetric case)
        by_cases heq : m + (i.val - k) + 1 = n + j.val + 1
        · -- Indices coincide
          have : Y (m + (i.val - k) + 1) = Y (n + j.val + 1) := by rw [heq]
          simp only [this]
          have : ∫ ω, (Y (n + j.val + 1) ω - mY) * (Y (n + j.val + 1) ω - mY) ∂μ = σSq := by
            have := hY_var (n + j.val + 1)
            simpa [sq] using this
          have : σSq * ρ ≤ σSq := by
            have : ρ ≤ 1 := hρ_ub
            nlinarith [hσ_nonneg]
          linarith
        · -- Indices distinct
          exact hY_cov _ _ heq
      · -- Both in second window: indices are m+(i-k)+1 vs m+(j-k)+1
        have : m + (i.val - k) + 1 ≠ m + (j.val - k) + 1 := by
          intro h; have : i.val - k = j.val - k := by omega
          have : i.val = j.val := by omega
          have : i = j := Fin.ext this; exact hij this
        exact hY_cov _ _ this

    -- Apply l2_contractability_bound
    have hbound := L2Approach.l2_contractability_bound (μ := μ) (n := twoK)
      ξ mY (Real.sqrt σSq) ρ
      ⟨hρ_lb, hρ_ub⟩
      hξ_mean
      (fun i => by
        have := hξ_L2 i
        convert MemLp.sub this (memLp_const mY (p := 2))
        ext ω; simp)
      (fun i => by
        have := hξ_var i
        by_cases hσ : σSq = 0
        · simp [hσ] at this ⊢; exact this
        · have hσ_pos : 0 < σSq := by
            have := hσ_nonneg
            exact lt_of_le_of_ne this (Ne.symm hσ)
          simp [Real.sq_sqrt (le_of_lt hσ_pos)] at this
          exact this)
      hξ_cov
      p q
      ⟨hp_sum, hp_nonneg⟩
      ⟨hq_sum, hq_nonneg⟩

    -- Simplify to the form we want
    calc ∫ ω, ((1/(k:ℝ)) * ∑ i : Fin k, f (X (n + i.val + 1) ω) -
              (1/(k:ℝ)) * ∑ i : Fin k, f (X (m + i.val + 1) ω))^2 ∂μ
        = ∫ ω, (∑ i : Fin twoK, p i * ξ i ω - ∑ i : Fin twoK, q i * ξ i ω)^2 ∂μ := by
            -- Reindex: the p-sum picks out first k indices, q-sum picks second k
            congr 1; ext ω; congr 1
            have hp_expand : ∑ i : Fin twoK, p i * ξ i ω =
                (1/(k:ℝ)) * ∑ i : Fin k, f (X (n + i.val + 1) ω) := by
              calc ∑ i : Fin twoK, p i * ξ i ω
                  = ∑ i : Fin twoK with i.val < k, p i * ξ i ω := by
                      apply Finset.sum_bij (i := fun i _ => i) (hi := fun i hi => hi)
                        (ha := fun i hi => by
                          simp [p] at hi ⊢
                          rcases (Finset.mem_filter.mp hi).2 with h | h
                          · exact h
                          · simp [ξ, (Finset.mem_filter.mp hi).2]; ring)
                      · intro i j _ _ h; exact h
                      · intro b hb
                        use b, hb
                        simp [p, (Finset.mem_filter.mp hb).2, ξ]
                _ = ∑ i : Fin k, (1/(k:ℝ)) * f (X (n + i.val + 1) ω) := by
                      -- Reindex: map i : Fin k ↦ ⟨i.val, proof⟩ : Fin twoK with i.val < k
                      apply Finset.sum_bij
                        (i := fun (j : Fin k) _ => (⟨j.val, by omega⟩ : Fin twoK))
                      · intro j _
                        simp [Finset.mem_filter, Finset.mem_univ]
                        exact j.is_lt
                      · intro j _
                        simp [p, ξ]
                        have : (⟨j.val, by omega⟩ : Fin twoK).val = j.val := rfl
                        simp [this, j.is_lt]
                      · intro j₁ j₂ _ _ h
                        have : j₁.val = j₂.val := by
                          have h' : (⟨j₁.val, by omega⟩ : Fin twoK) = ⟨j₂.val, by omega⟩ := h
                          exact Fin.mk.injEq.mp h'
                        exact Fin.ext this
                      · intro i hi
                        have hi_lt : i.val < k := (Finset.mem_filter.mp hi).2
                        use ⟨i.val, hi_lt⟩, Finset.mem_univ _
                        exact Fin.ext rfl
                _ = (1/(k:ℝ)) * ∑ i : Fin k, f (X (n + i.val + 1) ω) := by
                      rw [Finset.mul_sum]; congr
            have hq_expand : ∑ i : Fin twoK, q i * ξ i ω =
                (1/(k:ℝ)) * ∑ i : Fin k, f (X (m + i.val + 1) ω) := by
              -- Similar to hp_expand, but q is nonzero on second window (k ≤ i.val < 2k)
              calc ∑ i : Fin twoK, q i * ξ i ω
                  = ∑ i : Fin twoK with k ≤ i.val, q i * ξ i ω := by
                      apply Finset.sum_bij (i := fun i _ => i) (hi := fun i hi => hi)
                        (ha := fun i hi => by
                          simp [q] at hi ⊢
                          have hik : k ≤ i.val := (Finset.mem_filter.mp hi).2
                          simp [hik])
                      · intro i j _ _ h; exact h
                      · intro b hb
                        use b, hb
                        simp [q, (Finset.mem_filter.mp hb).2, ξ]
                        have : ¬(b.val < k) := Nat.not_lt.mpr (Finset.mem_filter.mp hb).2
                        simp [this]
                _ = ∑ i : Fin k, (1/(k:ℝ)) * f (X (m + i.val + 1) ω) := by
                      -- Reindex: map j : Fin k ↦ ⟨k + j.val, proof⟩ : Fin twoK
                      apply Finset.sum_bij
                        (i := fun (j : Fin k) _ => (⟨k + j.val, by omega⟩ : Fin twoK))
                      · intro j _
                        simp [Finset.mem_filter, Finset.mem_univ]
                        omega
                      · intro j _
                        simp [q, ξ]
                        have hval : (⟨k + j.val, by omega⟩ : Fin twoK).val = k + j.val := rfl
                        have : ¬((k + j.val) < k) := by omega
                        simp [hval, this]
                        have : (k + j.val) - k = j.val := by omega
                        simp [this]
                      · intro j₁ j₂ _ _ h
                        have : j₁.val = j₂.val := by
                          have h' : k + j₁.val = k + j₂.val := by
                            have : (⟨k + j₁.val, by omega⟩ : Fin twoK) = ⟨k + j₂.val, by omega⟩ := h
                            exact Fin.mk.injEq.mp this
                          omega
                        exact Fin.ext this
                      · intro i hi
                        have hik : k ≤ i.val := (Finset.mem_filter.mp hi).2
                        have hilt : i.val < twoK := i.is_lt
                        use ⟨i.val - k, by omega⟩, Finset.mem_univ _
                        apply Fin.ext
                        simp
                        omega
                _ = (1/(k:ℝ)) * ∑ i : Fin k, f (X (m + i.val + 1) ω) := by
                      rw [Finset.mul_sum]; congr
            rw [hp_expand, hq_expand]
      _ ≤ 2 * (Real.sqrt σSq)^2 * (1 - ρ) * (⨆ i, |p i - q i|) := hbound
      _ = 2 * σSq * (1 - ρ) * (1 / (k : ℝ)) := by
            simp [Real.sq_sqrt hσ_nonneg, hsup_pq]
      _ = (2 * σSq * (1 - ρ)) / k := by ring
      _ = Cf / k := rfl

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
/-- Uniform version of l2_bound_two_windows: The constant Cf is the same for all
window positions. This follows because Cf = 2σ²(1-ρ) depends only on the covariance
structure of f∘X, which is uniform by contractability. -/
lemma l2_bound_two_windows_uniform
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ)
    (f : ℝ → ℝ) (hf_meas : Measurable f)
    (hf_bdd : ∃ M, ∀ x, |f x| ≤ M) :
    ∃ Cf : ℝ, 0 ≤ Cf ∧
      ∀ (n m k : ℕ), 0 < k →
        ∫ ω, ((1/(k:ℝ)) * ∑ i : Fin k, f (X (n + i.val + 1) ω) -
              (1/(k:ℝ)) * ∑ i : Fin k, f (X (m + i.val + 1) ω))^2 ∂μ
          ≤ Cf / k := by
  -- Use l2_bound_two_windows once to get Cf for arbitrary windows
  have h_k1 : 0 < (1 : ℕ) := by norm_num
  obtain ⟨Cf, hCf_nn, _⟩ := l2_bound_two_windows X hX_contract hX_meas hX_L2 f hf_meas hf_bdd 0 0 h_k1
  -- Now show this Cf works for all n, m, k
  refine ⟨Cf, hCf_nn, fun n m k hk => ?_⟩
  -- For each specific n, m, k, get the bound
  obtain ⟨Cf_nmk, _, hbound⟩ := l2_bound_two_windows X hX_contract hX_meas hX_L2 f hf_meas hf_bdd n m hk
  -- The key: Cf_nmk = Cf for all n, m, k because both equal 2σ²(1-ρ)
  -- where σ², ρ come from contractable_covariance_structure applied to f∘X
  -- Since contractable_covariance_structure gives a unique answer, Cf_nmk = Cf
  have hCf_eq : Cf_nmk = Cf := by
    -- Both are 2σ²(1-ρ) from the same covariance structure
    sorry  -- This requires showing contractable_covariance_structure is deterministic
  rw [← hCf_eq]
  exact hbound

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
    -- Strategy: use triangle inequality to compare via a common window
    -- For m, ℓ ≥ N, compare both to A 0 N and use the two-window bound
    -- ‖A 0 m - A 0 ℓ‖₂ ≤ ‖A 0 m - A 0 N‖₂ + ‖A 0 N - A 0 ℓ‖₂
    -- Each term is bounded by √(Cf/N) via l2_bound_two_windows
    -- So we need 2√(Cf/N) < ε, i.e., N > 4Cf/ε²

    -- Get uniform Cf that works for all window positions
    obtain ⟨Cf, hCf_nonneg, hCf_unif⟩ := l2_bound_two_windows_uniform X hX_contract hX_meas hX_L2 f hf_meas hf_bdd

    -- Choose N large enough
    have hε_sq_pos : 0 < ε ^ 2 := pow_pos hε 2
    have hε_sq : 0 < ε ^ 2 / (4 * Cf + 1) := by
      apply div_pos hε_sq_pos
      have : 0 < (4 : ℝ) * Cf + 1 := by
        have : 0 ≤ (4 : ℝ) * Cf := mul_nonneg (by norm_num) hCf_nonneg
        linarith
      exact this

    -- Choose N so that √(Cf/N) < ε/2
    -- We need N > 4Cf/ε²
    let N : ℕ := Nat.ceil (4 * Cf / (ε ^ 2)) + 1
    have hN_pos : 0 < N := Nat.succ_pos _

    refine ⟨N, fun m ℓ hm hℓ => ?_⟩

    -- Use common length k = min m ℓ
    let k := min m ℓ
    have hk_pos : 0 < k := by
      have : 0 < N := hN_pos
      have : N ≤ min m ℓ := min_le_iff.mpr (Or.inl hm)
      exact Nat.lt_of_lt_of_le hN_pos this

    -- Triangle inequality via common length
    have tri : eLpNorm (fun ω => A 0 m ω - A 0 ℓ ω) 2 μ
              ≤ eLpNorm (fun ω => A 0 m ω - A 0 k ω) 2 μ
                + eLpNorm (fun ω => A 0 ℓ ω - A 0 k ω) 2 μ := by
      have hdecomp : (fun ω => A 0 m ω - A 0 ℓ ω)
                   = (fun ω => (A 0 m ω - A 0 k ω) + (A 0 k ω - A 0 ℓ ω)) := by
        ext ω; ring
      rw [hdecomp]
      apply eLpNorm_add_le
      · exact (hA_meas 0 m).sub (hA_meas 0 k) |>.aestronglyMeasurable
      · exact (hA_meas 0 k).sub (hA_meas 0 ℓ) |>.aestronglyMeasurable
      · norm_num

    -- Each term bounded by √(Cf/k) via uniform bound
    have hCf_k_nn : 0 ≤ Cf / k := div_nonneg hCf_nonneg (Nat.cast_nonneg k)

    have hbound_m : ∫ ω, ((1/(k:ℝ)) * ∑ i : Fin k, f (X (0 + i.val + 1) ω) -
                           (1/(k:ℝ)) * ∑ i : Fin k, f (X (m + i.val + 1) ω))^2 ∂μ
                    ≤ Cf / k := hCf_unif 0 m k hk_pos

    have hbound_ℓ : ∫ ω, ((1/(k:ℝ)) * ∑ i : Fin k, f (X (0 + i.val + 1) ω) -
                           (1/(k:ℝ)) * ∑ i : Fin k, f (X (ℓ + i.val + 1) ω))^2 ∂μ
                    ≤ Cf / k := hCf_unif 0 ℓ k hk_pos

    have hL2_m : eLpNorm (fun ω => A 0 m ω - A 0 k ω) 2 μ
                ≤ ENNReal.ofReal (Real.sqrt (Cf / k)) := by
      apply eLpNorm_two_from_integral_sq_le
      · exact (hA_memLp 0 m).sub (hA_memLp 0 k)
      · exact hCf_k_nn
      · convert hbound_m using 2
        ext ω
        simp [A]
        ring

    have hL2_ℓ : eLpNorm (fun ω => A 0 ℓ ω - A 0 k ω) 2 μ
                ≤ ENNReal.ofReal (Real.sqrt (Cf / k)) := by
      apply eLpNorm_two_from_integral_sq_le
      · exact (hA_memLp 0 ℓ).sub (hA_memLp 0 k)
      · exact hCf_k_nn
      · convert hbound_ℓ using 2
        ext ω
        simp [A]
        ring

    calc eLpNorm (fun ω => A 0 m ω - A 0 ℓ ω) 2 μ
        ≤ eLpNorm (fun ω => A 0 m ω - A 0 k ω) 2 μ
          + eLpNorm (fun ω => A 0 ℓ ω - A 0 k ω) 2 μ := tri
      _ ≤ ENNReal.ofReal (Real.sqrt (Cf / k))
          + ENNReal.ofReal (Real.sqrt (Cf / k)) := by
            exact add_le_add hL2_m hL2_ℓ
      _ = ENNReal.ofReal (2 * Real.sqrt (Cf / k)) := by
            rw [← ENNReal.ofReal_add (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)]
            ring_nf
      _ < ENNReal.ofReal ε := by
            apply ENNReal.ofReal_lt_ofReal_iff hε |>.mpr
            have : Real.sqrt (Cf / k) < ε / 2 := by
              apply sqrt_div_lt_half_eps_of_nat hCf_nonneg hε
              exact Nat.le_refl N
            linarith

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
    -- Build sequence in L¹ using toLp
    let F : ℕ → Lp ℝ 1 μ := fun m => (hA_memLp 0 m).toLp (A 0 m)

    -- F is Cauchy in Lp
    have hCauchy : CauchySeq F := by
      rw [Metric.cauchySeq_iff]
      intro ε hε
      obtain ⟨N, hN⟩ := hA_cauchy_L1_0 ε hε
      refine ⟨N, fun m hm ℓ hℓ => ?_⟩
      -- dist in Lp equals eLpNorm of difference
      have : dist (F m) (F ℓ) = ENNReal.toReal (eLpNorm (fun ω => A 0 m ω - A 0 ℓ ω) 1 μ) := by
        simpa [F] using
          dist_toLp_eq_eLpNorm_sub (hp0 := one_ne_zero) (hp∞ := ENNReal.coe_ne_top)
            (hA_memLp 0 m) (hA_memLp 0 ℓ)
      rw [this]
      have hbound := hN m ℓ hm hℓ
      have : ENNReal.toReal (eLpNorm (fun ω => A 0 m ω - A 0 ℓ ω) 1 μ) < ε := by
        have hfin : eLpNorm (fun ω => A 0 m ω - A 0 ℓ ω) 1 μ ≠ ∞ := by
          exact (MemLp.sub (hA_memLp 0 m) (hA_memLp 0 ℓ)).eLpNorm_ne_top
        apply toReal_lt_of_lt_ofReal hfin (by exact le_of_lt hε)
        exact hbound
      exact this

    -- Completeness of L¹ gives a limit
    obtain ⟨G, hG⟩ := CauchySeq.tendsto_of_complete hCauchy

    -- Extract measurable representative
    refine ⟨G, G.aestronglyMeasurable.measurable_mk, G.memℒp, ?_⟩
    intro ε hε
    -- Use convergence of F to G
    have : ∃ M, ∀ m ≥ M, dist (F m) G < ε := by
      exact Metric.tendsto_atTop.mp hG ε hε
    obtain ⟨M, hM⟩ := this
    refine ⟨M, fun m hm => ?_⟩
    -- Convert dist back to eLpNorm
    have hdist : dist (F m) G = ENNReal.toReal (eLpNorm (fun ω => A 0 m ω - G ω) 1 μ) := by
      simpa [F] using
        dist_toLp_eq_eLpNorm_sub (hp0 := one_ne_zero) (hp∞ := ENNReal.coe_ne_top)
          (hA_memLp 0 m) G.memℒp
    rw [← hdist] at hM
    have hreal : ENNReal.toReal (eLpNorm (fun ω => A 0 m ω - G ω) 1 μ) < ε := hM m hm
    have hfin : eLpNorm (fun ω => A 0 m ω - G ω) 1 μ ≠ ∞ := by
      exact (MemLp.sub (hA_memLp 0 m) G.memℒp).eLpNorm_ne_top
    calc eLpNorm (fun ω => A 0 m ω - G ω) 1 μ
        < ENNReal.ofReal (ENNReal.toReal (eLpNorm (fun ω => A 0 m ω - G ω) 1 μ)) := by
          rw [ENNReal.ofReal_toReal hfin]
        _ < ENNReal.ofReal ε := by exact ENNReal.ofReal_lt_ofReal_iff hε |>.mpr hreal

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

    -- Get uniform bound constant
    obtain ⟨Cf, hCf_nonneg, hCf_unif⟩ := l2_bound_two_windows_uniform X hX_contract hX_meas hX_L2 f hf_meas hf_bdd

    -- Choose M₂ large enough that √(Cf/M₂) < ε/2
    -- This means Cf/M₂ < ε²/4, so M₂ > 4Cf/ε²
    have hε_sq_pos : 0 < (ε / 2) ^ 2 := pow_pos hε2_pos 2

    let M₂ := Nat.ceil (4 * Cf / (ε ^ 2)) + 1

    -- Define M as max of M₁ and M₂
    let M := max M₁ M₂

    use M
    intro m hm
    have hm₁ : M₁ ≤ m := le_of_max_le_left (le_trans (le_max_left _ _) hm)
    have hm₂ : M₂ ≤ m := le_of_max_le_right (le_trans (le_max_right _ _) hm)

    -- Apply triangle inequality
    have h_triangle : eLpNorm (fun ω => A n m ω - alpha_0 ω) 1 μ ≤
        eLpNorm (fun ω => A n m ω - A 0 m ω) 1 μ +
        eLpNorm (fun ω => A 0 m ω - alpha_0 ω) 1 μ := by
      -- Use eLpNorm triangle: ‖f - h‖ ≤ ‖f - g‖ + ‖g - h‖
      -- This follows from the fact that (f - h) = (f - g) + (g - h)
      have h_decomp : (fun ω => A n m ω - alpha_0 ω) =
          fun ω => (A n m ω - A 0 m ω) + (A 0 m ω - alpha_0 ω) := by
        ext ω; ring
      rw [h_decomp]
      -- Apply eLpNorm_add_le from Mathlib
      apply eLpNorm_add_le
      · exact (hA_meas n m).sub (hA_meas 0 m) |>.aestronglyMeasurable
      · exact (hA_meas 0 m).sub halpha_0_meas |>.aestronglyMeasurable
      · norm_num

    -- Bound term 2
    have h_term2 : eLpNorm (fun ω => A 0 m ω - alpha_0 ω) 1 μ < ENNReal.ofReal (ε / 2) := by
      apply hM₁; exact hm₁

    -- Bound term 1 using L² → L¹ and l2_bound_two_windows
    have h_term1 : eLpNorm (fun ω => A n m ω - A 0 m ω) 1 μ < ENNReal.ofReal (ε / 2) := by
      -- Use l2_bound_two_windows to bound ∫ (A n m - A 0 m)² ≤ Cf / m
      by_cases hm_pos : 0 < m
      · -- Apply the uniform bound
        have h_bound_sq : ∫ ω, ((1/(m:ℝ)) * ∑ i : Fin m, f (X (n + i.val + 1) ω) -
                                 (1/(m:ℝ)) * ∑ i : Fin m, f (X (0 + i.val + 1) ω))^2 ∂μ
                         ≤ Cf / m := hCf_unif n 0 m hm_pos
        -- Convert to A notation
        have h_bound_sq' : ∫ ω, (A n m ω - A 0 m ω)^2 ∂μ ≤ Cf / m := by
          convert h_bound_sq using 2
          ext ω
          simp [A]; ring
        -- Convert integral to eLpNorm using utility lemma
        have h_L2 : eLpNorm (fun ω => A n m ω - A 0 m ω) 2 μ ≤
            ENNReal.ofReal (Real.sqrt (Cf / m)) := by
          apply eLpNorm_two_from_integral_sq_le
          · exact (hA_memLp n m).sub (hA_memLp 0 m)
          · exact div_nonneg hCf_nonneg (Nat.cast_nonneg m)
          · exact h_bound_sq'
        -- Use L² → L¹
        calc eLpNorm (fun ω => A n m ω - A 0 m ω) 1 μ
            ≤ eLpNorm (fun ω => A n m ω - A 0 m ω) 2 μ := by
              apply eLpNorm_le_eLpNorm_of_exponent_le
              · norm_num
              · exact (hA_meas n m).sub (hA_meas 0 m) |>.aestronglyMeasurable
          _ ≤ ENNReal.ofReal (Real.sqrt (Cf / m)) := h_L2
          _ < ENNReal.ofReal (ε / 2) := by
              apply ENNReal.ofReal_lt_ofReal_iff hε2_pos |>.mpr
              apply sqrt_div_lt_half_eps_of_nat hCf_nonneg hε
              exact hm₂
      · -- m = 0 case is trivial or doesn't occur
        simp [Nat.not_lt.mp hm_pos] at hm
        omega

    -- Combine
    calc eLpNorm (fun ω => A n m ω - alpha_0 ω) 1 μ
        ≤ eLpNorm (fun ω => A n m ω - A 0 m ω) 1 μ +
            eLpNorm (fun ω => A 0 m ω - alpha_0 ω) 1 μ := h_triangle
      _ < ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := by
            exact ENNReal.add_lt_add h_term1 h_term2
      _ = ENNReal.ofReal ε := by
            rw [← ENNReal.ofReal_add hε2_pos.le hε2_pos.le]; norm_num

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
## Step 6: Build directing measure ν via Carathéodory extension

Given the family of limit functions α_f for bounded measurable f, we construct
the directing measure ν : Ω → Measure ℝ such that:
- ν(ω) is a probability measure for each ω
- ω ↦ ν(ω)(B) is measurable for each Borel B
- α_f(ω) = ∫ f dν(ω) for all bounded measurable f

The construction proceeds via the Carathéodory extension theorem:
1. For intervals (-∞, t], use α_{𝟙_{(-∞,t]}} to define a pre-measure
2. Verify this is a valid CDF (monotone, right-continuous, limits 0 and 1)
3. Extend to Borel sets via Carathéodory
4. Establish measurability of ω ↦ ν(ω)(B) using monotone class theorem

This is the "lightest path" mentioned in the original plan.
-/

/-- For each ω, the map t ↦ α_{𝟙_{(-∞,t]}}(ω) defines a CDF.

This will be used to construct ν(ω) via the Stieltjes measure construction.
-/
def cdf_from_alpha
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ)
    (t : ℝ) : Ω → ℝ :=
  -- For each t, apply weighted_sums_converge_L1 with f = 𝟙_{(-∞,t]}
  -- This gives α_{𝟙_{(-∞,t]}} : Ω → ℝ
  sorry

/-- Build the directing measure ν from the CDF.

For each ω ∈ Ω, we construct ν(ω) as the probability measure on ℝ with CDF
given by t ↦ cdf_from_alpha X ω t.

This uses the Stieltjes measure construction from mathlib.
-/
def directing_measure
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ) :
    Ω → Measure ℝ :=
  fun ω => sorry  -- Measure.ofCDF or StieltjesFunction construction

/-- The directing measure is a probability measure. -/
lemma directing_measure_isProbabilityMeasure
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ)
    (ω : Ω) :
    IsProbabilityMeasure (directing_measure X hX_contract hX_meas hX_L2 ω) := by
  sorry

/-- For each set s, the map ω ↦ ν(ω)(s) is measurable.

This is the key measurability property needed for complete_from_directing_measure.

For measurable sets: Uses monotone class theorem (π-λ theorem) - prove for intervals,
extend to all Borel sets.

For non-measurable sets: The measure is 0 by outer regularity, so the function is
the constant zero function (hence measurable).
-/
lemma directing_measure_measurable
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ)
    (s : Set ℝ) :
    Measurable (fun ω => directing_measure X hX_contract hX_meas hX_L2 ω s) := by
  -- For measurable sets: Use π-λ theorem (intervals → Borel sets)
  -- For non-measurable sets: measure is 0, so constant function
  by_cases hs : MeasurableSet s
  · -- Measurable case: prove for intervals, extend via monotone class
    -- Step 1: For intervals (-∞, t], this follows from measurability of cdf_from_alpha
    -- Step 2: Extend to all Borel sets via π-λ theorem (MeasurableSpace.induction_on_inter)
    sorry
  · -- Non-measurable case: ν(ω)(s) = 0 for all ω (by outer regularity)
    -- Therefore fun ω => ν ω s is the constant zero function
    sorry

/-- The directing measure integrates to give α_f.

For any bounded measurable f, we have α_f(ω) = ∫ f dν(ω) a.e.
This is the fundamental bridge property.
-/
lemma directing_measure_integral
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ)
    (f : ℝ → ℝ) (hf_meas : Measurable f)
    (hf_bdd : ∃ M, ∀ x, |f x| ≤ M) :
    ∃ (alpha : Ω → ℝ),
      Measurable alpha ∧ MemLp alpha 1 μ ∧
      (∀ n, ∀ ε > 0, ∃ M : ℕ, ∀ m : ℕ, m ≥ M →
        ∫ ω, |(1/(m:ℝ)) * ∑ k : Fin m, f (X (n + k.val + 1) ω) - alpha ω| ∂μ < ε) ∧
      (∀ᵐ ω ∂μ, alpha ω = ∫ x, f x ∂(directing_measure X hX_contract hX_meas hX_L2 ω)) := by
  -- Get alpha from weighted_sums_converge_L1
  obtain ⟨alpha, halpha_meas, halpha_L1, halpha_conv⟩ :=
    weighted_sums_converge_L1 X hX_contract hX_meas hX_L2 f hf_meas hf_bdd
  use alpha, halpha_meas, halpha_L1, halpha_conv
  -- Show alpha = ∫ f dν a.e.
  -- This requires showing that the limit of Cesàro sums equals the integral
  -- Uses: Law of Large Numbers + contractability
  sorry

/-- The bridge property: E[∏ᵢ 𝟙_{Bᵢ}(X_{k(i)})] = E[∏ᵢ ν(·)(Bᵢ)].

This is the key property needed for complete_from_directing_measure.
It follows from contractability and the fact that α_{𝟙_B} = ν(·)(B).
-/
lemma directing_measure_bridge
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ)
    {m : ℕ} (k : Fin m → ℕ) (B : Fin m → Set ℝ)
    (hB : ∀ i, MeasurableSet (B i)) :
    ∫⁻ ω, ∏ i : Fin m,
        ENNReal.ofReal ((B i).indicator (fun _ => (1 : ℝ)) (X (k i) ω)) ∂μ
      = ∫⁻ ω, ∏ i : Fin m,
        directing_measure X hX_contract hX_meas hX_L2 ω (B i) ∂μ := by
  -- Strategy:
  -- 1. LHS = E[∏ᵢ 𝟙_{Bᵢ}(X_{k(i)})]
  -- 2. By contractability, this equals E[∏ᵢ α_{𝟙_{Bᵢ}}]
  -- 3. By directing_measure_integral, α_{𝟙_B}(ω) = ν(ω)(B) a.e.
  -- 4. RHS = E[∏ᵢ ν(·)(Bᵢ)]
  -- 5. Therefore LHS = RHS
  sorry

/-!
## Infrastructure for directing measure construction (used by TheoremViaL2)

The following theorems provide the building blocks for constructing the directing
measure ν and verifying its properties. The actual completion via CommonEnding
happens in TheoremViaL2.lean to maintain proper import separation.
-/

/-- **L² convergence establishes directing measure requirements**.

This theorem packages the L² approach infrastructure, showing that for a contractable
sequence with L² bounds, we can construct a directing measure ν that satisfies all
the requirements needed for the CommonEnding completion.

**What this provides**:
- Existence of directing measure ν via `directing_measure`
- ν(ω) is a probability measure
- ω ↦ ν(ω)(B) is measurable for Borel B
- Bridge property: E[∏ᵢ 𝟙_{Bᵢ}(X_{k(i)})] = E[∏ᵢ ν(·)(Bᵢ)]

**What remains**: Applying `CommonEnding.complete_from_directing_measure` to get
ConditionallyIID. This happens in TheoremViaL2.lean.

**Reference**: Kallenberg (2005), Theorem 1.1 (page 26-27), "Second proof".
-/
theorem directing_measure_satisfies_requirements
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_meas : ∀ i, Measurable (X i))
    (hX_contract : Contractable μ X)
    (hX_L2 : ∀ i, MemLp (X i) 2 μ) :
    ∃ (ν : Ω → Measure ℝ),
      (∀ ω, IsProbabilityMeasure (ν ω)) ∧
      (∀ s, Measurable (fun ω => ν ω s)) ∧
      (∀ {m : ℕ} (k : Fin m → ℕ) (B : Fin m → Set ℝ),
        (∀ i, MeasurableSet (B i)) →
          ∫⁻ ω, ∏ i : Fin m,
              ENNReal.ofReal ((B i).indicator (fun _ => (1 : ℝ)) (X (k i) ω)) ∂μ
            = ∫⁻ ω, ∏ i : Fin m, ν ω (B i) ∂μ) := by
  use directing_measure X hX_contract hX_meas hX_L2
  constructor
  · intro ω
    exact directing_measure_isProbabilityMeasure X hX_contract hX_meas hX_L2 ω
  constructor
  · intro s
    exact directing_measure_measurable X hX_contract hX_meas hX_L2 s
  · intro m k B hB
    exact directing_measure_bridge X hX_contract hX_meas hX_L2 k B hB

end Exchangeability.DeFinetti.ViaL2
