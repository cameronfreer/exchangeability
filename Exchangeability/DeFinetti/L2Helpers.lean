/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Exchangeability.Contractability
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# Helper Lemmas for L² de Finetti Proof

This file contains auxiliary lemmas used in the L² approach to de Finetti's theorem
(`ViaL2.lean`). All lemmas here are complete (no sorries) and compile cleanly.

## Contents

1. **CovarianceHelpers**: Lemmas about contractable sequences and covariance structure
2. **Lp Utility Lemmas**: Standard Lp space and ENNReal conversion helpers
3. **FinIndexHelpers**: Fin reindexing lemmas for two-window bounds

## Key Results

- `contractable_map_single`: All marginals have the same distribution
- `contractable_map_pair`: All bivariate marginals have the same joint distribution
- `contractable_comp`: Contractability preserved under measurable postcomposition
- `dist_toLp_eq_eLpNorm_sub`: Distance in L^p equals norm of difference
- Various arithmetic bounds for convergence rates
- Fin index reindexing lemmas for filtered sums

-/

noncomputable section

namespace Exchangeability.DeFinetti.L2Helpers

open MeasureTheory ProbabilityTheory BigOperators Filter Topology
open Exchangeability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

open scoped BigOperators

section CovarianceHelpers

variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable (X : ℕ → Ω → ℝ)
variable (hX_contract : Contractable μ X)
variable (hX_meas : ∀ i, Measurable (X i))

/-
Note: Some lemmas in this section explicitly include type and measurability parameters that shadow
section variables. This makes certain section variables unused for those lemmas, requiring
`set_option linter.unusedSectionVars false` before each affected declaration.
-/

/-- The unique element of Fin 1. -/
private def fin1Zero : Fin 1 := ⟨0, by decide⟩
/-- First element of Fin 2. -/
private def fin2Zero : Fin 2 := ⟨0, by decide⟩
/-- Second element of Fin 2. -/
private def fin2One : Fin 2 := ⟨1, by decide⟩

/-- Evaluation at fin1Zero is measurable. -/
private lemma measurable_eval_fin1 :
    Measurable fun g : (Fin 1 → ℝ) => g (fin1Zero) :=
  measurable_pi_apply _

/-- Evaluation at any element of Fin 2 is measurable. -/
private lemma measurable_eval_fin2 {i : Fin 2} :
    Measurable fun g : (Fin 2 → ℝ) => g i :=
  measurable_pi_apply _

set_option linter.unusedSectionVars false in
/-- **All marginals have the same distribution in a contractable sequence.**

For a contractable sequence, the law of each coordinate agrees with the law of `X 0`.
This follows from contractability by taking the singleton subsequence `{i}`.

This is used to establish uniform covariance structure across all pairs of coordinates. -/
lemma contractable_map_single (hX_contract : Contractable μ X) (hX_meas : ∀ i, Measurable (X i)) {i : ℕ} :
    Measure.map (fun ω => X i ω) μ = Measure.map (fun ω => X 0 ω) μ := by
  classical
  -- `k` selects the singleton subsequence `{i}`.
  let k : Fin 1 → ℕ := fun _ => i
  have hk : StrictMono k := by
    intro a b hab
    simp_all [Fin.eq_zero a, Fin.eq_zero b]
  have h_map := hX_contract 1 k hk
  let eval : (Fin 1 → ℝ) → ℝ := fun g => g fin1Zero
  have h_eval_meas : Measurable eval := measurable_eval_fin1
  have h_meas_k : Measurable fun ω => fun j : Fin 1 => X (k j) ω := by
    fun_prop
  have h_meas_std : Measurable fun ω => fun j : Fin 1 => X j.val ω := by
    fun_prop
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

/-- **Strict monotonicity for two-point subsequence selection.**

For `i < j`, the function mapping `0 ↦ i, 1 ↦ j` is strictly monotone on Fin 2. -/
private lemma strictMono_two {i j : ℕ} (hij : i < j) :
    StrictMono fun t : Fin 2 => if t = fin2Zero then i else j := by
  classical
  intro a b hlt
  -- Reduce to: a.val = 0, b.val = 1 (only possibility in Fin 2 with a < b)
  have hval : a.val < b.val := Fin.lt_def.mp hlt
  have hb_val_le : b.val ≤ 1 := Nat.lt_succ_iff.mp (show b.val < 2 by simp [b.is_lt])
  have hb_ne_zero : b.val ≠ 0 := by intro hb; simp [hb] at hval
  have hb_val : b.val = 1 :=
    le_antisymm hb_val_le (Nat.succ_le_of_lt (Nat.pos_of_ne_zero hb_ne_zero))
  have ha_val : a.val = 0 :=
    Nat.lt_one_iff.mp (by simp only [hb_val] at hval; exact hval)
  -- Apply to conclusion
  have ha : a = fin2Zero := by ext; simp [fin2Zero, ha_val]
  have hb : b = fin2One := by ext; simp [fin2One, hb_val]
  subst ha; subst hb
  simp [fin2Zero, fin2One, hij]

set_option linter.unusedSectionVars false in
/-- **All bivariate marginals have the same distribution in a contractable sequence.**

For a contractable sequence, every increasing pair `(i,j)` with `i < j` has the same
joint law as `(X 0, X 1)`. This follows from contractability by taking the two-point
subsequence `{i, j}`.

Combined with `contractable_map_single`, this establishes that covariances are uniform:
Cov(X_i, X_j) depends only on whether i = j, giving the covariance structure needed
for the L² contractability bound. -/
lemma contractable_map_pair (hX_contract : Contractable μ X) (hX_meas : ∀ i, Measurable (X i))
    {i j : ℕ} (hij : i < j) :
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
    refine (measurable_eval_fin2 (i := fin2Zero)).prodMk ?_
    exact measurable_eval_fin2 (i := fin2One)
  have h_meas_k : Measurable fun ω => fun t : Fin 2 => X (k t) ω := by
    refine measurable_pi_lambda _ ?_
    intro t
    by_cases ht : t = fin2Zero
    · have : k t = i := by simp [k, ht]
      simp [this]; exact hX_meas i
    · have : k t = j := by simp [k, if_neg ht]
      simp [this]; exact hX_meas j
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

set_option linter.unusedSectionVars false in
/-- **Contractability is preserved under measurable postcomposition.**

If X is a contractable sequence and f is measurable, then `f ∘ X` is also contractable.
This allows transferring contractability from one sequence to another via measurable
transformations, which is useful for studying bounded functions of contractable sequences. -/
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
    fun_prop
  have h_meas_std : Measurable fun ω => fun i : Fin n => X i.val ω := by
    fun_prop
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

/-- **Young's inequality for products: |ab| ≤ (a² + b²)/2.**

Elementary inequality used to dominate products by squares, derived from
the identity `0 ≤ (|a| - |b|)²`. Used in covariance bounds. -/
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

/-- **Distance in L^p space equals the L^p norm of the difference.**

For functions in L^p, the metric distance between their `toLp` representatives equals
the `eLpNorm` of their pointwise difference (after converting from ENNReal).

This bridges the abstract metric structure of L^p spaces with concrete norm calculations. -/
lemma dist_toLp_eq_eLpNorm_sub
  {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {p : ENNReal}
  {f g : Ω → ℝ} (hf : MemLp f p μ) (hg : MemLp g p μ) :
  dist (hf.toLp f) (hg.toLp g)
    = ENNReal.toReal (eLpNorm (fun ω => f ω - g ω) p μ) := by
  rw [Lp.dist_edist, Lp.edist_toLp_toLp]
  rfl

/-- **Converting ENNReal inequalities to real inequalities.**

If `x < ofReal ε` in ENNReal (with x finite), then `toReal x < ε` in ℝ.
Bridges extended and real arithmetic in L^p norm bounds. -/
lemma toReal_lt_of_lt_ofReal {x : ENNReal} {ε : ℝ}
    (_hx : x ≠ ⊤) (hε : 0 ≤ ε) :
    x < ENNReal.ofReal ε → ENNReal.toReal x < ε := by
  intro h
  have : ENNReal.toReal x < ENNReal.toReal (ENNReal.ofReal ε) :=
    ENNReal.toReal_strict_mono (ENNReal.ofReal_ne_top) h
  simp [ENNReal.toReal_ofReal hε] at this
  exact this

/-- **Arithmetic bound for convergence rates: √(Cf/m) < ε/2 when m is large.**

Given a constant Cf and target precision ε, provides an explicit threshold for m
such that √(Cf/m) < ε/2. Used to establish L² Cauchy sequences converge in L¹. -/
lemma sqrt_div_lt_half_eps_of_nat
  {Cf ε : ℝ} (hCf : 0 ≤ Cf) (hε : 0 < ε) :
  ∀ ⦃m : ℕ⦄, m ≥ Nat.ceil (4 * Cf / (ε^2)) + 1 →
    Real.sqrt (Cf / m) < ε / 2 := by
  intro m hm
  have hA_lt_m : 4*Cf/ε^2 < (m : ℝ) := by
    calc 4*Cf/ε^2
        ≤ Nat.ceil (4*Cf/ε^2) := Nat.le_ceil _
      _ < (Nat.ceil (4*Cf/ε^2) : ℝ) + 1 := by linarith
      _ ≤ m := by exact_mod_cast hm
  by_cases hCf0 : Cf = 0
  · simp [hCf0, div_pos hε (by norm_num : (0:ℝ) < 2)]
  have hCfpos : 0 < Cf := lt_of_le_of_ne hCf (Ne.symm hCf0)
  have hmpos : 0 < (m : ℝ) := by linarith [show 0 < 4*Cf/ε^2 by positivity, hA_lt_m]
  have hdenom_pos : 0 < 4*Cf/ε^2 := by positivity
  have hdiv : Cf / (m : ℝ) < Cf / (4*Cf/ε^2) :=
    div_lt_div_of_pos_left hCfpos hdenom_pos hA_lt_m
  have heq : Cf / (4*Cf/ε^2) = ε^2 / 4 := by
    field_simp [ne_of_gt hCfpos]
  have hlt : Cf / (m : ℝ) < ε^2 / 4 := by
    rw [← heq]; exact hdiv
  have hnonneg : 0 ≤ Cf / (m : ℝ) := div_nonneg hCf (Nat.cast_nonneg m)
  calc Real.sqrt (Cf / m)
      < Real.sqrt (ε^2 / 4) := Real.sqrt_lt_sqrt hnonneg hlt
    _ = Real.sqrt ((ε/2)^2) := by
        congr 1
        rw [sq]
        ring
    _ = |ε / 2| := Real.sqrt_sq_eq_abs _
    _ = ε / 2 := abs_of_pos (div_pos hε (by norm_num))

/-- **Arithmetic bound for convergence rates: 3·√(Cf/m) < ε when m is large.**

Similar to `sqrt_div_lt_half_eps_of_nat` but with factor 3 instead of 1/2.
Used in the Cauchy argument where we sum three L² bounds via triangle inequality. -/
lemma sqrt_div_lt_third_eps_of_nat
  {Cf ε : ℝ} (hCf : 0 ≤ Cf) (hε : 0 < ε) :
  ∀ ⦃m : ℕ⦄, m ≥ Nat.ceil (9 * Cf / (ε^2)) + 1 →
    3 * Real.sqrt (Cf / m) < ε := by
  intro m hm
  have hA_lt_m : 9*Cf/ε^2 < (m : ℝ) := by
    calc 9*Cf/ε^2
        ≤ Nat.ceil (9*Cf/ε^2) := Nat.le_ceil _
      _ < (Nat.ceil (9*Cf/ε^2) : ℝ) + 1 := by linarith
      _ ≤ m := by exact_mod_cast hm
  by_cases hCf0 : Cf = 0
  · simp [hCf0, hε]
  have hCfpos : 0 < Cf := lt_of_le_of_ne hCf (Ne.symm hCf0)
  have hmpos : 0 < (m : ℝ) := by linarith [show 0 < 9*Cf/ε^2 by positivity, hA_lt_m]
  have hdenom_pos : 0 < 9*Cf/ε^2 := by positivity
  have hdiv : Cf / (m : ℝ) < Cf / (9*Cf/ε^2) :=
    div_lt_div_of_pos_left hCfpos hdenom_pos hA_lt_m
  have heq : Cf / (9*Cf/ε^2) = ε^2 / 9 := by
    field_simp [ne_of_gt hCfpos]
  have hlt : Cf / (m : ℝ) < ε^2 / 9 := by
    rw [← heq]; exact hdiv
  have hnonneg : 0 ≤ Cf / (m : ℝ) := div_nonneg hCf (Nat.cast_nonneg m)
  have h_sqrt_simpl : Real.sqrt (ε^2 / 9) = ε / 3 := by
    rw [Real.sqrt_div (sq_nonneg ε), Real.sqrt_sq (le_of_lt hε),
        show (9 : ℝ) = 3^2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 3)]
  calc 3 * Real.sqrt (Cf / m)
      < 3 * Real.sqrt (ε^2 / 9) := by linarith [Real.sqrt_lt_sqrt hnonneg hlt]
    _ = 3 * (ε / 3) := by rw [h_sqrt_simpl]
    _ = ε := by ring

/-- Convert an L² integral bound to an eLpNorm bound. -/
lemma eLpNorm_two_from_integral_sq_le
  {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  {g : Ω → ℝ} (hg : MemLp g 2 μ)
  {C : ℝ} (hC : 0 ≤ C)
  (h : ∫ ω, (g ω)^2 ∂μ ≤ C) :
  eLpNorm g 2 μ ≤ ENNReal.ofReal (Real.sqrt C) := by
  -- For real-valued g, use ‖g‖ = |g| and sq_abs
  have h_sq_eq : ∀ ω, ‖g ω‖^2 = (g ω)^2 := by
    intro ω; rw [Real.norm_eq_abs, sq_abs]
  -- Get integral bound in terms of ‖g‖^2
  have h_int_le : ∫ ω, ‖g ω‖^2 ∂μ ≤ C := by
    have : (fun ω => ‖g ω‖^2) = fun ω => (g ω)^2 := funext h_sq_eq
    rw [this]; exact h
  -- Integral is nonnegative
  have h_int_nonneg : 0 ≤ ∫ ω, ‖g ω‖^2 ∂μ := by
    apply integral_nonneg; intro ω; exact sq_nonneg _
  -- Strategy: eLpNorm g 2 μ = (∫ ‖g‖²)^(1/2) by definition (via MemLp characterization).
  -- We have ∫ ‖g‖² ≤ C, so (∫ ‖g‖²)^(1/2) ≤ C^(1/2) = √C.

  -- Use the MemLp characterization to convert eLpNorm to an integral
  rw [MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num) hg]
  simp only [ENNReal.toReal_ofNat]
  -- Now we have: ofReal((∫ ‖g‖² ∂μ)^(1/2)) ≤ ofReal(√C)
  -- Use ofReal monotonicity
  apply ENNReal.ofReal_le_ofReal
  -- Show (∫ ‖g‖² ∂μ)^(2⁻¹) ≤ √C
  -- The goal has 2⁻¹ which is the same as (1/2)
  have h_C_nonneg : 0 ≤ C := by linarith [h_int_nonneg, h_int_le]
  -- Convert 2⁻¹ to (1/2) and use rpow monotonicity
  show (∫ ω, ‖g ω‖ ^ 2 ∂μ) ^ (2⁻¹ : ℝ) ≤ Real.sqrt C
  rw [show (2⁻¹ : ℝ) = (1 / 2 : ℝ) by norm_num]
  -- Goal is now (∫ ‖g‖²)^(1/2) ≤ √C
  rw [Real.sqrt_eq_rpow]
  -- Goal is (∫ ‖g‖²)^(1/2) ≤ C^(1/2)
  -- Note: the ‖g‖^2 in the integral is with ^(2:ℕ), need to be careful with types
  have h_int_le' : (∫ ω, ‖g ω‖ ^ (2:ℝ) ∂μ) ≤ C := by
    convert h_int_le using 2
    ext ω
    simp [sq]
  gcongr

end LpUtilities

/-- **Any function from Fin 1 is vacuously strictly monotone.**

Since Fin 1 has only one element, the premise `i < j` is impossible. -/
private lemma fin1_strictMono_vacuous (k : Fin 1 → ℕ) : StrictMono k := by
  intro i j hij
  exfalso
  have hi : i = 0 := Fin.eq_zero i
  have hj : j = 0 := Fin.eq_zero j
  rw [hi, hj] at hij
  exact LT.lt.false hij

/-- **Single marginals have identical distribution in contractable sequences.**

For contractable sequences, all variables `X_k` have the same distribution as `X_0`.
This is a direct application of `contractable_map_single`.

**Note**: This wrapper is kept for compatibility, but `contractable_map_single` can be
used directly when measurability hypotheses are available. -/
lemma contractable_single_marginal_eq
    {μ : Measure Ω} {X : ℕ → Ω → α}
    (hX_contract : Contractable μ X) (hX_meas : ∀ i, Measurable (X i)) (k : ℕ) :
    Measure.map (X k) μ = Measure.map (X 0) μ := by
  -- Apply contractability to the singleton subsequence {k}
  classical
  let κ : Fin 1 → ℕ := fun _ => k
  have hκ : StrictMono κ := fin1_strictMono_vacuous κ
  have h_map := hX_contract 1 κ hκ
  -- h_map says: map of (ω ↦ (i ↦ X (κ i) ω)) equals map of (ω ↦ (i ↦ X i.val ω))
  -- We need to extract the single coordinate from Fin 1 → α
  let eval : (Fin 1 → α) → α := fun g => g ⟨0, by decide⟩
  have h_eval_meas : Measurable eval := measurable_pi_apply _
  have h_meas_κ : Measurable fun ω => fun j : Fin 1 => X (κ j) ω := by
    fun_prop
  have h_meas_std : Measurable fun ω => fun j : Fin 1 => X j.val ω := by
    fun_prop
  -- Apply eval to both sides
  have h_left := (Measure.map_map h_eval_meas h_meas_κ (μ := μ)).symm
  have h_right := Measure.map_map h_eval_meas h_meas_std (μ := μ)
  have h_eval := congrArg (Measure.map eval) h_map
  have h_comp := h_left.trans (h_eval.trans h_right)
  -- Simplify the compositions
  have h_comp_left : (fun ω => eval (fun j : Fin 1 => X (κ j) ω)) = fun ω => X k ω := by
    funext ω; simp [eval, κ]
  have h_comp_right : (fun ω => eval (fun j : Fin 1 => X j.val ω)) = fun ω => X 0 ω := by
    funext ω; simp [eval]
  simpa [Function.comp, h_comp_left, h_comp_right] using h_comp

-- Helper lemmas for Fin index gymnastics in two-window bounds.
-- These lemmas isolate the technical reindexing and cardinality proofs needed for
-- the weighted average machinery.
namespace FinIndexHelpers

open scoped BigOperators
open Finset

/-- Auxiliary lemma: the two filtered sets partition Fin(2k). -/
private lemma card_filter_partition (k : ℕ) :
  ((univ : Finset (Fin (2*k))).filter (fun i => i.val < k)).card +
  ((univ : Finset (Fin (2*k))).filter (fun i => ¬(i.val < k))).card = 2*k := by
  have h_partition : (univ : Finset (Fin (2*k)))
                   = (univ : Finset (Fin (2*k))).filter (fun i => i.val < k)
                   ∪ (univ : Finset (Fin (2*k))).filter (fun i => ¬(i.val < k)) := by
    ext i; simp only [mem_union, mem_filter, mem_univ, true_and]; tauto
  have h_disj : Disjoint ((univ : Finset (Fin (2*k))).filter (fun i => i.val < k))
                         ((univ : Finset (Fin (2*k))).filter (fun i => ¬(i.val < k))) := by
    rw [disjoint_iff_ne]
    intro a ha b hb
    simp only [mem_filter, mem_univ, true_and] at ha hb
    intro heq
    rw [heq] at ha
    exact hb ha
  have h_card_sum := card_union_of_disjoint h_disj
  rw [← h_partition] at h_card_sum
  simp only [card_fin] at h_card_sum
  convert h_card_sum.symm using 2

/-- Cardinality of `{i : Fin(2k) | i.val < k}` is k. -/
lemma card_filter_fin_val_lt_two_mul (k : ℕ) :
  ((univ : Finset (Fin (2*k))).filter (fun i => i.val < k)).card = k := by
  -- Use symmetry: both halves of Fin (2k) have equal size
  have h_part := card_filter_partition k
  -- Prove both sets have size k by showing they partition 2k equally
  suffices h : ((univ : Finset (Fin (2*k))).filter (fun i => i.val < k)).card =
               ((univ : Finset (Fin (2*k))).filter (fun i => ¬(i.val < k))).card by omega
  -- Use Finset.card_bij to show the two filtered sets have equal cardinality
  apply Finset.card_bij (fun (a : Fin (2*k)) (ha : a ∈ (univ.filter (fun i => i.val < k))) => (⟨a.val + k, by simp at ha; omega⟩ : Fin (2*k)))
  · intro a ha
    simp only [mem_filter, mem_univ, true_and] at ha ⊢
    omega
  · intro a b ha hb h
    simp at h
    exact Fin.ext (by omega)
  · intro b hb
    simp only [mem_filter, mem_univ, true_and, not_lt] at hb
    use ⟨b.val - k, by omega⟩
    refine ⟨?_, ?_⟩
    · simp only [mem_filter, mem_univ, true_and]
      have : k ≤ b.val := hb
      have : b.val < 2 * k := b.isLt
      omega
    · ext
      simp
      have : k ≤ b.val := hb
      omega

/-- Cardinality of `{i : Fin(2k) | i.val ≥ k}` is k. -/
lemma card_filter_fin_val_ge_two_mul (k : ℕ) :
  ((univ : Finset (Fin (2*k))).filter (fun i => ¬(i.val < k))).card = k := by
  have h_lt := card_filter_fin_val_lt_two_mul k
  have h_part := card_filter_partition k
  omega

/-- Sum over `{i : Fin n | i.val < k}` equals sum over Fin k when k ≤ n. -/
lemma sum_filter_fin_val_lt_eq_sum_fin {β : Type*} [AddCommMonoid β] (n k : ℕ) (hk : k ≤ n) (g : ℕ → β) :
  ∑ i ∈ ((univ : Finset (Fin n)).filter (fun i => i.val < k)), g i.val
    = ∑ j : Fin k, g j.val := by
  -- The filtered set equals the image of Fin k under the embedding
  have h_eq : ((univ : Finset (Fin n)).filter (fun i => i.val < k))
            = Finset.image (fun (j : Fin k) => (⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩ : Fin n)) univ := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hi
      use ⟨i.val, hi⟩
    · rintro ⟨j, _, rfl⟩
      exact j.isLt
  rw [h_eq, Finset.sum_image]
  · intro a b _ _ hab
    simp only [Fin.mk.injEq] at hab
    exact Fin.ext hab

/-- Sum over `{i : Fin n | i.val ≥ k}` equals sum over Fin (n-k) with offset, when k ≤ n. -/
lemma sum_filter_fin_val_ge_eq_sum_fin {β : Type*} [AddCommMonoid β] (n k : ℕ) (hk : k ≤ n) (g : ℕ → β) :
  ∑ i ∈ ((univ : Finset (Fin n)).filter (fun i => ¬(i.val < k))), g i.val
    = ∑ j : Fin (n - k), g (k + j.val) := by
  -- The filtered set equals the image of Fin (n-k) under the shift map
  have h_eq : ((univ : Finset (Fin n)).filter (fun i => ¬(i.val < k)))
            = Finset.image (fun (j : Fin (n - k)) => (⟨k + j.val, by omega⟩ : Fin n)) univ := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, not_lt]
    constructor
    · intro hi
      use ⟨i.val - k, by omega⟩
      ext
      simp
      omega
    · rintro ⟨j, _, rfl⟩
      simp
  rw [h_eq, Finset.sum_image]
  · intro a b _ _ hab
    simp only [Fin.mk.injEq] at hab
    exact Fin.ext (by omega)

/-- Sum over last k elements of Fin(n+k) equals sum over Fin k with offset. -/
lemma sum_last_block_eq_sum_fin {β : Type*} [AddCommMonoid β] (n k : ℕ) (g : ℕ → β) :
  ∑ i ∈ ((univ : Finset (Fin (n + k))).filter (fun i => n ≤ i.val)), g i.val
    = ∑ j : Fin k, g (n + j.val) := by
  -- The filtered set equals the image of Fin k under the shift map
  have h_eq : ((univ : Finset (Fin (n + k))).filter (fun i => n ≤ i.val))
            = Finset.image (fun (j : Fin k) => (⟨n + j.val, by omega⟩ : Fin (n + k))) univ := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hi
      use ⟨i.val - n, by omega⟩
      ext
      simp
      omega
    · rintro ⟨j, _, rfl⟩
      simp
  rw [h_eq, Finset.sum_image]
  · intro a b _ _ hab
    simp only [Fin.mk.injEq] at hab
    exact Fin.ext (by omega)

end FinIndexHelpers
end Exchangeability.DeFinetti.L2Helpers

/-!
## L² Contractability Bound

This section contains Kallenberg's L² contractability bound (Lemma 1.2), which provides
an elementary proof of de Finetti's theorem using L² estimates without requiring
the full Mean Ergodic Theorem machinery.

For detailed mathematical background, see the module docstring in the original L2Approach.lean.
-/

namespace Exchangeability.DeFinetti.L2Approach

open MeasureTheory BigOperators

variable {α : Type*} [MeasurableSpace α]
variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Step 1:** Centering reduction - when coefficients sum to zero, we can replace
variables with centered variables in weighted sums. -/
lemma integral_sq_weighted_sum_eq_centered {μ : Measure Ω}
    {n : ℕ} (ξ : Fin n → Ω → ℝ) (c : Fin n → ℝ) (m : ℝ)
    (hc_sum : ∑ i, c i = 0) :
    ∫ ω, (∑ i, c i * ξ i ω)^2 ∂μ = ∫ ω, (∑ i, c i * (ξ i ω - m))^2 ∂μ := by
  congr 1; ext ω; congr 1
  conv_lhs => arg 2; ext i; rw [show ξ i ω = (ξ i ω - m) + m by ring]
  simp only [mul_add, Finset.sum_add_distrib, add_eq_left, ← Finset.sum_mul, hc_sum]
  ring

/-- **Step 2:** Expand L² norm as bilinear form - converts integral of square to
double sum of covariances. -/
lemma integral_sq_weighted_sum_eq_double_sum {μ : Measure Ω}
    {n : ℕ} (η : Fin n → Ω → ℝ) (c : Fin n → ℝ)
    (h_integrable : ∀ i j, Integrable (fun ω => η i ω * η j ω) μ) :
    ∫ ω, (∑ i, c i * η i ω)^2 ∂μ =
    ∑ i, ∑ j, c i * c j * ∫ ω, η i ω * η j ω ∂μ := by
  calc ∫ ω, (∑ i, c i * η i ω)^2 ∂μ
      = ∫ ω, ∑ i, ∑ j, (c i * c j) * (η i ω * η j ω) ∂μ := by
          congr 1; ext ω
          rw [sq, Finset.sum_mul_sum]
          apply Finset.sum_congr rfl
          intro i _; apply Finset.sum_congr rfl
          intro j _; ring
    _ = ∑ i, ∑ j, ∫ ω, (c i * c j) * (η i ω * η j ω) ∂μ := by
          rw [integral_finset_sum _ (fun i _ => ?_)]
          congr 1; ext i
          rw [integral_finset_sum _ (fun j _ => ?_)]
          · exact (h_integrable i j).const_mul (c i * c j)
          · exact integrable_finset_sum _ (fun j _ => (h_integrable i j).const_mul _)
    _ = ∑ i, ∑ j, c i * c j * ∫ ω, η i ω * η j ω ∂μ := by
          congr 1; ext i; congr 1; ext j
          rw [integral_const_mul]

/-- **Step 3:** Separate diagonal from off-diagonal terms in covariance expansion. -/
lemma double_sum_covariance_formula {n : ℕ} {c : Fin n → ℝ} (σSq ρ : ℝ)
    (cov_diag : ℝ) (cov_offdiag : ℝ)
    (h_diag : cov_diag = σSq)
    (h_offdiag : cov_offdiag = σSq * ρ) :
    ∑ i, ∑ j, c i * c j * (if i = j then cov_diag else cov_offdiag) =
    σSq * ρ * (∑ i, c i)^2 + σSq * (1 - ρ) * ∑ i, (c i)^2 := by
  -- Split into diagonal and off-diagonal
  have h_diag_sum : ∑ i, c i * c i * cov_diag = σSq * ∑ i, (c i)^2 := by
    simp [h_diag, ← Finset.sum_mul, pow_two]; ring
  have h_offdiag_sum : ∑ i, ∑ j with j ≠ i, c i * c j * cov_offdiag =
      σSq * ρ * ∑ i, ∑ j with j ≠ i, c i * c j := by
    simp [h_offdiag, Finset.mul_sum, mul_assoc, mul_comm]
  have h_offdiag_expand :
      ∑ i, ∑ j with j ≠ i, c i * c j = (∑ i, c i)^2 - ∑ i, (c i)^2 := by
    classical
    have h_sq : (∑ i, c i)^2 = ∑ i, ∑ j, c i * c j := by
      rw [pow_two, Finset.sum_mul_sum (s := (Finset.univ : Finset (Fin n)))
        (t := (Finset.univ : Finset (Fin n))) (f := fun i => c i) (g := fun j => c j)]
    have h_inner_split : ∀ i, ∑ j, c i * c j = c i * c i + ∑ j with j ≠ i, c i * c j := by
      intro i; classical
      conv_lhs => rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => j = i)]
      congr 1
      have : Finset.filter (fun j => j = i) Finset.univ = {i} := by ext j; simp [eq_comm]
      simp [this]
    have h_split :
        ∑ i, ∑ j, c i * c j = ∑ i, c i * c i + ∑ i, ∑ j with j ≠ i, c i * c j := by
      simp_rw [h_inner_split]; simp [Finset.sum_add_distrib]
    calc ∑ i, ∑ j with j ≠ i, c i * c j
        = ∑ i, ∑ j, c i * c j - ∑ i, c i * c i := by linarith [h_split]
      _ = (∑ i, c i)^2 - ∑ i, (c i)^2 := by simp [h_sq, pow_two]
  -- Now split the original double sum
  classical
  have h_inner_split : ∀ i, ∑ j, c i * c j * (if i = j then cov_diag else cov_offdiag) =
      c i * c i * cov_diag + ∑ j with j ≠ i, c i * c j * cov_offdiag := by
    intro i; classical
    conv_lhs => rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => j = i)]
    congr 1
    · have : Finset.filter (fun j => j = i) Finset.univ = {i} := by ext j; simp [eq_comm]
      simp [this]
    · apply Finset.sum_congr rfl; intro j hj
      simp [Ne.symm (Finset.mem_filter.mp hj).2]
  have h_split : ∑ i, ∑ j, c i * c j * (if i = j then cov_diag else cov_offdiag) =
      ∑ i, c i * c i * cov_diag + ∑ i, ∑ j with j ≠ i, c i * c j * cov_offdiag := by
    simp_rw [h_inner_split]; simp [Finset.sum_add_distrib]
  calc ∑ i, ∑ j, c i * c j * (if i = j then cov_diag else cov_offdiag)
      = ∑ i, c i * c i * cov_diag + ∑ i, ∑ j with j ≠ i, c i * c j * cov_offdiag := h_split
    _ = σSq * ∑ i, (c i)^2 + σSq * ρ * ((∑ i, c i)^2 - ∑ i, (c i)^2) := by
          rw [h_diag_sum, h_offdiag_sum, h_offdiag_expand]
    _ = σSq * ρ * (∑ i, c i)^2 + σSq * (1 - ρ) * ∑ i, (c i)^2 := by ring

/-- **Step 4:** When coefficients sum to zero, the correlation term vanishes. -/
lemma covariance_formula_zero_sum {n : ℕ} {c : Fin n → ℝ} (σSq ρ : ℝ)
    (hc_sum : ∑ i, c i = 0) :
    σSq * ρ * (∑ i, c i)^2 + σSq * (1 - ρ) * ∑ i, (c i)^2 =
    σSq * (1 - ρ) * ∑ i, (c i)^2 := by
  rw [hc_sum]; simp [zero_pow (Nat.succ_ne_zero 1)]

/-- **Step 5:** Sum of squares bounded by L¹ norm times supremum. -/
lemma sum_sq_le_sum_abs_mul_sup {n : ℕ} {c : Fin n → ℝ} :
    ∑ i, (c i)^2 ≤ ∑ i, |c i| * (⨆ j, |c j|) := by
  have hbdd : BddAbove (Set.range fun j : Fin n => |c j|) := ⟨∑ k, |c k|, by
    intro y ⟨k, hk⟩; rw [← hk]
    exact Finset.single_le_sum (fun i _ => abs_nonneg (c i)) (Finset.mem_univ k)⟩
  apply Finset.sum_le_sum; intro i _
  calc (c i)^2 = |c i|^2 := (sq_abs _).symm
     _ = |c i| * |c i| := sq _
     _ ≤ |c i| * (⨆ j, |c j|) := mul_le_mul_of_nonneg_left (le_ciSup hbdd i) (abs_nonneg _)

/-- **Step 6:** Combine all steps into final bound. Takes the chain of equalities and
inequalities from the previous steps and produces the final L² contractability bound. -/
lemma l2_bound_from_steps {n : ℕ} {c p q : Fin n → ℝ} (σSq ρ : ℝ)
    (hσSq_nonneg : 0 ≤ σSq) (hρ_bd : ρ ≤ 1)
    (hc_def : c = fun i => p i - q i)
    (hc_abs_sum : ∑ i, |c i| ≤ 2)
    (step5 : ∑ i, (c i)^2 ≤ ∑ i, |c i| * (⨆ j, |c j|)) :
    σSq * (1 - ρ) * ∑ i, (c i)^2 ≤ 2 * σSq * (1 - ρ) * (⨆ i, |p i - q i|) := by
  have hbdd : BddAbove (Set.range fun j : Fin n => |c j|) := ⟨∑ k, |c k|, by
    intro y ⟨k, hk⟩; rw [← hk]
    exact Finset.single_le_sum (fun i _ => abs_nonneg (c i)) (Finset.mem_univ k)⟩
  have hσ_1ρ_nonneg : 0 ≤ σSq * (1 - ρ) := mul_nonneg hσSq_nonneg (by linarith)
  have hsup_nonneg : 0 ≤ ⨆ j, |c j| := by
    by_cases h : Nonempty (Fin n)
    · obtain ⟨j0⟩ := h
      calc (0 : ℝ) ≤ |c j0| := abs_nonneg _
        _ ≤ ⨆ j, |c j| := le_ciSup hbdd j0
    · haveI : IsEmpty (Fin n) := not_nonempty_iff.mp h
      have : (Set.range fun j : Fin n => |c j|) = ∅ := by
        ext x; simp only [Set.mem_range, Set.mem_empty_iff_false, iff_false]
        rintro ⟨j, _⟩; exact IsEmpty.false j
      rw [iSup, this, Real.sSup_empty]
  calc σSq * (1 - ρ) * ∑ i, (c i)^2
      ≤ σSq * (1 - ρ) * (∑ i, |c i| * (⨆ j, |c j|)) :=
          mul_le_mul_of_nonneg_left step5 hσ_1ρ_nonneg
    _ = σSq * (1 - ρ) * ((∑ i, |c i|) * (⨆ j, |c j|)) := by rw [Finset.sum_mul]
    _ ≤ σSq * (1 - ρ) * (2 * (⨆ j, |c j|)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hc_abs_sum hsup_nonneg) hσ_1ρ_nonneg
    _ = 2 * σSq * (1 - ρ) * (⨆ j, |c j|) := by ring
    _ = 2 * σSq * (1 - ρ) * (⨆ i, |p i - q i|) := by simp [hc_def]

/--
**Kallenberg's Lemma 1.2:** L² contractability bound for weighted averages of
exchangeable sequences.

**Statement:** Given `ξ₁, ..., ξₙ ∈ L²` with:
- Common mean: `E[ξⱼ] = m` for all `j`
- Common variance: `Var(ξⱼ) = σ²` for all `j`
- **Constant correlation:** `Cov(ξᵢ, ξⱼ) = σ²ρ` for all `i ≠ j`

Then for any probability distributions `p = (p₁, ..., pₙ)` and `q = (q₁, ..., qₙ)`:

  `E[(∑ᵢ pᵢξᵢ - ∑ᵢ qᵢξᵢ)²] ≤ 2σ²(1-ρ) sup_j |pⱼ - qⱼ|`

**Mathematical significance:** This is the key lemma for Kallenberg's "elementary"
proof of de Finetti's theorem. It shows that weighted averages with similar weights
give similar results in L², with an **explicit quantitative bound**.

**Intuition:** For exchangeable sequences:
1. The correlation `ρ` measures how "exchangeable" the sequence is
2. When `ρ ≈ 1`, all the `ξᵢ` are highly correlated (nearly equal)
3. The bound `2σ²(1-ρ)` goes to 0 as `ρ → 1`
4. This forces all weighted averages to converge to the same limit

**Why constant correlation?** Exchangeable sequences have a special covariance
structure: all pairs `(ξᵢ, ξⱼ)` with `i ≠ j` have the same correlation. This
follows from the symmetry - if we swap indices, the distribution doesn't change,
so the covariance must be the same for all off-diagonal pairs.

**Connection to de Finetti:** For an infinite exchangeable sequence, the finite
sub-sequences have correlations `ρₙ → 1` as `n → ∞` (they become "more exchangeable").
Applying this lemma shows:
- Empirical averages `n⁻¹ ∑ᵢ ξᵢ` form a Cauchy sequence in L²
- They converge to a limit `ξ̄` (the tail σ-algebra)
- The limit is independent of the weights chosen
- This yields de Finetti's representation

**Proof strategy:**
1. **Centering:** Define `cⱼ = pⱼ - qⱼ`, noting that `∑ cⱼ = 0` (both are probability
   distributions). Use this to replace `ξⱼ` with `ξⱼ - m` (centered variables).

2. **Expand the square:** Use linearity of expectation to expand:
   ```
   E[(∑ cᵢ(ξᵢ-m))²] = ∑ᵢⱼ cᵢcⱼ E[(ξᵢ-m)(ξⱼ-m)]
                    = ∑ᵢⱼ cᵢcⱼ Cov(ξᵢ,ξⱼ)
   ```

3. **Separate diagonal from off-diagonal:**
   ```
   = ∑ᵢ cᵢ² σ² + ∑ᵢ≠ⱼ cᵢcⱼ σ²ρ
     (using Var(ξᵢ) = σ², Cov(ξᵢ,ξⱼ) = σ²ρ)
   = σ²∑cᵢ² + σ²ρ(∑ᵢcᵢ)² - σ²ρ∑cᵢ²
     (since ∑ᵢ≠ⱼ cᵢcⱼ = (∑cᵢ)² - ∑cᵢ²)
   = σ²(1-ρ)∑cᵢ²  (using ∑cᵢ = 0)
   ```

4. **Bound the sum of squares:**
   ```
   ∑cᵢ² ≤ (sup|cᵢ|) · (∑|cᵢ|) ≤ (sup|cᵢ|) · 2
   ```
   The final inequality uses `∑|cᵢ| ≤ 2` (the L¹ distance between two probability
   distributions is at most 2).

5. **Combine:** Putting it together gives the desired bound.

**Historical note:** This is Kallenberg's "second proof" of de Finetti's theorem
(Chapter 1, Lemma 1.2). It's more elementary than the ergodic approach but requires
finite variance. The elegance is that it reduces a sophisticated theorem to a
straightforward L² calculation.

**Comparison with ergodic approach:** The Mean Ergodic Theorem gives the same
convergence result via abstract functional analysis (orthogonal projections in
Hilbert space). This lemma gives an explicit bound and a direct proof, at the
cost of requiring finite variance.
-/
-- For probability distributions p and q, the L¹ distance is at most 2
private lemma prob_dist_diff_abs_sum_le_two {n : ℕ}
    (p q : Fin n → ℝ)
    (hp_prob : (∑ i, p i) = 1 ∧ ∀ i, 0 ≤ p i)
    (hq_prob : (∑ i, q i) = 1 ∧ ∀ i, 0 ≤ q i) :
    ∑ j, |p j - q j| ≤ 2 := by
  classical
  let c : Fin n → ℝ := fun i => p i - q i
  have hc_sum : ∑ j, c j = 0 := by
    simp only [c, Finset.sum_sub_distrib, hp_prob.1, hq_prob.1]; ring

  let Pos := Finset.univ.filter fun j : Fin n => 0 ≤ c j
  let Neg := Finset.univ.filter fun j : Fin n => c j < 0

  have hsplit_c : ∑ j ∈ Pos, c j + ∑ j ∈ Neg, c j = 0 := by
    have h := Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
      (p := fun j : Fin n => 0 ≤ c j) (f := fun j => c j)
    have hsum_univ : ∑ j ∈ (Finset.univ : Finset (Fin n)), c j = 0 := by simpa using hc_sum
    simpa [Pos, Neg, hsum_univ] using h

  have hbalance : ∑ j ∈ Pos, c j = -∑ j ∈ Neg, c j :=
    eq_neg_of_add_eq_zero_left hsplit_c

  have hsplit_abs : ∑ j, |c j| = ∑ j ∈ Pos, |c j| + ∑ j ∈ Neg, |c j| := by
    have h := Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
      (p := fun j : Fin n => 0 ≤ c j) (f := fun j => |c j|)
    simpa [Pos, Neg] using h.symm

  have habs_pos : ∑ j ∈ Pos, |c j| = ∑ j ∈ Pos, c j :=
    Finset.sum_congr rfl (fun j hj => abs_of_nonneg (Finset.mem_filter.mp hj).2)

  have habs_neg : ∑ j ∈ Neg, |c j| = -∑ j ∈ Neg, c j :=
    calc ∑ j ∈ Neg, |c j|
        = ∑ j ∈ Neg, (-c j) := Finset.sum_congr rfl
            (fun j hj => abs_of_neg (Finset.mem_filter.mp hj).2)
      _ = -∑ j ∈ Neg, c j := by simp [Finset.sum_neg_distrib]

  have hdouble : ∑ j, |c j| = 2 * ∑ j ∈ Pos, c j :=
    calc ∑ j, |c j|
        = ∑ j ∈ Pos, |c j| + ∑ j ∈ Neg, |c j| := hsplit_abs
      _ = ∑ j ∈ Pos, c j + (-∑ j ∈ Neg, c j) := by simp [habs_pos, habs_neg]
      _ = ∑ j ∈ Pos, c j + ∑ j ∈ Pos, c j := by simp [hbalance]
      _ = 2 * ∑ j ∈ Pos, c j := by ring

  have hle_one : ∑ j ∈ Pos, p j ≤ 1 :=
    calc ∑ j ∈ Pos, p j ≤ ∑ j, p j :=
          Finset.sum_le_sum_of_subset_of_nonneg (fun j _ => Finset.mem_univ j)
            (fun j _ _ => hp_prob.2 j)
      _ = 1 := hp_prob.1

  calc ∑ j, |c j|
      = 2 * ∑ j ∈ Pos, c j := hdouble
    _ ≤ 2 * ∑ j ∈ Pos, p j := mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun j _ => sub_le_self _ (hq_prob.2 j)) (by norm_num)
    _ ≤ 2 * 1 := mul_le_mul_of_nonneg_left hle_one (by norm_num)
    _ = 2 := by norm_num

theorem l2_contractability_bound
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} (ξ : Fin n → Ω → ℝ)
    (m : ℝ) (σ ρ : ℝ)
    (_hρ_bd : -1 ≤ ρ ∧ ρ ≤ 1)
    (_hmean : ∀ k, ∫ ω, ξ k ω ∂μ = m)
    (_hL2 : ∀ k, MemLp (fun ω => ξ k ω - m) 2 μ)
    (_hvar : ∀ k, ∫ ω, (ξ k ω - m)^2 ∂μ = σ ^ 2)
    (_hcov : ∀ i j, i ≠ j → ∫ ω, (ξ i ω - m) * (ξ j ω - m) ∂μ = σ ^ 2 * ρ)
    (p q : Fin n → ℝ)
    (_hp_prob : (∑ i, p i) = 1 ∧ ∀ i, 0 ≤ p i)
    (_hq_prob : (∑ i, q i) = 1 ∧ ∀ i, 0 ≤ q i) :
    ∫ ω, (∑ i, p i * ξ i ω - ∑ i, q i * ξ i ω)^2 ∂μ ≤
      2 * σ ^ 2 * (1 - ρ) * (⨆ i, |p i - q i|) := by
  -- Proof following Kallenberg page 26, Lemma 1.2 exactly
  classical
  let c : Fin n → ℝ := fun i => p i - q i
  set σSq : ℝ := σ ^ 2

  -- Preliminary facts about c = p - q
  have hc_sum : ∑ j, c j = 0 := by
    simp only [c, Finset.sum_sub_distrib, _hp_prob.1, _hq_prob.1]; ring
  have hc_abs_sum : ∑ j, |c j| ≤ 2 :=
    prob_dist_diff_abs_sum_le_two p q _hp_prob _hq_prob

  -- Step 1: E(∑cᵢξᵢ)² = E(∑cᵢ(ξᵢ-m))² using ∑cⱼ = 0
  have step1 : ∫ ω, (∑ i, c i * ξ i ω)^2 ∂μ =
               ∫ ω, (∑ i, c i * (ξ i ω - m))^2 ∂μ :=
    integral_sq_weighted_sum_eq_centered ξ c m hc_sum

  -- Step 2: = ∑ᵢⱼ cᵢcⱼ cov(ξᵢ, ξⱼ) by expanding square and linearity
  have h_integrable :
      ∀ i j, Integrable (fun ω => (ξ i ω - m) * (ξ j ω - m)) μ := fun i j => by
    classical
    have h_mul : MemLp (fun ω => (ξ i ω - m) * (ξ j ω - m)) 1 μ :=
      (MemLp.mul' (hf := _hL2 j) (hφ := _hL2 i) : _)
    simpa [memLp_one_iff_integrable] using h_mul
  have step2 : ∫ ω, (∑ i, c i * (ξ i ω - m))^2 ∂μ =
               ∑ i, ∑ j, c i * c j * ∫ ω, (ξ i ω - m) * (ξ j ω - m) ∂μ :=
    integral_sq_weighted_sum_eq_double_sum (fun i => fun ω => ξ i ω - m) c h_integrable

  -- Step 3: = σ²ρ(∑cᵢ)² + σ²(1-ρ)∑cᵢ² by separating i=j from i≠j
  have step3 : ∑ i, ∑ j, c i * c j * ∫ ω, (ξ i ω - m) * (ξ j ω - m) ∂μ =
               σSq * ρ * (∑ i, c i)^2 + σSq * (1 - ρ) * ∑ i, (c i)^2 := by
    have hvar : ∀ k, ∫ ω, (ξ k ω - m)^2 ∂μ = σSq := fun k => _hvar k
    have hcov :
        ∀ i j, i ≠ j → ∫ ω, (ξ i ω - m) * (ξ j ω - m) ∂μ = σSq * ρ :=
      fun i j hij => _hcov i j hij
    trans (∑ i, ∑ j, c i * c j * (if i = j then σSq else σSq * ρ))
    · congr 1; ext i; congr 1; ext j
      split_ifs with h
      · subst h
        have h_sq :
            (fun ω => (ξ i ω - m) * (ξ i ω - m)) = (fun ω => (ξ i ω - m)^2) := by
          funext ω; ring
        rw [h_sq]; exact congr_arg (c i * c i * ·) (hvar i)
      · exact congr_arg (c i * c j * ·) (hcov i j h)
    · exact double_sum_covariance_formula σSq ρ σSq (σSq * ρ) rfl rfl

  -- Step 4: = σ²(1-ρ)∑cᵢ² since (∑cᵢ)² = 0
  have step4 : σSq * ρ * (∑ i, c i)^2 + σSq * (1 - ρ) * ∑ i, (c i)^2 =
               σSq * (1 - ρ) * ∑ i, (c i)^2 :=
    covariance_formula_zero_sum σSq ρ hc_sum

  -- Steps 5-6: Combine inequalities to get final bound
  have step5 : ∑ i, (c i)^2 ≤ ∑ i, |c i| * (⨆ j, |c j|) :=
    sum_sq_le_sum_abs_mul_sup

  calc ∫ ω, (∑ i, p i * ξ i ω - ∑ i, q i * ξ i ω)^2 ∂μ
      = ∫ ω, (∑ i, c i * ξ i ω)^2 ∂μ := by
          congr 1; ext ω; congr 1
          conv_lhs => rw [← Finset.sum_sub_distrib]
          simp only [c]; congr 1; ext i; ring
    _ = ∫ ω, (∑ i, c i * (ξ i ω - m))^2 ∂μ := step1
    _ = ∑ i, ∑ j, c i * c j * ∫ ω, (ξ i ω - m) * (ξ j ω - m) ∂μ := step2
    _ = σSq * ρ * (∑ i, c i)^2 + σSq * (1 - ρ) * ∑ i, (c i)^2 := step3
    _ = σSq * (1 - ρ) * ∑ i, (c i)^2 := step4
    _ ≤ 2 * σSq * (1 - ρ) * (⨆ i, |p i - q i|) :=
          l2_bound_from_steps σSq ρ (sq_nonneg σ) _hρ_bd.2 rfl hc_abs_sum step5
    _ = 2 * σ ^ 2 * (1 - ρ) * (⨆ i, |p i - q i|) := by
          simp [σSq, pow_two, mul_comm, mul_left_comm, mul_assoc]

end Exchangeability.DeFinetti.L2Approach
