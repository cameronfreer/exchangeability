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
* `weighted_sums_converge_L1`: L² bound implies L¹ convergence
* `reverse_martingale_limit`: Tail-measurable limit via reverse martingale

Auxiliary results (in separate file):
* `CovarianceStructure.contractable_covariance_structure`: Uniform covariance structure

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

/-- **Strict monotonicity for two-point subsequence selection.**

For `i < j`, the function mapping `0 ↦ i, 1 ↦ j` is strictly monotone on Fin 2. -/
private lemma strictMono_two {i j : ℕ} (hij : i < j) :
    StrictMono fun t : Fin 2 => if t = fin2Zero then i else j := by
  classical
  intro a b hlt
  -- Reduce to: a.val = 0, b.val = 1 (only possibility in Fin 2 with a < b)
  have hval : a.val < b.val := Fin.lt_iff_val_lt_val.mp hlt
  have hb_val_le : b.val ≤ 1 := Nat.lt_succ_iff.mp (show b.val < 2 by simp [b.is_lt])
  have hb_ne_zero : b.val ≠ 0 := by intro hb; simp [hb] at hval
  have hb_val : b.val = 1 := by
    exact le_antisymm hb_val_le (Nat.succ_le_of_lt (Nat.pos_of_ne_zero hb_ne_zero))
  have ha_val : a.val = 0 := by
    exact Nat.lt_one_iff.mp (by simp only [hb_val] at hval; exact hval)
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
  have : ENNReal.toReal x < ENNReal.toReal (ENNReal.ofReal ε) := by
    exact ENNReal.toReal_strict_mono (ENNReal.ofReal_ne_top) h
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

/-- **Arithmetic bound for convergence rates: 3·√(Cf/m) < ε when m is large.**

Similar to `sqrt_div_lt_half_eps_of_nat` but with factor 3 instead of 1/2.
Used in the Cauchy argument where we sum three L² bounds via triangle inequality. -/
lemma sqrt_div_lt_third_eps_of_nat
  {Cf ε : ℝ} (hCf : 0 ≤ Cf) (hε : 0 < ε) :
  ∀ ⦃m : ℕ⦄, m ≥ Nat.ceil (9 * Cf / (ε^2)) + 1 →
    3 * Real.sqrt (Cf / m) < ε := by
  intro m hm
  have hm_real : ((Nat.ceil (9*Cf/ε^2) : ℝ) + 1) ≤ m := by exact_mod_cast hm
  have hA_lt_m : 9*Cf/ε^2 < (m : ℝ) := by
    calc 9*Cf/ε^2
        ≤ Nat.ceil (9*Cf/ε^2) := Nat.le_ceil _
      _ < (Nat.ceil (9*Cf/ε^2) : ℝ) + 1 := by linarith
      _ ≤ m := hm_real
  by_cases hCf0 : Cf = 0
  · simp [hCf0, hε]
  have hCfpos : 0 < Cf := lt_of_le_of_ne hCf (Ne.symm hCf0)
  have hmpos : 0 < (m : ℝ) := by
    calc (0 : ℝ) < 9*Cf/ε^2 := by positivity
      _ < m := hA_lt_m
  have hdenom_pos : 0 < 9*Cf/ε^2 := by positivity
  have hdiv : Cf / (m : ℝ) < Cf / (9*Cf/ε^2) := by
    exact div_lt_div_of_pos_left hCfpos hdenom_pos hA_lt_m
  have heq : Cf / (9*Cf/ε^2) = ε^2 / 9 := by
    field_simp [ne_of_gt hCfpos]
  have hlt : Cf / (m : ℝ) < ε^2 / 9 := by
    calc Cf / (m : ℝ)
        < Cf / (9*Cf/ε^2) := hdiv
      _ = ε^2 / 9 := heq
  have hnonneg : 0 ≤ Cf / (m : ℝ) := div_nonneg hCf (Nat.cast_nonneg m)
  have hsqrt : Real.sqrt (Cf / m) < Real.sqrt (ε^2 / 9) := by
    exact Real.sqrt_lt_sqrt hnonneg hlt
  have h_sqrt_simpl : Real.sqrt (ε^2 / 9) = ε / 3 := by
    rw [Real.sqrt_div (sq_nonneg ε), Real.sqrt_sq (le_of_lt hε)]
    rw [show (9 : ℝ) = 3^2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 3)]
  calc 3 * Real.sqrt (Cf / m)
      < 3 * Real.sqrt (ε^2 / 9) := by linarith [hsqrt]
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
    refine measurable_pi_lambda _ ?_
    intro j; simpa [κ] using hX_meas (κ j)
  have h_meas_std : Measurable fun ω => fun j : Fin 1 => X j.val ω := by
    refine measurable_pi_lambda _ ?_
    intro j; simpa using hX_meas j.val
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

/-!
## Step 2: L² bound implies L¹ convergence of weighted sums (Kallenberg's key step)
-/

/-- **Finite window of consecutive indices.**

The window `{n+1, n+2, ..., n+k}` represented as a `Finset ℕ`.
Used to express Cesàro averages: `(1/k) * ∑_{i ∈ window n k} f(X_i)`. -/
def window (n k : ℕ) : Finset ℕ :=
  (Finset.range k).image fun i => n + i + 1

/-- The window contains exactly k elements. -/
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

/-- Characterization of window membership. -/
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

/-- **Supremum of weight differences for two non-overlapping windows.**

For two weight vectors representing uniform averages over disjoint windows of size k,
the supremum of their pointwise differences is exactly 1/k. This is the key parameter
in the L² contractability bound.

Uses `ciSup_const` since ℝ is only a `ConditionallyCompleteLattice`. -/
private lemma sup_two_window_weights {k : ℕ} (hk : 0 < k)
    (p q : Fin (2 * k) → ℝ)
    (hp : p = fun i => if i.val < k then 1 / (k : ℝ) else 0)
    (hq : q = fun i => if i.val < k then 0 else 1 / (k : ℝ)) :
    ⨆ i, |p i - q i| = 1 / (k : ℝ) := by
  have h_eq : ∀ i : Fin (2 * k), |p i - q i| = 1 / (k : ℝ) := by
    intro i
    rw [hp, hq]
    simp only
    split_ifs <;> simp [abs_neg]
  haveI : Nonempty (Fin (2 * k)) := ⟨⟨0, Nat.mul_pos (by decide : 0 < 2) hk⟩⟩
  simp_rw [h_eq]
  exact ciSup_const

/-- Uniform version of l2_bound_two_windows: The constant Cf is the same for all
window positions. This follows because Cf = 2σ²(1-ρ) depends only on the covariance
structure of f∘X, which is uniform by contractability.

We use `l2_contractability_bound` from L2Approach directly by positing that f∘X has
a uniform covariance structure (which it must, by contractability). -/
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
  -- Strategy: Apply l2_contractability_bound from L2Approach
  -- For any window of size k starting at positions n and m, we have:
  -- - ξ_i = f(X_{n+i+1}) or f(X_{m+i+1})
  -- - By contractability, these have uniform covariance structure (m, σ², ρ)
  -- - Equal weights: p_i = q_i = 1/k (different windows)
  -- - For different starting positions, one weight vector is for indices n+1..n+k,
  --   the other for m+1..m+k

  -- The cleanest approach: use that the bound depends only on the covariance structure,
  -- which is the same for all windows by contractability

  -- We use Hölder's inequality (p=q=2 case) to bound the L² distance
  -- between window averages. The key is that the bound depends only on
  -- the covariance structure of f∘X, which is uniform by contractability.

  obtain ⟨M, hM⟩ := hf_bdd
  -- Use bound Cf = 2M² derived from Hölder's inequality
  let Cf := 2 * M^2
  refine ⟨Cf, by positivity, fun n m k hk => ?_⟩

  -- Apply Hölder's inequality to bound the squared difference
  -- Let Y_i = f(X_{n+i+1}) and Z_i = f(X_{m+i+1})
  -- We want to bound E[(1/k ∑ Y_i - 1/k ∑ Z_i)²]

  -- Step 1: Expand the square and use linearity of expectation
  have h_sq_exp : ∫ ω, ((1/(k:ℝ)) * ∑ i : Fin k, f (X (n + i.val + 1) ω) -
                        (1/(k:ℝ)) * ∑ i : Fin k, f (X (m + i.val + 1) ω))^2 ∂μ
                = ∫ ω, (1/(k:ℝ))^2 * (∑ i : Fin k, f (X (n + i.val + 1) ω) -
                                       ∑ i : Fin k, f (X (m + i.val + 1) ω))^2 ∂μ := by
    congr 1; ext ω; ring

  -- Step 2: Bound using triangle inequality and boundedness
  -- For any ω: |∑_i (f(X_{n+i}(ω)) - f(X_{m+i}(ω)))| ≤ k · 2M (triangle ineq + |f| ≤ M)
  -- So |(1/k) ∑_i ...|² ≤ (2M)², and E[...] ≤ (2M)²/k since the bound is deterministic.

  sorry  -- TODO: Complete using Finset.abs_sum_le_sum_abs, abs_sub bounds, and integral_mono

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
  obtain ⟨Cf, hCf_nonneg, hCf_unif⟩ :=
    l2_bound_two_windows_uniform X hX_contract hX_meas hX_L2 f hf_meas hf_bdd
  exact ⟨Cf, hCf_nonneg, hCf_unif n m k hk⟩

/-- Reindex the last `k`-block of a length-`m` sum.

For `m,k : ℕ` with `0 < k ≤ m`, and any real constant `c` and function `F : ℕ → ℝ`,
the sum over the last `k` positions of a length-`m` vector can be reindexed to a sum over `Fin k`:
∑_{i<m} (1_{i ≥ m-k} · c) · F(i) = c · ∑_{j<k} F(m - k + j).
-/
private lemma sum_tail_block_reindex
    {m k : ℕ} (hk_pos : 0 < k) (hkm : k ≤ m)
    (c : ℝ) (F : ℕ → ℝ) :
    ∑ i : Fin m, (if i.val < m - k then 0 else c) * F i.val
      = c * ∑ j : Fin k, F (m - k + j.val) := by
  sorry -- TODO: Implement full proof (currently blocked by Lean 4.24 syntax issue with Finset.sum in calc)

/-- Long average vs tail average bound: Comparing the average of the first m terms
with the average of the last k terms (where k ≤ m) has the same L² contractability bound.

This is the key lemma needed to complete the Cauchy argument in weighted_sums_converge_L1.
-/
private lemma l2_bound_long_vs_tail
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ)
    (f : ℝ → ℝ) (hf_meas : Measurable f)
    (hf_bdd : ∃ M, ∀ x, |f x| ≤ M)
    (Cf : ℝ) (hCf_nonneg : 0 ≤ Cf)
    (hCf_unif : ∀ (n m k : ℕ), 0 < k →
      ∫ ω, ((1/(k:ℝ)) * ∑ i : Fin k, f (X (n + i.val + 1) ω) -
            (1/(k:ℝ)) * ∑ i : Fin k, f (X (m + i.val + 1) ω))^2 ∂μ ≤ Cf / k)
    (n m k : ℕ) (hk : 0 < k) (hkm : k ≤ m) :
    ∫ ω, ((1 / (m : ℝ)) * ∑ i : Fin m, f (X (n + i.val + 1) ω) -
          (1 / (k : ℝ)) * ∑ i : Fin k, f (X (n + (m - k) + i.val + 1) ω))^2 ∂μ
      ≤ Cf / k := by
  -- Strategy: The key observation is that comparing a long average (1/m) with
  -- a tail average (1/k over last k terms) is the same as comparing two different
  -- weight vectors over the same m terms.

  -- Since Cf is already the uniform bound for equal-weight windows (from hCf_unif),
  -- and this comparison uses weights that differ by at most 1/k at each position,
  -- the bound follows from the general weight lemma.

  -- Specifically:
  -- - Long avg: sum_{i<m} (1/m) f(X_{n+i+1})
  -- - Tail avg: sum_{i<k} (1/k) f(X_{n+(m-k)+i+1}) = sum_{i in [m-k,m)} (1/k) f(X_{n+i+1})
  -- These can be written as:
  --   p_i = 1/m for all i
  --   q_i = 0 for i < m-k, and 1/k for i >= m-k
  -- So sup|p-q| = max(1/m, 1/k) = 1/k (since k ≤ m)

  -- The bound from l2_contractability_bound would be: 2σ²(1-ρ) · (1/k) = Cf/k
  -- which is exactly what we need to prove.

  -- However, we can also use the existing hCf_unif more directly:
  -- Note that the tail average is just an equal-weight window starting at n+(m-k),
  -- so we can bound the difference using a triangle inequality approach.

  -- For now, leave as sorry until contractable_covariance_structure is complete
  sorry

/-- **Weighted sums converge in L¹ for contractable sequences.**

For a contractable sequence X and bounded measurable f, the Cesàro averages
`(1/m) * ∑_{i<m} f(X_{n+i+1})` converge in L¹ to a limit α : Ω → ℝ that does not depend on n.

This is the key convergence result needed for de Finetti's theorem via the L² approach.
The proof uses L² contractability bounds to show the averages form a Cauchy sequence in L¹. -/
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
                    ≤ ∑ k : Fin m, |f (X (n + k.val + 1) ω)| :=
                Finset.abs_sum_le_sum_abs
                  (fun k : Fin m => f (X (n + k.val + 1) ω))
                  Finset.univ
              have h_inv_abs : |1 / (m : ℝ)| = 1 / (m : ℝ) :=
                abs_of_pos h_inv_pos
              calc
                |(1 / (m : ℝ)) * ∑ k : Fin m, f (X (n + k.val + 1) ω)|
                    = (1 / (m : ℝ)) *
                        |∑ k : Fin m, f (X (n + k.val + 1) ω)| := by
                      simp [abs_mul]
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
            · have : (1 / (m : ℝ)) * ∑ k : Fin m, M = M := by
                simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
                field_simp [Nat.cast_ne_zero.mpr hm]
                ring
              rw [this]
    exact MemLp.of_bound (hA_meas n m).aestronglyMeasurable M hA_ae_bdd

  -- A n m is also in L² (bounded functions on probability spaces)
  have hA_memLp_two : ∀ n m, MemLp (A n m) 2 μ := by
    intro n m
    obtain ⟨M, hM⟩ := hf_bdd
    have hA_ae_bdd : ∀ᵐ ω ∂μ, ‖A n m ω‖ ≤ M := by
      filter_upwards with ω
      simp only [A, Real.norm_eq_abs]
      -- Same bound as L¹ case
      classical
      by_cases hm : m = 0
      · simp [hm]; exact le_trans (abs_nonneg _) (hM 0)
      · calc |(1 / (m : ℝ)) * ∑ k : Fin m, f (X (n + k.val + 1) ω)|
            ≤ (1 / (m : ℝ)) * ∑ k : Fin m, |f (X (n + k.val + 1) ω)| := by
              have hm_pos : 0 < (m : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm)
              rw [abs_mul, abs_of_pos (div_pos zero_lt_one hm_pos)]
              exact mul_le_mul_of_nonneg_left
                (Finset.abs_sum_le_sum_abs _ _) (le_of_lt (div_pos zero_lt_one hm_pos))
          _ ≤ (1 / (m : ℝ)) * ∑ k : Fin m, M := by
              gcongr; exact hM _
          _ = M := by
              simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
              field_simp [Nat.cast_ne_zero.mpr hm]
              ring
    exact MemLp.of_bound (hA_meas n m).aestronglyMeasurable M hA_ae_bdd

  -- Step 1: For n=0, show (A 0 m)_m is Cauchy in L² hence L¹
  have hA_cauchy_L2_0 : ∀ ε > 0, ∃ N, ∀ m ℓ, m ≥ N → ℓ ≥ N →
      eLpNorm (fun ω => A 0 m ω - A 0 ℓ ω) 2 μ < ENNReal.ofReal ε := by
    intro ε hε
    -- Uniform two-window bound: ∫ (...)^2 ≤ Cf / k
    obtain ⟨Cf, hCf_nonneg, hCf_unif⟩ :=
      l2_bound_two_windows_uniform X hX_contract hX_meas hX_L2 f hf_meas hf_bdd
    -- Choose N so that 3 * √(Cf/N) < ε
    let N : ℕ := Nat.ceil (9 * Cf / (ε ^ 2)) + 1
    have hN_pos : 0 < N := Nat.succ_pos _
    refine ⟨N, ?_⟩
    intro m ℓ hm hℓ
    -- Common tail length k = min m ℓ
    let k := min m ℓ
    have hk_ge_N : N ≤ k := by
      have : N ≤ min m ℓ := Nat.le_min.mpr ⟨hm, hℓ⟩
      simpa [k] using this
    have hk_pos : 0 < k := lt_of_lt_of_le hN_pos hk_ge_N

    -- Three same-length comparisons (tail-averages):
    -- T1: (0 vs m-k), T2: ((m-k) vs (ℓ-k)), T3: ((ℓ-k) vs 0), all of length k.
    have h1sq :
      ∫ ω, (A 0 k ω - A (m - k) k ω)^2 ∂μ ≤ Cf / k := by
      simpa [A] using hCf_unif 0 (m - k) k hk_pos
    have h2sq :
      ∫ ω, (A (m - k) k ω - A (ℓ - k) k ω)^2 ∂μ ≤ Cf / k := by
      simpa [A] using hCf_unif (m - k) (ℓ - k) k hk_pos
    have h3sq :
      ∫ ω, (A (ℓ - k) k ω - A 0 k ω)^2 ∂μ ≤ Cf / k := by
      simpa [A] using hCf_unif (ℓ - k) 0 k hk_pos

    -- Long vs tail comparisons for h1_L2 and h3_L2
    have hkm : k ≤ m := Nat.min_le_left m ℓ
    have hkℓ : k ≤ ℓ := Nat.min_le_right m ℓ

    have h1sq_long :
      ∫ ω, (A 0 m ω - A (m - k) k ω)^2 ∂μ ≤ Cf / k := by
      simpa [A] using l2_bound_long_vs_tail X hX_contract hX_meas hX_L2 f hf_meas hf_bdd
        Cf hCf_nonneg hCf_unif 0 m k hk_pos hkm

    have h3sq_long :
      ∫ ω, (A (ℓ - k) k ω - A 0 ℓ ω)^2 ∂μ ≤ Cf / k := by
      have : ∫ ω, (A (ℓ - k) k ω - A 0 ℓ ω)^2 ∂μ
           = ∫ ω, (A 0 ℓ ω - A (ℓ - k) k ω)^2 ∂μ := by
        congr 1; ext ω; ring_nf
      rw [this]
      simpa [A] using l2_bound_long_vs_tail X hX_contract hX_meas hX_L2 f hf_meas hf_bdd
        Cf hCf_nonneg hCf_unif 0 ℓ k hk_pos hkℓ

    -- Convert each integral bound to an L² eLpNorm bound
    -- For now, use the uniform bound - we need bounds that match the triangle inequality terms
    -- Term 1: eLpNorm (A 0 m - A (m-k) k)
    -- This compares a long average with its tail - uses l2_bound_long_vs_tail
    have h1_L2 :
      eLpNorm (fun ω => A 0 m ω - A (m - k) k ω) 2 μ
        ≤ ENNReal.ofReal (Real.sqrt (Cf / k)) := by
      apply eLpNorm_two_from_integral_sq_le
      · exact (hA_memLp_two 0 m).sub (hA_memLp_two (m - k) k)
      · exact div_nonneg hCf_nonneg (Nat.cast_nonneg k)
      · exact h1sq_long
    have h2_L2 :
      eLpNorm (fun ω => A (m - k) k ω - A (ℓ - k) k ω) 2 μ
        ≤ ENNReal.ofReal (Real.sqrt (Cf / k)) := by
      apply eLpNorm_two_from_integral_sq_le
      · exact (hA_memLp_two (m - k) k).sub (hA_memLp_two (ℓ - k) k)
      · exact div_nonneg hCf_nonneg (Nat.cast_nonneg k)
      · exact h2sq
    have h3_L2 :
      eLpNorm (fun ω => A (ℓ - k) k ω - A 0 ℓ ω) 2 μ
        ≤ ENNReal.ofReal (Real.sqrt (Cf / k)) := by
      apply eLpNorm_two_from_integral_sq_le
      · exact (hA_memLp_two (ℓ - k) k).sub (hA_memLp_two 0 ℓ)
      · exact div_nonneg hCf_nonneg (Nat.cast_nonneg k)
      · exact h3sq_long

    -- Triangle inequality on three segments:
    -- (A 0 m - A 0 ℓ) = (A 0 m - A (m - k) k) + (A (m - k) k - A (ℓ - k) k) + (A (ℓ - k) k - A 0 ℓ)
    have tri :
      eLpNorm (fun ω => A 0 m ω - A 0 ℓ ω) 2 μ
        ≤ eLpNorm (fun ω => A 0 m ω - A (m - k) k ω) 2 μ
          + eLpNorm (fun ω => A (m - k) k ω - A (ℓ - k) k ω) 2 μ
          + eLpNorm (fun ω => A (ℓ - k) k ω - A 0 ℓ ω) 2 μ := by
      -- split into T1 + (T2 + T3), then split T2 + T3
      have hsplit :
        (fun ω => A 0 m ω - A 0 ℓ ω)
          = (fun ω =>
                (A 0 m ω - A (m - k) k ω)
                + ((A (m - k) k ω - A (ℓ - k) k ω)
                  + (A (ℓ - k) k ω - A 0 ℓ ω))) := by
        ext ω; ring
      have step1 :
        eLpNorm
          (fun ω =>
            (A 0 m ω - A (m - k) k ω)
            + ((A (m - k) k ω - A (ℓ - k) k ω)
              + (A (ℓ - k) k ω - A 0 ℓ ω))) 2 μ
        ≤ eLpNorm (fun ω => A 0 m ω - A (m - k) k ω) 2 μ
            + eLpNorm (fun ω =>
                (A (m - k) k ω - A (ℓ - k) k ω)
                + (A (ℓ - k) k ω - A 0 ℓ ω)) 2 μ := by
        apply eLpNorm_add_le
        · exact ((hA_meas 0 m).sub (hA_meas (m - k) k)).aestronglyMeasurable
        · exact (Measurable.add ((hA_meas (m - k) k).sub (hA_meas (ℓ - k) k))
                ((hA_meas (ℓ - k) k).sub (hA_meas 0 ℓ))).aestronglyMeasurable
        · norm_num
      have step2 :
        eLpNorm (fun ω =>
            (A (m - k) k ω - A (ℓ - k) k ω)
          + (A (ℓ - k) k ω - A 0 ℓ ω)) 2 μ
        ≤ eLpNorm (fun ω => A (m - k) k ω - A (ℓ - k) k ω) 2 μ
            + eLpNorm (fun ω => A (ℓ - k) k ω - A 0 ℓ ω) 2 μ := by
        apply eLpNorm_add_le
        · exact ((hA_meas (m - k) k).sub (hA_meas (ℓ - k) k)).aestronglyMeasurable
        · exact ((hA_meas (ℓ - k) k).sub (hA_meas 0 ℓ)).aestronglyMeasurable
        · norm_num
      -- reassociate the sums of bounds
      have : eLpNorm (fun ω => A 0 m ω - A 0 ℓ ω) 2 μ
            ≤ eLpNorm (fun ω => A 0 m ω - A (m - k) k ω) 2 μ
              + (eLpNorm (fun ω => A (m - k) k ω - A (ℓ - k) k ω) 2 μ
                + eLpNorm (fun ω => A (ℓ - k) k ω - A 0 ℓ ω) 2 μ) := by
        simpa [hsplit] using
          (le_trans step1 <| add_le_add_left step2 _)
      simpa [add_assoc] using this

    -- Bound each term by √(Cf/k), then sum to 3√(Cf/k)
    have bound3 :
      eLpNorm (fun ω => A 0 m ω - A 0 ℓ ω) 2 μ
        ≤ ENNReal.ofReal (3 * Real.sqrt (Cf / k)) := by
      have h0 : 0 ≤ Real.sqrt (Cf / k) := Real.sqrt_nonneg _
      calc
        eLpNorm (fun ω => A 0 m ω - A 0 ℓ ω) 2 μ
            ≤ eLpNorm (fun ω => A 0 m ω - A (m - k) k ω) 2 μ
              + eLpNorm (fun ω => A (m - k) k ω - A (ℓ - k) k ω) 2 μ
              + eLpNorm (fun ω => A (ℓ - k) k ω - A 0 ℓ ω) 2 μ := tri
        _ ≤ (ENNReal.ofReal (Real.sqrt (Cf / k))
              + ENNReal.ofReal (Real.sqrt (Cf / k)))
              + ENNReal.ofReal (Real.sqrt (Cf / k)) := by
              apply add_le_add
              · apply add_le_add h1_L2 h2_L2
              · exact h3_L2
        _ = ENNReal.ofReal (2 * Real.sqrt (Cf / k))
              + ENNReal.ofReal (Real.sqrt (Cf / k)) := by
              rw [← ENNReal.ofReal_add h0 h0]
              simp [two_mul]
        _ = ENNReal.ofReal (3 * Real.sqrt (Cf / k)) := by
              have h2_nonneg : 0 ≤ 2 * Real.sqrt (Cf / k) := by nlinarith
              rw [← ENNReal.ofReal_add h2_nonneg h0]
              ring_nf

    -- Choose k large ⇒ 3 √(Cf/k) < ε
    have hlt_real : 3 * Real.sqrt (Cf / k) < ε := by
      apply sqrt_div_lt_third_eps_of_nat hCf_nonneg hε
      exact hk_ge_N
    have hlt : ENNReal.ofReal (3 * Real.sqrt (Cf / k)) < ENNReal.ofReal ε :=
      (ENNReal.ofReal_lt_ofReal_iff hε).mpr hlt_real
    exact lt_of_le_of_lt bound3 hlt

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

  -- Step 2: Completeness of L¹ gives α₀ as the limit of the base averages.
  have h_exist_alpha_0 :
      ∃ alpha_0 : Ω → ℝ, Measurable alpha_0 ∧ MemLp alpha_0 1 μ ∧
        (∀ ε > 0, ∃ M, ∀ m ≥ M,
          eLpNorm (fun ω => A 0 m ω - alpha_0 ω) 1 μ < ENNReal.ofReal ε) := by
    classical
    -- View the base averages as a sequence in L¹.
    let F : ℕ → Lp ℝ 1 μ := fun m => (hA_memLp 0 m).toLp (A 0 m)
    -- Show this sequence is Cauchy.
    have hCauchy : CauchySeq F := by
      rw [Metric.cauchySeq_iff]
      intro ε hε
      obtain ⟨N, hN⟩ := hA_cauchy_L1_0 ε hε
      refine ⟨N, fun m hm ℓ hℓ => ?_⟩
      have hdist :
          dist (F m) (F ℓ) =
            ENNReal.toReal (eLpNorm (fun ω => A 0 m ω - A 0 ℓ ω) 1 μ) := by
        simpa [F] using
          dist_toLp_eq_eLpNorm_sub (hA_memLp 0 m) (hA_memLp 0 ℓ)
      have hfin :
          eLpNorm (fun ω => A 0 m ω - A 0 ℓ ω) 1 μ ≠ ⊤ :=
        (MemLp.sub (hA_memLp 0 m) (hA_memLp 0 ℓ)).eLpNorm_ne_top
      have hbound := hN m ℓ hm hℓ
      have hlt :
          ENNReal.toReal (eLpNorm (fun ω => A 0 m ω - A 0 ℓ ω) 1 μ) < ε :=
        toReal_lt_of_lt_ofReal hfin (le_of_lt hε) hbound
      simpa [hdist]
    -- Since L¹ is complete, the sequence converges to some `G`.
    rcases CompleteSpace.complete (show Cauchy (atTop.map F) from hCauchy) with ⟨G, hG⟩
    have hG' : Tendsto F atTop (𝓝 G) := hG
    -- Choose a measurable representative of `G`.
    let alpha : Ω → ℝ := (Lp.aestronglyMeasurable G).mk G
    have h_alpha_ae : G =ᵐ[μ] alpha :=
      (Lp.aestronglyMeasurable G).ae_eq_mk
    have halpha_meas : Measurable alpha :=
      (Lp.aestronglyMeasurable G).measurable_mk
    have halpha_mem : MemLp alpha 1 μ :=
      MemLp.ae_eq h_alpha_ae (Lp.memLp G)
    refine ⟨alpha, halpha_meas, halpha_mem, ?_⟩
    -- Convert convergence in L¹ to convergence of raw functions.
    intro ε hε
    obtain ⟨M, hM⟩ := Metric.tendsto_atTop.mp hG' ε hε
    refine ⟨M, fun m hm => ?_⟩
    have hdist_lt : dist (F m) G < ε := hM m hm
    have hdist :
        dist (F m) G =
          ENNReal.toReal (eLpNorm (fun ω => A 0 m ω - G ω) 1 μ) := by
      simpa [F] using
        dist_toLp_eq_eLpNorm_sub (hA_memLp 0 m) (Lp.memLp G)
    have hfin :
        eLpNorm (fun ω => A 0 m ω - G ω) 1 μ ≠ ⊤ :=
      (MemLp.sub (hA_memLp 0 m) (Lp.memLp G)).eLpNorm_ne_top
    have htoReal :
        ENNReal.toReal (eLpNorm (fun ω => A 0 m ω - G ω) 1 μ) < ε := by
      simpa [hdist] using hdist_lt
    -- Relate the difference with `alpha` via the a.e. equality.
    have h_sub :
        (fun ω => A 0 m ω - alpha ω) =ᵐ[μ]
          fun ω => A 0 m ω - G ω := by
      filter_upwards [h_alpha_ae] with ω hω
      simp [A, hω]
    have h_eq :
        eLpNorm (fun ω => A 0 m ω - alpha ω) 1 μ =
          eLpNorm (fun ω => A 0 m ω - G ω) 1 μ :=
      (eLpNorm_congr_ae h_sub).trans rfl
    -- Convert the real inequality to one in `ℝ≥0∞`.
    have h_lt :
        eLpNorm (fun ω => A 0 m ω - G ω) 1 μ
          < ENNReal.ofReal ε := by
      have h_ofReal :
          ENNReal.ofReal (ENNReal.toReal
            (eLpNorm (fun ω => A 0 m ω - G ω) 1 μ)) < ENNReal.ofReal ε :=
        ENNReal.ofReal_lt_ofReal_iff hε |>.mpr htoReal
      rw [ENNReal.ofReal_toReal hfin] at h_ofReal
      exact h_ofReal
    rw [h_eq]
    exact h_lt

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
    have hm₁ : M₁ ≤ m := le_trans (le_max_left M₁ M₂) hm
    have hm₂ : M₂ ≤ m := le_trans (le_max_right M₁ M₂) hm

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
        have h_L2 : eLpNorm (fun ω => A n m ω - A 0 m ω) 2 μ ≤
            ENNReal.ofReal (Real.sqrt (Cf / m)) := by
          apply eLpNorm_two_from_integral_sq_le
          · exact (hA_memLp_two n m).sub (hA_memLp_two 0 m)
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
        simp at hm
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
    (_X : ℕ → Ω → ℝ) (_hX_contract : Contractable μ _X)
    (_hX_meas : ∀ i, Measurable (_X i))
    (_α : ℕ → Ω → ℝ)
    (_f : ℝ → ℝ) (_hf_meas : Measurable _f) :
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
