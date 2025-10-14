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
import Mathlib.MeasureTheory.MeasurableSpace.MeasurablyGenerated
import Mathlib.MeasureTheory.PiSystem
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
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

/-- Sum over a window of length `k` can be reindexed as a sum over `Fin k`. -/
lemma sum_window_eq_sum_fin {β : Type*} [AddCommMonoid β]
    (n k : ℕ) (g : ℕ → β) :
    ∑ t ∈ window n k, g t = ∑ i : Fin k, g (n + i.val + 1) := by
  classical
  unfold window
  -- Show the image map used to define the window is injective
  have h_inj :
      ∀ a ∈ Finset.range k, ∀ b ∈ Finset.range k,
        (n + a + 1 = n + b + 1 → a = b) := by
    intro a ha b hb h
    have h' : a + 1 = b + 1 := by
      have : n + (a + 1) = n + (b + 1) := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.succ_eq_add_one] using h
      exact Nat.add_left_cancel this
    exact Nat.succ.inj h'
  -- Convert the window sum to a range sum via the image definition
  have h_sum_range :
      ∑ t ∈ Finset.image (fun i => n + i + 1) (Finset.range k), g t
        = ∑ i ∈ Finset.range k, g (n + i + 1) :=
    Finset.sum_image <| by
      intro a ha b hb h
      exact h_inj a ha b hb h
  -- Replace the range sum with a sum over `Fin k`
  have h_range_to_fin :
      ∑ i ∈ Finset.range k, g (n + i + 1)
        = ∑ i : Fin k, g (n + i.val + 1) := by
    classical
    refine (Finset.sum_bij (fun (i : Fin k) _ => i.val)
        (fun i _ => by
          simp [Finset.mem_range, i.is_lt])
        (fun i hi j hj h => by
          exact Fin.ext h)
        (fun b hb => ?_)
        (fun i _ => rfl)).symm
    · rcases Finset.mem_range.mp hb with hb_lt
      refine ⟨⟨b, hb_lt⟩, ?_, rfl⟩
      simp
  simpa using h_sum_range.trans h_range_to_fin


/-!
### Covariance structure lemma

This auxiliary result characterizes the complete second-moment structure of contractable sequences.
It's included here for use in applying l2_contractability_bound.
-/

/-- **Uniform covariance structure for contractable L² sequences.**

A contractable sequence X in L²(μ) has uniform second-moment structure:
- All X_i have the same mean m
- All X_i have the same variance σ²
- All distinct pairs (X_i, X_j) have the same covariance σ²·ρ
- The correlation coefficient satisfies |ρ| ≤ 1

This is proved using the Cauchy-Schwarz inequality and the fact that contractability
forces all marginals of the same dimension to have identical distributions. -/
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
  -- Strategy: Use contractability to show all marginals of same size have same distribution
  -- This implies all X_i have the same mean and variance, and all pairs have same covariance

  -- Define m as the mean of X_0 (all X_i have the same distribution by contractability)
  let m := ∫ ω, X 0 ω ∂μ

  -- All X_i have the same mean by contractability (single-variable marginal)
  have hmean : ∀ k, ∫ ω, X k ω ∂μ = m := by
    intro k
    -- Use contractable_single_marginal_eq to show X_k has same distribution as X_0
    have h_eq_dist := contractable_single_marginal_eq (X := X) hX_contract hX_meas k
    -- Transfer integral via equal distributions
    have h_int_k : ∫ ω, X k ω ∂μ = ∫ x, x ∂(Measure.map (X k) μ) := by
      have h_ae : AEStronglyMeasurable (id : ℝ → ℝ) (Measure.map (X k) μ) :=
        aestronglyMeasurable_id
      exact (integral_map (hX_meas k).aemeasurable h_ae).symm
    have h_int_0 : ∫ ω, X 0 ω ∂μ = ∫ x, x ∂(Measure.map (X 0) μ) := by
      have h_ae : AEStronglyMeasurable (id : ℝ → ℝ) (Measure.map (X 0) μ) :=
        aestronglyMeasurable_id
      exact (integral_map (hX_meas 0).aemeasurable h_ae).symm
    rw [h_int_k, h_eq_dist, ← h_int_0]

  -- Define σSq as the variance of X_0
  let σSq := ∫ ω, (X 0 ω - m)^2 ∂μ

  -- All X_i have the same variance
  have hvar : ∀ k, ∫ ω, (X k ω - m)^2 ∂μ = σSq := by
    intro k
    -- Use equal distribution to transfer the variance integral
    have h_eq_dist := contractable_single_marginal_eq (X := X) hX_contract hX_meas k
    have hmean_k := hmean k
    -- The variance with k's mean equals variance with m (since they're equal)
    show ∫ ω, (X k ω - m)^2 ∂μ = σSq
    -- Transform X_k integral to X_0 integral via measure map
    have h_int_k : ∫ ω, (X k ω - m)^2 ∂μ = ∫ x, (x - m)^2 ∂(Measure.map (X k) μ) := by
      have h_ae : AEStronglyMeasurable (fun x : ℝ => (x - m)^2) (Measure.map (X k) μ) := by
        exact (continuous_id.sub continuous_const).pow 2 |>.aestronglyMeasurable
      exact (integral_map (hX_meas k).aemeasurable h_ae).symm
    have h_int_0 : ∫ ω, (X 0 ω - m)^2 ∂μ = ∫ x, (x - m)^2 ∂(Measure.map (X 0) μ) := by
      have h_ae : AEStronglyMeasurable (fun x : ℝ => (x - m)^2) (Measure.map (X 0) μ) := by
        exact (continuous_id.sub continuous_const).pow 2 |>.aestronglyMeasurable
      exact (integral_map (hX_meas 0).aemeasurable h_ae).symm
    rw [h_int_k, h_eq_dist, ← h_int_0]

  -- Define ρ from the covariance of (X_0, X_1)
  have hσSq_nonneg : 0 ≤ σSq := by
    apply integral_nonneg
    intro ω
    exact sq_nonneg _

  by_cases hσSq_pos : 0 < σSq
  · -- Case: positive variance
    let ρ := (∫ ω, (X 0 ω - m) * (X 1 ω - m) ∂μ) / σSq

    -- All pairs have the same covariance
    have hcov : ∀ i j, i ≠ j → ∫ ω, (X i ω - m) * (X j ω - m) ∂μ = σSq * ρ := by
      intro i j hij
      -- Apply contractability to get equal distributions for pairs
      by_cases h_ord : i < j
      · -- Case i < j: use contractable_map_pair directly
        have h_eq_dist := contractable_map_pair (X := X) hX_contract hX_meas h_ord
        -- Transfer the covariance integral via measure map
        have h_int_ij : ∫ ω, (X i ω - m) * (X j ω - m) ∂μ
            = ∫ p : ℝ × ℝ, (p.1 - m) * (p.2 - m) ∂(Measure.map (fun ω => (X i ω, X j ω)) μ) := by
          have h_ae : AEStronglyMeasurable (fun p : ℝ × ℝ => (p.1 - m) * (p.2 - m))
              (Measure.map (fun ω => (X i ω, X j ω)) μ) := by
            exact ((continuous_fst.sub continuous_const).mul
              (continuous_snd.sub continuous_const)).aestronglyMeasurable
          have h_comp : (fun ω => (X i ω - m) * (X j ω - m))
              = (fun p : ℝ × ℝ => (p.1 - m) * (p.2 - m)) ∘ (fun ω => (X i ω, X j ω)) := rfl
          rw [h_comp]
          exact (integral_map ((hX_meas i).prodMk (hX_meas j)).aemeasurable h_ae).symm
        have h_int_01 : ∫ ω, (X 0 ω - m) * (X 1 ω - m) ∂μ
            = ∫ p : ℝ × ℝ, (p.1 - m) * (p.2 - m) ∂(Measure.map (fun ω => (X 0 ω, X 1 ω)) μ) := by
          have h_ae : AEStronglyMeasurable (fun p : ℝ × ℝ => (p.1 - m) * (p.2 - m))
              (Measure.map (fun ω => (X 0 ω, X 1 ω)) μ) := by
            exact ((continuous_fst.sub continuous_const).mul
              (continuous_snd.sub continuous_const)).aestronglyMeasurable
          have h_comp : (fun ω => (X 0 ω - m) * (X 1 ω - m))
              = (fun p : ℝ × ℝ => (p.1 - m) * (p.2 - m)) ∘ (fun ω => (X 0 ω, X 1 ω)) := rfl
          rw [h_comp]
          exact (integral_map ((hX_meas 0).prodMk (hX_meas 1)).aemeasurable h_ae).symm
        rw [h_int_ij, h_eq_dist, ← h_int_01]
        -- Now need to show: ∫ (X 0 ω - m) * (X 1 ω - m) ∂μ = σSq * ρ
        -- This follows from the definition of ρ
        have hρ_def : ρ = (∫ ω, (X 0 ω - m) * (X 1 ω - m) ∂μ) / σSq := rfl
        rw [hρ_def]
        field_simp [ne_of_gt hσSq_pos]
      · -- Case j < i: use symmetry
        push_neg at h_ord
        have h_ji : j < i := Nat.lt_of_le_of_ne h_ord (Ne.symm hij)
        have h_eq_dist := contractable_map_pair (X := X) hX_contract hX_meas h_ji
        have h_int_ji : ∫ ω, (X j ω - m) * (X i ω - m) ∂μ
            = ∫ p : ℝ × ℝ, (p.1 - m) * (p.2 - m) ∂(Measure.map (fun ω => (X j ω, X i ω)) μ) := by
          have h_ae : AEStronglyMeasurable (fun p : ℝ × ℝ => (p.1 - m) * (p.2 - m))
              (Measure.map (fun ω => (X j ω, X i ω)) μ) := by
            exact ((continuous_fst.sub continuous_const).mul
              (continuous_snd.sub continuous_const)).aestronglyMeasurable
          have h_comp : (fun ω => (X j ω - m) * (X i ω - m))
              = (fun p : ℝ × ℝ => (p.1 - m) * (p.2 - m)) ∘ (fun ω => (X j ω, X i ω)) := rfl
          rw [h_comp]
          exact (integral_map ((hX_meas j).prodMk (hX_meas i)).aemeasurable h_ae).symm
        have h_int_01 : ∫ ω, (X 0 ω - m) * (X 1 ω - m) ∂μ
            = ∫ p : ℝ × ℝ, (p.1 - m) * (p.2 - m) ∂(Measure.map (fun ω => (X 0 ω, X 1 ω)) μ) := by
          have h_ae : AEStronglyMeasurable (fun p : ℝ × ℝ => (p.1 - m) * (p.2 - m))
              (Measure.map (fun ω => (X 0 ω, X 1 ω)) μ) := by
            exact ((continuous_fst.sub continuous_const).mul
              (continuous_snd.sub continuous_const)).aestronglyMeasurable
          have h_comp : (fun ω => (X 0 ω - m) * (X 1 ω - m))
              = (fun p : ℝ × ℝ => (p.1 - m) * (p.2 - m)) ∘ (fun ω => (X 0 ω, X 1 ω)) := rfl
          rw [h_comp]
          exact (integral_map ((hX_meas 0).prodMk (hX_meas 1)).aemeasurable h_ae).symm
        have h_symm : ∫ ω, (X i ω - m) * (X j ω - m) ∂μ = ∫ ω, (X j ω - m) * (X i ω - m) ∂μ := by
          congr 1; ext ω; ring
        rw [h_symm, h_int_ji, h_eq_dist, ← h_int_01]
        -- Now need to show: ∫ (X 0 ω - m) * (X 1 ω - m) ∂μ = σSq * ρ
        -- This follows from the definition of ρ
        have hρ_def : ρ = (∫ ω, (X 0 ω - m) * (X 1 ω - m) ∂μ) / σSq := rfl
        rw [hρ_def]
        field_simp [ne_of_gt hσSq_pos]

    -- Bound on ρ from Cauchy-Schwarz
    have hρ_bd : -1 ≤ ρ ∧ ρ ≤ 1 := by
      -- By Cauchy-Schwarz: |E[(X-m)(Y-m)]|² ≤ E[(X-m)²] · E[(Y-m)²]
      -- For X_0, X_1: |Cov|² ≤ σ² · σ² = σ⁴
      -- So |Cov| ≤ σ², and thus |ρ| = |Cov/σ²| ≤ 1

      -- The centered variables are in L²
      have hf₀ : MemLp (fun ω => X 0 ω - m) 2 μ := (hX_L2 0).sub (memLp_const m)
      have hf₁ : MemLp (fun ω => X 1 ω - m) 2 μ := (hX_L2 1).sub (memLp_const m)

      -- Their product is integrable
      have h_int : Integrable (fun ω => (X 0 ω - m) * (X 1 ω - m)) μ := hf₀.integrable_mul hf₁

      -- Apply Cauchy-Schwarz: |∫ f·g| ≤ √(∫ f²) · √(∫ g²)
      have h_cs : |∫ ω, (X 0 ω - m) * (X 1 ω - m) ∂μ|
          ≤ Real.sqrt (∫ ω, (X 0 ω - m)^2 ∂μ) * Real.sqrt (∫ ω, (X 1 ω - m)^2 ∂μ) := by
        -- Apply Hölder's inequality directly to the integrand
        have h_tri : |∫ ω, (X 0 ω - m) * (X 1 ω - m) ∂μ| ≤ ∫ ω, |(X 0 ω - m) * (X 1 ω - m)| ∂μ :=
          MeasureTheory.norm_integral_le_integral_norm (fun ω => (X 0 ω - m) * (X 1 ω - m))
        have h_abs_mul : ∫ ω, |(X 0 ω - m) * (X 1 ω - m)| ∂μ = ∫ ω, |X 0 ω - m| * |X 1 ω - m| ∂μ := by
          congr 1
          funext ω
          exact abs_mul (X 0 ω - m) (X 1 ω - m)
        have h_holder : ∫ ω, |X 0 ω - m| * |X 1 ω - m| ∂μ
            ≤ (∫ ω, |X 0 ω - m| ^ 2 ∂μ) ^ (1/2 : ℝ) * (∫ ω, |X 1 ω - m| ^ 2 ∂μ) ^ (1/2 : ℝ) := by
          have h_nonneg₀ : ∀ᵐ ω ∂μ, 0 ≤ |X 0 ω - m| := ae_of_all μ (fun ω => abs_nonneg _)
          have h_nonneg₁ : ∀ᵐ ω ∂μ, 0 ≤ |X 1 ω - m| := ae_of_all μ (fun ω => abs_nonneg _)
          have h_key : ∫ ω, |X 0 ω - m| * |X 1 ω - m| ∂μ
              ≤ (∫ ω, |X 0 ω - m| ^ (2:ℝ) ∂μ) ^ ((2:ℝ)⁻¹) * (∫ ω, |X 1 ω - m| ^ (2:ℝ) ∂μ) ^ ((2:ℝ)⁻¹) := by
            have hpq : (2:ℝ).HolderConjugate 2 := by
              constructor
              · norm_num
              · norm_num
              · norm_num
            have hf₀' : MemLp (fun ω => |X 0 ω - m|) (ENNReal.ofReal 2) μ := by
              have h2 : (ENNReal.ofReal 2 : ENNReal) = (2 : ENNReal) := by norm_num
              rw [h2]
              have : MemLp (fun ω => ‖X 0 ω - m‖) 2 μ := hf₀.norm
              have h_eq : (fun ω => ‖X 0 ω - m‖) =ᵐ[μ] (fun ω => |X 0 ω - m|) := by
                filter_upwards with ω
                exact Real.norm_eq_abs _
              exact MemLp.ae_eq h_eq this
            have hf₁' : MemLp (fun ω => |X 1 ω - m|) (ENNReal.ofReal 2) μ := by
              have h2 : (ENNReal.ofReal 2 : ENNReal) = (2 : ENNReal) := by norm_num
              rw [h2]
              have : MemLp (fun ω => ‖X 1 ω - m‖) 2 μ := hf₁.norm
              have h_eq : (fun ω => ‖X 1 ω - m‖) =ᵐ[μ] (fun ω => |X 1 ω - m|) := by
                filter_upwards with ω
                exact Real.norm_eq_abs _
              exact MemLp.ae_eq h_eq this
            have := MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg hpq h_nonneg₀ h_nonneg₁ hf₀' hf₁'
            convert this using 2 <;> norm_num
          convert h_key using 2
          · norm_num
          · norm_num
        have h_sqrt_conv : (∫ ω, |X 0 ω - m| ^ 2 ∂μ) ^ (1/2 : ℝ) * (∫ ω, |X 1 ω - m| ^ 2 ∂μ) ^ (1/2 : ℝ)
            = Real.sqrt (∫ ω, (X 0 ω - m)^2 ∂μ) * Real.sqrt (∫ ω, (X 1 ω - m)^2 ∂μ) := by
          have h4 : (∫ ω, |X 0 ω - m| ^ 2 ∂μ) ^ (1/2 : ℝ) = Real.sqrt (∫ ω, (X 0 ω - m)^2 ∂μ) := by
            rw [Real.sqrt_eq_rpow]
            congr 1
            congr 1
            funext ω
            rw [sq_abs]
          have h5 : (∫ ω, |X 1 ω - m| ^ 2 ∂μ) ^ (1/2 : ℝ) = Real.sqrt (∫ ω, (X 1 ω - m)^2 ∂μ) := by
            rw [Real.sqrt_eq_rpow]
            congr 1
            congr 1
            funext ω
            rw [sq_abs]
          rw [h4, h5]
        calc |∫ ω, (X 0 ω - m) * (X 1 ω - m) ∂μ|
            ≤ ∫ ω, |(X 0 ω - m) * (X 1 ω - m)| ∂μ := h_tri
          _ = ∫ ω, |X 0 ω - m| * |X 1 ω - m| ∂μ := h_abs_mul
          _ ≤ (∫ ω, |X 0 ω - m| ^ 2 ∂μ) ^ (1/2 : ℝ) * (∫ ω, |X 1 ω - m| ^ 2 ∂μ) ^ (1/2 : ℝ) := h_holder
          _ = Real.sqrt (∫ ω, (X 0 ω - m)^2 ∂μ) * Real.sqrt (∫ ω, (X 1 ω - m)^2 ∂μ) := h_sqrt_conv

      -- Substitute the variances
      rw [hvar 0, hvar 1] at h_cs
      have h_sqrt_sq : Real.sqrt σSq * Real.sqrt σSq = σSq := by
        have : σSq * σSq = σSq ^ 2 := (sq σSq).symm
        rw [← Real.sqrt_mul hσSq_nonneg, this, Real.sqrt_sq hσSq_nonneg]
      rw [h_sqrt_sq] at h_cs

      -- The covariance equals σSq * ρ by definition
      have h_cov_eq : ∫ ω, (X 0 ω - m) * (X 1 ω - m) ∂μ = σSq * ρ := by
        have : ρ = (∫ ω, (X 0 ω - m) * (X 1 ω - m) ∂μ) / σSq := rfl
        rw [this]; field_simp [ne_of_gt hσSq_pos]
      rw [h_cov_eq] at h_cs

      -- Now |σSq * ρ| ≤ σSq
      rw [abs_mul, abs_of_pos hσSq_pos, mul_comm] at h_cs
      have h_ρ_bd : |ρ| * σSq ≤ σSq := h_cs
      have : |ρ| ≤ 1 := (mul_le_iff_le_one_left hσSq_pos).mp h_ρ_bd
      exact abs_le.mp this

    exact ⟨m, σSq, ρ, hmean, hvar, hcov, hσSq_nonneg, hρ_bd⟩

  · -- Case: zero variance (all X_i are constant a.s.)
    push_neg at hσSq_pos
    have hσSq_zero : σSq = 0 := le_antisymm hσSq_pos hσSq_nonneg

    -- When variance is 0, all X_i = m almost surely
    have hX_const : ∀ i, ∀ᵐ ω ∂μ, X i ω = m := by
      intro i
      -- Use the fact that variance of X_i is 0
      have h_var_i : ∫ ω, (X i ω - m)^2 ∂μ = 0 := by
        rw [hvar i, hσSq_zero]
      -- When ∫ f² = 0 for a nonnegative function, f = 0 a.e.
      have h_ae_zero : ∀ᵐ ω ∂μ, (X i ω - m)^2 = 0 := by
        have h_nonneg : ∀ ω, 0 ≤ (X i ω - m)^2 := fun ω => sq_nonneg _
        have h_integrable : Integrable (fun ω => (X i ω - m)^2) μ := by
          have : MemLp (fun ω => X i ω - m) 2 μ := (hX_L2 i).sub (memLp_const m)
          exact this.integrable_sq
        exact integral_eq_zero_iff_of_nonneg_ae (ae_of_all _ h_nonneg) h_integrable |>.mp h_var_i
      -- Square equals zero iff the value equals zero
      filter_upwards [h_ae_zero] with ω h
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp h)

    -- Covariance is 0
    have hcov : ∀ i j, i ≠ j → ∫ ω, (X i ω - m) * (X j ω - m) ∂μ = 0 := by
      intro i j _
      -- Use the fact that X_i = m and X_j = m almost everywhere
      have h_ae_prod : ∀ᵐ ω ∂μ, (X i ω - m) * (X j ω - m) = 0 := by
        filter_upwards [hX_const i, hX_const j] with ω hi hj
        rw [hi, hj]
        ring
      -- Integral of a.e. zero function is zero
      have h_integrable : Integrable (fun ω => (X i ω - m) * (X j ω - m)) μ := by
        have h_i : MemLp (fun ω => X i ω - m) 2 μ := (hX_L2 i).sub (memLp_const m)
        have h_j : MemLp (fun ω => X j ω - m) 2 μ := (hX_L2 j).sub (memLp_const m)
        exact h_i.integrable_mul h_j
      exact integral_eq_zero_of_ae h_ae_prod

    -- ρ = 0 works
    use m, σSq, 0
    refine ⟨hmean, hvar, ?_, hσSq_nonneg, ?_⟩
    · intro i j hij
      rw [hcov i j hij, hσSq_zero]
      ring
    · norm_num

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

-- Helper lemmas for Fin index gymnastics in two-window bounds.
-- These lemmas isolate the technical reindexing and cardinality proofs needed for
-- the weighted average machinery.
namespace FinIndexHelpers

open scoped BigOperators
open Finset

/-- Auxiliary lemma: the two filtered sets partition Fin(2k). -/
private lemma card_filter_partition (k : ℕ) :
  let s_lt := (univ : Finset (Fin (2*k))).filter (fun i => i.val < k)
  let s_ge := (univ : Finset (Fin (2*k))).filter (fun i => ¬(i.val < k))
  s_lt.card + s_ge.card = 2*k := by
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

  -- NEW APPROACH: Use l2_contractability_bound with covariance structure

  -- Step 1: Show f∘X is contractable
  have hfX_contract : Contractable μ (fun n ω => f (X n ω)) :=
    @contractable_comp Ω _ μ _ X hX_contract hX_meas f hf_meas

  -- Step 2: Get covariance structure (m, σ², ρ) of f∘X
  obtain ⟨M, hM⟩ := hf_bdd
  have hfX_L2 : ∀ i, MemLp (fun ω => f (X i ω)) 2 μ := by
    intro i
    apply MemLp.of_bound (hf_meas.comp (hX_meas i)).aestronglyMeasurable M
    filter_upwards with ω
    simp [Real.norm_eq_abs]
    exact hM (X i ω)

  have hfX_meas : ∀ i, Measurable (fun ω => f (X i ω)) := by
    intro i
    exact hf_meas.comp (hX_meas i)

  obtain ⟨mf, σSqf, ρf, hmean, hvar, hcov, hσSq_nonneg, hρ_bd⟩ :=
    contractable_covariance_structure
      (fun n ω => f (X n ω)) hfX_contract hfX_meas hfX_L2

  -- Step 3: Set Cf = 2σ²(1-ρ)
  let Cf := 2 * σSqf * (1 - ρf)
  have hCf_nonneg : 0 ≤ Cf := by
    apply mul_nonneg
    apply mul_nonneg
    · norm_num
    · exact hσSq_nonneg
    · linarith [hρ_bd.2]

  refine ⟨Cf, hCf_nonneg, fun n m k hk => ?_⟩
  classical

  have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hk_ne : (k : ℝ) ≠ 0 := ne_of_gt hk_pos

  -- Index set: union of the two windows
  set S := window n k ∪ window m k with hS_def
  have h_subset_n : window n k ⊆ S := by
    intro t ht
    exact Finset.mem_union.mpr (Or.inl ht)
  have h_subset_m : window m k ⊆ S := by
    intro t ht
    exact Finset.mem_union.mpr (Or.inr ht)

  -- Random family indexed by natural numbers
  set Y : ℕ → Ω → ℝ := fun t ω => f (X t ω) with hY_def

  -- Weight vectors on the natural numbers (restricted to S)
  set pS : ℕ → ℝ := fun t => if t ∈ window n k then (1 / (k : ℝ)) else 0 with hpS_def
  set qS : ℕ → ℝ := fun t => if t ∈ window m k then (1 / (k : ℝ)) else 0 with hqS_def
  set δ : ℕ → ℝ := fun t => pS t - qS t with hδ_def

  -- Helper lemma: restrict the uniform weight to any subset of S
  have h_weight_restrict :
      ∀ (A : Finset ℕ) (hA : A ⊆ S) ω,
        ∑ t ∈ S, (if t ∈ A then (1 / (k : ℝ)) else 0) * Y t ω
          = (1 / (k : ℝ)) * ∑ t ∈ A, Y t ω := by
    intro A hA ω
    classical
    have h_filter :
        S.filter (fun t => t ∈ A) = A := by
      ext t
      by_cases htA : t ∈ A
      · have : t ∈ S := hA htA
        simp [Finset.mem_filter, htA, this]
      · simp [Finset.mem_filter, htA]
    have h_lhs :
        ∑ t ∈ S, (if t ∈ A then (1 / (k : ℝ)) else 0) * Y t ω
          = ∑ t ∈ S, (if t ∈ A then (1 / (k : ℝ)) * Y t ω else 0) := by
      refine Finset.sum_congr rfl ?_
      intro t ht
      by_cases htA : t ∈ A
      · simp [htA]
      · simp [htA]
    have h_sum :
        ∑ t ∈ S, (if t ∈ A then (1 / (k : ℝ)) else 0) * Y t ω =
          ∑ t ∈ A, (1 / (k : ℝ)) * Y t ω := by
      have h_indicator :=
        (Finset.sum_filter (s := S) (p := fun t => t ∈ A)
            (f := fun t => (1 / (k : ℝ)) * Y t ω)).symm
      simpa [h_lhs, h_filter] using h_indicator
    calc
      ∑ t ∈ S, (if t ∈ A then (1 / (k : ℝ)) else 0) * Y t ω
          = ∑ t ∈ A, (1 / (k : ℝ)) * Y t ω := h_sum
      _ = (1 / (k : ℝ)) * ∑ t ∈ A, Y t ω := by
            simp [Finset.mul_sum]

  -- Difference of window averages written as a single sum over S with weights δ
  have h_sum_delta :
      ∀ ω,
        ∑ t ∈ S, δ t * Y t ω =
          (1 / (k : ℝ)) * ∑ t ∈ window n k, Y t ω -
          (1 / (k : ℝ)) * ∑ t ∈ window m k, Y t ω := by
    intro ω
    have h_sum_p :
        ∑ t ∈ S, pS t * Y t ω =
          (1 / (k : ℝ)) * ∑ t ∈ window n k, Y t ω := by
      simpa [pS] using h_weight_restrict (window n k) h_subset_n ω
    have h_sum_q :
        ∑ t ∈ S, qS t * Y t ω =
          (1 / (k : ℝ)) * ∑ t ∈ window m k, Y t ω := by
      simpa [qS] using h_weight_restrict (window m k) h_subset_m ω
    have h_expand :
        ∑ t ∈ S, δ t * Y t ω =
          ∑ t ∈ S, (pS t * Y t ω - qS t * Y t ω) := by
      refine Finset.sum_congr rfl ?_
      intro t ht
      have : (pS t - qS t) * Y t ω = pS t * Y t ω - qS t * Y t ω := by
        ring
      simpa [δ] using this
    have h_split :
        ∑ t ∈ S, δ t * Y t ω =
          ∑ t ∈ S, pS t * Y t ω - ∑ t ∈ S, qS t * Y t ω := by
      simpa using
        (h_expand.trans
          (Finset.sum_sub_distrib (s := S)
            (f := fun t => pS t * Y t ω)
            (g := fun t => qS t * Y t ω)))
    simpa [h_sum_p, h_sum_q] using h_split

  have h_goal :
      ∀ ω,
        (1 / (k : ℝ)) * ∑ i : Fin k, f (X (n + i.val + 1) ω) -
        (1 / (k : ℝ)) * ∑ i : Fin k, f (X (m + i.val + 1) ω)
          = ∑ t ∈ S, δ t * Y t ω := by
    intro ω
    have := h_sum_delta ω
    simpa [Y, sum_window_eq_sum_fin, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this.symm

  -- Total weights
  have h_sum_pS :
      ∑ t ∈ S, pS t = 1 := by
    classical
    have h_filter :
        S.filter (fun t => t ∈ window n k) = window n k := by
      ext t
      by_cases ht : t ∈ window n k
      · have : t ∈ S := h_subset_n ht
        simp [Finset.mem_filter, ht, this]
      · simp [Finset.mem_filter, ht]
    have h_sum :
        ∑ t ∈ S, pS t = ∑ t ∈ window n k, (1 / (k : ℝ)) := by
      have h_indicator :=
        (Finset.sum_filter (s := S) (p := fun t => t ∈ window n k)
            (f := fun _ : ℕ => (1 / (k : ℝ)))).symm
      simpa [pS, h_filter]
        using h_indicator
    have h_card : (window n k).card = k := window_card n k
    have hk_ne' : (k : ℝ) ≠ 0 := ne_of_gt hk_pos
    have h_one : (window n k).card * (1 / (k : ℝ)) = 1 := by
      simp [h_card, one_div, hk_ne']
    have h_const :
        ∑ t ∈ window n k, (1 / (k : ℝ))
          = (window n k).card * (1 / (k : ℝ)) := by
      simp [Finset.sum_const]
    calc
      ∑ t ∈ S, pS t = (window n k).card * (1 / (k : ℝ)) := by
        simpa [h_sum, h_const]
      _ = 1 := h_one

  have h_sum_qS :
      ∑ t ∈ S, qS t = 1 := by
    classical
    have h_filter :
        S.filter (fun t => t ∈ window m k) = window m k := by
      ext t
      by_cases ht : t ∈ window m k
      · have : t ∈ S := h_subset_m ht
        simp [Finset.mem_filter, ht, this]
      · simp [Finset.mem_filter, ht]
    have h_sum :
        ∑ t ∈ S, qS t = ∑ t ∈ window m k, (1 / (k : ℝ)) := by
      have h_indicator :=
        (Finset.sum_filter (s := S) (p := fun t => t ∈ window m k)
            (f := fun _ : ℕ => (1 / (k : ℝ)))).symm
      simpa [qS, h_filter]
        using h_indicator
    have h_card : (window m k).card = k := window_card m k
    have hk_ne' : (k : ℝ) ≠ 0 := ne_of_gt hk_pos
    have h_one : (window m k).card * (1 / (k : ℝ)) = 1 := by
      simp [h_card, one_div, hk_ne']
    have h_const :
        ∑ t ∈ window m k, (1 / (k : ℝ))
          = (window m k).card * (1 / (k : ℝ)) := by
      simp [Finset.sum_const]
    calc
      ∑ t ∈ S, qS t = (window m k).card * (1 / (k : ℝ)) := by
        simpa [h_sum, h_const]
      _ = 1 := h_one

  -- Positivity of the weights
  have hpS_nonneg : ∀ t, 0 ≤ pS t := by
    intro t
    by_cases ht : t ∈ window n k
    · have hk_nonneg : 0 ≤ 1 / (k : ℝ) := div_nonneg zero_le_one (le_of_lt hk_pos)
      simpa [pS, ht] using hk_nonneg
    · simp [pS, ht]

  have hqS_nonneg : ∀ t, 0 ≤ qS t := by
    intro t
    by_cases ht : t ∈ window m k
    · have hk_nonneg : 0 ≤ 1 / (k : ℝ) := div_nonneg zero_le_one (le_of_lt hk_pos)
      simpa [qS, ht] using hk_nonneg
    · simp [qS, ht]

  -- Absolute bound on δ on S
  have hδ_abs_le :
      ∀ t ∈ S, |δ t| ≤ 1 / (k : ℝ) := by
    intro t htS
    by_cases ht_n : t ∈ window n k
    · by_cases ht_m : t ∈ window m k
      · have : δ t = 0 := by simp [δ, pS, qS, ht_n, ht_m]
        simpa [this] using abs_nonneg (δ t)
      · have : δ t = 1 / (k : ℝ) := by simp [δ, pS, qS, ht_n, ht_m]
        simpa [this]
    · by_cases ht_m : t ∈ window m k
      · have : δ t = - (1 / (k : ℝ)) := by simp [δ, pS, qS, ht_n, ht_m]
        have : |δ t| = 1 / (k : ℝ) := by simpa [this, abs_neg]
        simpa [this]
      · have : δ t = 0 := by simp [δ, pS, qS, ht_n, ht_m]
        simpa [this] using abs_nonneg (δ t)

  -- Reindex the union set `S` as a finite type
  let β := {t : ℕ // t ∈ S}
  let nS : ℕ := Fintype.card β
  let eβ : Fin nS ≃ β := (Fintype.equivFin β).symm
  let idx : Fin nS → ℕ := fun i => (eβ i).1
  have h_idx_mem : ∀ i : Fin nS, idx i ∈ S := fun i => (eβ i).2

  -- Random family indexed by `Fin nS`
  let ξ : Fin nS → Ω → ℝ := fun i ω => Y (idx i) ω

  -- Weights transferred to `Fin nS`
  let p : Fin nS → ℝ := fun i => pS (idx i)
  let q : Fin nS → ℝ := fun i => qS (idx i)

  -- Probability properties for the reindexed weights
  have hp_prob : (∑ i : Fin nS, p i) = 1 ∧ ∀ i, 0 ≤ p i := by
    constructor
    · have h_equiv :
        ∑ i : Fin nS, p i = ∑ t ∈ S, pS t := by
        classical
        have h_sum_equiv :
            ∑ i : Fin nS, pS (idx i) =
              ∑ b : β, pS b.1 :=
          (Fintype.sum_equiv eβ (fun b : β => pS b.1)).symm
        have h_sum_attach :
            ∑ b : β, pS b.1 = ∑ t ∈ S, pS t := by
          simpa [β] using Finset.sum_attach (s := S) (f := fun t => pS t)
        simpa [p, idx] using h_sum_equiv.trans h_sum_attach
      simpa [h_equiv, h_sum_pS]
    · intro i
      simpa [p, idx] using hpS_nonneg (idx i)

  have hq_prob : (∑ i : Fin nS, q i) = 1 ∧ ∀ i, 0 ≤ q i := by
    constructor
    · have h_equiv :
        ∑ i : Fin nS, q i = ∑ t ∈ S, qS t := by
        classical
        have h_sum_equiv :
            ∑ i : Fin nS, qS (idx i) =
              ∑ b : β, qS b.1 :=
          (Fintype.sum_equiv eβ (fun b : β => qS b.1)).symm
        have h_sum_attach :
            ∑ b : β, qS b.1 = ∑ t ∈ S, qS t := by
          simpa [β] using Finset.sum_attach (s := S) (f := fun t => qS t)
        simpa [q, idx] using h_sum_equiv.trans h_sum_attach
      simpa [h_equiv, h_sum_qS]
    · intro i
      simpa [q, idx] using hqS_nonneg (idx i)

  -- Supremum bound on the weight difference
  have h_sup_le :
      (⨆ i : Fin nS, |p i - q i|) ≤ 1 / (k : ℝ) := by
    refine iSup_le ?_
    intro i
    have hmem : idx i ∈ S := h_idx_mem i
    have hδ_bound := hδ_abs_le (idx i) hmem
    have hδ_eq : δ (idx i) = p i - q i := by simp [δ, p, q, idx]
    simpa [hδ_eq] using hδ_bound

  -- Injectivity of the indexing map
  have h_idx_ne : ∀ {i j : Fin nS}, i ≠ j → idx i ≠ idx j := by
    intro i j hij hval
    have : eβ i = eβ j := by
      apply Subtype.ext
      exact hval
    exact hij (eβ.injective this)

  -- Mean and L² structure for ξ
  have hξ_mean : ∀ i : Fin nS, ∫ ω, ξ i ω ∂μ = mf := by
    intro i
    simpa [ξ, Y, idx, hY_def] using hmean (idx i)

  have hξ_L2 : ∀ i : Fin nS, MemLp (fun ω => ξ i ω - mf) 2 μ := by
    intro i
    simpa [ξ, Y, idx, hY_def] using
      (hfX_L2 (idx i)).sub (memLp_const mf)

  have hξ_var : ∀ i : Fin nS, ∫ ω, (ξ i ω - mf)^2 ∂μ = (Real.sqrt σSqf) ^ 2 := by
    intro i
    simpa [ξ, Y, idx, hY_def] using hvar (idx i)

  have hξ_cov :
      ∀ i j : Fin nS, i ≠ j →
        ∫ ω, (ξ i ω - mf) * (ξ j ω - mf) ∂μ = (Real.sqrt σSqf) ^ 2 * ρf := by
    intro i j hij
    have hneq : idx i ≠ idx j := h_idx_ne hij
    simpa [ξ, Y, idx, hY_def, hneq] using hcov (idx i) (idx j) hneq

  -- Express the δ-weighted sum in terms of the Fin-indexed weights
  have h_sum_p_fin :
      ∀ ω,
        ∑ i : Fin nS, p i * ξ i ω =
          ∑ t ∈ S, pS t * Y t ω := by
    intro ω
    classical
    have h_sum_equiv :
        ∑ i : Fin nS, p i * ξ i ω =
          ∑ b : β, pS b.1 * Y b.1 ω :=
      (Fintype.sum_equiv eβ (fun b : β => pS b.1 * Y b.1 ω)).symm
    have h_sum_attach :
        ∑ b : β, pS b.1 * Y b.1 ω =
          ∑ t ∈ S, pS t * Y t ω := by
      simpa [β] using
        Finset.sum_attach (s := S) (f := fun t => pS t * Y t ω)
    simpa [p, ξ, idx, Y] using h_sum_equiv.trans h_sum_attach

  have h_sum_q_fin :
      ∀ ω,
        ∑ i : Fin nS, q i * ξ i ω =
          ∑ t ∈ S, qS t * Y t ω := by
    intro ω
    classical
    have h_sum_equiv :
        ∑ i : Fin nS, q i * ξ i ω =
          ∑ b : β, qS b.1 * Y b.1 ω :=
      (Fintype.sum_equiv eβ (fun b : β => qS b.1 * Y b.1 ω)).symm
    have h_sum_attach :
        ∑ b : β, qS b.1 * Y b.1 ω =
          ∑ t ∈ S, qS t * Y t ω := by
      simpa [β] using
        Finset.sum_attach (s := S) (f := fun t => qS t * Y t ω)
    simpa [q, ξ, idx, Y] using h_sum_equiv.trans h_sum_attach

  have h_delta_fin :
      ∀ ω,
        ∑ t ∈ S, δ t * Y t ω =
          ∑ i : Fin nS, p i * ξ i ω - ∑ i : Fin nS, q i * ξ i ω := by
    intro ω
    have h_sum_p := h_sum_p_fin ω
    have h_sum_q := h_sum_q_fin ω
    have h_expand :
        ∑ t ∈ S, δ t * Y t ω =
          ∑ t ∈ S, (pS t * Y t ω - qS t * Y t ω) := by
      refine Finset.sum_congr rfl ?_
      intro t ht
      simp [δ, mul_sub]
    have h_split :
        ∑ t ∈ S, δ t * Y t ω =
          ∑ t ∈ S, pS t * Y t ω - ∑ t ∈ S, qS t * Y t ω := by
      simpa using
        (h_expand.trans
          (Finset.sum_sub_distrib (s := S)
            (f := fun t => pS t * Y t ω)
            (g := fun t => qS t * Y t ω)))
    simpa [h_sum_p, h_sum_q] using h_split

  have h_goal_fin :
      ∀ ω,
        (1 / (k : ℝ)) * ∑ i : Fin k, f (X (n + i.val + 1) ω) -
        (1 / (k : ℝ)) * ∑ i : Fin k, f (X (m + i.val + 1) ω)
          = ∑ i : Fin nS, p i * ξ i ω - ∑ i : Fin nS, q i * ξ i ω := by
    intro ω
    have h_goal' := h_goal ω
    have h_delta := h_delta_fin ω
    simpa [h_goal', h_delta]

  -- Apply the L² contractability bound on the reindexed weights
  have h_bound :=
    @L2Approach.l2_contractability_bound Ω _ μ _ nS ξ mf (Real.sqrt σSqf) ρf
      hρ_bd hξ_mean hξ_L2 hξ_var hξ_cov p q hp_prob hq_prob

  have h_factor_nonneg :
      0 ≤ 2 * (Real.sqrt σSqf) ^ 2 * (1 - ρf) := by
    have hσ_nonneg : 0 ≤ (Real.sqrt σSqf) ^ 2 := by exact sq_nonneg _
    have hρ_nonneg : 0 ≤ 1 - ρf := sub_nonneg.mpr hρ_bd.2
    have : 0 ≤ (2 : ℝ) := by norm_num
    exact mul_nonneg (mul_nonneg this hσ_nonneg) hρ_nonneg

  -- Final bound
  have h_sqrt_sq : (Real.sqrt σSqf) ^ 2 = σSqf := Real.sq_sqrt hσSq_nonneg

  calc
    ∫ ω,
        ((1 / (k : ℝ)) * ∑ i : Fin k, f (X (n + i.val + 1) ω) -
        (1 / (k : ℝ)) * ∑ i : Fin k, f (X (m + i.val + 1) ω))^2 ∂μ
        = ∫ ω, (∑ i : Fin nS, p i * ξ i ω - ∑ i : Fin nS, q i * ξ i ω)^2 ∂μ := by
            congr 1
            funext ω
            simpa [h_goal_fin ω]
  _ ≤ 2 * (Real.sqrt σSqf) ^ 2 * (1 - ρf) *
        (⨆ i : Fin nS, |p i - q i|) := h_bound
  _ ≤ 2 * (Real.sqrt σSqf) ^ 2 * (1 - ρf) * (1 / (k : ℝ)) := by
        refine mul_le_mul_of_nonneg_left h_sup_le h_factor_nonneg
  _ = Cf / k := by
        have : 2 * (Real.sqrt σSqf) ^ 2 * (1 - ρf) = Cf := by
          simp [Cf, h_sqrt_sq, mul_comm, mul_left_comm, mul_assoc]
        simpa [this, div_eq_mul_inv]

/-- **L² bound wrapper for two starting windows**.

For contractable sequences, the L² difference between averages starting at different
indices n and m is uniformly small. This gives us the key uniform bound we need.

NOTE: This wrapper is not used in the main proof. The uniform version with disjointness
hypothesis is used instead. This wrapper is left for potential future use.
-/
lemma l2_bound_two_windows
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ)
    (f : ℝ → ℝ) (hf_meas : Measurable f)
    (hf_bdd : ∃ M, ∀ x, |f x| ≤ M)
    (n m : ℕ) {k : ℕ} (hk : 0 < k)
    (hdisj : Disjoint (window n k) (window m k)) :
    ∃ Cf : ℝ, 0 ≤ Cf ∧
      ∫ ω, ((1/(k:ℝ)) * ∑ i : Fin k, f (X (n + i.val + 1) ω) -
            (1/(k:ℝ)) * ∑ i : Fin k, f (X (m + i.val + 1) ω))^2 ∂μ
        ≤ Cf / k := by
  -- With disjointness, this is exactly l2_bound_two_windows_uniform
  obtain ⟨Cf, hCf_nonneg, hCf_unif⟩ := l2_bound_two_windows_uniform X hX_contract hX_meas hX_L2 f hf_meas hf_bdd
  refine ⟨Cf, hCf_nonneg, ?_⟩
  exact hCf_unif n m k hk

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
  -- Split the sum into indices < m-k (which contribute 0) and indices ≥ m-k
  calc ∑ i : Fin m, (if i.val < m - k then 0 else c) * F i.val
      = ∑ i : Fin m, if i.val < m - k then 0 else c * F i.val := by
          congr 1; ext i; split_ifs <;> ring
    _ = ∑ i ∈ Finset.univ.filter (fun i : Fin m => ¬ i.val < m - k), c * F i.val := by
          have : ∀ i : Fin m, (if i.val < m - k then 0 else c * F i.val) =
                               (if ¬ i.val < m - k then c * F i.val else 0) := by
            intro i; by_cases h : i.val < m - k <;> simp [h]
          simp_rw [this]
          rw [Finset.sum_filter]
    _ = c * ∑ i ∈ Finset.univ.filter (fun i : Fin m => ¬ i.val < m - k), F i.val := by
          rw [← Finset.mul_sum]
    _ = c * ∑ j : Fin k, F (m - k + j.val) := by
          congr 1
          have h_sub : m - (m - k) = k := by omega
          trans (∑ j : Fin (m - (m - k)), F ((m - k) + j.val))
          · exact FinIndexHelpers.sum_filter_fin_val_ge_eq_sum_fin m (m - k) (by omega) F
          · rw [h_sub]

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
    (n m k : ℕ) (hk : 0 < k) (hkm : k ≤ m) :
    ∃ Ctail : ℝ, 0 ≤ Ctail ∧
      ∫ ω, ((1 / (m : ℝ)) * ∑ i : Fin m, f (X (n + i.val + 1) ω) -
            (1 / (k : ℝ)) * ∑ i : Fin k, f (X (n + (m - k) + i.val + 1) ω))^2 ∂μ
        ≤ Ctail / k := by
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

  -- Direct approach using hCf_unif:
  -- The tail average is an equal-weight window of size k starting at n+(m-k):
  --   (1/k) ∑_{j<k} f(X_{n+(m-k)+j+1})
  --
  -- Strategy:
  -- 1. Use triangle inequality: |long_avg - tail_avg| ≤ |long_avg - some_window| + |some_window - tail_avg|
  -- 2. The tail window is exactly window starting at position n+(m-k)
  -- 3. Can compare it with a window of size k starting at n using hCf_unif
  -- 4. The bound Cf/k applies since both are equal-weight windows of size k
  --
  -- Rewrite long average (1/m) * ∑_{i<m} f(X_{n+i+1}) in terms of weights on each position
  -- We can split it as: sum over first (m-k) terms + sum over last k terms
  -- Then compare with the tail average which is just the last k terms weighted by 1/k

  -- Key insight: Write the difference as a weighted combination where we can apply sum_tail_block_reindex
  -- Long avg = (1/m) * [first (m-k) terms + last k terms]
  -- Tail avg = (1/k) * [last k terms]
  -- Difference involves the last k terms with weight (1/m - 1/k) and first terms with weight 1/m

  -- Since |1/m - 1/k| ≤ 1/k and we have at most m terms each bounded,
  -- this reduces to applying the uniform bound hCf_unif

  -- Use that we can rewrite the long average to isolate the tail portion
  -- and apply the uniform bound

  obtain ⟨M, hM⟩ := hf_bdd

  -- The key is to use boundedness to show the difference is controlled
  -- For a more direct proof, we use that:
  -- |long_avg - tail_avg|² ≤ |long_avg - window_avg|² + |window_avg - tail_avg|²
  -- where both terms can be bounded using hCf_unif

  -- However, for simplicity, we can use the fact that both averages involve
  -- bounded functions and the weight difference is small

  -- Direct bound using triangle inequality and boundedness
  have h_bdd_integrand : ∀ ω, ((1 / (m : ℝ)) * ∑ i : Fin m, f (X (n + i.val + 1) ω) -
        (1 / (k : ℝ)) * ∑ i : Fin k, f (X (n + (m - k) + i.val + 1) ω))^2
      ≤ (4 * M)^2 := by
    intro ω
    have h1 : |(1 / (m : ℝ)) * ∑ i : Fin m, f (X (n + i.val + 1) ω)| ≤ M := by
      calc |(1 / (m : ℝ)) * ∑ i : Fin m, f (X (n + i.val + 1) ω)|
          = (1 / (m : ℝ)) * |∑ i : Fin m, f (X (n + i.val + 1) ω)| := by
              rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1 / (m : ℝ))]
        _ ≤ (1 / (m : ℝ)) * (m * M) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            calc |∑ i : Fin m, f (X (n + i.val + 1) ω)|
                ≤ ∑ i : Fin m, |f (X (n + i.val + 1) ω)| := Finset.abs_sum_le_sum_abs _ _
              _ ≤ ∑ i : Fin m, M := by
                  apply Finset.sum_le_sum
                  intro i _; exact hM _
              _ = m * M := by rw [Finset.sum_const, Finset.card_fin]; ring
        _ = M := by
            have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr (Nat.lt_of_lt_of_le hk hkm)
            field_simp [ne_of_gt hm_pos]
    have h2 : |(1 / (k : ℝ)) * ∑ i : Fin k, f (X (n + (m - k) + i.val + 1) ω)| ≤ M := by
      calc |(1 / (k : ℝ)) * ∑ i : Fin k, f (X (n + (m - k) + i.val + 1) ω)|
          = (1 / (k : ℝ)) * |∑ i : Fin k, f (X (n + (m - k) + i.val + 1) ω)| := by
              rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1 / (k : ℝ))]
        _ ≤ (1 / (k : ℝ)) * (k * M) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            calc |∑ i : Fin k, f (X (n + (m - k) + i.val + 1) ω)|
                ≤ ∑ i : Fin k, |f (X (n + (m - k) + i.val + 1) ω)| := Finset.abs_sum_le_sum_abs _ _
              _ ≤ ∑ i : Fin k, M := by
                  apply Finset.sum_le_sum
                  intro i _; exact hM _
              _ = k * M := by rw [Finset.sum_const, Finset.card_fin]; ring
        _ = M := by
          have hk_pos : (0:ℝ) < k := Nat.cast_pos.mpr hk
          field_simp [ne_of_gt hk_pos]
    have ha : |(1 / (m : ℝ)) * ∑ i : Fin m, f (X (n + i.val + 1) ω) -
          (1 / (k : ℝ)) * ∑ i : Fin k, f (X (n + (m - k) + i.val + 1) ω)| ≤
        |(1 / (m : ℝ)) * ∑ i : Fin m, f (X (n + i.val + 1) ω)| +
           |(1 / (k : ℝ)) * ∑ i : Fin k, f (X (n + (m - k) + i.val + 1) ω)| :=
      abs_sub _ _
    calc ((1 / (m : ℝ)) * ∑ i : Fin m, f (X (n + i.val + 1) ω) -
          (1 / (k : ℝ)) * ∑ i : Fin k, f (X (n + (m - k) + i.val + 1) ω))^2
        ≤ (|(1 / (m : ℝ)) * ∑ i : Fin m, f (X (n + i.val + 1) ω)| +
           |(1 / (k : ℝ)) * ∑ i : Fin k, f (X (n + (m - k) + i.val + 1) ω)|)^2 := by
            apply sq_le_sq'
            · have : 0 ≤ |(1 / (m : ℝ)) * ∑ i : Fin m, f (X (n + i.val + 1) ω)| +
                         |(1 / (k : ℝ)) * ∑ i : Fin k, f (X (n + (m - k) + i.val + 1) ω)| := by positivity
              have : -(|(1 / (m : ℝ)) * ∑ i : Fin m, f (X (n + i.val + 1) ω)| +
                      |(1 / (k : ℝ)) * ∑ i : Fin k, f (X (n + (m - k) + i.val + 1) ω)|) ≤
                     (1 / (m : ℝ)) * ∑ i : Fin m, f (X (n + i.val + 1) ω) -
                     (1 / (k : ℝ)) * ∑ i : Fin k, f (X (n + (m - k) + i.val + 1) ω) :=
                neg_le_of_abs_le ha
              linarith
            · exact le_of_abs_le ha
      _ ≤ (M + M)^2 := by
          apply sq_le_sq'
          · have hM_nonneg : 0 ≤ M := by
              have : |f 0| ≤ M := hM 0
              exact le_trans (abs_nonneg _) this
            have : 0 ≤ M + M := by linarith
            have h_sum_bound : |(1 / (m : ℝ)) * ∑ i : Fin m, f (X (n + i.val + 1) ω)| +
                               |(1 / (k : ℝ)) * ∑ i : Fin k, f (X (n + (m - k) + i.val + 1) ω)| ≤ M + M := by
              linarith [h1, h2]
            have : -(M + M) ≤ |(1 / (m : ℝ)) * ∑ i : Fin m, f (X (n + i.val + 1) ω)| +
                               |(1 / (k : ℝ)) * ∑ i : Fin k, f (X (n + (m - k) + i.val + 1) ω)| := by
              have h_nonneg : 0 ≤ |(1 / (m : ℝ)) * ∑ i : Fin m, f (X (n + i.val + 1) ω)| +
                                   |(1 / (k : ℝ)) * ∑ i : Fin k, f (X (n + (m - k) + i.val + 1) ω)| := by positivity
              linarith [h_nonneg, hM_nonneg]
            linarith [h_sum_bound]
          · linarith [h1, h2]
      _ = (2 * M)^2 := by ring
      _ ≤ (4 * M)^2 := by
          apply sq_le_sq'
          · have hM_nonneg : 0 ≤ M := by
              -- |f 0| ≤ M implies 0 ≤ M
              have : |f 0| ≤ M := hM 0
              exact le_trans (abs_nonneg _) this
            have : 0 ≤ 4 * M := by linarith
            linarith [this, hM_nonneg]
          · have hM_nonneg : 0 ≤ M := by
              have : |f 0| ≤ M := hM 0
              exact le_trans (abs_nonneg _) this
            linarith [hM_nonneg]

  -- The key insight: We can bound this by decomposing the long average
  -- and using triangle inequality with a common window of size k

  -- Introduce an intermediate window: (1/k) * ∑_{i<k} f(X_{n+i+1})
  -- Then: |long_avg - tail_avg|² ≤ 2|long_avg - window_avg|² + 2|window_avg - tail_avg|²

  -- The second term |window_avg - tail_avg|² can be bounded by hCf_unif since
  -- both are equal-weight windows of size k at positions n and n+(m-k)

  -- For the first term, we use that the long average (1/m) is close to any k-window (1/k)
  -- This follows from the fact that the long average is a weighted combination that
  -- includes the k-window with smaller weight

  -- However, the cleanest approach requires more machinery about weighted averages
  -- For now, we have established the integrand is bounded, which is the key
  -- integrability property needed for the convergence proof

  -- Apply l2_contractability_bound with weight vectors:
  --   p = (1/m, 1/m, ..., 1/m)  [m terms]
  --   q = (0, ..., 0, 1/k, ..., 1/k)  [m-k zeros, then k terms of 1/k]
  -- The sup |p - q| = 1/k, giving bound 2σ²(1-ρ) · (1/k) = Cf/k

  -- First, get the covariance structure of f∘X
  have hfX_contract : Contractable μ (fun n ω => f (X n ω)) :=
    @contractable_comp Ω _ μ _ X hX_contract hX_meas f hf_meas

  have hfX_L2' : ∀ i, MemLp (fun ω => f (X i ω)) 2 μ := by
    intro i
    apply MemLp.of_bound (hf_meas.comp (hX_meas i)).aestronglyMeasurable M
    filter_upwards with ω
    simp [Real.norm_eq_abs]
    exact hM (X i ω)

  have hfX_meas' : ∀ i, Measurable (fun ω => f (X i ω)) := by
    intro i
    exact hf_meas.comp (hX_meas i)

  obtain ⟨mf, σSqf, ρf, hmean_f, hvar_f, hcov_f, hσSq_nonneg, hρ_bd⟩ :=
    contractable_covariance_structure (fun n ω => f (X n ω)) hfX_contract hfX_meas' hfX_L2'

  -- Cf = 2σ²(1-ρ) by definition in the calling context
  -- We need to relate this to Cf from the hypothesis
  -- Actually, hCf_unif tells us the bound is Cf/k, so we can deduce what Cf must be

  -- Define the sequence ξ on m elements
  let ξ : Fin m → Ω → ℝ := fun i ω => f (X (n + i.val + 1) ω)

  -- Define weight vectors p and q
  let p : Fin m → ℝ := fun _ => 1 / (m : ℝ)
  let q : Fin m → ℝ := fun i => if i.val < m - k then 0 else 1 / (k : ℝ)

  -- Verify these are probability distributions
  have hp_prob : (∑ i : Fin m, p i) = 1 ∧ ∀ i, 0 ≤ p i := by
    constructor
    · simp only [p, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
      have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr (Nat.lt_of_lt_of_le hk hkm)
      field_simp [ne_of_gt hm_pos]
    · intro i; simp only [p]; positivity

  have hq_prob : (∑ i : Fin m, q i) = 1 ∧ ∀ i, 0 ≤ q i := by
    constructor
    · -- Sum equals 1: only terms with i.val ≥ m-k contribute
      calc ∑ i : Fin m, q i
        = ∑ i ∈ Finset.filter (fun i => i.val < m - k) Finset.univ, q i +
          ∑ i ∈ Finset.filter (fun i => ¬(i.val < m - k)) Finset.univ, q i := by
            rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ) (p := fun i => i.val < m - k)]
      _ = 0 + ∑ i ∈ Finset.filter (fun i : Fin m => ¬(i.val < m - k)) Finset.univ, (1/(k:ℝ)) := by
            congr 1
            · apply Finset.sum_eq_zero
              intro i hi
              have : i.val < m - k := Finset.mem_filter.mp hi |>.2
              simp [q, this]
            · apply Finset.sum_congr rfl
              intro i hi
              have : ¬(i.val < m - k) := Finset.mem_filter.mp hi |>.2
              simp [q, this]
      _ = (Finset.filter (fun i : Fin m => ¬(i.val < m - k)) Finset.univ).card * (1/(k:ℝ)) := by
            simp [Finset.sum_const]
      _ = k * (1/(k:ℝ)) := by
            congr 1
            -- The number of i with i.val ≥ m-k is k
            have : (Finset.filter (fun i : Fin m => ¬(i.val < m - k)) Finset.univ).card = k := by
              have h_eq : Finset.filter (fun i : Fin m => ¬(i.val < m - k)) Finset.univ =
                          Finset.image (fun (j : Fin k) => (⟨(m - k) + j.val, by omega⟩ : Fin m)) Finset.univ := by
                ext i
                simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, not_lt]
                constructor
                · intro hi
                  use ⟨i.val - (m - k), by omega⟩
                  simp only []
                  ext; simp; omega
                · rintro ⟨j, _, rfl⟩
                  simp
              rw [h_eq, Finset.card_image_of_injective]
              · simp only [Finset.card_fin]
              · intro a b hab
                simp only [Fin.mk.injEq] at hab
                exact Fin.ext (by omega)
            simpa
      _ = 1 := by
            have hk_pos : (0:ℝ) < k := Nat.cast_pos.mpr hk
            field_simp [ne_of_gt hk_pos]
    · intro i; simp [q]; split_ifs <;> positivity

  -- Now we need to verify that ξ has the covariance structure
  have hξ_mean : ∀ i, ∫ ω, ξ i ω ∂μ = mf := by
    intro i
    simp [ξ]
    exact hmean_f (n + i.val + 1)

  have hξ_L2 : ∀ i, MemLp (fun ω => ξ i ω - mf) 2 μ := by
    intro i
    simp [ξ]
    exact (hfX_L2' (n + i.val + 1)).sub (memLp_const mf)

  have hξ_var : ∀ i, ∫ ω, (ξ i ω - mf)^2 ∂μ = (Real.sqrt σSqf) ^ 2 := by
    intro i
    simp [ξ]
    have : (Real.sqrt σSqf) ^ 2 = σSqf := Real.sq_sqrt hσSq_nonneg
    rw [this]
    exact hvar_f (n + i.val + 1)

  have hξ_cov : ∀ i j, i ≠ j → ∫ ω, (ξ i ω - mf) * (ξ j ω - mf) ∂μ = (Real.sqrt σSqf) ^ 2 * ρf := by
    intro i j hij
    simp [ξ]
    have : (Real.sqrt σSqf) ^ 2 = σSqf := Real.sq_sqrt hσSq_nonneg
    rw [this]
    apply hcov_f
    omega

  -- Apply l2_contractability_bound
  have h_bound := @L2Approach.l2_contractability_bound Ω _ μ _ m ξ mf
    (Real.sqrt σSqf) ρf hρ_bd hξ_mean hξ_L2 hξ_var hξ_cov p q hp_prob hq_prob

  -- Compute the supremum |p - q|
  -- p i = 1/m for all i
  -- q i = 0 if i.val < m - k, else 1/k
  -- So |p i - q i| = 1/m if i.val < m - k
  --                = |1/m - 1/k| if i.val ≥ m - k
  -- Since k ≤ m - k (from hkm), we have m ≥ 2k, so 1/k > 1/m
  -- Thus |1/m - 1/k| = 1/k - 1/m
  -- Therefore: sup |p i - q i| = max(1/m, 1/k - 1/m) = 1/k - 1/m
  --
  -- For the proof, we bound: 1/k - 1/m ≤ 1/k
  -- This gives a slightly looser but still valid bound
  have h_sup_bound : (⨆ i : Fin m, |p i - q i|) ≤ 1 / (k : ℝ) := by
    -- Show that for all i, |p i - q i| ≤ 1/k
    haveI : Nonempty (Fin m) := by
      apply Fin.pos_iff_nonempty.mp
      exact Nat.lt_of_lt_of_le hk hkm
    apply ciSup_le
    intro i
    simp only [p, q]
    have hk_pos : (0:ℝ) < k := Nat.cast_pos.mpr hk
    have hm_pos : (0:ℝ) < m := Nat.cast_pos.mpr (Nat.lt_of_lt_of_le hk hkm)
    split_ifs with hi
    · -- Case: i.val < m - k, so |1/m - 0| = 1/m ≤ 1/k
      simp only [sub_zero]
      rw [abs_of_pos (by positivity : (0:ℝ) < 1/m)]
      -- 1/m ≤ 1/k follows from k ≤ m
      -- Use: 1/a ≤ 1/b ↔ b ≤ a (for positive a, b)
      rw [one_div_le_one_div hm_pos hk_pos]
      exact Nat.cast_le.mpr hkm
    · -- Case: i.val ≥ m - k, so |1/m - 1/k| ≤ 1/k
      -- Since k ≤ m, we have 1/k ≥ 1/m, so 1/m - 1/k ≤ 0, thus |1/m - 1/k| = 1/k - 1/m
      have h_div_order : (1:ℝ)/m ≤ 1/k := by
        rw [one_div_le_one_div hm_pos hk_pos]
        exact Nat.cast_le.mpr hkm
      -- abs_of_nonpos: |1/m - 1/k| = -(1/m - 1/k) = 1/k - 1/m when 1/m - 1/k ≤ 0
      rw [abs_of_nonpos (by linarith : (1:ℝ)/m - 1/k ≤ 0)]
      -- Goal: 1/k - 1/m ≤ 1/k, which simplifies to 0 ≤ 1/m
      -- Since m > 0, we have 1/m > 0
      have : (0:ℝ) < 1/m := by positivity
      linarith

  -- The bound from l2_contractability_bound is 2·σSqf·(1-ρf)·(⨆ i, |p i - q i|)
  -- We have h_sup_bound : (⨆ i, |p i - q i|) ≤ 1/k
  -- So we can bound by 2·σSqf·(1-ρf)·(1/k)

  -- Now we need to show this is bounded by Cf/k
  -- The hypothesis hCf_unif tells us that for any two k-windows,
  -- the L² distance is ≤ Cf/k
  -- By the definition of contractability and the L² approach, Cf = 2·σSqf·(1-ρf)

  -- Simplify (Real.sqrt σSqf)^2 = σSqf
  have h_sqrt_sq : (Real.sqrt σSqf) ^ 2 = σSqf := Real.sq_sqrt hσSq_nonneg

  -- Strengthen h_bound using h_sup_bound
  have h_bound_strengthened : ∫ ω, (∑ i, p i * ξ i ω - ∑ i, q i * ξ i ω)^2 ∂μ ≤
      2 * σSqf * (1 - ρf) * (1 / (k : ℝ)) := by
    calc ∫ ω, (∑ i, p i * ξ i ω - ∑ i, q i * ξ i ω)^2 ∂μ
      ≤ 2 * (Real.sqrt σSqf) ^ 2 * (1 - ρf) * (⨆ i, |p i - q i|) := h_bound
    _ ≤ 2 * (Real.sqrt σSqf) ^ 2 * (1 - ρf) * (1 / (k : ℝ)) := by
        apply mul_le_mul_of_nonneg_left h_sup_bound
        apply mul_nonneg
        · apply mul_nonneg
          · linarith
          · exact sq_nonneg _
        · linarith [hρ_bd.2]
    _ = 2 * σSqf * (1 - ρf) * (1 / (k : ℝ)) := by rw [h_sqrt_sq]

  -- Now verify that the LHS of h_bound equals our goal's LHS
  have h_lhs_eq : (∫ ω, (∑ i, p i * ξ i ω - ∑ i, q i * ξ i ω)^2 ∂μ) =
      ∫ ω, ((1 / (m : ℝ)) * ∑ i : Fin m, f (X (n + i.val + 1) ω) -
            (1 / (k : ℝ)) * ∑ i : Fin k, f (X (n + (m - k) + i.val + 1) ω))^2 ∂μ := by
    congr 1
    ext ω
    congr 1
    -- Expand definitions of p, q, ξ
    simp only [p, q, ξ]
    -- LHS: ∑ i, p i * ξ i ω = ∑ i, (1/m) * f(X(n + i.val + 1) ω) = (1/m) * ∑ i, f(X(...))
    rw [show ∑ i : Fin m, (1 / (m : ℝ)) * f (X (n + i.val + 1) ω) =
             (1 / (m : ℝ)) * ∑ i : Fin m, f (X (n + i.val + 1) ω)
        by rw [← Finset.mul_sum]]
    -- RHS: ∑ i, q i * ξ i ω where q i = 0 if i.val < m-k, else 1/k
    -- So this equals ∑_{i : i.val ≥ m-k} (1/k) * f(X(n + i.val + 1) ω)
    -- Reindex: when i.val ≥ m-k, write i.val = (m-k) + j for j ∈ [0, k)
    have h_q_sum : ∑ i : Fin m, q i * f (X (n + i.val + 1) ω) =
        (1 / (k : ℝ)) * ∑ i : Fin k, f (X (n + (m - k) + i.val + 1) ω) := by
      -- Split sum based on whether i.val < m - k
      calc ∑ i : Fin m, q i * f (X (n + i.val + 1) ω)
        = ∑ i ∈ Finset.filter (fun i => i.val < m - k) Finset.univ, q i * f (X (n + i.val + 1) ω) +
          ∑ i ∈ Finset.filter (fun i => ¬(i.val < m - k)) Finset.univ, q i * f (X (n + i.val + 1) ω) := by
            rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ) (p := fun i => i.val < m - k)]
      _ = 0 + ∑ i ∈ Finset.filter (fun i : Fin m => ¬(i.val < m - k)) Finset.univ,
            (1 / (k : ℝ)) * f (X (n + i.val + 1) ω) := by
            congr 1
            · apply Finset.sum_eq_zero
              intro i hi
              have : i.val < m - k := Finset.mem_filter.mp hi |>.2
              simp [q, this]
            · apply Finset.sum_congr rfl
              intro i hi
              have : ¬(i.val < m - k) := Finset.mem_filter.mp hi |>.2
              simp [q, this]
      _ = (1 / (k : ℝ)) * ∑ i : Fin k, f (X (n + (m - k) + i.val + 1) ω) := by
            simp only [zero_add]
            rw [← Finset.mul_sum]
            congr 1
            -- Reindex: i with i.val ≥ m-k ↔ i = ⟨(m-k) + j.val, _⟩ for j : Fin k
            -- The filtered set equals the image of the map j ↦ ⟨(m-k) + j, _⟩
            trans (∑ i ∈ Finset.image (fun (j : Fin k) => (⟨(m - k) + j.val, by omega⟩ : Fin m)) Finset.univ,
                    f (X (n + i.val + 1) ω))
            · congr 1
              ext i
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
              constructor
              · intro hi
                use ⟨i.val - (m - k), by omega⟩
                simp only [Finset.mem_univ, true_and]
                ext
                simp only [Fin.val_mk]
                omega
              · rintro ⟨j, _, rfl⟩
                simp only [Fin.val_mk]
                omega
            · -- Now the sum is over an image, apply sum_image with injectivity
              rw [Finset.sum_image]
              · congr 1
                ext j
                simp only [Fin.val_mk]
                ring
              -- Prove injectivity
              · intro j₁ _ j₂ _ h
                simp only [Fin.mk.injEq] at h
                exact Fin.ext (by omega)
    rw [h_q_sum]

  -- Define Ctail from the covariance structure
  let Ctail := 2 * σSqf * (1 - ρf)
  have hCtail_nonneg : 0 ≤ Ctail := by
    have : 0 ≤ 1 - ρf := by linarith [hρ_bd.2]
    nlinarith [hσSq_nonneg, this]

  -- Prove the bound with Ctail
  have h_bound_with_Ctail : ∫ ω, ((1 / (m : ℝ)) * ∑ i : Fin m, f (X (n + i.val + 1) ω) -
            (1 / (k : ℝ)) * ∑ i : Fin k, f (X (n + (m - k) + i.val + 1) ω))^2 ∂μ
        ≤ Ctail / k := by
    calc ∫ ω, ((1 / (m : ℝ)) * ∑ i : Fin m, f (X (n + i.val + 1) ω) -
                (1 / (k : ℝ)) * ∑ i : Fin k, f (X (n + (m - k) + i.val + 1) ω))^2 ∂μ
        = ∫ ω, (∑ i, p i * ξ i ω - ∑ i, q i * ξ i ω)^2 ∂μ := h_lhs_eq.symm
      _ ≤ 2 * σSqf * (1 - ρf) * (1 / (k : ℝ)) := h_bound_strengthened
      _ = Ctail * (1 / (k : ℝ)) := rfl
      _ = Ctail / k := by ring

  exact ⟨Ctail, hCtail_nonneg, h_bound_with_Ctail⟩

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

    -- Choose N to handle BOTH separated and close cases
    --
    -- SEPARATED CASE: Need 3 * √(C_star/N) < ε
    --   ⟹ 9 * C_star / N < ε²
    --   ⟹ N > 9 * C_star / ε²
    --   With C_star ≤ 3 * Cf: N > 27 * Cf / ε²
    --
    -- CLOSE CASE: Need 2Mk/ℓ < ε where k = N and ℓ ≥ 2N
    --   With ℓ = 2N: 2Mk/(2N) = Mk/N < ε
    --   ⟹ N > Mk/ε = MN/ε
    --   This is impossible unless we use k = N/2 or similar
    --   Alternative: require N² > Mk, i.e., N > √(Mk)
    --   But M is fixed and k = N, so N² > MN, i.e., N > M
    --
    -- REVISED CLOSE CASE: Use tighter bound from telescoping
    --   |A 0 m - A 0 ℓ| ≤ 2M * |m-ℓ|/min(m,ℓ) < 2M * k/ℓ
    --   For ℓ ≥ 2N: 2M * N/(2N) = M
    --   This is CONSTANT, not shrinking with ε!
    --
    -- PRAGMATIC FIX: Use separated case threshold
    -- The close case pairs have |m - ℓ| < k, so they are genuinely close.
    -- As m, ℓ → ∞, even with constant bound M, the sequence is Cauchy in L²,
    -- which is sufficient for the proof structure.

    obtain ⟨M, hM⟩ := hf_bdd
    let N : ℕ := Nat.ceil (27 * Cf / (ε ^ 2)) + 1
    have hN_pos : 0 < N := Nat.succ_pos _
    -- Require m, ℓ ≥ 2N to ensure windows are disjoint
    refine ⟨2 * N, ?_⟩
    intro m ℓ hm hℓ
    -- Use fixed k = N (not min m ℓ) to ensure 2k ≤ m and 2k ≤ ℓ
    let k := N
    have hk_pos : 0 < k := hN_pos
    -- With m, ℓ ≥ 2N and k = N, we have 2k ≤ m and 2k ≤ ℓ
    have h2k_le_m : 2 * k ≤ m := by simpa [k] using hm
    have h2k_le_ℓ : 2 * k ≤ ℓ := by simpa [k] using hℓ

    -- UNIFIED 3-SEGMENT DECOMPOSITION (works for all m, ℓ, even with overlap)
    -- Triangle inequality: ||A_m - A_ℓ||₂ ≤ ||seg1|| + ||seg2|| + ||seg3||
    -- Each segment bounded by √(C/k), giving total bound 3√(C/k) < ε

    -- Three same-length comparisons (tail-averages):
    -- T1: (0 vs m-k), T2: ((m-k) vs (ℓ-k)), T3: ((ℓ-k) vs 0), all of length k.
    have h1sq :
        ∫ ω, (A 0 k ω - A (m - k) k ω)^2 ∂μ ≤ Cf / k := by
        simpa [A] using hCf_unif 0 (m - k) k hk_pos
    have h2sq :
      ∫ ω, (A (m - k) k ω - A (ℓ - k) k ω)^2 ∂μ ≤ Cf / k := by
        -- Middle segment: the relaxed uniform bound handles overlapping windows directly.
        simpa [A] using hCf_unif (m - k) (ℓ - k) k hk_pos
    have h3sq :
      ∫ ω, (A (ℓ - k) k ω - A 0 k ω)^2 ∂μ ≤ Cf / k := by
      simpa [A] using hCf_unif (ℓ - k) 0 k hk_pos
  
    -- Long vs tail comparisons for h1_L2 and h3_L2
    have hkm : k ≤ m := by
      calc k = N := rfl
           _ ≤ 2 * N := Nat.le_mul_of_pos_left _ (by decide : 0 < 2)
           _ ≤ m := hm
    have hkℓ : k ≤ ℓ := by
      calc k = N := rfl
           _ ≤ 2 * N := Nat.le_mul_of_pos_left _ (by decide : 0 < 2)
           _ ≤ ℓ := hℓ
  
    -- Get Ctail constants from long-vs-tail bounds
    obtain ⟨Ctail1, hC1_nonneg, h1sq_long⟩ :=
      l2_bound_long_vs_tail X hX_contract hX_meas hX_L2 f hf_meas ⟨M, hM⟩ 0 m k hk_pos hkm

    obtain ⟨Ctail3, hC3_nonneg, h3sq_long_prelim⟩ :=
      l2_bound_long_vs_tail X hX_contract hX_meas hX_L2 f hf_meas ⟨M, hM⟩ 0 ℓ k hk_pos hkℓ
  
    have h1sq_long : ∫ ω, (A 0 m ω - A (m - k) k ω)^2 ∂μ ≤ Ctail1 / k := by
      simpa [A] using h1sq_long
  
    have h3sq_long : ∫ ω, (A (ℓ - k) k ω - A 0 ℓ ω)^2 ∂μ ≤ Ctail3 / k := by
      have : ∫ ω, (A (ℓ - k) k ω - A 0 ℓ ω)^2 ∂μ
           = ∫ ω, (A 0 ℓ ω - A (ℓ - k) k ω)^2 ∂μ := by
        congr 1; ext ω; ring_nf
      rw [this]
      simpa [A] using h3sq_long_prelim
  
    -- Define C_star := max of all three constants
    let C_star : ℝ := max Cf (max Ctail1 Ctail3)
    have hC_star_nonneg : 0 ≤ C_star := by
      apply le_max_iff.mpr
      left; exact hCf_nonneg
    have hCf_le_C_star : Cf ≤ C_star := le_max_left _ _
    have hC1_le_C_star : Ctail1 ≤ C_star := le_trans (le_max_left _ _) (le_max_right _ _)
    have hC3_le_C_star : Ctail3 ≤ C_star := le_trans (le_max_right _ _) (le_max_right _ _)
  
    -- Strengthen the integral bounds to use C_star
    have h1sq_C_star : ∫ ω, (A 0 m ω - A (m - k) k ω)^2 ∂μ ≤ C_star / k := by
      calc ∫ ω, (A 0 m ω - A (m - k) k ω)^2 ∂μ
          ≤ Ctail1 / k := h1sq_long
        _ ≤ C_star / k := by exact div_le_div_of_nonneg_right hC1_le_C_star (Nat.cast_nonneg k)
    have h2sq_C_star : ∫ ω, (A (m - k) k ω - A (ℓ - k) k ω)^2 ∂μ ≤ C_star / k := by
      calc ∫ ω, (A (m - k) k ω - A (ℓ - k) k ω)^2 ∂μ
          ≤ Cf / k := h2sq
        _ ≤ C_star / k := by exact div_le_div_of_nonneg_right hCf_le_C_star (Nat.cast_nonneg k)
    have h3sq_C_star : ∫ ω, (A (ℓ - k) k ω - A 0 ℓ ω)^2 ∂μ ≤ C_star / k := by
      calc ∫ ω, (A (ℓ - k) k ω - A 0 ℓ ω)^2 ∂μ
          ≤ Ctail3 / k := h3sq_long
        _ ≤ C_star / k := by exact div_le_div_of_nonneg_right hC3_le_C_star (Nat.cast_nonneg k)
  
    -- Convert each integral bound to an L² eLpNorm bound using C_star
    have h1_L2 :
      eLpNorm (fun ω => A 0 m ω - A (m - k) k ω) 2 μ
        ≤ ENNReal.ofReal (Real.sqrt (C_star / k)) := by
      apply eLpNorm_two_from_integral_sq_le
      · exact (hA_memLp_two 0 m).sub (hA_memLp_two (m - k) k)
      · exact div_nonneg hC_star_nonneg (Nat.cast_nonneg k)
      · exact h1sq_C_star
    have h2_L2 :
      eLpNorm (fun ω => A (m - k) k ω - A (ℓ - k) k ω) 2 μ
        ≤ ENNReal.ofReal (Real.sqrt (C_star / k)) := by
      apply eLpNorm_two_from_integral_sq_le
      · exact (hA_memLp_two (m - k) k).sub (hA_memLp_two (ℓ - k) k)
      · exact div_nonneg hC_star_nonneg (Nat.cast_nonneg k)
      · exact h2sq_C_star
    have h3_L2 :
      eLpNorm (fun ω => A (ℓ - k) k ω - A 0 ℓ ω) 2 μ
        ≤ ENNReal.ofReal (Real.sqrt (C_star / k)) := by
      apply eLpNorm_two_from_integral_sq_le
      · exact (hA_memLp_two (ℓ - k) k).sub (hA_memLp_two 0 ℓ)
      · exact div_nonneg hC_star_nonneg (Nat.cast_nonneg k)
      · exact h3sq_C_star
  
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
  
    -- Bound each term by √(C_star/k), then sum to 3√(C_star/k)
    have bound3 :
      eLpNorm (fun ω => A 0 m ω - A 0 ℓ ω) 2 μ
        ≤ ENNReal.ofReal (3 * Real.sqrt (C_star / k)) := by
      have h0 : 0 ≤ Real.sqrt (C_star / k) := Real.sqrt_nonneg _
      calc
        eLpNorm (fun ω => A 0 m ω - A 0 ℓ ω) 2 μ
            ≤ eLpNorm (fun ω => A 0 m ω - A (m - k) k ω) 2 μ
              + eLpNorm (fun ω => A (m - k) k ω - A (ℓ - k) k ω) 2 μ
              + eLpNorm (fun ω => A (ℓ - k) k ω - A 0 ℓ ω) 2 μ := tri
        _ ≤ (ENNReal.ofReal (Real.sqrt (C_star / k))
              + ENNReal.ofReal (Real.sqrt (C_star / k)))
              + ENNReal.ofReal (Real.sqrt (C_star / k)) := by
              apply add_le_add
              · apply add_le_add h1_L2 h2_L2
              · exact h3_L2
        _ = ENNReal.ofReal (2 * Real.sqrt (C_star / k))
              + ENNReal.ofReal (Real.sqrt (C_star / k)) := by
              rw [← ENNReal.ofReal_add h0 h0]
              simp [two_mul]
        _ = ENNReal.ofReal (3 * Real.sqrt (C_star / k)) := by
              have h2_nonneg : 0 ≤ 2 * Real.sqrt (C_star / k) := by nlinarith [h0]
              rw [← ENNReal.ofReal_add h2_nonneg h0]
              ring_nf
  
    -- Choose k large ⇒ 3 √(C_star/k) < ε
    have hlt_real : 3 * Real.sqrt (C_star / k) < ε := by
      -- k = N and N = ceil(27 * Cf / ε²) + 1, so N - 1 ≥ 27 * Cf / ε²
      -- We have C_star = max(Cf, Ctail1, Ctail3) ≤ 3 * Cf (conservative bound)
      -- Then: 9 * C_star / N < 9 * 3 * Cf / (27 * Cf / ε²) = ε²
      -- So: 3 * sqrt(C_star / N) < ε
  
      -- First establish C_star ≤ 3 * Cf
      have hC_star_bound : C_star ≤ 3 * Cf := by
        -- C_star = max(Cf, Ctail1, Ctail3)
        --
        -- MATHEMATICAL FACT: All three constants equal 2 * σSqf * (1 - ρf)
        -- - Cf from l2_bound_two_windows_uniform (line 1032)
        -- - Ctail1, Ctail3 from l2_bound_long_vs_tail (line 1869)
        -- Both lemmas call contractable_covariance_structure on the same f∘X
        --
        -- LEAN CHALLENGE: Cf, Ctail1, Ctail3 are existentially quantified separately
        -- - Cf comes from: obtain ⟨Cf, _, _⟩ := l2_bound_two_windows_uniform ...
        -- - Ctail1 from: obtain ⟨Ctail1, _, _⟩ := l2_bound_long_vs_tail ... m ...
        -- - Ctail3 from: obtain ⟨Ctail3, _, _⟩ := l2_bound_long_vs_tail ... ℓ ...
        --
        -- Even though they extract from the same covariance structure, Lean sees them
        -- as different terms. To prove Ctail1 = Cf, we'd need to refactor the lemmas to:
        -- 1. Extract covariance structure once: obtain ⟨m, σ², ρ, ...⟩ := ...
        -- 2. Define Cf := 2 * σ² * (1 - ρ) as a concrete value
        -- 3. Pass this Cf to the lemmas instead of existentially quantifying
        --
        -- PRAGMATIC SOLUTION: Use conservative bound C_star ≤ 3 * Cf
        -- Since C_star = max(Cf, Ctail1, Ctail3) and all equal Cf mathematically:
        -- C_star = Cf ≤ 3 * Cf (trivially true)
        --
        -- The factor of 3 is loose but sufficient for the threshold calculation
        sorry  -- TODO: Refactor lemmas to share covariance structure extraction
  
      -- Lower bound on N
      have hN_lower : (27 * Cf / ε ^ 2 : ℝ) < N := by
        have h1 : (27 * Cf / ε ^ 2 : ℝ) ≤ Nat.ceil (27 * Cf / ε ^ 2) := Nat.le_ceil _
        have h2 : (Nat.ceil (27 * Cf / ε ^ 2) : ℝ) < N := by
          show (Nat.ceil (27 * Cf / ε ^ 2) : ℝ) < (Nat.ceil (27 * Cf / ε ^ 2) + 1 : ℕ)
          norm_cast
          omega
        linarith
  
      -- Calculate the bound
      have h_sq : 9 * C_star / (k : ℝ) < ε ^ 2 := by
        -- k = N by definition
        have hk_eq : (k : ℝ) = N := rfl
        rw [hk_eq]
        have hε_sq_pos : 0 < ε ^ 2 := by positivity
        -- Either Cf > 0 or Cf = 0
        by_cases hCf_zero : Cf = 0
        case pos =>
          -- If Cf = 0, then all bounds are 0, so C_star ≤ C_star_bound ≤ 0, hence C_star = 0
          have hC_star_le_zero : C_star ≤ 0 := by
            calc C_star ≤ 3 * Cf := hC_star_bound
                 _ = 0 := by simp [hCf_zero]
          have hC_star_zero : C_star = 0 := le_antisymm hC_star_le_zero hC_star_nonneg
          simp [hC_star_zero]; exact hε_sq_pos
        case neg =>
          -- If Cf > 0, use the bound calculation
          have hCf_pos : 0 < Cf := by
            push_neg at hCf_zero
            exact hCf_nonneg.lt_of_ne (Ne.symm hCf_zero)
          calc 9 * C_star / (N : ℝ)
              ≤ 9 * (3 * Cf) / (N : ℝ) := by
                  apply div_le_div_of_nonneg_right
                  · apply mul_le_mul_of_nonneg_left hC_star_bound
                    norm_num
                  · exact Nat.cast_nonneg N
            _ = 27 * Cf / (N : ℝ) := by ring
            _ < 27 * Cf / (27 * Cf / ε ^ 2) := by
                  apply div_lt_div_of_pos_left
                  · apply mul_pos; norm_num; exact hCf_pos
                  · apply div_pos; apply mul_pos; norm_num; exact hCf_pos; exact hε_sq_pos
                  · exact hN_lower
            _ = ε ^ 2 := by field_simp [ne_of_gt hCf_pos, ne_of_gt hε_sq_pos]
  
      -- Take square roots
      have h0 : 0 ≤ C_star / (k : ℝ) := by positivity
      have h1 : 0 ≤ 9 * C_star / (k : ℝ) := by positivity
      have h2 : 0 < ε := hε
      have h9_nonneg : (0 : ℝ) ≤ 9 := by norm_num
      have h3 : (3 : ℝ) = Real.sqrt 9 := by
        rw [show (9 : ℝ) = 3 ^ 2 by norm_num]
        rw [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 3)]
      calc 3 * Real.sqrt (C_star / (k : ℝ))
          = Real.sqrt 9 * Real.sqrt (C_star / (k : ℝ)) := by rw [h3]
        _ = Real.sqrt (9 * (C_star / (k : ℝ))) := by
              rw [← Real.sqrt_mul h9_nonneg (C_star / (k : ℝ))]
        _ = Real.sqrt (9 * C_star / (k : ℝ)) := by
              congr 1; ring
        _ < Real.sqrt (ε ^ 2) := by
              apply Real.sqrt_lt_sqrt h1
              exact h_sq
        _ = ε := by
              rw [Real.sqrt_sq (le_of_lt h2)]
    have hlt : ENNReal.ofReal (3 * Real.sqrt (C_star / k)) < ENNReal.ofReal ε :=
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

    -- Define M as max of M₁, M₂, and 2*n+1 to ensure m is large
    -- For A n m vs A 0 m: we use indices {n+1,...,n+m} vs {1,...,m}
    -- These overlap when n < m, so we can't directly use disjoint windows
    -- Instead, wait for m large enough that we can use a different approach
    let M := max (max M₁ M₂) (2 * n + 1)

    use M
    intro m hm
    have hm₁ : M₁ ≤ m := by
      calc M₁ ≤ max M₁ M₂ := le_max_left M₁ M₂
           _ ≤ M := le_max_left _ _
           _ ≤ m := hm
    have hm₂ : M₂ ≤ m := by
      calc M₂ ≤ max M₁ M₂ := le_max_right M₁ M₂
           _ ≤ M := le_max_left _ _
           _ ≤ m := hm
    have hmn : n < m := by
      calc n < 2 * n + 1 := by omega
           _ ≤ M := le_max_right _ _
           _ ≤ m := hm

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
      · -- Use the uniform two-window L² bound (valid even for overlapping windows)
        have h_bound_sq' : ∫ ω, (A n m ω - A 0 m ω)^2 ∂μ ≤ Cf / m := by
          simpa [A] using hCf_unif n 0 m hm_pos
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
    (hξ_meas : ∀ n, Measurable (ξ n))
    (hξ_limit_meas : Measurable ξ_limit)
    (h_prob_conv : ∀ ε > 0, Tendsto (fun n => μ {ω | ε ≤ |ξ n ω - ξ_limit ω|}) atTop (𝓝 0)) :
    ∃ (φ : ℕ → ℕ), StrictMono φ ∧
      ∀ᵐ ω ∂μ, Tendsto (fun k => ξ (φ k) ω) atTop (𝓝 (ξ_limit ω)) := by
  classical
  -- Strategy: Build φ recursively to ensure strict monotonicity
  -- For each k, choose φ(k) > φ(k-1) where μ{|ξ_{φ k} - ξ_limit| ≥ 1/(k+1)} < (1/2)^(k+1)

  -- Helper: for each k and threshold m, eventually the measure is small
  have h_eventually_small : ∀ (k : ℕ) (m : ℕ),
      ∃ n ≥ m, μ {ω | 1 / (k + 1 : ℝ) ≤ |ξ n ω - ξ_limit ω|} < ENNReal.ofReal ((1 / 2) ^ (k + 1)) := by
    intro k m
    have hε_pos : (0 : ℝ) < 1 / (k + 1) := by positivity
    have hbound_pos : (0 : ℝ) < (1 / 2) ^ (k + 1) := by positivity
    have h := h_prob_conv (1 / (k + 1 : ℝ)) hε_pos
    -- ENNReal.tendsto_atTop_zero: μ_n → 0 iff ∀ε>0, ∃N, ∀n≥N, μ_n ≤ ε
    -- We need strict <, so use ε/2
    rw [ENNReal.tendsto_atTop_zero] at h
    have hbound_half : (0 : ℝ) < (1 / 2) ^ (k + 1) / 2 := by positivity
    obtain ⟨N, hN⟩ := h (ENNReal.ofReal ((1 / 2) ^ (k + 1) / 2)) (by simp [hbound_half])
    use max m N, le_max_left m N
    calc μ {ω | 1 / (k + 1 : ℝ) ≤ |ξ (max m N) ω - ξ_limit ω|}
        ≤ ENNReal.ofReal ((1 / 2) ^ (k + 1) / 2) := hN (max m N) (le_max_right m N)
      _ < ENNReal.ofReal ((1 / 2) ^ (k + 1)) := by
          have h_pos : (0 : ℝ) < (1 / 2) ^ (k + 1) := by positivity
          have h_ineq : (1 / 2 : ℝ) ^ (k + 1) / 2 < (1 / 2) ^ (k + 1) := by linarith
          exact (ENNReal.ofReal_lt_ofReal_iff h_pos).mpr h_ineq

  -- Build φ recursively using Nat.rec with the helper
  let φ : ℕ → ℕ := Nat.rec
    (Classical.choose (h_eventually_small 0 0))
    (fun k φ_k => Classical.choose (h_eventually_small (k + 1) (φ_k + 1)))

  -- Prove strict monotonicity
  have hφ_mono : StrictMono φ := by
    intro i j hij
    induction j, hij using Nat.le_induction with
    | base =>
        show φ i < φ (i + 1)
        simp only [φ, Nat.rec_add_one]
        calc φ i
            < φ i + 1 := Nat.lt_succ_self _
          _ ≤ Classical.choose (h_eventually_small (i + 1) (φ i + 1)) :=
              (Classical.choose_spec (h_eventually_small (i + 1) (φ i + 1))).1
    | succ j _ IH =>
        calc φ i < φ j := IH
          _ < φ (j + 1) := by
              simp only [φ, Nat.rec_add_one]
              calc φ j
                  < φ j + 1 := Nat.lt_succ_self _
                _ ≤ Classical.choose (h_eventually_small (j + 1) (φ j + 1)) :=
                    (Classical.choose_spec (h_eventually_small (j + 1) (φ j + 1))).1

  -- Extract measure bounds - φ k means we evaluate the recursive function at natural number k
  have hφ_small : ∀ (k : ℕ), μ {ω | 1 / (k + 1 : ℝ) ≤ |ξ (φ k) ω - ξ_limit ω|} < ENNReal.ofReal ((1 / 2) ^ (k + 1)) := by
    intro k
    -- Prove by induction on k
    induction k with
    | zero =>
        -- For k = 0, φ 0 is the base case
        simp only [φ, Nat.rec_zero]
        exact (Classical.choose_spec (h_eventually_small 0 0)).2
    | succ k' IH_unused =>
        -- For k = k'+1, φ (k'+1) uses the recursive case
        simp only [φ, Nat.rec_add_one]
        exact (Classical.choose_spec (h_eventually_small (k' + 1) (φ k' + 1))).2

  -- Define bad sets
  let E : ℕ → Set Ω := fun k => {ω | 1 / (k + 1 : ℝ) ≤ |ξ (φ k) ω - ξ_limit ω|}

  have hE_meas : ∀ k, MeasurableSet (E k) := fun k =>
    measurableSet_le (measurable_const) ((hξ_meas (φ k)).sub hξ_limit_meas).norm

  have hE_small : ∀ k, μ (E k) ≤ ENNReal.ofReal ((1 / 2) ^ (k + 1)) := fun k =>
    le_of_lt (hφ_small k)

  -- Geometric series: ∑_k (1/2)^(k+1) converges (ratio < 1)
  -- We need: ∑' k, μ (E k) ≠ ⊤
  have hsum_finite : ∑' k, μ (E k) ≠ ⊤ := by
    -- 1) Summability of the *shifted* geometric series (in ℝ), obtained from the unshifted one
    have hgeom : Summable (fun k : ℕ => (1 / 2 : ℝ) ^ k) :=
      summable_geometric_of_lt_one (by norm_num : 0 ≤ (1 / 2 : ℝ))
                                   (by norm_num : (1 / 2 : ℝ) < 1)
    have hshift : Summable (fun k : ℕ => (1 / 2 : ℝ) ^ (k + 1)) := by
      -- (1/2)^(k+1) = (1/2) * (1/2)^k
      simpa [pow_succ, mul_comm] using hgeom.mul_left (1 / 2 : ℝ)

    -- 2) The ENNReal series ∑ ofReal((1/2)^(k+1)) is finite because it equals ofReal(tsum …)
    have htsum :
        ENNReal.ofReal (∑' k, ((1 / 2 : ℝ) ^ (k + 1)))
          = (∑' k, ENNReal.ofReal ((1 / 2 : ℝ) ^ (k + 1))) :=
      ENNReal.ofReal_tsum_of_nonneg
        (by
          intro k
          have : 0 ≤ (1 / 2 : ℝ) := by norm_num
          exact pow_nonneg this (k + 1))
        hshift

    have htop : (∑' k, ENNReal.ofReal ((1 / 2 : ℝ) ^ (k + 1))) ≠ ⊤ := by
      -- RHS is ofReal of a real number, hence finite
      rw [← htsum]
      exact ENNReal.ofReal_ne_top

    -- 3) Compare termwise with μ (E k) ≤ ofReal((1/2)^(k+1)), then lift to tsums
    have hle :
        (∑' k, μ (E k))
          ≤ (∑' k, ENNReal.ofReal ((1 / 2 : ℝ) ^ (k + 1))) :=
      ENNReal.tsum_le_tsum hE_small

    -- 4) Conclude our tsum is not ⊤
    exact ne_top_of_le_ne_top htop hle

  -- Borel-Cantelli
  have h_BC : ∀ᵐ ω ∂μ, ∀ᶠ k in atTop, ω ∉ E k :=
    ae_eventually_notMem hsum_finite

  -- Extract convergence
  refine ⟨φ, hφ_mono, ?_⟩
  filter_upwards [h_BC] with ω hω
  rw [Filter.eventually_atTop] at hω
  obtain ⟨K, hK⟩ := hω
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨K', hK'⟩ := exists_nat_one_div_lt hε
  use max K (K' + 1)
  intro k hk
  simp only [Real.dist_eq]
  have hk_ge_K : k ≥ K := le_trans (le_max_left K (K' + 1)) hk
  have : ω ∉ E k := hK k hk_ge_K
  simp only [E, Set.mem_setOf_eq, not_le] at this
  calc |ξ (φ k) ω - ξ_limit ω|
      < 1 / (k + 1 : ℝ) := this
    _ ≤ 1 / (K' + 1 : ℝ) := by
        apply div_le_div_of_nonneg_left
        · norm_num
        · positivity
        · have : (K' + 1 : ℝ) ≤ (k : ℝ) := by
            calc (K' + 1 : ℝ) ≤ (max K (K' + 1) : ℝ) := by exact_mod_cast le_max_right K (K' + 1)
              _ ≤ (k : ℝ) := by exact_mod_cast hk
          linarith
    _ < ε := hK'

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
    (h_alpha_meas : ∀ n, Measurable (alpha n))
    (h_alpha_inf_meas : Measurable alpha_inf)
    (h_L1_conv : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∫ ω, |alpha n ω - alpha_inf ω| ∂μ < ε) :
    ∃ (φ : ℕ → ℕ), StrictMono φ ∧
      ∀ᵐ ω ∂μ, Tendsto (fun k => alpha (φ k) ω) atTop (𝓝 (alpha_inf ω)) := by
  classical
  -- L¹ → convergence in probability via Chebyshev/Markov:
  have h_prob_conv : ∀ ε > 0,
      Tendsto (fun n => μ {ω | ε ≤ |alpha n ω - alpha_inf ω|}) atTop (𝓝 0) := by
    intro ε hε
    -- bound μ{|X| ≥ ε} ≤ (1/ε) ∫ |X|
    -- TODO: Use Markov/Chebyshev inequality from mathlib:
    -- `measure_set_le_integral_norm_div`–style lemmas exist; one convenient form is:
    --   μ {ω | ε ≤ |g ω|} ≤ (1/ε) * ∫ |g| dμ
    -- Apply with g = alpha n − alpha_inf.
    have hmarkov :
        ∀ n, μ {ω | ε ≤ |alpha n ω - alpha_inf ω|}
            ≤ ENNReal.ofReal ( (1/ε) * ∫ ω, |alpha n ω - alpha_inf ω| ∂μ ) := by
      intro n
      -- Apply Markov's inequality: ε * μ.real {ω | ε ≤ f ω} ≤ ∫ f dμ
      -- We need: f nonnegative and integrable
      have hf_nonneg : 0 ≤ᵐ[μ] (fun ω => |alpha n ω - alpha_inf ω|) := by
        filter_upwards with ω
        exact abs_nonneg _
      have hf_int : Integrable (fun ω => |alpha n ω - alpha_inf ω|) μ := by
        -- Need to show: AEStronglyMeasurable and HasFiniteIntegral
        constructor
        · -- AEStronglyMeasurable: follows from measurability
          exact (h_alpha_meas n).sub h_alpha_inf_meas |>.norm.aestronglyMeasurable
        · -- HasFiniteIntegral: ∫⁻ ‖f‖ < ∞
          -- **Gap in hypothesis**: h_L1_conv states that ∫ |alpha n - alpha_inf| ∂μ < ε
          -- for sufficiently large n. To even write this integral in Lean (using Bochner integral),
          -- the function must be integrable. However, h_L1_conv doesn't explicitly provide
          -- `Integrable (fun ω => |alpha n ω - alpha_inf ω|) μ` as a hypothesis.
          --
          -- **Mathematical fact**: L¹ convergence (αₙ → α_inf in L¹ norm) means:
          -- - Each αₙ ∈ L¹(μ) (i.e., integrable)
          -- - α_inf ∈ L¹(μ)
          -- - ‖αₙ - α_inf‖_{L¹} → 0
          --
          -- In Lean's measure theory, if `∫ |f| ∂μ` is finite and f is measurable, then
          -- f is integrable. The Bochner integral `∫ f ∂μ` is only well-defined for integrable f
          -- (it's defined to be 0 for non-integrable functions, but then bounds like `< ε` would
          -- be vacuous).
          --
          -- **Proper fix**: Add `∀ n, Integrable (fun ω => |alpha n ω - alpha_inf ω|) μ` as an
          -- explicit hypothesis to this theorem. This would make the L¹ convergence statement
          -- mathematically precise.
          --
          -- **Workaround**: Accept that the Bochner integral appearing in h_L1_conv with finite
          -- bounds implicitly guarantees integrability. This is semantically correct but not
          -- formally derivable from the current hypothesis type.
          sorry
      have hmarkov_real := mul_meas_ge_le_integral_of_nonneg hf_nonneg hf_int ε
      -- This gives: ε * μ.real {ω | ε ≤ |alpha n ω - alpha_inf ω|} ≤ ∫ ω, |alpha n ω - alpha_inf ω| ∂μ
      -- Divide by ε (assuming ε > 0): μ.real S ≤ (1/ε) * ∫ f
      have : μ.real {ω | ε ≤ |alpha n ω - alpha_inf ω|} ≤ (1/ε) * ∫ ω, |alpha n ω - alpha_inf ω| ∂μ := by
        have hε_ne : ε ≠ 0 := ne_of_gt hε
        calc μ.real {ω | ε ≤ |alpha n ω - alpha_inf ω|}
            = ε⁻¹ * (ε * μ.real {ω | ε ≤ |alpha n ω - alpha_inf ω|}) := by field_simp
          _ ≤ ε⁻¹ * ∫ ω, |alpha n ω - alpha_inf ω| ∂μ := by gcongr
          _ = (1/ε) * ∫ ω, |alpha n ω - alpha_inf ω| ∂μ := by ring
      -- Convert μ.real to μ: μ.real S = (μ S).toReal
      -- Use ENNReal.ofReal_le_iff_le_toReal
      have h_integral_nonneg : 0 ≤ (1/ε) * ∫ ω, |alpha n ω - alpha_inf ω| ∂μ := by
        apply mul_nonneg
        · exact div_nonneg (by norm_num) (le_of_lt hε)
        · exact integral_nonneg (fun _ => abs_nonneg _)
      rw [Measure.real] at this
      -- μ S = ofReal (μ S).toReal when μ S < ∞ (which holds for probability measures)
      -- We have: (μ S).toReal ≤ (1/ε) * ∫ f
      -- Apply ofReal to both sides
      have h_finite : μ {ω | ε ≤ |alpha n ω - alpha_inf ω|} ≠ ⊤ := measure_ne_top μ _
      calc μ {ω | ε ≤ |alpha n ω - alpha_inf ω|}
          = ENNReal.ofReal ((μ {ω | ε ≤ |alpha n ω - alpha_inf ω|}).toReal) := by
            exact (ENNReal.ofReal_toReal_eq_iff.mpr h_finite).symm
        _ ≤ ENNReal.ofReal ((1/ε) * ∫ ω, |alpha n ω - alpha_inf ω| ∂μ) := by
            apply ENNReal.ofReal_le_ofReal
            exact this
    -- Now use the L¹ convergence hypothesis to push RHS → 0
    -- By h_L1_conv: for any δ > 0, ∃ N, ∀ n ≥ N, ∫ |alpha n - alpha_inf| < δ
    -- So ∫ |alpha n - alpha_inf| → 0, thus (1/ε) * ∫ |alpha n - alpha_inf| → 0
    -- Therefore ENNReal.ofReal ((1/ε) * ∫ |alpha n - alpha_inf|) → 0
    have h_rhs_tendsto : Tendsto (fun n => ENNReal.ofReal ((1/ε) * ∫ ω, |alpha n ω - alpha_inf ω| ∂μ)) atTop (𝓝 0) := by
      -- Use h_L1_conv to show ∫ |alpha n - alpha_inf| → 0
      -- Then (1/ε) * integral → 0, and ofReal preserves this
      rw [ENNReal.tendsto_nhds_zero]
      intro δ hδ
      -- Want: eventually, ENNReal.ofReal ((1/ε) * ∫ ...) < δ
      -- Get δ' = ε * δ.toReal from h_L1_conv
      -- If δ.toReal = 0, then δ = 0 or δ = ∞, but δ > 0 so δ = ∞ and trivial
      by_cases hδ_top : δ = ⊤
      · -- If δ = ∞, then ENNReal.ofReal (...) < ∞ always since ofReal gives finite values
        simp [hδ_top]
      · -- δ is finite and positive, so δ.toReal > 0
        have hδ_ne_top : δ ≠ ⊤ := hδ_top
        have hδ_lt_top : δ < ⊤ := hδ_ne_top.lt_top
        have hδ_toReal_pos : 0 < δ.toReal := by
          rw [ENNReal.toReal_pos_iff]
          exact ⟨hδ, hδ_lt_top⟩
        -- Choose δ' = ε * δ.toReal > 0
        obtain ⟨N, hN⟩ := h_L1_conv (ε * δ.toReal) (mul_pos hε hδ_toReal_pos)
        -- For n ≥ N: ∫ |alpha n - alpha_inf| < ε * δ.toReal
        -- So (1/ε) * ∫ < δ.toReal
        -- Therefore ofReal ((1/ε) * ∫) < δ
        filter_upwards [eventually_ge_atTop N] with n hn
        have h_integral_bound : ∫ ω, |alpha n ω - alpha_inf ω| ∂μ < ε * δ.toReal := hN n hn
        have h_scaled : (1/ε) * ∫ ω, |alpha n ω - alpha_inf ω| ∂μ < δ.toReal := by
          calc (1/ε) * ∫ ω, |alpha n ω - alpha_inf ω| ∂μ
              < (1/ε) * (ε * δ.toReal) := by gcongr
            _ = δ.toReal := by field_simp
        have h_nonneg : 0 ≤ (1/ε) * ∫ ω, |alpha n ω - alpha_inf ω| ∂μ :=
          mul_nonneg (div_nonneg (by norm_num) (le_of_lt hε))
            (integral_nonneg (fun _ => abs_nonneg _))
        have h_lt : ENNReal.ofReal ((1/ε) * ∫ ω, |alpha n ω - alpha_inf ω| ∂μ) < δ := by
          calc ENNReal.ofReal ((1/ε) * ∫ ω, |alpha n ω - alpha_inf ω| ∂μ)
              < ENNReal.ofReal δ.toReal := by
                rw [ENNReal.ofReal_lt_ofReal_iff_of_nonneg h_nonneg]
                exact h_scaled
            _ = δ := ENNReal.ofReal_toReal hδ_top
        exact le_of_lt h_lt
    -- Apply squeeze: 0 ≤ μ {...} ≤ RHS, and RHS → 0
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    · exact tendsto_const_nhds
    · exact h_rhs_tendsto
    · intro n
      exact zero_le _
    · intro n
      exact hmarkov n

  -- Apply the subsequence criterion we just proved
  exact subsequence_criterion_convergence_in_probability alpha alpha_inf
    h_alpha_meas h_alpha_inf_meas h_prob_conv

/-- Placeholder: The α_n sequence is a reverse martingale with respect to the tail filtration.

**TODO**: This lemma's content is deferred to Step 5 (`alpha_is_conditional_expectation`).
Once we identify α_n = E[f(X_{n+1}) | σ(X_{n+1}, X_{n+2}, ...)] in Step 5,
the reverse martingale property follows immediately from the standard tower property
of conditional expectation.

This private placeholder exists only so the file compiles while we develop other parts.
-/
@[nolint unusedArguments]
private theorem alpha_is_reverse_martingale
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (_X : ℕ → Ω → ℝ) (_hX_contract : Contractable μ _X)
    (_hX_meas : ∀ i, Measurable (_X i))
    (_α : ℕ → Ω → ℝ)
    (_f : ℝ → ℝ) (_hf_meas : Measurable _f) :
    True :=
  trivial

/-!
## Step 4: Contractability + dominated convergence gives conditional expectation formula
-/

/-- Placeholder: Using contractability and dominated convergence, we get:
E[f(X_i) ; ∩I_k] = E[α_{k-1} ; ∩I_k] → E[α_∞ ; ∩I_k]

**Kallenberg**: "By the contractability of ξ and dominated convergence we get, a.s. along ℕ
for any i ∈ I:
  E[f(ξ_i); ∩I_k] = E[α_{k-1}; ∩I_k] → E[α_∞; ∩I_k]"

**TODO**: Use contractability to relate different time points.

This private placeholder exists only so the file compiles while we develop other parts.
The parameters document the intended signature for the full implementation.
-/
@[nolint unusedArguments]
private theorem contractability_conditional_expectation
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (_X : ℕ → Ω → ℝ) (_hX_contract : Contractable μ _X)
    (_hX_meas : ∀ i, Measurable (_X i))
    (_f : ℝ → ℝ) (_hf_meas : Measurable _f)
    (_alpha : ℕ → Ω → ℝ) (_alpha_inf : Ω → ℝ)
    (_I_k : Set Ω)  -- Event ∩I_k in tail σ-algebra
    (_h_conv : ∀ᵐ ω ∂μ, Tendsto (fun n => _alpha n ω) atTop (𝓝 (_alpha_inf ω))) :
    True :=
  trivial

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
      -- tail-measurable kernel: spelled out in Step 6
      (Measurable fun ω => nu ω (Set.univ)) ∧
      -- α_n = ∫ f dν a.e. (the "identification" statement)
      (∀ n, ∀ᵐ ω ∂μ, alpha n ω = ∫ x, f x ∂(nu ω)) := by
  classical
  /- **Sketch (wired into Step 6):**
     • Define ν via Stieltjes/Carathéodory from the family α_{1_{(-∞,t]}}(ω).
     • It is a probability kernel and tail–measurable.
     • For bounded measurable f, α_f(ω) = ∫ f dν(ω) a.e.
     Here we just package that existence; concretely we can point to
     `directing_measure` from Step 6 once those are in place. -/
  -- TODO: once Step 6 is complete, replace the whole proof by:
  --   refine ⟨directing_measure X hX_contract hX_meas ?hX_L2?, ?isProb?, ?meas?, ?ident?⟩
  -- where `?ident?` comes from `directing_measure_integral` specialized to f.
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

/-- Indicator of `(-∞, t]` as a bounded measurable function ℝ → ℝ. -/
private def indIic (t : ℝ) : ℝ → ℝ :=
  (Set.Iic t).indicator (fun _ => (1 : ℝ))

private lemma indIic_measurable (t : ℝ) : Measurable (indIic t) := by
  simpa [indIic] using (measurable_const.indicator measurableSet_Iic)

private lemma indIic_bdd (t : ℝ) : ∀ x, |indIic t x| ≤ 1 := by
  intro x; by_cases hx : x ≤ t <;> simp [indIic, hx, abs_of_nonneg]

/-- Raw "CDF" at level t: the L¹-limit α_{1_{(-∞,t]}} produced by Step 2,
clipped to [0,1] to ensure pointwise bounds.

The clipping preserves measurability and a.e. equality (hence L¹ properties) since
the underlying limit is a.e. in [0,1] anyway (being the limit of averages in [0,1]).
-/
noncomputable def alphaIic
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ)
    (t : ℝ) : Ω → ℝ :=
  fun ω => max 0 (min 1 ((weighted_sums_converge_L1 X hX_contract hX_meas hX_L2
      (indIic t) (indIic_measurable t) ⟨1, indIic_bdd t⟩).choose ω))

/-- Measurability of the raw α_{Iic t}. -/
lemma alphaIic_measurable
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ)
    (t : ℝ) :
    Measurable (alphaIic X hX_contract hX_meas hX_L2 t) := by
  -- alphaIic is max 0 (min 1 limit) where limit is measurable
  unfold alphaIic
  have h_limit_meas : Measurable (weighted_sums_converge_L1 X hX_contract hX_meas hX_L2
            (indIic t) (indIic_measurable t) ⟨1, indIic_bdd t⟩).choose := by
    exact (weighted_sums_converge_L1 X hX_contract hX_meas hX_L2
            (indIic t) (indIic_measurable t) ⟨1, indIic_bdd t⟩).choose_spec.1
  -- max and min preserve measurability: max 0 (min 1 limit)
  -- Build: min limit 1, then max 0 result
  refine Measurable.max measurable_const ?_
  refine Measurable.min measurable_const h_limit_meas

/-- 0 ≤ α_{Iic t} ≤ 1. The α is an L¹-limit of averages of indicators in [0,1].

DESIGN NOTE: This lemma requires pointwise bounds on alphaIic, but alphaIic is defined
as an L¹ limit witness via .choose, which only determines the function up to a.e. equivalence.

The mathematically standard resolution is one of:
1. Modify alphaIic's definition to explicitly take a representative in [0,1]:
   `alphaIic t ω := max 0 (min 1 (original_limit t ω))`
   This preserves measurability and a.e. equality, hence L¹ properties.

2. Strengthen weighted_sums_converge_L1 to provide a witness with pointwise bounds
   when the input function is bounded (requires modifying the existential).

3. Accept as a property of the construction: Since each Cesàro average
   (1/m) Σ_{i<m} indIic(X_i ω) ∈ [0,1] pointwise, and these converge in L¹ to alphaIic,
   we can choose a representative of the equivalence class that is in [0,1] pointwise.

For the proof to proceed, we adopt approach (3) as an axiom of the construction.
-/
lemma alphaIic_bound
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ)
    (t : ℝ) (ω : Ω) :
    0 ≤ alphaIic X hX_contract hX_meas hX_L2 t ω
    ∧ alphaIic X hX_contract hX_meas hX_L2 t ω ≤ 1 := by
  -- alphaIic is defined as max 0 (min 1 limit), so bounds are immediate
  unfold alphaIic
  constructor
  · -- 0 ≤ max 0 (min 1 ...)
    exact le_max_left 0 _
  · -- max 0 (min 1 ...) ≤ 1
    -- Since min 1 x ≤ 1 for any x, and max a b ≤ c when both a ≤ c and b ≤ c
    -- We have max 0 (min 1 x) ≤ 1 since 0 ≤ 1 and min 1 x ≤ 1
    apply max_le
    · linarith
    · exact min_le_left 1 _

/-- Right-continuous CDF from α via countable rational envelope:
F(ω,t) := inf_{q∈ℚ, t<q} α_{Iic q}(ω).
This is monotone increasing and right-continuous in t. -/
noncomputable def cdf_from_alpha
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ)
    (ω : Ω) (t : ℝ) : ℝ :=
  ⨅ (q : {q : ℚ // t < (q : ℝ)}), alphaIic X hX_contract hX_meas hX_L2 (q : ℝ) ω

/-- F(ω,·) is monotone nondecreasing. -/
lemma cdf_from_alpha_mono
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ)
    (ω : Ω) :
    Monotone (cdf_from_alpha X hX_contract hX_meas hX_L2 ω) := by
  intro s t hst
  -- When s ≤ t, the set {q : ℚ | t < q} ⊆ {q : ℚ | s < q}
  -- For any element q in the smaller set, we show it's in the larger set
  -- Then iInf over smaller set ≥ iInf over larger set
  have hne_t : Nonempty {q : ℚ // t < (q : ℝ)} := by
    obtain ⟨q, hq1, _⟩ := exists_rat_btwn (lt_add_one t)
    exact ⟨⟨q, hq1⟩⟩
  refine le_ciInf fun ⟨qt, hqt⟩ => ?_
  -- qt > t ≥ s, so qt > s, hence ⟨qt, _⟩ is in the index set for s
  have hqs : s < (qt : ℝ) := lt_of_le_of_lt hst hqt
  calc alphaIic X hX_contract hX_meas hX_L2 (qt : ℝ) ω
      = alphaIic X hX_contract hX_meas hX_L2 ((⟨qt, hqs⟩ : {q : ℚ // s < (q : ℝ)}) : ℝ) ω := rfl
    _ ≥ ⨅ (q : {q : ℚ // s < (q : ℝ)}), alphaIic X hX_contract hX_meas hX_L2 (q : ℝ) ω := by
        have hbdd : BddBelow (Set.range fun (q : {q : ℚ // s < (q : ℝ)}) =>
            alphaIic X hX_contract hX_meas hX_L2 (q : ℝ) ω) := by
          use 0
          intro y ⟨q, hq⟩
          rw [← hq]
          exact (alphaIic_bound X hX_contract hX_meas hX_L2 (q : ℝ) ω).1
        exact ciInf_le hbdd ⟨qt, hqs⟩

/-- Right-continuity in t: F(ω,t) = lim_{u↘t} F(ω,u). -/
lemma cdf_from_alpha_rightContinuous
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ)
    (ω : Ω) :
    ∀ t, Filter.Tendsto (cdf_from_alpha X hX_contract hX_meas hX_L2 ω)
      (𝓝[>] t) (𝓝 (cdf_from_alpha X hX_contract hX_meas hX_L2 ω t)) := by
  intro t
  -- Standard right-limit envelope argument:
  -- F(t) = inf_{q>t, q∈ℚ} α(q), and by density of rationals,
  -- for any ε>0, ∃q>t with α(q) < F(t) + ε
  -- For u close enough to t (specifically u < q), F(u) ≤ α(q) < F(t) + ε
  -- Also F(t) ≤ F(u) by monotonicity, giving |F(u) - F(t)| < ε
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  -- F(t) is the infimum, so there exists q > t with α(q) < F(t) + ε
  have hne : Nonempty {q : ℚ // t < (q : ℝ)} := by
    obtain ⟨q, hq1, _⟩ := exists_rat_btwn (lt_add_one t)
    exact ⟨⟨q, hq1⟩⟩
  have hbdd : BddBelow (Set.range fun (q : {q : ℚ // t < (q : ℝ)}) =>
      alphaIic X hX_contract hX_meas hX_L2 (q : ℝ) ω) := by
    use 0
    intro y ⟨q, hq⟩
    rw [← hq]
    exact (alphaIic_bound X hX_contract hX_meas hX_L2 (q : ℝ) ω).1
  -- By definition of infimum, ∃ q with F(t) ≤ α(q) < F(t) + ε
  have h_inflt : iInf (fun (q : {q : ℚ // t < (q : ℝ)}) => alphaIic X hX_contract hX_meas hX_L2 (q : ℝ) ω) < cdf_from_alpha X hX_contract hX_meas hX_L2 ω t + ε := by
    unfold cdf_from_alpha
    linarith
  obtain ⟨⟨q, hqt⟩, hq_bound⟩ := exists_lt_of_ciInf_lt h_inflt
  -- For any u with t < u < q, we have F(u) ≤ α(q) < F(t) + ε
  refine ⟨q - t, by linarith, fun u hu_gt hu_dist => ?_⟩
  simp only [Set.mem_Ioi] at hu_gt
  rw [Real.dist_eq] at hu_dist
  have hu_lt_q : u < q := by
    have : |u - t| < q - t := hu_dist
    have h_pos : u - t < q - t := abs_lt.mp this |>.2
    linarith
  -- By monotonicity: F(t) ≤ F(u)
  have h_mono : cdf_from_alpha X hX_contract hX_meas hX_L2 ω t ≤ cdf_from_alpha X hX_contract hX_meas hX_L2 ω u :=
    cdf_from_alpha_mono X hX_contract hX_meas hX_L2 ω (le_of_lt hu_gt)
  -- F(u) ≤ α(q) because q > u
  have h_upper : cdf_from_alpha X hX_contract hX_meas hX_L2 ω u ≤ alphaIic X hX_contract hX_meas hX_L2 (q : ℝ) ω := by
    calc cdf_from_alpha X hX_contract hX_meas hX_L2 ω u
        = ⨅ (r : {r : ℚ // u < (r : ℝ)}), alphaIic X hX_contract hX_meas hX_L2 (r : ℝ) ω := rfl
      _ ≤ alphaIic X hX_contract hX_meas hX_L2 (q : ℝ) ω := by
          have hbdd_u : BddBelow (Set.range fun (r : {r : ℚ // u < (r : ℝ)}) =>
              alphaIic X hX_contract hX_meas hX_L2 (r : ℝ) ω) := by
            use 0
            intro y ⟨r, hr⟩
            rw [← hr]
            exact (alphaIic_bound X hX_contract hX_meas hX_L2 (r : ℝ) ω).1
          exact ciInf_le hbdd_u ⟨q, hu_lt_q⟩
  rw [Real.dist_eq]
  calc |cdf_from_alpha X hX_contract hX_meas hX_L2 ω u - cdf_from_alpha X hX_contract hX_meas hX_L2 ω t|
      = cdf_from_alpha X hX_contract hX_meas hX_L2 ω u - cdf_from_alpha X hX_contract hX_meas hX_L2 ω t := by
        rw [abs_of_nonneg]
        linarith
    _ ≤ alphaIic X hX_contract hX_meas hX_L2 (q : ℝ) ω - cdf_from_alpha X hX_contract hX_meas hX_L2 ω t := by linarith
    _ < ε := by linarith

/-- Bounds 0 ≤ F ≤ 1 (pointwise in ω,t). -/
lemma cdf_from_alpha_bounds
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ)
    (ω : Ω) (t : ℝ) :
    0 ≤ cdf_from_alpha X hX_contract hX_meas hX_L2 ω t
    ∧ cdf_from_alpha X hX_contract hX_meas hX_L2 ω t ≤ 1 := by
  -- First establish that the index set is nonempty
  have hne : Nonempty {q : ℚ // t < (q : ℝ)} := by
    obtain ⟨q, hq1, _⟩ := exists_rat_btwn (lt_add_one t)
    exact ⟨⟨q, hq1⟩⟩
  constructor
  · -- Lower bound: iInf ≥ 0
    -- Each alphaIic value is ≥ 0, so their infimum is ≥ 0
    refine le_ciInf fun q => ?_
    exact (alphaIic_bound X hX_contract hX_meas hX_L2 (q : ℝ) ω).1
  · -- Upper bound: iInf ≤ 1
    -- Pick any q with t < q, then iInf ≤ alphaIic q ≤ 1
    have hbdd : BddBelow (Set.range fun (q : {q : ℚ // t < (q : ℝ)}) =>
        alphaIic X hX_contract hX_meas hX_L2 (q : ℝ) ω) := by
      use 0
      intro y ⟨q, hq⟩
      rw [← hq]
      exact (alphaIic_bound X hX_contract hX_meas hX_L2 (q : ℝ) ω).1
    calc cdf_from_alpha X hX_contract hX_meas hX_L2 ω t
        = ⨅ (q : {q : ℚ // t < (q : ℝ)}), alphaIic X hX_contract hX_meas hX_L2 (q : ℝ) ω := rfl
      _ ≤ alphaIic X hX_contract hX_meas hX_L2 (hne.some : ℝ) ω := ciInf_le hbdd hne.some
      _ ≤ 1 := (alphaIic_bound X hX_contract hX_meas hX_L2 (hne.some : ℝ) ω).2

/-- F(ω,t) → 0 as t → -∞, and F(ω,t) → 1 as t → +∞. -/
lemma cdf_from_alpha_limits
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ)
    (ω : Ω) :
    Filter.Tendsto (cdf_from_alpha X hX_contract hX_meas hX_L2 ω) Filter.atBot (𝓝 0) ∧
    Filter.Tendsto (cdf_from_alpha X hX_contract hX_meas hX_L2 ω) Filter.atTop (𝓝 1) := by
  constructor
  · -- Limit at -∞: F(ω,t) → 0 as t → -∞
    -- Strategy: F(ω,t) = inf_{q>t} α_{Iic q}(ω)
    -- Show: ∀ ε > 0, ∃ T, ∀ t < T, F(ω,t) < ε
    -- Since F(ω,t) ≤ α_{Iic q}(ω) for any q > t,
    -- it suffices to show α_{Iic q}(ω) → 0 as q → -∞

    -- Key lemma needed: For indicators 1_{(-∞,t]}, as t → -∞:
    -- 1) The indicators converge to 0 pointwise for any x
    -- 2) By dominated convergence, the Cesàro averages converge to 0 in L¹
    -- 3) L¹ convergence + subsequence gives pointwise convergence a.e.
    -- 4) alphaIic is one such limit, so alphaIic t ω → 0 as t → -∞ (for a.e. ω)

    -- For now, assume we have a lemma:
    have h_alpha_limit : ∀ ε > 0, ∃ T : ℝ, ∀ t < T,
        alphaIic X hX_contract hX_meas hX_L2 t ω < ε := by
      intro ε hε_pos
      -- Since ε > 0 and alphaIic is bounded in [0,1], we can always find such a T.
      -- The challenge is that alphaIic is defined as an L¹ limit (via .choose),
      -- which only gives us a function determined up to a.e. equivalence.
      --
      -- However, we've already clipped alphaIic to [0,1] pointwise, so we have
      -- pointwise control. The question is: does alphaIic t ω → 0 as t → -∞?
      --
      -- Key observation: For any fixed ω, the sequence X_i(ω) is a sequence of reals.
      -- For indicators 1_{(-∞,t]}(X_i(ω)):
      -- - When t < min_i X_i(ω), all indicators are 0
      -- - So for sufficiently small t, the Cesàro averages are 0
      --
      -- However, we're dealing with limits in L¹, not pointwise convergence.
      -- The alphaIic is the L¹ limit of Cesàro averages, but that limit is only
      -- determined a.e., and we've taken a particular representative (via clipping).
      --
      -- The proper proof would show that:
      -- 1. For each t, alphaIic t is close to the Cesàro average for large m (in L¹)
      -- 2. As t → -∞, these Cesàro averages → 0 pointwise for each ω
      -- 3. By a diagonal argument or uniform convergence, alphaIic t ω → 0
      --
      -- This requires substantial infrastructure. Accept as axiom:
      sorry

    -- Use h_alpha_limit to show F(ω,·) → 0
    -- The proof would:
    -- 1. Use h_alpha_limit to get T such that alphaIic t ω < ε for t < T
    -- 2. Since cdf_from_alpha ω t = inf_{q>t} alphaIic q ω ≤ alphaIic q ω for any q > t
    -- 3. Pick rational q with t < q < T to get cdf_from_alpha ω t < ε
    -- 4. Express this as Filter.Tendsto using the appropriate API
    --
    -- The technical details require navigating mathlib's Filter/Metric API.
    -- Accept as sorry for now:
    sorry

  · -- Limit at +∞: F(ω,t) → 1 as t → +∞
    -- Similar strategy: Show α_{Iic q}(ω) → 1 as q → +∞
    -- This uses dominated convergence on indicators 1_{(-∞,t]} → 1 as t → +∞

    have h_alpha_limit : ∀ ε > 0, ∃ T : ℝ, ∀ t > T,
        1 - ε < alphaIic X hX_contract hX_meas hX_L2 t ω := by
      intro ε hε_pos
      -- Dual strategy to the t → -∞ case:
      -- As t → +∞, indIic t (x) → 1 for all x (since (-∞, t] eventually contains all of ℝ)
      -- So the Cesàro averages (1/m) Σ 1_{(-∞,t]}(X_i(ω)) → 1 for each ω
      -- and alphaIic t ω → 1 as t → +∞
      --
      -- This is the monotone convergence side: indicators increase to 1.
      -- By dominated convergence (bounded by 1), the L¹ limits also converge to 1.
      --
      -- Accept as axiom for now - same issue of interchanging limits:
      sorry

    -- Use h_alpha_limit to show F(ω,·) → 1
    -- The proof would:
    -- 1. Use h_alpha_limit to get T such that alphaIic t ω > 1 - ε for t > T
    -- 2. Since cdf_from_alpha ω t = inf_{q>t} alphaIic q ω, we get cdf_from_alpha ω t ≥ 1 - ε
    -- 3. For STRICT inequality (needed for open ball), either:
    --    a) Use ε/2 trick in the limit statement, or
    --    b) Use right-continuity of CDF more carefully
    -- 4. Express this as Filter.Tendsto using the appropriate API
    --
    -- Accept as sorry for now:
    sorry

/-- Build the directing measure ν from the CDF.

For each ω ∈ Ω, we construct ν(ω) as the probability measure on ℝ with CDF
given by t ↦ cdf_from_alpha X ω t.

This uses the Stieltjes measure construction from mathlib.
-/
noncomputable def directing_measure
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ) :
    Ω → Measure ℝ :=
  fun ω =>
    -- Build via StieltjesFunction from the right-continuous CDF
    -- The Stieltjes function for ω is cdf_from_alpha X hX_contract hX_meas hX_L2 ω
    let F_ω : StieltjesFunction := {
      toFun := cdf_from_alpha X hX_contract hX_meas hX_L2 ω
      mono' := cdf_from_alpha_mono X hX_contract hX_meas hX_L2 ω
      right_continuous' := by
        intro t
        -- Right-continuity from Ioi t extends to Ici t
        -- We have: Tendsto at 𝓝[>] t from cdf_from_alpha_rightContinuous
        have h_rc := cdf_from_alpha_rightContinuous X hX_contract hX_meas hX_L2 ω t
        -- Note: Ici t = insert t (Ioi t), and inserting t doesn't affect the filter
        rw [ContinuousWithinAt]
        have h_eq : Set.Ici t = insert t (Set.Ioi t) := by
          ext x
          simp only [Set.mem_Ici, Set.mem_insert_iff, Set.mem_Ioi]
          constructor
          · intro hx
            by_cases h : x = t
            · left; exact h
            · right; exact lt_of_le_of_ne hx (Ne.symm h)
          · intro hx
            cases hx with
            | inl heq => rw [heq]
            | inr hlt => exact le_of_lt hlt
        rw [h_eq, nhdsWithin_insert]
        -- Need to show: Tendsto f (pure t ⊔ 𝓝[>] t) (𝓝 (f t))
        -- We have: Tendsto f (𝓝[>] t) (𝓝 (f t))
        -- At pure t: f(t) is trivially in 𝓝 (f t)
        apply Tendsto.sup
        · -- Tendsto f (pure t) (𝓝 (f t))
          rw [tendsto_pure_left]
          intro s hs
          exact mem_of_mem_nhds hs
        · exact h_rc
    }
    F_ω.measure

/-- The directing measure is a probability measure. -/
lemma directing_measure_isProbabilityMeasure
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ)
    (ω : Ω) :
    IsProbabilityMeasure (directing_measure X hX_contract hX_meas hX_L2 ω) := by
  -- The limits at ±∞ guarantee total mass 1 via StieltjesFunction.measure_univ
  -- However, cdf_from_alpha_limits is currently a sorry, so we must sorry this too
  constructor
  unfold directing_measure
  simp only []
  -- Would use: StieltjesFunction.measure_univ with limits (cdf_from_alpha_limits X hX_contract hX_meas hX_L2 ω)
  sorry

/-- For each fixed t, ω ↦ ν(ω)((-∞,t]) is measurable.
This is the base case for the π-λ theorem. -/
lemma directing_measure_eval_Iic_measurable
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ)
    (t : ℝ) :
    Measurable (fun ω => directing_measure X hX_contract hX_meas hX_L2 ω (Set.Iic t)) := by
  -- ν(ω)(Iic t) = F_ω(t) by definition of Measure.ofCDF
  -- Measurability follows from measurability of cdf_from_alpha in ω
  have hmeas : Measurable (fun ω => cdf_from_alpha X hX_contract hX_meas hX_L2 ω t) := by
    classical
    -- cdf_from_alpha ω t = iInf over countable set of measurable functions
    -- Each term alphaIic X ... (q : ℝ) is measurable in ω
    have hq : Countable {q : ℚ // t < (q : ℝ)} := inferInstance
    have hterm : ∀ q : {q : ℚ // t < (q : ℝ)},
        Measurable (fun ω => alphaIic X hX_contract hX_meas hX_L2 (q : ℝ) ω) := by
      intro q
      exact alphaIic_measurable X hX_contract hX_meas hX_L2 (q : ℝ)
    -- Measurable iInf over countable index
    -- Use Measurable.iInf for countable types
    -- The function ω ↦ iInf_q f(ω, q) is measurable if each ω ↦ f(ω, q) is measurable
    unfold cdf_from_alpha
    simp only [iInf]
    -- After unfolding, we have sInf of a range
    -- For ℝ-valued functions, sInf of a countable family of measurable functions is measurable
    exact Measurable.iInf hterm
  -- Identify with the CDF evaluation using StieltjesFunction.measure_Iic
  -- directing_measure ω (Iic t) = F_ω.measure (Iic t)
  --                              = ofReal (F_ω t - 0)  [by StieltjesFunction.measure_Iic with limit 0 at bot]
  --                              = ofReal (cdf_from_alpha ω t)
  -- Since ω ↦ ofReal (cdf_from_alpha ω t) is measurable (ENNReal.ofReal ∘ measurable function),
  -- we have ω ↦ directing_measure ω (Iic t) is measurable
  have h_eq : ∀ ω, directing_measure X hX_contract hX_meas hX_L2 ω (Set.Iic t) =
      ENNReal.ofReal (cdf_from_alpha X hX_contract hX_meas hX_L2 ω t) := by
    intro ω
    unfold directing_measure
    simp only []
    -- F_ω.measure (Iic t) = ofReal (F_ω t - 0) where F_ω has limit 0 at bot
    -- But cdf_from_alpha_limits is a sorry, so we must sorry this identification
    sorry
  simp_rw [h_eq]
  exact ENNReal.measurable_ofReal.comp hmeas

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
  classical
  by_cases hs : MeasurableSet s
  ·
    -- π–λ theorem approach:
    -- Define the class of "good" measurable sets G = {s measurable | ω ↦ ν(ω)(s) is measurable}
    -- We restrict to measurable sets so that measure properties (compl, union) can be used
    let G : Set (Set ℝ) :=
      {s | MeasurableSet s ∧ Measurable (fun ω => directing_measure X hX_contract hX_meas hX_L2 ω s)}

    -- Step 1: Show G contains the π-system of half-lines
    have h_pi : ∀ t : ℝ, Set.Iic t ∈ G := by
      intro t
      constructor
      · exact measurableSet_Iic
      · exact directing_measure_eval_Iic_measurable X hX_contract hX_meas hX_L2 t

    -- Step 2: Show G is a Dynkin system (λ-system)
    have h_empty : ∅ ∈ G := by
      constructor
      · exact MeasurableSet.empty
      · change Measurable (fun ω => directing_measure X hX_contract hX_meas hX_L2 ω ∅)
        simp only [measure_empty]
        exact measurable_const

    have h_compl : ∀ s ∈ G, sᶜ ∈ G := by
      intro s ⟨hs_meas, hs_eval⟩
      constructor
      · exact hs_meas.compl
      · -- ν(ω)(sᶜ) = ν(ω)(univ) - ν(ω)(s) = 1 - ν(ω)(s)
        -- Since ν(ω) is a probability measure, ν(ω)(univ) = 1
        -- ω ↦ ν(ω)(s) is measurable by hs_eval
        -- ω ↦ 1 - ν(ω)(s) is measurable as difference of measurable functions
        have h_univ_s : ∀ ω, directing_measure X hX_contract hX_meas hX_L2 ω (sᶜ) =
            directing_measure X hX_contract hX_meas hX_L2 ω Set.univ -
            directing_measure X hX_contract hX_meas hX_L2 ω s := by
          intro ω
          -- directing_measure ω is a measure (StieltjesFunction.measure), so measure_compl applies
          -- Need IsFiniteMeasure instance - follows from IsProbabilityMeasure (once that's proved)
          haveI : IsFiniteMeasure (directing_measure X hX_contract hX_meas hX_L2 ω) := by
            -- This should follow from directing_measure_isProbabilityMeasure
            -- but that's currently a sorry
            sorry
          rw [measure_compl hs_meas (measure_ne_top _ s)]
        simp_rw [h_univ_s]
        -- ω ↦ ν(ω)(univ) is constant 1 (probability measure), so measurable
        -- ω ↦ ν(ω)(s) is measurable by hs_eval
        -- Their difference is measurable
        have h_univ_const : ∀ ω, directing_measure X hX_contract hX_meas hX_L2 ω Set.univ = 1 := by
          intro ω
          -- This follows from directing_measure_isProbabilityMeasure
          -- But that depends on cdf_from_alpha_limits which is a sorry
          sorry
        simp_rw [h_univ_const]
        -- (fun ω => 1 - ν(ω)(s)) is measurable
        -- Constant 1 minus measurable function
        exact Measurable.const_sub hs_eval 1

    have h_iUnion : ∀ (f : ℕ → Set ℝ),
        (∀ i j, i ≠ j → Disjoint (f i) (f j)) →
        (∀ n, f n ∈ G) →
        (⋃ n, f n) ∈ G := by
      intro f hdisj hf
      constructor
      · -- ⋃ n, f n is measurable as countable union of measurable sets
        exact MeasurableSet.iUnion (fun n => (hf n).1)
      · -- ω ↦ ν(ω)(⋃ f n) is measurable
        -- ν(ω)(⋃ f n) = ∑ n, ν(ω)(f n) by σ-additivity (since f n are pairwise disjoint and measurable)
        have h_union_eq : ∀ ω, directing_measure X hX_contract hX_meas hX_L2 ω (⋃ n, f n) =
            ∑' n, directing_measure X hX_contract hX_meas hX_L2 ω (f n) := by
          intro ω
          -- directing_measure ω is a measure (StieltjesFunction.measure), so measure_iUnion applies
          exact measure_iUnion hdisj (fun n => (hf n).1)
        simp_rw [h_union_eq]
        -- ∑' n, ν(ω)(f n) is measurable as tsum of measurable functions
        exact Measurable.ennreal_tsum (fun n => (hf n).2)

    -- Step 3: Apply π-λ theorem (induction_on_inter)
    -- The Borel σ-algebra on ℝ is generated by half-lines {Iic t | t ∈ ℝ}
    -- G contains this π-system and is a Dynkin system,
    -- hence G contains all Borel sets
    -- Since s is measurable (by hypothesis hs), we need to show s ∈ G

    -- Define the property: C(t) = "t ∈ G"
    let C : ∀ (t : Set ℝ), MeasurableSet t → Prop := fun t _ => t ∈ G

    -- Apply π-λ theorem with π-system = range Iic
    -- Define the generating set
    let S : Set (Set ℝ) := Set.range (Set.Iic : ℝ → Set ℝ)

    -- Prove the necessary facts about S
    have h_gen : (inferInstance : MeasurableSpace ℝ) = MeasurableSpace.generateFrom S :=
      @borel_eq_generateFrom_Iic ℝ _ _ _ _

    have h_pi_S : IsPiSystem S := by
      -- {Iic t | t ∈ ℝ} is a π-system
      -- For any Iic s, Iic t: if (Iic s) ∩ (Iic t) is nonempty, then it's in S
      -- (Iic s) ∩ (Iic t) = Iic (min s t)
      intro u hu v hv _
      -- u ∈ S means u = Iic s for some s
      -- v ∈ S means v = Iic t for some t
      obtain ⟨s, rfl⟩ := hu
      obtain ⟨t, rfl⟩ := hv
      -- Need to show: Iic s ∩ Iic t ∈ S
      use min s t
      exact Set.Iic_inter_Iic.symm

    -- Apply the π-λ theorem
    have h_induction : ∀ t (htm : MeasurableSet t), C t htm := fun t htm =>
      MeasurableSpace.induction_on_inter h_gen h_pi_S
        h_empty
        (fun u ⟨r, hr⟩ => hr ▸ h_pi r)
        (fun u hum hu => h_compl u hu)
        (fun f hdisj hfm hf => h_iUnion f hdisj hf)
        t htm

    -- Apply to s to conclude
    exact (h_induction s hs).2
  ·
    -- NON-MEASURABLE CASE: s is not a measurable set
    --
    -- Context: directing_measure ω is defined as F_ω.measure where F_ω is a StieltjesFunction.
    -- In Lean, StieltjesFunction.measure extends to a complete measure via Carathéodory's
    -- extension theorem, so it's defined on ALL sets (not just measurable ones).
    --
    -- Mathematical fact: For non-measurable sets, the measure equals the outer measure:
    --   μ(s) = inf{μ(A) : A ⊇ s, A measurable}
    --
    -- The function ω ↦ directing_measure ω s should be measurable because:
    -- 1. The construction is uniform in ω (same Stieltjes CDF process for all ω)
    -- 2. The outer measure is σ-additive from below, inheriting measurability
    -- 3. For each ω, F_ω is constructed from cdf_from_alpha ω, which is measurable in ω
    --
    -- To prove this rigorously would require:
    -- - Showing outer measures preserve measurability in parameters
    -- - Using that the Carathéodory extension is functorial in the base measure
    -- - Possibly: showing the function equals a measurable function a.e.
    --
    -- This is a deep result in measure theory about parameter-dependent measures.
    -- For now, accept as sorry:
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
  classical
  -- α_f from Step 2 convergence:
  obtain ⟨alpha, hα_meas, hα_L1, hα_conv⟩ :=
    weighted_sums_converge_L1 X hX_contract hX_meas hX_L2 f hf_meas hf_bdd
  refine ⟨alpha, hα_meas, hα_L1, hα_conv, ?_⟩

  -- Identification α_f = ∫ f dν(·) a.e. via monotone class theorem

  -- Step 1: Base case for indicators of half-lines
  have base : ∀ t : ℝ,
      ∀ᵐ ω ∂μ, alphaIic X hX_contract hX_meas hX_L2 t ω
        = ∫ x, (Set.Iic t).indicator (fun _ => (1 : ℝ)) x
            ∂(directing_measure X hX_contract hX_meas hX_L2 ω) := by
    intro t
    -- The integral of an indicator equals the measure of the set
    -- ν(ω)(Iic t) = cdf_from_alpha ω t by Measure.ofCDF construction
    -- alphaIic approximates cdf_from_alpha via the rational envelope
    -- TODO: formalize a.e. equality:
    -- 1) ∫ 1_{Iic t} dν(ω) = ν(ω)(Iic t) (integral of indicator)
    -- 2) ν(ω)(Iic t) = cdf_from_alpha ω t (Measure.ofCDF property)
    -- 3) alphaIic t ω ≈ cdf_from_alpha ω t (L¹ limit + density of rationals)
    sorry

  -- Step 2: Define the good class of functions
  -- C = {f bounded Borel | ∀ᵐ ω, α_f(ω) = ∫ f dν(ω)}
  -- Show C contains indicators of half-lines (Step 1),
  -- closed under linear combinations, and closed under monotone limits

  -- Step 3: Apply monotone class theorem
  -- TODO: Use mathlib's monotone class API or implement manually
  -- Since C contains a π-system (indicators of half-lines) and is a monotone class,
  -- C contains all bounded Borel functions
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
  classical
  -- Proof by induction on m (number of factors)
  induction m with
  | zero =>
      -- Base case: empty product = 1
      simp [Finset.prod_empty]
  | succ m IH =>
      -- Inductive step: separate the last factor
      -- Strategy: Use tail-measurability and conditioning

      -- Step 1: Reorder indices if needed so last k(m) is maximal
      -- (Use exchangeability/contractability to reindex)
      -- TODO: Construct permutation putting max at end
      -- For now, assume WLOG that k is already ordered

      -- Step 2: Separate last factor from product of first m factors
      -- TODO: Define H = ∏_{i<m} 1_{B_i}(X_{k(i)}) as the "tail factor"

      -- Step 3: Use directing_measure_integral for indicators
      -- This gives: α_{1_B} = ν(·)(B) a.e. for each indicator
      -- TODO: Apply to each B_i

      -- Step 4: Use tail-measurability and tower property
      -- The first m factors are measurable w.r.t. σ(X_j | j ≤ N) for N = max_{i<m} k(i)
      -- The last factor X_{k(m)} is independent of this σ-field (by contractability)
      -- Hence E[H · 1_B(X_{k(m)})] = E[H · ν(·)(B)] by conditional expectation
      -- TODO: formalize tower property / conditional expectation argument

      -- Step 5: Apply induction hypothesis to H
      -- TODO: Use IH on the product of m factors
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
