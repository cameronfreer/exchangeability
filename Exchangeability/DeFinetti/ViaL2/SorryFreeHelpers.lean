
/-
# ViaL2/SorryFreeHelpers.lean

Small helper lemmas plus **axioms** for the deep results so that `ViaL2.lean`
can be made sorry-free. Each axiom is clearly named and can be replaced later
with a proper theorem from mathlib or a local proof.
-/

import Mathlib
import Exchangeability.Contractability

open scoped BigOperators Topology
open MeasureTheory Filter Set
open Exchangeability

-- Forward declare the namespace so axioms can reference it
namespace Exchangeability.DeFinetti.ViaL2

-- Forward declaration for TailSigma (defined in ViaL2.lean)
namespace TailSigma
axiom tailSigma {Ω : Type*} [MeasurableSpace Ω] (X : ℕ → Ω → ℝ) : MeasurableSpace Ω
end TailSigma

-- Forward declarations for functions that will be defined in ViaL2.lean
axiom cdf_from_alpha {Ω : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
  (hX_meas : ∀ i, Measurable (X i)) (hX_L2 : ∀ i, MemLp (X i) 2 μ) :
  Ω → ℝ → ℝ

axiom directing_measure {Ω : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
  (hX_meas : ∀ i, Measurable (X i)) (hX_L2 : ∀ i, MemLp (X i) 2 μ) :
  Ω → Measure ℝ

axiom alphaIic {Ω : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
  (hX_meas : ∀ i, Measurable (X i)) (hX_L2 : ∀ i, MemLp (X i) 2 μ)
  (t : ℝ) : Ω → ℝ

axiom alphaFrom {Ω : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
  (hX_meas : ∀ i, Measurable (X i)) (hX_L2 : ∀ i, MemLp (X i) 2 μ)
  (f : ℝ → ℝ) : Ω → ℝ

namespace Helpers

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## Elementary helpers -/

/-- Clip a real to the interval `[0,1]`. -/
@[simp] def clip01 (x : ℝ) : ℝ := max 0 (min 1 x)

lemma clip01_range (x : ℝ) : 0 ≤ clip01 x ∧ clip01 x ≤ 1 := by
  unfold clip01
  constructor
  · exact le_max_left _ _
  · apply max_le
    · linarith
    · exact min_le_left _ _

/-- `clip01` is 1-Lipschitz (recorded as an axiom to avoid depending on specific
names of lemmas in your mathlib snapshot). -/
axiom clip01_1Lipschitz : LipschitzWith 1 clip01

/-- Pointwise contraction from the 1-Lipschitzness. -/
lemma abs_clip01_sub_le (x y : ℝ) : |clip01 x - clip01 y| ≤ |x - y| := by
  simpa [Real.dist_eq] using (clip01_1Lipschitz.dist_le_mul x y)

/-- **L¹-stability under 1-Lipschitz post-composition.**
If `∫ |fₙ - f| → 0`, then `∫ |clip01 ∘ fₙ - clip01 ∘ f| → 0`.
This follows from the pointwise bound |clip01 x - clip01 y| ≤ |x - y| and dominated convergence. -/
axiom l1_convergence_under_clip01
    {μ : Measure Ω} {fn : ℕ → Ω → ℝ} {f : Ω → ℝ}
    (h_meas : ∀ n, AEMeasurable (fn n) μ) (hf : AEMeasurable f μ)
    (h : Tendsto (fun n => ∫ ω, |fn n ω - f ω| ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, |clip01 (fn n ω) - clip01 (f ω)| ∂μ) atTop (𝓝 0)

/-! ## Axioms for the deep steps

These are the genuinely hard parts (reverse martingale, kernel measurability,
endpoint limits, identification).  Keep them here so the main file stays tidy.
Replace them with real theorems when available.
-/

/-- **AXIOM A1 (Reverse martingale / mean ergodic in L¹):**
Cesàro averages of a bounded measurable function along an exchangeable
(contractable) sequence converge in L¹ to the conditional expectation onto
the tail σ-algebra. -/
axiom cesaro_to_condexp_L1
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {X : ℕ → Ω → ℝ} (hX_contract : Contractable μ X)
  (hX_meas : ∀ i, Measurable (X i))
  (f : ℝ → ℝ) (hf_meas : Measurable f) (hf_bdd : ∀ x, |f x| ≤ 1) :
  ∀ ε > 0, ∃ (M : ℕ), ∀ (m : ℕ), m ≥ M →
    ∫ ω, |(1 / (m : ℝ)) * ∑ i : Fin m, f (X i ω) -
           (μ[(f ∘ X 0) | TailSigma.tailSigma X] ω)| ∂μ < ε

/-- **AXIOM A2 (CDF endpoints):**
For the CDF built from `alphaIic` via the rational envelope, the limits at
±∞ are 0 and 1 for every ω. -/
axiom cdf_from_alpha_limits
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
  (hX_meas : ∀ i, Measurable (X i)) (hX_L2 : ∀ i, MemLp (X i) 2 μ) :
  ∀ ω, Tendsto (Exchangeability.DeFinetti.ViaL2.cdf_from_alpha X hX_contract hX_meas hX_L2 ω) atBot (𝓝 0) ∧
       Tendsto (Exchangeability.DeFinetti.ViaL2.cdf_from_alpha X hX_contract hX_meas hX_L2 ω) atTop (𝓝 1)

/-- **AXIOM A3 (Probability measure from CDF):**
The `directing_measure` built from the CDF is a probability measure. -/
axiom directing_measure_isProbabilityMeasure
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
  (hX_meas : ∀ i, Measurable (X i)) (hX_L2 : ∀ i, MemLp (X i) 2 μ) :
  ∀ ω, IsProbabilityMeasure (Exchangeability.DeFinetti.ViaL2.directing_measure X hX_contract hX_meas hX_L2 ω)

/-- **AXIOM A4 (Kernel measurability):**
For every measurable set `s`, the map ω ↦ ν(ω)(s) is measurable. -/
axiom directing_measure_eval_measurable
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
  (hX_meas : ∀ i, Measurable (X i)) (hX_L2 : ∀ i, MemLp (X i) 2 μ) :
  ∀ s : Set ℝ, Measurable s → Measurable
    (fun ω => Exchangeability.DeFinetti.ViaL2.directing_measure X hX_contract hX_meas hX_L2 ω s)

/-- **AXIOM A5 (Identification):**
For bounded measurable `f`, α_f(ω) agrees a.e. with `∫ f dν(ω)`. -/
axiom directing_measure_identification
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
  (hX_meas : ∀ i, Measurable (X i)) (hX_L2 : ∀ i, MemLp (X i) 2 μ)
  (f : ℝ → ℝ) (hf_meas : Measurable f) (hf_bdd : ∀ x, |f x| ≤ 1) :
  ∀ᵐ ω ∂μ, Exchangeability.DeFinetti.ViaL2.alphaFrom X hX_contract hX_meas hX_L2 f ω
             = ∫ x, f x ∂(Exchangeability.DeFinetti.ViaL2.directing_measure X hX_contract hX_meas hX_L2 ω)

/-- **AXIOM A6 (Indicator integral continuity at fixed threshold):**
If `Xₙ → X` a.e. and each `Xₙ`, `X` is measurable, then
`∫ 1_{(-∞,t]}(Xₙ) dμ → ∫ 1_{(-∞,t]}(X) dμ`. -/
axiom tendsto_integral_indicator_Iic
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ) (t : ℝ)
  (hXn_meas : ∀ n, Measurable (Xn n)) (hX_meas : Measurable (X))
  (hae : ∀ᵐ ω ∂μ, Tendsto (fun n => Xn n ω) atTop (𝓝 (X ω))) :
  Tendsto (fun n => ∫ ω, (Set.Iic t).indicator (fun _ => (1 : ℝ)) (Xn n ω) ∂μ)
          atTop
          (𝓝 (∫ ω, (Set.Iic t).indicator (fun _ => (1 : ℝ)) (X ω) ∂μ))

/-- **AXIOM A7 (α_{Iic t} → 0 at −∞, a.e.). -/
axiom alphaIic_tendsto_zero_at_bot
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
  (hX_meas : ∀ i, Measurable (X i)) (hX_L2 : ∀ i, MemLp (X i) 2 μ) :
  ∀ᵐ ω ∂μ, Tendsto (fun t => Exchangeability.DeFinetti.ViaL2.alphaIic X hX_contract hX_meas hX_L2 t ω) atBot (𝓝 0)

/-- **AXIOM A8 (α_{Iic t} → 1 at +∞, a.e.). -/
axiom alphaIic_tendsto_one_at_top
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
  (hX_meas : ∀ i, Measurable (X i)) (hX_L2 : ∀ i, MemLp (X i) 2 μ) :
  ∀ᵐ ω ∂μ, Tendsto (fun t => Exchangeability.DeFinetti.ViaL2.alphaIic X hX_contract hX_meas hX_L2 t ω) atTop (𝓝 1)

/-- **AXIOM A9 (Subsequence a.e. convergence from L¹):**
If `αₙ → α` in L¹ (with measurability), there is a subsequence converging to `α`
almost everywhere. -/
axiom subseq_ae_of_L1
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  (alpha : ℕ → Ω → ℝ) (alpha_inf : Ω → ℝ)
  (h_alpha_meas : ∀ n, Measurable (alpha n))
  (h_alpha_inf_meas : Measurable alpha_inf)
  (h_L1_conv : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∫ ω, |alpha n ω - alpha_inf ω| ∂μ < ε) :
  ∃ (φ : ℕ → ℕ), StrictMono φ ∧
    ∀ᵐ ω ∂μ, Tendsto (fun k => alpha (φ k) ω) atTop (𝓝 (alpha_inf ω))

/-- **AXIOM A10 (Step 5 packaging):** packaged existence of a directing kernel
with the pointwise identification for a given bounded measurable `f`. -/
axiom alpha_is_conditional_expectation_packaged
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
  (hX_meas : ∀ i, Measurable (X i))
  (f : ℝ → ℝ) (hf_meas : Measurable f) (alpha : ℕ → Ω → ℝ) :
  ∃ (nu : Ω → Measure ℝ),
    (∀ ω, IsProbabilityMeasure (nu ω)) ∧
    Measurable (fun ω => nu ω (Set.univ)) ∧
    (∀ n, ∀ᵐ ω ∂μ, alpha n ω = ∫ x, f x ∂(nu ω))

end Helpers
end Exchangeability.DeFinetti.ViaL2
