/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Exchangeability.DeFinetti.ViaL2.MainConvergence

/-!
# Alpha_Iic: Raw CDF Functions for Directing Measure

This file defines the raw CDF-building functions `indIic`, `alphaIic`, and `alphaIicRat`
used in the L² proof of de Finetti's theorem. These are the building blocks for
the directing measure construction via Carathéodory extension.

## Main definitions

* `indIic t`: Indicator of `(-∞, t]` as a bounded measurable function ℝ → ℝ
* `alphaIic`: Raw CDF at level t (clipped L¹ limit of Cesàro averages)
* `alphaIicRat`: Rational restriction of `alphaIic` for `stieltjesOfMeasurableRat`

## Main results

* `indIic_measurable`: `indIic t` is measurable
* `indIic_bdd`: `|indIic t x| ≤ 1` for all x
* `alphaIic_measurable`: `alphaIic` is measurable in ω
* `alphaIic_bound`: `0 ≤ alphaIic ω ≤ 1` for all ω
* `measurable_alphaIicRat`: Joint measurability for `stieltjesOfMeasurableRat`

## References

* Kallenberg (2005), *Probabilistic Symmetries and Invariance Principles*,
  Chapter 1, "Second proof of Theorem 1.1"
-/

noncomputable section

namespace Exchangeability.DeFinetti.ViaL2

open MeasureTheory ProbabilityTheory BigOperators Filter Topology
open Exchangeability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-!
## Indicator of Iic

The indicator function `1_{(-∞, t]}` serves as the basic building block for CDF construction.
-/

/-- Indicator of `(-∞, t]` as a bounded measurable function ℝ → ℝ. -/
def indIic (t : ℝ) : ℝ → ℝ :=
  (Set.Iic t).indicator (fun _ => (1 : ℝ))

@[fun_prop]
lemma indIic_measurable (t : ℝ) : Measurable (indIic t) := by
  simpa [indIic] using (measurable_const.indicator measurableSet_Iic)

lemma indIic_bdd (t : ℝ) : ∀ x, |indIic t x| ≤ 1 := by
  intro x; by_cases hx : x ≤ t <;> simp [indIic, hx, abs_of_nonneg]

/-!
## Raw CDF: alphaIic

The L¹-limit of Cesàro averages of `indIic t ∘ X_i`, clipped to [0,1] to ensure
pointwise bounds. This is the "raw" CDF before regularization.
-/

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

/-!
## Rational restriction: alphaIicRat

We restrict `alphaIic` to rationals to use mathlib's `stieltjesOfMeasurableRat` construction,
which patches the null set where pointwise CDF axioms fail.
-/

/-- Restrict α_{Iic} to rationals for use with stieltjesOfMeasurableRat. -/
noncomputable def alphaIicRat
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ) :
    Ω → ℚ → ℝ :=
  fun ω q => alphaIic X hX_contract hX_meas hX_L2 (q : ℝ) ω

/-- `alphaIicRat` is measurable, which is required for `stieltjesOfMeasurableRat`. -/
lemma measurable_alphaIicRat
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ) :
    Measurable (alphaIicRat X hX_contract hX_meas hX_L2) := by
  refine measurable_pi_iff.2 ?_
  intro q
  exact alphaIic_measurable X hX_contract hX_meas hX_L2 (q : ℝ)

end Exchangeability.DeFinetti.ViaL2
