/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Exchangeability.DeFinetti.ViaL2.MainConvergence
import Exchangeability.Probability.IntegrationHelpers

/-!
# Directing Measure Construction via Carathéodory Extension

This file constructs the directing measure ν : Ω → Measure ℝ for the L² proof
of de Finetti's theorem. The directing measure is built from the L¹ limits
of Cesàro averages via Carathéodory extension.

## Main definitions

* `indIic`: Indicator of `(-∞, t]` as a bounded measurable function
* `alphaIic`: Raw CDF at level t (clipped L¹ limit)
* `alphaIicRat`: Rational restriction for `stieltjesOfMeasurableRat`
* `alphaIicCE`: Canonical conditional expectation version
* `cdf_from_alpha`: The regularized CDF via Stieltjes extension
* `directing_measure`: The directing measure built from the CDF

## Main results

* `alphaIic_ae_eq_alphaIicCE`: Identification of raw and canonical versions
* `alphaIicCE_ae_tendsto_zero_atBot`: Endpoint limit at -∞
* `alphaIicCE_ae_tendsto_one_atTop`: Endpoint limit at +∞
* `directing_measure_isProbabilityMeasure`: ν(ω) is a probability measure

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

@[fun_prop]
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

/-!
### Rational restriction of alphaIic for stieltjesOfMeasurableRat

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

/-!
### Canonical conditional expectation version of alphaIic

The existential α from `weighted_sums_converge_L1` is unique in L¹ up to a.e. equality.
We now define the **canonical** version using conditional expectation onto the tail σ-algebra.
This avoids all pointwise headaches and gives us the endpoint limits for free.
-/

/-- **Canonical conditional expectation version** of α_{Iic t}.

This is the conditional expectation of the indicator function `1_{(-∞,t]}∘X_0` with respect
to the tail σ-algebra. By the reverse martingale convergence theorem, this equals the
existential `alphaIic` almost everywhere.

**Key advantages:**
- Has pointwise bounds `0 ≤ alphaIicCE ≤ 1` everywhere (not just a.e.)
- Monotone in `t` almost everywhere (from positivity of conditional expectation)
- Endpoint limits follow from L¹ contraction and dominated convergence
-/
noncomputable def alphaIicCE
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ)
    (t : ℝ) : Ω → ℝ := by
  classical
  -- Set up the tail σ-algebra and its sub-σ-algebra relation
  have hm_le : TailSigma.tailSigma X ≤ (inferInstance : MeasurableSpace Ω) :=
    TailSigma.tailSigma_le X hX_meas
  -- Create the Fact instance for the sub-σ-algebra relation
  haveI : Fact (TailSigma.tailSigma X ≤ (inferInstance : MeasurableSpace Ω)) := ⟨hm_le⟩
  -- Now we can call condExp with the tail σ-algebra
  exact μ[(indIic t) ∘ (X 0) | TailSigma.tailSigma X]

/-- Measurability of alphaIicCE.

TODO: Currently a sorry due to BorelSpace typeclass instance resolution issues.
The conditional expectation `condExp μ (tailSigma X) f` is measurable by
`stronglyMeasurable_condExp.measurable`, but Lean can't synthesize the required
`BorelSpace` instance automatically. This should be straightforward to fix. -/
lemma alphaIicCE_measurable
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ)
    (t : ℝ) :
    Measurable (alphaIicCE X hX_contract hX_meas hX_L2 t) := by
  unfold alphaIicCE
  -- The conditional expectation μ[f|m] is strongly measurable w.r.t. m
  -- Since m ≤ ambient, measurability w.r.t. m implies measurability w.r.t. ambient
  have hm_le := TailSigma.tailSigma_le X hX_meas
  refine Measurable.mono stronglyMeasurable_condExp.measurable hm_le le_rfl

/-- alphaIicCE is monotone nondecreasing in t (for each fixed ω). -/
lemma alphaIicCE_mono
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ) :
    ∀ s t : ℝ, s ≤ t → ∀ᵐ ω ∂μ,
      alphaIicCE X hX_contract hX_meas hX_L2 s ω
      ≤ alphaIicCE X hX_contract hX_meas hX_L2 t ω := by
  -- alphaIicCE is conditional expectation of (indIic ·) ∘ X 0
  -- indIic is monotone: s ≤ t ⇒ indIic s ≤ indIic t
  -- Conditional expectation preserves monotonicity a.e.
  intro s t hst

  -- Set up tail σ-algebra infrastructure
  have hm_le : TailSigma.tailSigma X ≤ (inferInstance : MeasurableSpace Ω) :=
    TailSigma.tailSigma_le X hX_meas
  haveI : Fact (TailSigma.tailSigma X ≤ (inferInstance : MeasurableSpace Ω)) := ⟨hm_le⟩

  -- Show indIic s ≤ indIic t pointwise
  have h_ind_mono : (indIic s) ∘ (X 0) ≤ᵐ[μ] (indIic t) ∘ (X 0) := by
    apply ae_of_all
    intro ω
    simp [indIic, Set.indicator]
    split_ifs with h1 h2
    · norm_num  -- Both in set: 1 ≤ 1
    · -- X 0 ω ≤ s but not ≤ t: contradiction since s ≤ t
      exfalso
      exact h2 (le_trans h1 hst)
    · norm_num  -- s not satisfied but t is: 0 ≤ 1
    · norm_num  -- Neither satisfied: 0 ≤ 0

  -- Integrability of both functions
  have h_int_s : Integrable ((indIic s) ∘ (X 0)) μ := by
    have : indIic s = Set.indicator (Set.Iic s) (fun _ => (1 : ℝ)) := rfl
    rw [this]
    exact Exchangeability.Probability.integrable_indicator_comp (hX_meas 0) measurableSet_Iic

  have h_int_t : Integrable ((indIic t) ∘ (X 0)) μ := by
    have : indIic t = Set.indicator (Set.Iic t) (fun _ => (1 : ℝ)) := rfl
    rw [this]
    exact Exchangeability.Probability.integrable_indicator_comp (hX_meas 0) measurableSet_Iic

  -- Apply condExp_mono
  unfold alphaIicCE
  exact condExp_mono (μ := μ) (m := TailSigma.tailSigma X) h_int_s h_int_t h_ind_mono

/-- alphaIicCE is bounded in [0,1] almost everywhere. -/
lemma alphaIicCE_nonneg_le_one
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ)
    (t : ℝ) :
    ∀ᵐ ω ∂μ, 0 ≤ alphaIicCE X hX_contract hX_meas hX_L2 t ω
             ∧ alphaIicCE X hX_contract hX_meas hX_L2 t ω ≤ 1 := by
  -- alphaIicCE = condExp of (indIic t) ∘ X 0
  -- Since 0 ≤ indIic t ≤ 1, we have 0 ≤ condExp(...) ≤ 1 a.e.

  -- Set up tail σ-algebra infrastructure
  have hm_le : TailSigma.tailSigma X ≤ (inferInstance : MeasurableSpace Ω) :=
    TailSigma.tailSigma_le X hX_meas
  haveI : Fact (TailSigma.tailSigma X ≤ (inferInstance : MeasurableSpace Ω)) := ⟨hm_le⟩

  -- Nonnegativity: 0 ≤ indIic t ∘ X 0 implies 0 ≤ condExp
  have h₀ : 0 ≤ᵐ[μ] alphaIicCE X hX_contract hX_meas hX_L2 t := by
    have : 0 ≤ᵐ[μ] (indIic t) ∘ (X 0) := by
      apply ae_of_all
      intro ω
      -- indIic t is an indicator function, so it's 0 or 1
      simp [indIic, Set.indicator]
      split_ifs <;> norm_num
    unfold alphaIicCE
    convert condExp_nonneg (μ := μ) (m := TailSigma.tailSigma X) this using 2

  -- Upper bound: indIic t ∘ X 0 ≤ 1 implies condExp ≤ 1
  have h₁ : alphaIicCE X hX_contract hX_meas hX_L2 t ≤ᵐ[μ] fun _ => (1 : ℝ) := by
    have h_le : (indIic t) ∘ (X 0) ≤ᵐ[μ] fun _ => (1 : ℝ) := by
      apply ae_of_all
      intro ω
      -- indIic t is an indicator function, so it's 0 or 1
      simp [indIic, Set.indicator]
      split_ifs <;> norm_num
    -- Need integrability
    have h_int : Integrable ((indIic t) ∘ (X 0)) μ := by
      -- Bounded indicator composition is integrable
      have : indIic t = Set.indicator (Set.Iic t) (fun _ => (1 : ℝ)) := rfl
      rw [this]
      exact Exchangeability.Probability.integrable_indicator_comp (hX_meas 0) measurableSet_Iic
    unfold alphaIicCE
    have h_mono := condExp_mono (μ := μ) (m := TailSigma.tailSigma X)
      h_int (integrable_const (1 : ℝ)) h_le
    rw [condExp_const (μ := μ) (m := TailSigma.tailSigma X) hm_le (1 : ℝ)] at h_mono
    exact h_mono

  filter_upwards [h₀, h₁] with ω h0 h1
  exact ⟨h0, h1⟩

/-!
### Identification lemma and endpoint limits for alphaIicCE

The key results that solve the endpoint limit problem:
1. **Identification**: The existential `alphaIic` equals the canonical `alphaIicCE` a.e.
2. **L¹ endpoint limits**: Using L¹ contraction of condExp, we get integral convergence
3. **A.e. endpoint limits**: Monotonicity + boundedness + L¹ limits ⇒ a.e. pointwise limits
-/

set_option maxHeartbeats 400000 in
/-- **Identification lemma**: alphaIic equals alphaIicCE almost everywhere.

**Proof strategy:**
Both are L¹ limits of the same Cesàro averages `(1/m) ∑ᵢ (indIic t) ∘ X_{n+i}`:
- `alphaIic` is defined as the L¹ limit from `weighted_sums_converge_L1`
- `alphaIicCE` is the conditional expectation `μ[(indIic t) ∘ X_0 | tailSigma X]`

By the reverse martingale convergence theorem (or direct L² analysis), the Cesàro averages
converge in L² (hence L¹) to the conditional expectation. Since L¹ limits are unique up
to a.e. equality, we get `alphaIic =ᵐ alphaIicCE`.

TODO: Implement using reverse martingale convergence or L² projection argument. -/
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
        · simp [hm_pos, A]
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
          push_neg at halpha halpha1
          rw [min_comm, min_eq_left halpha1, max_eq_right halpha]

    -- Prove integrability of A n m
    have hA_int : Integrable (A n m) μ := by
      have hA_meas_nm : Measurable (A n m) := by
        simp only [A]
        apply Measurable.const_mul
        apply Finset.measurable_sum
        intro k _
        exact (indIic_measurable t).comp (hX_meas _)
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
          _ = (1/(m:ℝ)) * m := by simp [Finset.sum_const, Finset.card_fin]
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
              · push_neg at h h1
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
        -- Factor out (1/m) and show the sums telescope
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
          | zero => simp [Finset.sum_range_zero]
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
              rw [integral_mul_left]
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
                  unfold indIic; simp [Set.indicator, abs_of_nonneg]; split_ifs <;> norm_num
                calc ∫ ω, |indIic t (X m ω)| ∂μ
                    ≤ ∫ ω, (1 : ℝ) ∂μ := this
                  _ = 1 := by simp [measure_univ]
              · -- ∫ |indIic t (X 0)| ≤ 1
                have : ∫ ω, |indIic t (X 0 ω)| ∂μ ≤ ∫ ω, (1 : ℝ) ∂μ := by
                  refine integral_mono (Integrable.abs hg_int) (integrable_const 1) ?_
                  intro ω
                  unfold indIic; simp [Set.indicator, abs_of_nonneg]; split_ifs <;> norm_num
                calc ∫ ω, |indIic t (X 0 ω)| ∂μ
                    ≤ ∫ ω, (1 : ℝ) ∂μ := this
                  _ = 1 := by simp [measure_univ]
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
            simpa [Nat.cast_max] using this

    have h2 : (m : ℝ) ≥ Nat.ceil (4/ε) := by
      calc (m : ℝ)
          ≥ max M₁ (Nat.ceil (4/ε)) := Nat.cast_le.mpr hm
        _ ≥ Nat.ceil (4/ε) := by
            have : max (M₁ : ℝ) (Nat.ceil (4/ε) : ℝ) ≥ Nat.ceil (4/ε) := le_max_right _ _
            simpa [Nat.cast_max] using this

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

    -- Triangle inequality for integrals
    calc ∫ ω, |(1/(m:ℝ)) * ∑ k : Fin m, indIic t (X (k.val + 1) ω) -
               μ[indIic t ∘ X 0|TailSigma.tailSigma X] ω| ∂μ
        ≤ ∫ ω, |(1/(m:ℝ)) * ∑ k : Fin m, indIic t (X (k.val + 1) ω) - B m ω| ∂μ +
          ∫ ω, |B m ω - μ[indIic t ∘ X 0|TailSigma.tailSigma X] ω| ∂μ := by
            -- Use pointwise triangle inequality: |a - c| ≤ |a - b| + |b - c|
            rw [← integral_add]
            · apply integral_mono
              · -- Integrability of |A - target|
                apply Integrable.abs
                apply Integrable.sub
                · -- A is integrable (bounded measurable on probability space)
                  have hA_meas : Measurable (fun ω => (1/(m:ℝ)) * ∑ k : Fin m, indIic t (X (k.val + 1) ω)) :=
                    Measurable.const_mul (Finset.measurable_sum _ (fun k _ =>
                      ((indIic_measurable t).comp (hX_meas _)))) _
                  apply Integrable.of_bound hA_meas.aestronglyMeasurable 1
                  filter_upwards with ω
                  simp [Real.norm_eq_abs]
                  -- Each indicator is in [0,1], so sum ≤ m, hence (1/m)*sum ≤ 1
                  -- Note: simp already converted |(1/m) * ∑...| to m⁻¹ * |∑...|
                  calc (m:ℝ)⁻¹ * |∑ k : Fin m, indIic t (X (k.val + 1) ω)|
                    _ ≤ (m:ℝ)⁻¹ * ∑ k : Fin m, |indIic t (X (k.val + 1) ω)| := by
                          gcongr; exact Finset.abs_sum_le_sum_abs _ _
                    _ ≤ (m:ℝ)⁻¹ * ∑ k : Fin m, (1 : ℝ) := by
                          gcongr with k
                          unfold indIic; simp [Set.indicator]; split_ifs <;> norm_num
                    _ = (1/(m:ℝ)) * m := by
                          rw [← one_div]; simp [Finset.sum_const, Finset.card_fin]
                    _ = 1 := by field_simp
                · -- target = condExp is integrable
                  exact integrable_condExp
              · -- Integrability of |A - B| + |B - target|
                apply Integrable.add
                · -- |A - B| is integrable
                  apply Integrable.abs
                  apply Integrable.sub
                  · -- A is integrable
                    have hA_meas : Measurable (fun ω => (1/(m:ℝ)) * ∑ k : Fin m, indIic t (X (k.val + 1) ω)) :=
                      Measurable.const_mul (Finset.measurable_sum _ (fun k _ =>
                        ((indIic_measurable t).comp (hX_meas _)))) _
                    apply Integrable.of_bound hA_meas.aestronglyMeasurable 1
                    filter_upwards with ω; simp [Real.norm_eq_abs]
                    -- Note: simp already converted |(1/m) * ∑...| to m⁻¹ * |∑...|
                    calc (m:ℝ)⁻¹ * |∑ k : Fin m, indIic t (X (k.val + 1) ω)|
                      _ ≤ (m:ℝ)⁻¹ * ∑ k : Fin m, |indIic t (X (k.val + 1) ω)| := by
                            gcongr; exact Finset.abs_sum_le_sum_abs _ _
                      _ ≤ (m:ℝ)⁻¹ * ∑ k : Fin m, (1 : ℝ) := by
                            gcongr with k
                            unfold indIic; simp [Set.indicator]; split_ifs <;> norm_num
                      _ = (1/(m:ℝ)) * m := by
                            rw [← one_div]; simp [Finset.sum_const, Finset.card_fin]
                      _ = 1 := by field_simp
                  · -- B is integrable
                    simp [B]
                    have hB_meas : Measurable (fun ω => (m:ℝ)⁻¹ * ∑ i : Fin m, indIic t (X i ω)) :=
                      Measurable.const_mul (Finset.measurable_sum _ (fun i _ =>
                        ((indIic_measurable t).comp (hX_meas _)))) _
                    apply Integrable.of_bound hB_meas.aestronglyMeasurable 1
                    filter_upwards with ω; simp [Real.norm_eq_abs]
                    -- Note: simp already converted |(m:ℝ)⁻¹ * ∑...| to (m:ℝ)⁻¹ * |∑...|
                    calc (m:ℝ)⁻¹ * |∑ i : Fin m, indIic t (X i ω)|
                      _ ≤ (m:ℝ)⁻¹ * ∑ i : Fin m, |indIic t (X i ω)| := by
                            gcongr; exact Finset.abs_sum_le_sum_abs _ _
                      _ ≤ (m:ℝ)⁻¹ * ∑ i : Fin m, (1 : ℝ) := by
                            gcongr with i
                            unfold indIic; simp [Set.indicator]; split_ifs <;> norm_num
                      _ = (m:ℝ)⁻¹ * m := by simp [Finset.sum_const, Finset.card_fin]
                      _ = 1 := by field_simp
                · -- |B - target| is integrable
                  apply Integrable.abs
                  apply Integrable.sub
                  · -- B is integrable
                    simp [B]
                    have hB_meas : Measurable (fun ω => (m:ℝ)⁻¹ * ∑ i : Fin m, indIic t (X i ω)) :=
                      Measurable.const_mul (Finset.measurable_sum _ (fun i _ =>
                        ((indIic_measurable t).comp (hX_meas _)))) _
                    apply Integrable.of_bound hB_meas.aestronglyMeasurable 1
                    filter_upwards with ω; simp [Real.norm_eq_abs]
                    -- Note: simp already converted |(m:ℝ)⁻¹ * ∑...| to (m:ℝ)⁻¹ * |∑...|
                    calc (m:ℝ)⁻¹ * |∑ i : Fin m, indIic t (X i ω)|
                      _ ≤ (m:ℝ)⁻¹ * ∑ i : Fin m, |indIic t (X i ω)| := by
                            gcongr; exact Finset.abs_sum_le_sum_abs _ _
                      _ ≤ (m:ℝ)⁻¹ * ∑ i : Fin m, (1 : ℝ) := by
                            gcongr with i
                            unfold indIic; simp [Set.indicator]; split_ifs <;> norm_num
                      _ = (m:ℝ)⁻¹ * m := by simp [Finset.sum_const, Finset.card_fin]
                      _ = 1 := by field_simp
                  · -- target is integrable
                    exact integrable_condExp
              · -- Pointwise bound: |a - c| ≤ |a - b| + |b - c|
                intro ω
                exact abs_sub_le _ _ _
            · -- Integrability of |A - B|
              apply Integrable.abs
              apply Integrable.sub
              · -- A is integrable
                have hA_meas : Measurable (fun ω => (1/(m:ℝ)) * ∑ k : Fin m, indIic t (X (k.val + 1) ω)) :=
                  Measurable.const_mul (Finset.measurable_sum _ (fun k _ =>
                    ((indIic_measurable t).comp (hX_meas _)))) _
                apply Integrable.of_bound hA_meas.aestronglyMeasurable 1
                filter_upwards with ω; simp [Real.norm_eq_abs]
                -- Note: simp already converted |(1/m) * ∑...| to m⁻¹ * |∑...|
                calc (m:ℝ)⁻¹ * |∑ k : Fin m, indIic t (X (k.val + 1) ω)|
                  _ ≤ (m:ℝ)⁻¹ * ∑ k : Fin m, |indIic t (X (k.val + 1) ω)| := by
                        gcongr; exact Finset.abs_sum_le_sum_abs _ _
                  _ ≤ (m:ℝ)⁻¹ * ∑ k : Fin m, (1 : ℝ) := by
                        gcongr with k
                        unfold indIic; simp [Set.indicator]; split_ifs <;> norm_num
                  _ = (1/(m:ℝ)) * m := by
                        rw [← one_div]; simp [Finset.sum_const, Finset.card_fin]
                  _ = 1 := by field_simp
              · -- B is integrable
                simp [B]
                have hB_meas : Measurable (fun ω => (m:ℝ)⁻¹ * ∑ i : Fin m, indIic t (X i ω)) :=
                  Measurable.const_mul (Finset.measurable_sum _ (fun i _ =>
                    ((indIic_measurable t).comp (hX_meas _)))) _
                apply Integrable.of_bound hB_meas.aestronglyMeasurable 1
                filter_upwards with ω; simp [Real.norm_eq_abs]
                -- Note: simp already converted |(m:ℝ)⁻¹ * ∑...| to (m:ℝ)⁻¹ * |∑...|
                calc (m:ℝ)⁻¹ * |∑ i : Fin m, indIic t (X i ω)|
                  _ ≤ (m:ℝ)⁻¹ * ∑ i : Fin m, |indIic t (X i ω)| := by
                        gcongr; exact Finset.abs_sum_le_sum_abs _ _
                  _ ≤ (m:ℝ)⁻¹ * ∑ i : Fin m, (1 : ℝ) := by
                        gcongr with i
                        unfold indIic; simp [Set.indicator]; split_ifs <;> norm_num
                  _ = (m:ℝ)⁻¹ * m := by simp [Finset.sum_const, Finset.card_fin]
                  _ = 1 := by field_simp
            · -- Integrability of |B - target|
              apply Integrable.abs
              apply Integrable.sub
              · -- B is integrable
                simp [B]
                have hB_meas : Measurable (fun ω => (m:ℝ)⁻¹ * ∑ i : Fin m, indIic t (X i ω)) :=
                  Measurable.const_mul (Finset.measurable_sum _ (fun i _ =>
                    ((indIic_measurable t).comp (hX_meas _)))) _
                apply Integrable.of_bound hB_meas.aestronglyMeasurable 1
                filter_upwards with ω; simp [Real.norm_eq_abs]
                -- Note: simp already converted |(m:ℝ)⁻¹ * ∑...| to (m:ℝ)⁻¹ * |∑...|
                calc (m:ℝ)⁻¹ * |∑ i : Fin m, indIic t (X i ω)|
                  _ ≤ (m:ℝ)⁻¹ * ∑ i : Fin m, |indIic t (X i ω)| := by
                        gcongr; exact Finset.abs_sum_le_sum_abs _ _
                  _ ≤ (m:ℝ)⁻¹ * ∑ i : Fin m, (1 : ℝ) := by
                        gcongr with i
                        unfold indIic; simp [Set.indicator]; split_ifs <;> norm_num
                  _ = (m:ℝ)⁻¹ * m := by simp [Finset.sum_const, Finset.card_fin]
                  _ = 1 := by field_simp
              · -- target is integrable
                exact integrable_condExp
      _ < 2/(m:ℝ) + ε/2 := by linarith [hAB_diff, hB_conv]
      _ ≤ ε/2 + ε/2 := by linarith [h_small]
      _ = ε := by ring

  -- Measurability of Cesàro averages
  have hA_meas : ∀ n m, AEStronglyMeasurable (A n m) μ := by
    intro n m
    -- A n m is a Cesàro average of indIic ∘ X, which are measurable
    -- Each indIic ∘ X_i is measurable, sum is measurable, scalar mult is measurable
    refine Measurable.aestronglyMeasurable ?_
    show Measurable fun ω => (1 / (m : ℝ)) * ∑ k : Fin m, indIic t (X (n + k.val + 1) ω)
    refine Measurable.const_mul ?_ _
    exact Finset.measurable_sum _ (fun k _ => (indIic_measurable t).comp (hX_meas _))

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
              _ = (m:ℝ)⁻¹ * m := by simp [Finset.sum_const, Finset.card_fin]
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
              _ = (m:ℝ)⁻¹ * m := by simp [Finset.sum_const, Finset.card_fin]
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

/-- **L¹ endpoint limit at -∞**: As t → -∞, alphaIicCE → 0 in L¹.

**Proof strategy:**
- For t → -∞, the indicator `1_{(-∞,t]}(X_0 ω)` → 0 for each fixed ω
- By dominated convergence (bounded by 1), `‖1_{(-∞,t]} ∘ X_0‖₁ → 0`
- By L¹ contraction of conditional expectation:
  ```
  ‖alphaIicCE t - 0‖₁ = ‖μ[1_{(-∞,t]} ∘ X_0 | tailSigma] - μ[0 | tailSigma]‖₁
                      ≤ ‖1_{(-∞,t]} ∘ X_0 - 0‖₁ → 0
  ```
-/
lemma alphaIicCE_L1_tendsto_zero_atBot
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ) :
    Tendsto (fun n : ℕ =>
      ∫ ω, |alphaIicCE X hX_contract hX_meas hX_L2 (-(n : ℝ)) ω| ∂μ)
      atTop (𝓝 0) := by
  -- Strategy: Use L¹ contraction property of conditional expectation
  -- ‖condExp m f‖₁ ≤ ‖f‖₁
  -- First show ‖(indIic (-(n:ℝ))) ∘ X 0‖₁ → 0 by dominated convergence

  -- Set up the tail σ-algebra Fact instance (needed for condExp)
  have hm_le : TailSigma.tailSigma X ≤ (inferInstance : MeasurableSpace Ω) :=
    TailSigma.tailSigma_le X hX_meas
  haveI : Fact (TailSigma.tailSigma X ≤ (inferInstance : MeasurableSpace Ω)) := ⟨hm_le⟩

  -- For each n, alphaIicCE (-(n:ℝ)) = μ[(indIic (-(n:ℝ))) ∘ X 0 | tailSigma]
  have h_def : ∀ n, alphaIicCE X hX_contract hX_meas hX_L2 (-(n : ℝ))
      = μ[(indIic (-(n : ℝ))) ∘ (X 0) | TailSigma.tailSigma X] := by
    intro n
    rfl

  -- Step 1: Show ∫ |(indIic (-(n:ℝ))) ∘ X 0| → 0
  -- Indicator integral = measure of set {X 0 ≤ -n} → 0 by continuity
  have h_indicator_tendsto : Tendsto (fun n : ℕ =>
      ∫ ω, |(indIic (-(n : ℝ))) (X 0 ω)| ∂μ) atTop (𝓝 0) := by
    -- Rewrite as integral = measure
    have h_eq : ∀ n : ℕ, ∫ ω, |(indIic (-(n : ℝ))) (X 0 ω)| ∂μ
        = (μ (X 0 ⁻¹' Set.Iic (-(n : ℝ)))).toReal := by
      intro n
      -- Indicator is nonnegative, so |indicator| = indicator
      have : (fun ω => |(indIic (-(n : ℝ))) (X 0 ω)|) = (indIic (-(n : ℝ))) ∘ (X 0) := by
        ext ω
        simp [indIic, Set.indicator]
        split_ifs <;> norm_num
      rw [this]
      -- Integral of indicator of measurable set = measure
      -- Rewrite composition as indicator on preimage
      have h_comp : (indIic (-(n : ℝ))) ∘ (X 0)
          = (X 0 ⁻¹' Set.Iic (-(n : ℝ))).indicator (fun _ => (1 : ℝ)) := by
        ext ω
        simp only [indIic, Function.comp_apply, Set.indicator_apply]
        rfl
      rw [h_comp, integral_indicator (measurableSet_preimage (hX_meas 0) measurableSet_Iic),
          setIntegral_one_eq_measureReal]
      rfl
    simp only [h_eq]
    -- The sets {X 0 ≤ -n} decrease to empty
    have h_antitone : Antitone (fun n : ℕ => X 0 ⁻¹' Set.Iic (-(n : ℝ))) := by
      intro n m hnm
      apply Set.preimage_mono
      intro x hx
      simp only [Set.mem_Iic] at hx ⊢
      calc x ≤ -(m : ℝ) := hx
           _ ≤ -(n : ℝ) := by simp [neg_le_neg_iff, Nat.cast_le, hnm]
    have h_empty : (⋂ (n : ℕ), X 0 ⁻¹' Set.Iic (-(n : ℝ))) = ∅ := by
      ext ω
      simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_Iic, Set.mem_empty_iff_false, iff_false]
      intro h
      -- For all n, X 0 ω ≤ -n, which means X 0 ω ≤ -n for arbitrarily large n
      -- This is impossible for any real number
      -- Use Archimedean property: exists n with -X 0 ω < n
      obtain ⟨n, hn⟩ := exists_nat_gt (-X 0 ω)
      -- This gives X 0 ω > -n, contradicting h n
      have h1 : X 0 ω > -(n : ℝ) := by linarith
      have h2 : X 0 ω ≤ -(n : ℝ) := h n
      linarith
    -- Apply tendsto_measure_iInter_atTop to get ENNReal convergence, then convert to Real
    have h_meas : ∀ (n : ℕ), NullMeasurableSet (X 0 ⁻¹' Set.Iic (-(n : ℝ))) μ := fun n =>
      (measurableSet_preimage (hX_meas 0) measurableSet_Iic).nullMeasurableSet
    have h_fin : ∃ (n : ℕ), μ (X 0 ⁻¹' Set.Iic (-(n : ℝ))) ≠ ⊤ := by
      use 0
      exact measure_ne_top μ _
    have h_tendsto_ennreal : Tendsto (fun (n : ℕ) => μ (X 0 ⁻¹' Set.Iic (-(n : ℝ)))) atTop (𝓝 0) := by
      have := tendsto_measure_iInter_atTop (μ := μ) h_meas h_antitone h_fin
      simp only [h_empty, measure_empty] at this
      simpa [Function.comp] using this
    -- Convert from ENNReal to Real using continuity of toReal at 0
    have h_ne_top : ∀ n, μ (X 0 ⁻¹' Set.Iic (-(n : ℝ))) ≠ ⊤ := fun n => measure_ne_top μ _
    have h_zero_ne_top : (0 : ENNReal) ≠ ⊤ := by norm_num
    rw [← ENNReal.toReal_zero]
    exact (ENNReal.continuousAt_toReal h_zero_ne_top).tendsto.comp h_tendsto_ennreal

  -- Step 2: L¹ contraction - ‖condExp f‖₁ ≤ ‖f‖₁
  have h_contraction : ∀ n : ℕ,
      ∫ ω, |alphaIicCE X hX_contract hX_meas hX_L2 (-(n : ℝ)) ω| ∂μ
      ≤ ∫ ω, |(indIic (-(n : ℝ))) (X 0 ω)| ∂μ := by
    intro n
    -- alphaIicCE is conditional expectation, so use integral_abs_condExp_le
    unfold alphaIicCE
    exact integral_abs_condExp_le (μ := μ) (m := TailSigma.tailSigma X) _

  -- Apply squeeze theorem: 0 ≤ ‖alphaIicCE‖₁ ≤ ‖indicator‖₁ → 0
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h_indicator_tendsto ?_ h_contraction
  intro n
  exact integral_nonneg (fun ω => abs_nonneg _)

/-- **L¹ endpoint limit at +∞**: As t → +∞, alphaIicCE → 1 in L¹.

**Proof strategy:**
Similar to the -∞ case, but `1_{(-∞,t]}(X_0 ω)` → 1 as t → +∞. -/
lemma alphaIicCE_L1_tendsto_one_atTop
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ) :
    Tendsto (fun n : ℕ =>
      ∫ ω, |alphaIicCE X hX_contract hX_meas hX_L2 (n : ℝ) ω - 1| ∂μ)
      atTop (𝓝 0) := by
  -- Strategy: Similar to atBot case, but now (indIic (n:ℝ)) → 1 pointwise
  -- So ∫ |(indIic (n:ℝ)) ∘ X 0 - 1| → 0

  -- Set up the tail σ-algebra Fact instance (needed for condExp)
  have hm_le : TailSigma.tailSigma X ≤ (inferInstance : MeasurableSpace Ω) :=
    TailSigma.tailSigma_le X hX_meas
  haveI : Fact (TailSigma.tailSigma X ≤ (inferInstance : MeasurableSpace Ω)) := ⟨hm_le⟩

  -- Step 1: Show ∫ |(indIic (n:ℝ)) ∘ X 0 - 1| → 0
  -- Integral of |indicator - 1| = μ(X 0 > n) → 0 by continuity
  have h_indicator_tendsto : Tendsto (fun n : ℕ =>
      ∫ ω, |(indIic (n : ℝ)) (X 0 ω) - 1| ∂μ) atTop (𝓝 0) := by
    -- |indIic n - 1| = indicator of (n, ∞) since indIic n = indicator of (-∞, n]
    have h_eq : ∀ n : ℕ, ∫ ω, |(indIic (n : ℝ)) (X 0 ω) - 1| ∂μ
        = (μ (X 0 ⁻¹' Set.Ioi (n : ℝ))).toReal := by
      intro n
      have : (fun ω => |(indIic (n : ℝ)) (X 0 ω) - 1|)
          = (Set.Ioi (n : ℝ)).indicator (fun _ => (1 : ℝ)) ∘ (X 0) := by
        ext ω
        simp only [indIic, Set.indicator, Function.comp_apply, Set.mem_Ioi, Set.mem_Iic]
        split_ifs with h1 h2
        · -- X 0 ω ≤ n and X 0 ω > n: contradiction
          linarith
        · -- X 0 ω ≤ n and ¬(X 0 ω > n): both give 0
          norm_num
        · -- ¬(X 0 ω ≤ n) and X 0 ω > n: both give 1
          norm_num
        · -- ¬(X 0 ω ≤ n) and ¬(X 0 ω > n): contradiction
          linarith
      rw [this]
      -- Rewrite composition as indicator on preimage
      have h_comp : (Set.Ioi (n : ℝ)).indicator (fun _ => (1 : ℝ)) ∘ (X 0)
          = (X 0 ⁻¹' Set.Ioi (n : ℝ)).indicator (fun _ => (1 : ℝ)) := by
        ext ω
        simp only [Function.comp_apply, Set.indicator_apply]
        rfl
      rw [h_comp, integral_indicator (measurableSet_preimage (hX_meas 0) measurableSet_Ioi),
          setIntegral_one_eq_measureReal]
      rfl
    simp only [h_eq]
    -- The sets {X 0 > n} decrease to empty
    have h_antitone : Antitone (fun n : ℕ => X 0 ⁻¹' Set.Ioi (n : ℝ)) := by
      intro n m hnm
      apply Set.preimage_mono
      intro x hx
      simp only [Set.mem_Ioi] at hx ⊢
      calc x > (m : ℝ) := hx
           _ ≥ (n : ℝ) := by simp [Nat.cast_le, hnm]
    have h_empty : (⋂ (n : ℕ), X 0 ⁻¹' Set.Ioi (n : ℝ)) = ∅ := by
      ext ω
      simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_Ioi, Set.mem_empty_iff_false, iff_false]
      intro h
      -- For all n, X 0 ω > n, impossible by Archimedean property
      obtain ⟨n, hn⟩ := exists_nat_gt (X 0 ω)
      have h1 : X 0 ω > (n : ℝ) := h n
      linarith
    have h_meas : ∀ (n : ℕ), NullMeasurableSet (X 0 ⁻¹' Set.Ioi (n : ℝ)) μ := fun n =>
      (measurableSet_preimage (hX_meas 0) measurableSet_Ioi).nullMeasurableSet
    have h_fin : ∃ (n : ℕ), μ (X 0 ⁻¹' Set.Ioi (n : ℝ)) ≠ ⊤ := by
      use 0
      exact measure_ne_top μ _
    have h_tendsto_ennreal : Tendsto (fun (n : ℕ) => μ (X 0 ⁻¹' Set.Ioi (n : ℝ))) atTop (𝓝 0) := by
      have := tendsto_measure_iInter_atTop (μ := μ) h_meas h_antitone h_fin
      simp only [h_empty, measure_empty] at this
      simpa [Function.comp] using this
    -- Convert from ENNReal to Real using continuity of toReal at 0
    have h_ne_top : ∀ n, μ (X 0 ⁻¹' Set.Ioi (n : ℝ)) ≠ ⊤ := fun n => measure_ne_top μ _
    have h_zero_ne_top : (0 : ENNReal) ≠ ⊤ := by norm_num
    rw [← ENNReal.toReal_zero]
    exact (ENNReal.continuousAt_toReal h_zero_ne_top).tendsto.comp h_tendsto_ennreal

  -- Step 2: L¹ contraction - ‖condExp f - condExp 1‖₁ ≤ ‖f - 1‖₁
  -- Since condExp 1 = 1, get ‖alphaIicCE - 1‖₁ ≤ ‖indicator - 1‖₁
  have h_contraction : ∀ n : ℕ,
      ∫ ω, |alphaIicCE X hX_contract hX_meas hX_L2 (n : ℝ) ω - 1| ∂μ
      ≤ ∫ ω, |(indIic (n : ℝ)) (X 0 ω) - 1| ∂μ := by
    intro n
    -- Use linearity: alphaIicCE - 1 = condExp(indicator) - condExp(1) = condExp(indicator - 1)
    have h_const : (fun _ : Ω => (1 : ℝ)) =ᵐ[μ]
        μ[(fun _ : Ω => (1 : ℝ)) | TailSigma.tailSigma X] :=
      (condExp_const (μ := μ) (m := TailSigma.tailSigma X) hm_le (1 : ℝ)).symm.eventuallyEq
    have h_ae : (fun ω => alphaIicCE X hX_contract hX_meas hX_L2 (n : ℝ) ω - 1)
        =ᵐ[μ] μ[(fun ω => (indIic (n : ℝ)) (X 0 ω) - 1) | TailSigma.tailSigma X] := by
      unfold alphaIicCE
      have h_int : Integrable ((indIic (n : ℝ)) ∘ (X 0)) μ := by
        have : indIic (n : ℝ) = Set.indicator (Set.Iic (n : ℝ)) (fun _ => (1 : ℝ)) := rfl
        rw [this]
        exact Exchangeability.Probability.integrable_indicator_comp (hX_meas 0) measurableSet_Iic
      filter_upwards [h_const, condExp_sub (μ := μ) (m := TailSigma.tailSigma X)
        h_int (integrable_const (1 : ℝ))] with ω h_const_ω h_sub_ω
      simp only [Pi.sub_apply] at h_sub_ω ⊢
      -- h_const_ω : 1 = μ[fun _ => 1|...] ω
      -- h_sub_ω : μ[indIic n ∘ X 0 - fun x => μ[fun x => 1|...] ω|...] ω = ...
      -- After substitution, we get the equality we need
      calc alphaIicCE X hX_contract hX_meas hX_L2 (n : ℝ) ω - 1
          = μ[indIic (n : ℝ) ∘ X 0|TailSigma.tailSigma X] ω - 1 := by rfl
        _ = μ[indIic (n : ℝ) ∘ X 0|TailSigma.tailSigma X] ω - μ[(fun _ => 1)|TailSigma.tailSigma X] ω := by rw [← h_const_ω]
        _ = μ[indIic (n : ℝ) ∘ X 0 - (fun _ => 1)|TailSigma.tailSigma X] ω := by rw [← h_sub_ω]
        _ = μ[(fun ω => indIic (n : ℝ) (X 0 ω) - 1)|TailSigma.tailSigma X] ω := by congr
    have h_ae_abs : (fun ω => |alphaIicCE X hX_contract hX_meas hX_L2 (n : ℝ) ω - 1|)
        =ᵐ[μ] (fun ω => |μ[(fun ω => (indIic (n : ℝ)) (X 0 ω) - 1) | TailSigma.tailSigma X] ω|) := by
      filter_upwards [h_ae] with ω hω
      rw [hω]
    rw [integral_congr_ae h_ae_abs]
    exact integral_abs_condExp_le (μ := μ) (m := TailSigma.tailSigma X) _

  -- Apply squeeze theorem: 0 ≤ ‖alphaIicCE - 1‖₁ ≤ ‖indicator - 1‖₁ → 0
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h_indicator_tendsto ?_ h_contraction
  intro n
  exact integral_nonneg (fun ω => abs_nonneg _)

/-- **A.e. pointwise endpoint limit at -∞**.

**Proof strategy:**
Combine monotonicity (from conditional expectation), boundedness (0 ≤ alphaIicCE ≤ 1),
and L¹ → 0 to conclude a.e. pointwise → 0 along integers. -/
lemma alphaIicCE_ae_tendsto_zero_atBot
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ =>
      alphaIicCE X hX_contract hX_meas hX_L2 (-(n : ℝ)) ω)
      atTop (𝓝 0) := by
  -- Strategy:
  -- 1. alphaIicCE is monotone decreasing in the sequence (-(n:ℝ))
  --    (since t ↦ alphaIicCE t is monotone increasing)
  -- 2. alphaIicCE ∈ [0,1] (bounded)
  -- 3. By monotone convergence, the sequence converges a.e. to some limit L
  -- 4. By L¹ convergence to 0, we have L = 0 a.e.

  -- Set up the tail σ-algebra (needed for conditional expectation)
  have hm_le : TailSigma.tailSigma X ≤ (inferInstance : MeasurableSpace Ω) :=
    TailSigma.tailSigma_le X hX_meas

  -- Step 1: Monotonicity - for each ω, alphaIicCE (-(m):ℝ) ω ≤ alphaIicCE (-(n):ℝ)) ω when n ≤ m
  have h_mono : ∀ᵐ ω ∂μ, ∀ n m : ℕ, n ≤ m →
      alphaIicCE X hX_contract hX_meas hX_L2 (-(m : ℝ)) ω
      ≤ alphaIicCE X hX_contract hX_meas hX_L2 (-(n : ℝ)) ω := by
    -- Use alphaIicCE_mono: s ≤ t implies alphaIicCE s ≤ alphaIicCE t a.e.
    -- When n ≤ m, we have -(m : ℝ) ≤ -(n : ℝ)
    -- Combine countably many ae statements using ae_all_iff
    rw [ae_all_iff]
    intro n
    rw [ae_all_iff]
    intro m
    by_cases hnm : n ≤ m
    · -- When n ≤ m, use alphaIicCE_mono with -(m:ℝ) ≤ -(n:ℝ)
      have h_le : -(m : ℝ) ≤ -(n : ℝ) := by
        simp [neg_le_neg_iff, Nat.cast_le, hnm]
      filter_upwards [alphaIicCE_mono X hX_contract hX_meas hX_L2 (-(m : ℝ)) (-(n : ℝ)) h_le] with ω hω
      intro _
      exact hω
    · -- When ¬(n ≤ m), the implication is vacuously true
      exact ae_of_all μ (fun ω h_contra => absurd h_contra hnm)

  -- Step 2: Boundedness - 0 ≤ alphaIicCE ≤ 1
  have h_bound : ∀ᵐ ω ∂μ, ∀ n : ℕ,
      0 ≤ alphaIicCE X hX_contract hX_meas hX_L2 (-(n : ℝ)) ω
      ∧ alphaIicCE X hX_contract hX_meas hX_L2 (-(n : ℝ)) ω ≤ 1 := by
    -- Use alphaIicCE_nonneg_le_one for each t, combine with ae_all_iff
    rw [ae_all_iff]
    intro n
    exact alphaIicCE_nonneg_le_one X hX_contract hX_meas hX_L2 (-(n : ℝ))

  -- Step 3: Monotone bounded sequences converge a.e.
  have h_ae_conv : ∀ᵐ ω ∂μ, ∃ L : ℝ, Tendsto (fun n : ℕ =>
      alphaIicCE X hX_contract hX_meas hX_L2 (-(n : ℝ)) ω) atTop (𝓝 L) := by
    -- Monotone decreasing bounded sequence converges (monotone convergence theorem)
    filter_upwards [h_mono, h_bound] with ω h_mono_ω h_bound_ω
    -- For this ω, the sequence is antitone and bounded, so it converges
    refine ⟨⨅ (n : ℕ), alphaIicCE X hX_contract hX_meas hX_L2 (-(n : ℝ)) ω, ?_⟩
    apply tendsto_atTop_ciInf
    · -- Antitone: n ≤ m implies f m ≤ f n
      intro n m hnm
      exact h_mono_ω n m hnm
    · -- Bounded below by 0
      refine ⟨0, ?_⟩
      rintro _ ⟨k, rfl⟩
      exact (h_bound_ω k).1

  -- Step 4: The limit is 0 by L¹ convergence
  -- Define the limit function L : Ω → ℝ
  -- For each ω in the convergence set, L(ω) = lim f_n(ω) = ⨅ n, f_n(ω)
  let L_fun : Ω → ℝ := fun ω => ⨅ (n : ℕ), alphaIicCE X hX_contract hX_meas hX_L2 (-(n : ℝ)) ω

  -- L_fun ≥ 0 a.e. (since each f_n ≥ 0 a.e.)
  have hL_nonneg : 0 ≤ᵐ[μ] L_fun := by
    filter_upwards [h_bound] with ω h_bound_ω
    apply le_ciInf
    intro n
    exact (h_bound_ω n).1

  -- From L¹ convergence ∫|f_n| → 0 and f_n ≥ 0, we get ∫ f_n → 0
  have h_L1_conv : Tendsto (fun n : ℕ =>
      ∫ ω, alphaIicCE X hX_contract hX_meas hX_L2 (-(n : ℝ)) ω ∂μ) atTop (𝓝 0) := by
    have h_abs := alphaIicCE_L1_tendsto_zero_atBot X hX_contract hX_meas hX_L2
    -- Since alphaIicCE ≥ 0 a.e., we have |alphaIicCE| = alphaIicCE a.e.
    -- Therefore ∫|f| = ∫ f
    refine h_abs.congr' ?_
    rw [EventuallyEq, eventually_atTop]
    use 0
    intro n _
    apply integral_congr_ae
    filter_upwards [alphaIicCE_nonneg_le_one X hX_contract hX_meas hX_L2 (-(n : ℝ))] with ω hω
    exact abs_of_nonneg hω.1

  -- By dominated convergence: ∫ L_fun = lim ∫ f_n = 0
  have hL_integral_zero : ∫ ω, L_fun ω ∂μ = 0 := by
    -- Use dominated convergence theorem with bound = 1 (constant function)
    have h_conv_ae : ∀ᵐ ω ∂μ, Tendsto (fun (n : ℕ) => alphaIicCE X hX_contract hX_meas hX_L2 (-(n : ℝ)) ω)
        atTop (𝓝 (L_fun ω)) := by
      filter_upwards [h_ae_conv, h_bound, h_mono] with ω ⟨L, hL⟩ h_bound_ω h_mono_ω
      have hL_is_inf : L = L_fun ω := by
        apply tendsto_nhds_unique hL
        apply tendsto_atTop_ciInf h_mono_ω
        exact ⟨0, fun y hy => by obtain ⟨k, hk⟩ := hy; rw [← hk]; exact (h_bound_ω k).1⟩
      rw [← hL_is_inf]
      exact hL
    have h_meas : ∀ (n : ℕ), AEStronglyMeasurable (fun ω => alphaIicCE X hX_contract hX_meas hX_L2 (-(n : ℝ)) ω) μ := by
      intro n
      -- alphaIicCE is conditional expectation μ[·|m], which is:
      -- 1. StronglyMeasurable[m] by stronglyMeasurable_condExp
      -- 2. AEStronglyMeasurable[m] by .aestronglyMeasurable
      -- 3. AEStronglyMeasurable[m₀] by .mono hm_le (where m ≤ m₀)
      unfold alphaIicCE
      exact stronglyMeasurable_condExp.aestronglyMeasurable.mono hm_le
    have h_bound_ae : ∀ (n : ℕ), ∀ᵐ ω ∂μ, ‖alphaIicCE X hX_contract hX_meas hX_L2 (-(n : ℝ)) ω‖ ≤ (1 : ℝ) := by
      intro n
      filter_upwards [alphaIicCE_nonneg_le_one X hX_contract hX_meas hX_L2 (-(n : ℝ))] with ω hω
      rw [Real.norm_eq_abs, abs_of_nonneg hω.1]
      exact hω.2
    have h_int : Integrable (fun _ : Ω => (1 : ℝ)) μ := integrable_const 1
    have h_lim := tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
      h_meas h_int h_bound_ae h_conv_ae
    rw [← tendsto_nhds_unique h_lim h_L1_conv]

  -- Since L_fun ≥ 0 a.e. and ∫ L_fun = 0, we have L_fun = 0 a.e.
  have hL_ae_zero : L_fun =ᵐ[μ] 0 := by
    -- Need to show L_fun is integrable first
    have hL_int : Integrable L_fun μ := by
      -- L_fun is bounded by 1 a.e., so it's integrable on a probability space
      have hL_bound : ∀ᵐ ω ∂μ, ‖L_fun ω‖ ≤ 1 := by
        filter_upwards [hL_nonneg, h_bound] with ω hω_nn h_bound_ω
        rw [Real.norm_eq_abs, abs_of_nonneg hω_nn]
        -- L_fun ω = ⨅ n, f(n) where each f(n) ≤ 1, so L_fun ω ≤ 1
        -- Use that infimum is ≤ any particular value
        calc L_fun ω
            = ⨅ (n : ℕ), alphaIicCE X hX_contract hX_meas hX_L2 (-(n : ℝ)) ω := rfl
          _ ≤ alphaIicCE X hX_contract hX_meas hX_L2 (-((0 : ℕ) : ℝ)) ω := by
              apply ciInf_le
              -- Bounded below by 0 (from alphaIicCE_nonneg_le_one)
              refine ⟨0, fun y hy => ?_⟩
              obtain ⟨k, hk⟩ := hy
              rw [← hk]
              exact (h_bound_ω k).1
          _ ≤ 1 := (h_bound_ω 0).2
      -- L_fun is AEStronglyMeasurable as the a.e. limit of measurable functions
      have hL_meas : AEStronglyMeasurable L_fun μ := by
        -- Each alphaIicCE (-(n:ℝ)) is AEStronglyMeasurable (conditional expectation)
        have h_meas_n : ∀ (n : ℕ), AEStronglyMeasurable (fun ω => alphaIicCE X hX_contract hX_meas hX_L2 (-(n : ℝ)) ω) μ := by
          intro n
          unfold alphaIicCE
          exact stronglyMeasurable_condExp.aestronglyMeasurable.mono hm_le
        -- They converge a.e. to L_fun (by monotone convergence)
        have h_conv_ae_n : ∀ᵐ ω ∂μ, Tendsto (fun (n : ℕ) => alphaIicCE X hX_contract hX_meas hX_L2 (-(n : ℝ)) ω)
            atTop (𝓝 (L_fun ω)) := by
          filter_upwards [h_ae_conv, h_bound, h_mono] with ω ⟨L, hL⟩ h_bound_ω h_mono_ω
          have hL_is_inf : L = L_fun ω := by
            apply tendsto_nhds_unique hL
            apply tendsto_atTop_ciInf h_mono_ω
            exact ⟨0, fun y hy => by obtain ⟨k, hk⟩ := hy; rw [← hk]; exact (h_bound_ω k).1⟩
          rw [← hL_is_inf]
          exact hL
        -- Apply aestronglyMeasurable_of_tendsto_ae
        exact aestronglyMeasurable_of_tendsto_ae atTop h_meas_n h_conv_ae_n
      exact Integrable.of_bound hL_meas 1 hL_bound
    -- Now apply integral_eq_zero_iff_of_nonneg_ae
    rw [← integral_eq_zero_iff_of_nonneg_ae hL_nonneg hL_int]
    exact hL_integral_zero

  -- Now show Tendsto f_n (𝓝 0) at a.e. ω
  filter_upwards [h_ae_conv, hL_ae_zero, h_bound, h_mono] with ω ⟨L, hL⟩ hL_zero h_bound_ω h_mono_ω
  -- At this ω, we have f_n → L and L_fun(ω) = 0
  have hL_eq : L = L_fun ω := by
    apply tendsto_nhds_unique hL
    apply tendsto_atTop_ciInf h_mono_ω
    exact ⟨0, fun y hy => by obtain ⟨k, hk⟩ := hy; rw [← hk]; exact (h_bound_ω k).1⟩
  rw [hL_eq, hL_zero] at hL
  exact hL

/-- **A.e. pointwise endpoint limit at +∞**.

**Proof strategy:**
Similar to the -∞ case, using monotonicity + boundedness + L¹ → 1. -/
lemma alphaIicCE_ae_tendsto_one_atTop
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ =>
      alphaIicCE X hX_contract hX_meas hX_L2 (n : ℝ) ω)
      atTop (𝓝 1) := by
  -- Strategy: Similar to atBot case
  -- 1. alphaIicCE is monotone increasing in n
  -- 2. alphaIicCE ∈ [0,1] (bounded)
  -- 3. By monotone convergence, the sequence converges a.e. to some limit L
  -- 4. By L¹ convergence to 1, we have L = 1 a.e.

  -- Step 1: Monotonicity - for each ω, alphaIicCE (n:ℝ) ω ≤ alphaIicCE (m:ℝ) ω when n ≤ m
  have h_mono : ∀ᵐ ω ∂μ, ∀ n m : ℕ, n ≤ m →
      alphaIicCE X hX_contract hX_meas hX_L2 (n : ℝ) ω
      ≤ alphaIicCE X hX_contract hX_meas hX_L2 (m : ℝ) ω := by
    -- Use alphaIicCE_mono with countable ae union
    rw [ae_all_iff]
    intro n
    rw [ae_all_iff]
    intro m
    by_cases hnm : n ≤ m
    · -- When n ≤ m, use alphaIicCE_mono with (n:ℝ) ≤ (m:ℝ)
      have h_le : (n : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hnm
      filter_upwards [alphaIicCE_mono X hX_contract hX_meas hX_L2 (n : ℝ) (m : ℝ) h_le] with ω hω
      intro _
      exact hω
    · -- When ¬(n ≤ m), the implication is vacuously true
      exact ae_of_all μ (fun ω h_contra => absurd h_contra hnm)

  -- Step 2: Boundedness - 0 ≤ alphaIicCE ≤ 1
  have h_bound : ∀ᵐ ω ∂μ, ∀ n : ℕ,
      0 ≤ alphaIicCE X hX_contract hX_meas hX_L2 (n : ℝ) ω
      ∧ alphaIicCE X hX_contract hX_meas hX_L2 (n : ℝ) ω ≤ 1 := by
    -- Use alphaIicCE_nonneg_le_one with countable ae union
    rw [ae_all_iff]
    intro n
    exact alphaIicCE_nonneg_le_one X hX_contract hX_meas hX_L2 (n : ℝ)

  -- Step 3: Monotone bounded sequences converge a.e.
  have h_ae_conv : ∀ᵐ ω ∂μ, ∃ L : ℝ, Tendsto (fun n : ℕ =>
      alphaIicCE X hX_contract hX_meas hX_L2 (n : ℝ) ω) atTop (𝓝 L) := by
    -- Monotone increasing bounded sequence converges (monotone convergence theorem)
    filter_upwards [h_mono, h_bound] with ω h_mono_ω h_bound_ω
    -- For this ω, the sequence is monotone and bounded, so it converges
    refine ⟨⨆ (n : ℕ), alphaIicCE X hX_contract hX_meas hX_L2 (n : ℝ) ω, ?_⟩
    apply tendsto_atTop_ciSup
    · -- Monotone: n ≤ m implies f n ≤ f m
      intro n m hnm
      exact h_mono_ω n m hnm
    · -- Bounded above by 1
      refine ⟨1, ?_⟩
      intro y hy
      obtain ⟨k, hk⟩ := hy
      rw [← hk]
      exact (h_bound_ω k).2

  -- Step 4: The limit is 1 by L¹ convergence
  -- If f_n → L a.e. and f_n → 1 in L¹, then L = 1 a.e.

  -- Set up the tail σ-algebra (needed for conditional expectation)
  have hm_le : TailSigma.tailSigma X ≤ (inferInstance : MeasurableSpace Ω) :=
    TailSigma.tailSigma_le X hX_meas

  -- Define the limit function U : Ω → ℝ (supremum instead of infimum)
  let U_fun : Ω → ℝ := fun ω => ⨆ (n : ℕ), alphaIicCE X hX_contract hX_meas hX_L2 (n : ℝ) ω

  -- U_fun ≤ 1 a.e.
  have hU_le_one : U_fun ≤ᵐ[μ] 1 := by
    filter_upwards [h_bound] with ω h_bound_ω
    apply ciSup_le
    intro n
    exact (h_bound_ω n).2

  -- Convert ∫|f_n - 1| → 0 to ∫ (1 - f_n) → 0
  have h_L1_conv : Tendsto (fun n : ℕ =>
      ∫ ω, (1 - alphaIicCE X hX_contract hX_meas hX_L2 (n : ℝ) ω) ∂μ) atTop (𝓝 0) := by
    have h_abs := alphaIicCE_L1_tendsto_one_atTop X hX_contract hX_meas hX_L2
    refine h_abs.congr' ?_
    rw [EventuallyEq, eventually_atTop]
    use 0
    intro n _
    apply integral_congr_ae
    filter_upwards [alphaIicCE_nonneg_le_one X hX_contract hX_meas hX_L2 (n : ℝ)] with ω hω
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hω.2)]

  -- Apply dominated convergence theorem
  have hU_integral_one : ∫ ω, U_fun ω ∂μ = 1 := by
    have h_conv_ae : ∀ᵐ ω ∂μ, Tendsto (fun (n : ℕ) => alphaIicCE X hX_contract hX_meas hX_L2 (n : ℝ) ω)
        atTop (𝓝 (U_fun ω)) := by
      filter_upwards [h_ae_conv, h_bound, h_mono] with ω ⟨L, hL⟩ h_bound_ω h_mono_ω
      have hU_is_sup : L = U_fun ω := by
        apply tendsto_nhds_unique hL
        apply tendsto_atTop_ciSup h_mono_ω
        exact ⟨1, fun y hy => by obtain ⟨k, hk⟩ := hy; rw [← hk]; exact (h_bound_ω k).2⟩
      rw [← hU_is_sup]
      exact hL
    have h_meas : ∀ (n : ℕ), AEStronglyMeasurable (fun ω => alphaIicCE X hX_contract hX_meas hX_L2 (n : ℝ) ω) μ := by
      intro n
      unfold alphaIicCE
      exact stronglyMeasurable_condExp.aestronglyMeasurable.mono hm_le
    have h_bound_ae : ∀ (n : ℕ), ∀ᵐ ω ∂μ, ‖alphaIicCE X hX_contract hX_meas hX_L2 (n : ℝ) ω‖ ≤ (1 : ℝ) := by
      intro n
      filter_upwards [alphaIicCE_nonneg_le_one X hX_contract hX_meas hX_L2 (n : ℝ)] with ω hω
      rw [Real.norm_eq_abs, abs_of_nonneg hω.1]
      exact hω.2
    have h_int : Integrable (fun _ : Ω => (1 : ℝ)) μ := integrable_const 1
    have h_lim := tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
      h_meas h_int h_bound_ae h_conv_ae
    have h_int_conv : Tendsto (fun n : ℕ => ∫ ω, alphaIicCE X hX_contract hX_meas hX_L2 (n : ℝ) ω ∂μ) atTop (𝓝 1) := by
      have : Tendsto (fun n : ℕ => 1 - ∫ ω, (1 - alphaIicCE X hX_contract hX_meas hX_L2 (n : ℝ) ω) ∂μ) atTop (𝓝 (1 - 0)) := by
        exact Tendsto.sub tendsto_const_nhds h_L1_conv
      have this' : Tendsto (fun n : ℕ => 1 - ∫ ω, (1 - alphaIicCE X hX_contract hX_meas hX_L2 (n : ℝ) ω) ∂μ) atTop (𝓝 1) := by
        convert this using 2
        norm_num
      -- Show integral convergence by algebra
      refine this'.congr' ?_
      rw [EventuallyEq, eventually_atTop]
      use 0
      intro n _
      -- Show: 1 - ∫ (1 - f) = ∫ f
      have h_f_int : Integrable (fun ω => alphaIicCE X hX_contract hX_meas hX_L2 (n : ℝ) ω) μ := by
        refine Integrable.of_bound (stronglyMeasurable_condExp.aestronglyMeasurable.mono hm_le) 1 ?_
        filter_upwards [alphaIicCE_nonneg_le_one X hX_contract hX_meas hX_L2 (n : ℝ)] with ω hω
        rw [Real.norm_eq_abs, abs_of_nonneg hω.1]
        exact hω.2
      calc 1 - ∫ ω, (1 - alphaIicCE X hX_contract hX_meas hX_L2 (n : ℝ) ω) ∂μ
          = 1 - (∫ ω, 1 ∂μ - ∫ ω, alphaIicCE X hX_contract hX_meas hX_L2 (n : ℝ) ω ∂μ) := by
              rw [integral_sub (integrable_const 1) h_f_int]
          _ = 1 - (μ.real Set.univ - ∫ ω, alphaIicCE X hX_contract hX_meas hX_L2 (n : ℝ) ω ∂μ) := by
              rw [integral_const, smul_eq_mul, mul_one]
          _ = 1 - (1 - ∫ ω, alphaIicCE X hX_contract hX_meas hX_L2 (n : ℝ) ω ∂μ) := by
              simp only [Measure.real]
              rw [measure_univ]
              simp
          _ = ∫ ω, alphaIicCE X hX_contract hX_meas hX_L2 (n : ℝ) ω ∂μ := by ring
    rw [← tendsto_nhds_unique h_lim h_int_conv]

  -- Conclude U_fun = 1 a.e.
  have hU_ae_one : U_fun =ᵐ[μ] 1 := by
    have hU_int : Integrable U_fun μ := by
      have hU_nonneg : 0 ≤ᵐ[μ] U_fun := by
        filter_upwards [h_bound] with ω h_bound_ω
        -- U_fun ω = sup of values all ≥ 0, so U_fun ω ≥ value at 0 ≥ 0
        refine le_trans ?_ (le_ciSup ⟨1, fun y hy => by obtain ⟨k, hk⟩ := hy; rw [← hk]; exact (h_bound_ω k).2⟩ (0 : ℕ))
        exact (h_bound_ω 0).1
      have hU_bound : ∀ᵐ ω ∂μ, ‖U_fun ω‖ ≤ 1 := by
        filter_upwards [hU_nonneg, h_bound] with ω hω_nn h_bound_ω
        rw [Real.norm_eq_abs, abs_of_nonneg hω_nn]
        -- U_fun ω = ⨆ n, f(n) where each f(n) ≤ 1, so U_fun ω ≤ 1
        -- Use that 1 is an upper bound for all values
        calc U_fun ω
            = ⨆ (n : ℕ), alphaIicCE X hX_contract hX_meas hX_L2 (n : ℝ) ω := rfl
          _ ≤ 1 := by
              apply ciSup_le
              intro n
              exact (h_bound_ω n).2
      have hU_meas : AEStronglyMeasurable U_fun μ := by
        -- Each alphaIicCE (n:ℝ) is AEStronglyMeasurable (conditional expectation)
        have h_meas_n : ∀ (n : ℕ), AEStronglyMeasurable (fun ω => alphaIicCE X hX_contract hX_meas hX_L2 (n : ℝ) ω) μ := by
          intro n
          unfold alphaIicCE
          exact stronglyMeasurable_condExp.aestronglyMeasurable.mono hm_le
        -- They converge a.e. to U_fun (by monotone convergence)
        have h_conv_ae_n : ∀ᵐ ω ∂μ, Tendsto (fun (n : ℕ) => alphaIicCE X hX_contract hX_meas hX_L2 (n : ℝ) ω)
            atTop (𝓝 (U_fun ω)) := by
          filter_upwards [h_ae_conv, h_bound, h_mono] with ω ⟨L, hL⟩ h_bound_ω h_mono_ω
          have hU_is_sup : L = U_fun ω := by
            apply tendsto_nhds_unique hL
            apply tendsto_atTop_ciSup h_mono_ω
            exact ⟨1, fun y hy => by obtain ⟨k, hk⟩ := hy; rw [← hk]; exact (h_bound_ω k).2⟩
          rw [← hU_is_sup]
          exact hL
        -- Apply aestronglyMeasurable_of_tendsto_ae
        exact aestronglyMeasurable_of_tendsto_ae atTop h_meas_n h_conv_ae_n
      exact Integrable.of_bound hU_meas 1 hU_bound
    -- Show U_fun = 1 a.e. by showing 1 - U_fun = 0 a.e.
    have h_diff_nonneg : 0 ≤ᵐ[μ] fun ω => 1 - U_fun ω := by
      filter_upwards [hU_le_one] with ω hω
      exact sub_nonneg.mpr hω
    have h_diff_int : Integrable (fun ω => 1 - U_fun ω) μ := by
      exact Integrable.sub (integrable_const 1) hU_int
    have h_diff_zero : ∫ ω, (1 - U_fun ω) ∂μ = 0 := by
      rw [integral_sub (integrable_const 1) hU_int, integral_const, smul_eq_mul, mul_one, hU_integral_one]
      norm_num
    have : (fun ω => 1 - U_fun ω) =ᵐ[μ] 0 := by
      rw [← integral_eq_zero_iff_of_nonneg_ae h_diff_nonneg h_diff_int]
      exact h_diff_zero
    filter_upwards [this] with ω hω
    have h_eq : 1 - U_fun ω = 0 := by simpa using hω
    have : 1 = U_fun ω := sub_eq_zero.mp h_eq
    exact this.symm

  -- Now show Tendsto f_n (𝓝 1) at a.e. ω
  filter_upwards [h_ae_conv, hU_ae_one, h_bound, h_mono] with ω ⟨L, hL⟩ hU_one h_bound_ω h_mono_ω
  -- At this ω, we have f_n → L and U_fun(ω) = 1
  have hL_eq : L = U_fun ω := by
    apply tendsto_nhds_unique hL
    apply tendsto_atTop_ciSup h_mono_ω
    exact ⟨1, fun y hy => by obtain ⟨k, hk⟩ := hy; rw [← hk]; exact (h_bound_ω k).2⟩
  rw [hL_eq, hU_one] at hL
  exact hL

/-- Right-continuous CDF built via mathlib's `stieltjesOfMeasurableRat`.

This construction automatically patches the null set where pointwise CDF axioms would
fail for the raw L¹ limit. The resulting CDF satisfies:
- Monotonicity everywhere (not just a.e.)
- Right-continuity everywhere
- Limits 0 at -∞ and 1 at +∞ for ALL ω (not just a.e.)

This enables the construction of `directing_measure` as a probability measure for all ω. -/
noncomputable def cdf_from_alpha
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ)
    (ω : Ω) (t : ℝ) : ℝ :=
  (ProbabilityTheory.stieltjesOfMeasurableRat
      (alphaIicRat X hX_contract hX_meas hX_L2)
      (measurable_alphaIicRat X hX_contract hX_meas hX_L2)
      ω) t

/-- F(ω,·) is monotone nondecreasing. -/
lemma cdf_from_alpha_mono
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ)
    (ω : Ω) :
    Monotone (cdf_from_alpha X hX_contract hX_meas hX_L2 ω) := fun s t hst =>
  (ProbabilityTheory.stieltjesOfMeasurableRat
      (alphaIicRat X hX_contract hX_meas hX_L2)
      (measurable_alphaIicRat X hX_contract hX_meas hX_L2)
      ω).mono hst

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
  -- StieltjesFunction.right_continuous gives ContinuousWithinAt at Ici t
  -- We need Tendsto at 𝓝[>] t = 𝓝[Ioi t] t
  -- continuousWithinAt_Ioi_iff_Ici provides the equivalence
  let f := ProbabilityTheory.stieltjesOfMeasurableRat
      (alphaIicRat X hX_contract hX_meas hX_L2)
      (measurable_alphaIicRat X hX_contract hX_meas hX_L2)
      ω
  have h_rc : ContinuousWithinAt f (Set.Ici t) t := f.right_continuous t
  -- Convert ContinuousWithinAt (Ici) to ContinuousWithinAt (Ioi)
  rw [← continuousWithinAt_Ioi_iff_Ici] at h_rc
  exact h_rc

/-- Bounds 0 ≤ F ≤ 1 (pointwise in ω,t). -/
lemma cdf_from_alpha_bounds
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ)
    (ω : Ω) (t : ℝ) :
    0 ≤ cdf_from_alpha X hX_contract hX_meas hX_L2 ω t
    ∧ cdf_from_alpha X hX_contract hX_meas hX_L2 ω t ≤ 1 := by
  -- The stieltjesOfMeasurableRat construction produces a function with limits 0 at -∞ and 1 at +∞.
  -- By monotonicity, all values are in [0,1].
  let f := ProbabilityTheory.stieltjesOfMeasurableRat
      (alphaIicRat X hX_contract hX_meas hX_L2)
      (measurable_alphaIicRat X hX_contract hX_meas hX_L2)
      ω
  have h_tendsto_bot : Filter.Tendsto (f ·) Filter.atBot (𝓝 0) :=
    ProbabilityTheory.tendsto_stieltjesOfMeasurableRat_atBot
      (measurable_alphaIicRat X hX_contract hX_meas hX_L2) ω
  have h_tendsto_top : Filter.Tendsto (f ·) Filter.atTop (𝓝 1) :=
    ProbabilityTheory.tendsto_stieltjesOfMeasurableRat_atTop
      (measurable_alphaIicRat X hX_contract hX_meas hX_L2) ω
  have h_mono : Monotone (f ·) := f.mono
  constructor
  · -- Lower bound: f(t) ≥ 0
    -- For any s < t, f(s) ≤ f(t) by monotonicity.
    -- As s → -∞, f(s) → 0, so 0 ≤ f(t).
    -- Proof by contradiction: if f(t) < 0, pick ε = -f(t)/2 > 0.
    -- Then eventually f(s) ∈ (-ε, ε), so f(s) > -ε = f(t)/2.
    -- But also f(s) ≤ f(t) for s ≤ t, contradicting f(s) > f(t)/2 > f(t).
    by_contra h_neg
    push_neg at h_neg
    -- f(t) < 0, so ε := -f(t)/2 > 0
    set ε := -cdf_from_alpha X hX_contract hX_meas hX_L2 ω t / 2 with hε_def
    have hε_pos : 0 < ε := by simp [hε_def]; linarith
    -- Eventually f(s) ∈ (-ε, ε)
    have h_nhds : Set.Ioo (-ε) ε ∈ 𝓝 (0 : ℝ) := Ioo_mem_nhds (by linarith) hε_pos
    have h_preimage := h_tendsto_bot h_nhds
    rw [Filter.mem_map, Filter.mem_atBot_sets] at h_preimage
    obtain ⟨N, hN⟩ := h_preimage
    -- Take s = min N t, then s ≤ N and s ≤ t
    let s := min N t
    have hs_le_N : s ≤ N := min_le_left N t
    have hs_le_t : s ≤ t := min_le_right N t
    -- f(s) ∈ (-ε, ε)
    have hs_in : f s ∈ Set.Ioo (-ε) ε := hN s hs_le_N
    simp only [Set.mem_Ioo] at hs_in
    -- f(s) ≤ f(t) by monotonicity
    have hs_mono : f s ≤ f t := h_mono hs_le_t
    -- Connect f t with cdf_from_alpha
    have h_eq_t : (f : ℝ → ℝ) t = cdf_from_alpha X hX_contract hX_meas hX_L2 ω t := rfl
    -- Now we have: f(s) > -ε = f(t)/2 and f(s) ≤ f(t) < 0
    have h1 : f s > -ε := hs_in.1
    have h2 : -ε = cdf_from_alpha X hX_contract hX_meas hX_L2 ω t / 2 := by
      simp [hε_def]; ring
    -- f(s) > f(t)/2 and f(s) ≤ f(t) < 0
    -- If f(t) < 0, then f(t)/2 > f(t), so f(s) > f(t)/2 > f(t) contradicts f(s) ≤ f(t).
    have h_contra : cdf_from_alpha X hX_contract hX_meas hX_L2 ω t / 2 >
                    cdf_from_alpha X hX_contract hX_meas hX_L2 ω t := by linarith
    linarith [h1, h2, hs_mono, h_eq_t, h_contra]
  · -- Upper bound: f(t) ≤ 1
    -- Similar argument: for any s > t, f(t) ≤ f(s) by monotonicity.
    -- As s → +∞, f(s) → 1, so f(t) ≤ 1.
    by_contra h_gt
    push_neg at h_gt
    -- f(t) > 1, so ε := (f(t) - 1)/2 > 0
    set ε := (cdf_from_alpha X hX_contract hX_meas hX_L2 ω t - 1) / 2 with hε_def
    have hε_pos : 0 < ε := by simp [hε_def]; linarith
    -- Eventually f(s) ∈ (1-ε, 1+ε)
    have h_nhds : Set.Ioo (1 - ε) (1 + ε) ∈ 𝓝 (1 : ℝ) := Ioo_mem_nhds (by linarith) (by linarith)
    have h_preimage := h_tendsto_top h_nhds
    rw [Filter.mem_map, Filter.mem_atTop_sets] at h_preimage
    obtain ⟨N, hN⟩ := h_preimage
    -- Take s = max N t, then s ≥ N and s ≥ t
    let s := max N t
    have hs_ge_N : N ≤ s := le_max_left N t
    have hs_ge_t : t ≤ s := le_max_right N t
    -- f(s) ∈ (1-ε, 1+ε)
    have hs_in : f s ∈ Set.Ioo (1 - ε) (1 + ε) := hN s hs_ge_N
    simp only [Set.mem_Ioo] at hs_in
    -- f(t) ≤ f(s) by monotonicity
    have hs_mono : f t ≤ f s := h_mono hs_ge_t
    -- Connect f t with cdf_from_alpha
    have h_eq_t : (f : ℝ → ℝ) t = cdf_from_alpha X hX_contract hX_meas hX_L2 ω t := rfl
    -- f(s) < 1 + ε = 1 + (f(t) - 1)/2 = (f(t) + 1)/2
    have h1 : f s < 1 + ε := hs_in.2
    have h2 : 1 + ε = (cdf_from_alpha X hX_contract hX_meas hX_L2 ω t + 1) / 2 := by
      simp [hε_def]; ring
    -- f(t) ≤ f(s) < (f(t) + 1)/2
    -- So f(t) < (f(t) + 1)/2, which means 2*f(t) < f(t) + 1, i.e., f(t) < 1.
    -- But we assumed f(t) > 1, contradiction.
    linarith [h1, h2, hs_mono, h_eq_t, h_gt]

/-- **A.e. convergence of α_{Iic t} → 0 as t → -∞ (along integers).**

This is the a.e. version of the endpoint limit. The statement for all ω cannot be
proven from the L¹ construction since `alphaIic` is defined via existential L¹ choice.

**Proof strategy:**
Combine the a.e. equality `alphaIic =ᵐ alphaIicCE` with `alphaIicCE_ae_tendsto_zero_atBot`.
Since both are a.e. statements and we take countable intersection over integers, we
get a.e. convergence of `alphaIic` along the integer sequence `-(n:ℝ)`.
-/
lemma alphaIic_ae_tendsto_zero_at_bot
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ =>
      alphaIic X hX_contract hX_meas hX_L2 (-(n : ℝ)) ω) atTop (𝓝 0) := by
  -- Step 1: For a.e. ω, alphaIic agrees with alphaIicCE at all integers
  have h_ae_eq : ∀ᵐ ω ∂μ, ∀ n : ℕ,
      alphaIic X hX_contract hX_meas hX_L2 (-(n : ℝ)) ω =
      alphaIicCE X hX_contract hX_meas hX_L2 (-(n : ℝ)) ω := by
    rw [ae_all_iff]
    intro n
    exact alphaIic_ae_eq_alphaIicCE X hX_contract hX_meas hX_L2 (-(n : ℝ))

  -- Step 2: alphaIicCE converges to 0 as t → -∞ for a.e. ω
  have h_CE_conv := alphaIicCE_ae_tendsto_zero_atBot X hX_contract hX_meas hX_L2

  -- Step 3: Combine to get alphaIic convergence for a.e. ω
  filter_upwards [h_ae_eq, h_CE_conv] with ω h_eq h_conv
  -- At this ω, alphaIic = alphaIicCE at all integers, and alphaIicCE → 0
  exact h_conv.congr (fun n => (h_eq n).symm)

/-- **A.e. convergence of α_{Iic t} → 1 as t → +∞ (along integers).**

This is the dual of `alphaIic_ae_tendsto_zero_at_bot`. The statement for all ω cannot be
proven from the L¹ construction since `alphaIic` is defined via existential L¹ choice.

**Proof strategy:**
Combine the a.e. equality `alphaIic =ᵐ alphaIicCE` with `alphaIicCE_ae_tendsto_one_atTop`.
-/
lemma alphaIic_ae_tendsto_one_at_top
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ =>
      alphaIic X hX_contract hX_meas hX_L2 (n : ℝ) ω) atTop (𝓝 1) := by
  -- Step 1: For a.e. ω, alphaIic agrees with alphaIicCE at all positive integers
  have h_ae_eq : ∀ᵐ ω ∂μ, ∀ n : ℕ,
      alphaIic X hX_contract hX_meas hX_L2 (n : ℝ) ω =
      alphaIicCE X hX_contract hX_meas hX_L2 (n : ℝ) ω := by
    rw [ae_all_iff]
    intro n
    exact alphaIic_ae_eq_alphaIicCE X hX_contract hX_meas hX_L2 (n : ℝ)

  -- Step 2: alphaIicCE converges to 1 as t → +∞ for a.e. ω
  have h_CE_conv := alphaIicCE_ae_tendsto_one_atTop X hX_contract hX_meas hX_L2

  -- Step 3: Combine to get alphaIic convergence for a.e. ω
  filter_upwards [h_ae_eq, h_CE_conv] with ω h_eq h_conv
  exact h_conv.congr (fun n => (h_eq n).symm)

-- **Note on `cdf_from_alpha_limits`:**
-- The axiom in MoreL2Helpers.lean requires the CDF limits to hold for ALL ω.
-- However, from the L¹ construction, we can only prove a.e. convergence:
-- - `alphaIic_ae_tendsto_zero_at_bot`: a.e. convergence to 0 as t → -∞
-- - `alphaIic_ae_tendsto_one_at_top`: a.e. convergence to 1 as t → +∞
--
-- The axiom should be weakened to an a.e. statement, and the `directing_measure`
-- construction should handle the null set by using a default probability measure
-- for ω outside the "good" set. This is a standard technique in probability theory.

/-- Build the directing measure ν from the CDF.

For each ω ∈ Ω, we construct ν(ω) as the probability measure on ℝ with CDF
given by t ↦ cdf_from_alpha X ω t.

This is defined directly using `stieltjesOfMeasurableRat.measure`, which gives a
probability measure for ALL ω (not just a.e.) because the `stieltjesOfMeasurableRat`
construction patches the null set automatically. -/
noncomputable def directing_measure
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ) :
    Ω → Measure ℝ :=
  fun ω =>
    (ProbabilityTheory.stieltjesOfMeasurableRat
        (alphaIicRat X hX_contract hX_meas hX_L2)
        (measurable_alphaIicRat X hX_contract hX_meas hX_L2)
        ω).measure

/-- The directing measure is a probability measure.

This is now trivial because `directing_measure` is defined via `stieltjesOfMeasurableRat.measure`,
which automatically has an `IsProbabilityMeasure` instance from mathlib. -/
lemma directing_measure_isProbabilityMeasure
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ)
    (ω : Ω) :
    IsProbabilityMeasure (directing_measure X hX_contract hX_meas hX_L2 ω) :=
  ProbabilityTheory.instIsProbabilityMeasure_stieltjesOfMeasurableRat
    (measurable_alphaIicRat X hX_contract hX_meas hX_L2) ω


