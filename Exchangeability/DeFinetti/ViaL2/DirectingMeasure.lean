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

/-- **Right-continuity of alphaIicCE at any real t.**

For any real t, the infimum over rationals greater than t is at most the value at t:
`⨅ q > t (rational), alphaIicCE q ω ≤ alphaIicCE t ω` a.e.

Combined with monotonicity (which gives the reverse inequality), this proves
the infimum equals the value.

**Proof strategy:**
- Indicators 1_{Iic s} are right-continuous in s: as s ↓ t, 1_{Iic s} ↓ 1_{Iic t}
- By dominated convergence for condExp, E[1_{Iic s}(X₀)|tail] → E[1_{Iic t}(X₀)|tail] in L¹
- For monotone decreasing sequences, L¹ convergence + boundedness ⇒ a.e. convergence
- Therefore ⨅ s > t, alphaIicCE s = alphaIicCE t a.e.

TODO: Implement using dominated convergence for conditional expectations.
The mathematical argument is standard: for CDFs built from conditional expectations,
right-continuity follows from dominated convergence applied to decreasing indicators.
-/
lemma alphaIicCE_right_continuous_at
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ)
    (t : ℝ) :
    ∀ᵐ ω ∂μ, ⨅ q : {q : ℚ // t < q}, alphaIicCE X hX_contract hX_meas hX_L2 (q : ℝ) ω
             ≤ alphaIicCE X hX_contract hX_meas hX_L2 t ω := by
  /-
  **Proof strategy (standard CDF right-continuity via DCT):**

  1. Get decreasing sequence qₙ → t of rationals with qₙ > t
     (via `Real.exists_seq_rat_strictAnti_tendsto`)

  2. Show ⨅_{all q > t} alphaIicCE q ≤ ⨅_n alphaIicCE qₙ
     (the infimum over a larger set is ≤ infimum over a subset)

  3. Show ⨅_n alphaIicCE qₙ = alphaIicCE t a.e.:
     - Indicators 1_{Iic qₙ} ↓ 1_{Iic t} pointwise (since ⋂_n Iic qₙ = Iic t)
     - By dominated convergence for condExp: condExp(1_{Iic qₙ}) → condExp(1_{Iic t}) in L¹
     - For monotone bounded sequences, L¹ convergence ⟹ a.e. convergence
     - So alphaIicCE qₙ → alphaIicCE t a.e.
     - For monotone decreasing sequences, ⨅_n = lim_n

  4. Conclude: ⨅_{q > t} alphaIicCE q ≤ ⨅_n alphaIicCE qₙ = alphaIicCE t a.e.

  The key mathlib lemmas are:
  - `tendsto_condExpL1_of_dominated_convergence` for L¹ convergence
  - `TendstoInMeasure.exists_seq_tendsto_ae` for a.e. convergence from L¹

  **Implementation outline:**
  1. Get decreasing sequence u_n → t of rationals with u_n > t
     (via `Real.exists_seq_rat_strictAnti_tendsto`)
  2. Show ⨅_{q > t} alphaIicCE q ≤ ⨅_n alphaIicCE (u_n) (infimum over larger set)
  3. Indicators 1_{Iic u_n} ↓ 1_{Iic t} pointwise as u_n ↓ t
  4. Apply DCT: condExp(1_{Iic u_n}) → condExp(1_{Iic t}) in L¹
  5. For monotone bounded sequences, L¹ convergence ⟹ a.e. convergence
  6. Therefore ⨅_n alphaIicCE (u_n) = lim_n alphaIicCE (u_n) = alphaIicCE t a.e.
  7. Conclude: ⨅_{q > t} alphaIicCE q ≤ alphaIicCE t a.e.

  This is standard CDF right-continuity via dominated convergence.
  -/
  -- PROOF STRUCTURE (standard CDF right-continuity via DCT):
  --
  -- Step 1: Get decreasing sequence u_n → t of rationals with u_n > t
  --         via Real.exists_seq_rat_strictAnti_tendsto
  --
  -- Step 2: Show ⨅_{q > t} alphaIicCE q ≤ ⨅_n alphaIicCE (u_n) (subset property)
  --         The sequence {u_n} ⊆ {q : ℚ // t < q}, so infimum over larger set ≤ infimum over subset
  --
  -- Step 3: Show ⨅_n alphaIicCE (u_n) ≤ alphaIicCE t a.e. via:
  --    a. Indicators 1_{Iic u_n} ↓ 1_{Iic t} pointwise (⋂_n Iic u_n = Iic t)
  --    b. Apply tendsto_condExpL1_of_dominated_convergence:
  --       condExp(1_{Iic u_n} ∘ X 0) → condExp(1_{Iic t} ∘ X 0) in L¹
  --       (bound by 1, limit exists pointwise)
  --    c. For monotone bounded L¹-convergent sequences, TendstoInMeasure.exists_seq_tendsto_ae
  --       gives a.e. convergent subsequence
  --    d. alphaIicCE is monotone (alphaIicCE_mono), so sequence is antitone
  --    e. For antitone sequences bounded below, ⨅_n = lim_n
  --
  -- Step 4: Combine: ⨅_{q > t} ≤ ⨅_n = lim_n = alphaIicCE t a.e.
  --
  -- Key lemmas:
  -- - Real.exists_seq_rat_strictAnti_tendsto
  -- - tendsto_condExpL1_of_dominated_convergence
  -- - TendstoInMeasure.exists_seq_tendsto_ae
  -- - alphaIicCE_mono

  -- Set up tail σ-algebra infrastructure
  have hm_le : TailSigma.tailSigma X ≤ (inferInstance : MeasurableSpace Ω) :=
    TailSigma.tailSigma_le X hX_meas
  haveI h_fact : Fact (TailSigma.tailSigma X ≤ (inferInstance : MeasurableSpace Ω)) := ⟨hm_le⟩
  haveI h_sf : SigmaFinite (μ.trim hm_le) :=
    Exchangeability.Probability.sigmaFinite_trim μ hm_le

  -- Step 1: Get decreasing rational sequence u_n → t with u_n > t
  obtain ⟨u, u_anti, u_gt, u_tendsto⟩ := Real.exists_seq_rat_strictAnti_tendsto t

  -- Step 2: The infimum over all q > t is at most the infimum over the sequence {u_n}
  -- because {u_n : n ∈ ℕ} ⊆ {q : ℚ // t < q}
  -- This holds a.e. where alphaIicCE is bounded below by 0
  have h_infs_le_ae : ∀ᵐ ω ∂μ, ⨅ q : {q : ℚ // t < q},
      alphaIicCE X hX_contract hX_meas hX_L2 (q : ℝ) ω ≤
      ⨅ n : ℕ, alphaIicCE X hX_contract hX_meas hX_L2 (u n : ℝ) ω := by
    -- First get a.e. boundedness
    have h_bdd_all : ∀ᵐ ω ∂μ, ∀ q : ℚ, 0 ≤ alphaIicCE X hX_contract hX_meas hX_L2 (q : ℝ) ω := by
      rw [ae_all_iff]; intro q
      filter_upwards [alphaIicCE_nonneg_le_one X hX_contract hX_meas hX_L2 (q : ℝ)]
        with ω ⟨h0, _⟩; exact h0
    filter_upwards [h_bdd_all] with ω h_bdd
    apply le_ciInf
    intro n
    have h_mem : t < (u n : ℝ) := u_gt n
    have h_bddBelow : BddBelow (Set.range (fun q : {q : ℚ // t < q} =>
        alphaIicCE X hX_contract hX_meas hX_L2 (q : ℝ) ω)) := by
      use 0
      intro x ⟨q, hq⟩
      rw [← hq]
      exact h_bdd q.val
    exact ciInf_le h_bddBelow ⟨u n, h_mem⟩

  -- Step 3: Show ⨅_n alphaIicCE (u_n) ≤ alphaIicCE t a.e.
  -- The key is that alphaIicCE (u_n) → alphaIicCE t a.e. and the sequence is antitone

  -- 3a: Define the sequence of functions f_n = indIic (u_n) ∘ X 0
  let fs (n : ℕ) := fun ω => indIic (u n : ℝ) (X 0 ω)
  let f := fun ω => indIic t (X 0 ω)

  -- 3b: Pointwise convergence: 1_{Iic u_n} → 1_{Iic t} pointwise as n → ∞
  -- This is because ⋂_n Iic u_n = Iic t when u_n ↓ t
  have h_ptwise : ∀ᵐ x ∂μ, Filter.Tendsto (fun n => fs n x) Filter.atTop (nhds (f x)) := by
    apply ae_of_all
    intro ω
    simp only [fs, f, indIic]
    by_cases hxt : X 0 ω ≤ t
    · -- X 0 ω ≤ t, so eventually X 0 ω ≤ u_n, hence eventually indicator = 1
      simp only [Set.indicator_apply, Set.mem_Iic]
      have h_ev : ∀ n, X 0 ω ≤ (u n : ℝ) := fun n =>
        hxt.trans (le_of_lt (u_gt n))
      simp only [h_ev, ↓reduceIte, hxt]
      exact tendsto_const_nhds
    · -- X 0 ω > t, so eventually X 0 ω > u_n (since u_n → t)
      push_neg at hxt
      simp only [Set.indicator_apply, Set.mem_Iic, not_le.mpr hxt, ↓reduceIte]
      -- u_n → t and X 0 ω > t, so eventually u_n < X 0 ω
      have h_ev : ∀ᶠ n in Filter.atTop, (u n : ℝ) < X 0 ω := by
        have : Filter.Tendsto (fun n => (u n : ℝ)) Filter.atTop (nhds t) := u_tendsto
        rw [Metric.tendsto_atTop] at this
        specialize this ((X 0 ω) - t) (by linarith)
        obtain ⟨N, hN⟩ := this
        apply Filter.eventually_atTop.mpr
        use N
        intro n hn
        specialize hN n hn
        rw [Real.dist_eq, abs_lt] at hN
        linarith
      apply Filter.Tendsto.congr' _ tendsto_const_nhds
      filter_upwards [h_ev] with n hn
      simp only [Set.mem_Iic, not_le.mpr hn, ↓reduceIte]

  -- 3c: Each f_n is a.e. strongly measurable
  have h_meas : ∀ n, AEStronglyMeasurable (fs n) μ := fun n =>
    ((indIic_measurable (u n : ℝ)).comp (hX_meas 0)).aestronglyMeasurable

  -- 3d: Uniform bound by 1
  have h_bound : ∀ n, ∀ᵐ x ∂μ, ‖fs n x‖ ≤ (1 : ℝ) := by
    intro n
    apply ae_of_all
    intro x
    simp only [fs]
    calc ‖indIic (u n : ℝ) (X 0 x)‖ = |indIic (u n : ℝ) (X 0 x)| := Real.norm_eq_abs _
      _ ≤ 1 := indIic_bdd (u n : ℝ) (X 0 x)

  -- 3e: Apply DCT to get L¹ convergence of condExpL1
  have h_L1_conv : Filter.Tendsto (fun n => condExpL1 hm_le μ (fs n))
      Filter.atTop (nhds (condExpL1 hm_le μ f)) := by
    apply tendsto_condExpL1_of_dominated_convergence (bound_fs := fun _ => 1)
    · exact h_meas
    · exact integrable_const 1
    · exact h_bound
    · exact h_ptwise

  -- 3f: L¹ convergence implies convergence in measure
  have h_in_measure : TendstoInMeasure μ
      (fun n => (↑(condExpL1 hm_le μ (fs n)) : Ω → ℝ))
      Filter.atTop
      ((↑(condExpL1 hm_le μ f) : Ω → ℝ)) :=
    tendstoInMeasure_of_tendsto_Lp h_L1_conv

  -- 3g: Extract a.e. convergent subsequence
  obtain ⟨ns, ns_mono, h_ae_conv⟩ := h_in_measure.exists_seq_tendsto_ae

  -- 3h: The condExpL1 representatives are a.e. equal to alphaIicCE
  have h_repr_eq : ∀ n, (↑(condExpL1 hm_le μ (fs n)) : Ω → ℝ) =ᵐ[μ]
      alphaIicCE X hX_contract hX_meas hX_L2 (u n : ℝ) := by
    intro n
    unfold alphaIicCE fs
    exact (condExp_ae_eq_condExpL1 hm_le _).symm

  have h_repr_eq_lim : (↑(condExpL1 hm_le μ f) : Ω → ℝ) =ᵐ[μ]
      alphaIicCE X hX_contract hX_meas hX_L2 t := by
    unfold alphaIicCE f
    exact (condExp_ae_eq_condExpL1 hm_le _).symm

  -- 3i: alphaIicCE (u (ns n)) → alphaIicCE t a.e.
  have h_ae_conv_alpha : ∀ᵐ ω ∂μ, Filter.Tendsto
      (fun n => alphaIicCE X hX_contract hX_meas hX_L2 (u (ns n) : ℝ) ω)
      Filter.atTop (nhds (alphaIicCE X hX_contract hX_meas hX_L2 t ω)) := by
    -- Combine the a.e. equalities with the a.e. convergence
    have h_all_repr : ∀ᵐ ω ∂μ, ∀ n, (↑(condExpL1 hm_le μ (fs n)) : Ω → ℝ) ω =
        alphaIicCE X hX_contract hX_meas hX_L2 (u n : ℝ) ω := by
      rw [ae_all_iff]
      intro n
      exact h_repr_eq n
    filter_upwards [h_ae_conv, h_all_repr, h_repr_eq_lim] with ω h_conv h_eq h_eq_lim
    -- h_conv: condExpL1(fs (ns n)) ω → condExpL1(f) ω
    -- h_eq: condExpL1(fs n) ω = alphaIicCE (u n) ω for all n
    -- h_eq_lim: condExpL1(f) ω = alphaIicCE t ω
    rw [← h_eq_lim]
    have h_eq_fun : (fun n => (↑(condExpL1 hm_le μ (fs (ns n))) : Ω → ℝ) ω) =
        (fun n => alphaIicCE X hX_contract hX_meas hX_L2 (u (ns n) : ℝ) ω) := by
      ext n
      exact h_eq (ns n)
    rw [← h_eq_fun]
    exact h_conv

  -- 3j: The sequence alphaIicCE (u_n) is antitone (since u_n is decreasing and alphaIicCE is monotone)
  have h_antitone_ae : ∀ᵐ ω ∂μ, ∀ m n : ℕ, m ≤ n →
      alphaIicCE X hX_contract hX_meas hX_L2 (u n : ℝ) ω ≤
      alphaIicCE X hX_contract hX_meas hX_L2 (u m : ℝ) ω := by
    -- Get a.e. monotonicity for all pairs of indices
    have h_all_mono : ∀ᵐ ω ∂μ, ∀ m n : ℕ, (u n : ℝ) ≤ (u m : ℝ) →
        alphaIicCE X hX_contract hX_meas hX_L2 (u n : ℝ) ω ≤
        alphaIicCE X hX_contract hX_meas hX_L2 (u m : ℝ) ω := by
      rw [ae_all_iff]; intro m
      rw [ae_all_iff]; intro n
      by_cases hle : (u n : ℝ) ≤ (u m : ℝ)
      · filter_upwards [alphaIicCE_mono X hX_contract hX_meas hX_L2 (u n : ℝ) (u m : ℝ) hle]
          with ω hω _; exact hω
      · exact ae_of_all μ (fun ω h_contra => absurd h_contra hle)
    filter_upwards [h_all_mono] with ω h_mono m n hmn
    -- u is strictly anti, so m ≤ n implies u n ≤ u m
    have h_u_le : (u n : ℝ) ≤ (u m : ℝ) := by
      rcases hmn.lt_or_eq with h | h
      · exact le_of_lt (Rat.cast_lt.mpr (u_anti.lt_iff_lt.mpr h))
      · simp [h]
    exact h_mono m n h_u_le

  -- 3k: Boundedness: alphaIicCE is bounded in [0, 1]
  have h_bdd_ae : ∀ᵐ ω ∂μ, ∀ n : ℕ,
      0 ≤ alphaIicCE X hX_contract hX_meas hX_L2 (u n : ℝ) ω := by
    rw [ae_all_iff]; intro n
    filter_upwards [alphaIicCE_nonneg_le_one X hX_contract hX_meas hX_L2 (u n : ℝ)] with ω ⟨h0, _⟩
    exact h0

  -- 3l: For an antitone bounded-below sequence converging to a limit, ⨅_n = lim_n
  -- Since the subsequence converges, the full infimum is at most the limit
  have h_inf_le_lim : ∀ᵐ ω ∂μ, ⨅ n : ℕ, alphaIicCE X hX_contract hX_meas hX_L2 (u n : ℝ) ω ≤
      alphaIicCE X hX_contract hX_meas hX_L2 t ω := by
    filter_upwards [h_ae_conv_alpha, h_antitone_ae, h_bdd_ae] with ω h_conv h_anti h_bdd
    -- The sequence along ns converges to alphaIicCE t ω
    -- The full infimum ≤ infimum along subsequence = limit along subsequence = alphaIicCE t ω

    -- First, ⨅_n ≤ ⨅_{n in subsequence} because we're taking inf over more terms
    have h1 : ⨅ n : ℕ, alphaIicCE X hX_contract hX_meas hX_L2 (u n : ℝ) ω ≤
        ⨅ k : ℕ, alphaIicCE X hX_contract hX_meas hX_L2 (u (ns k) : ℝ) ω := by
      apply le_ciInf
      intro k
      exact ciInf_le ⟨0, fun x ⟨n, hn⟩ => hn ▸ h_bdd n⟩ (ns k)

    -- For antitone sequences with a limit, ⨅ = lim
    -- The subsequence is also antitone (composition of monotone ns with antitone (alpha ∘ u))
    have h_sub_anti : Antitone (fun k => alphaIicCE X hX_contract hX_meas hX_L2 (u (ns k) : ℝ) ω) := by
      intro k1 k2 hk
      exact h_anti (ns k1) (ns k2) (ns_mono.monotone hk)

    -- The infimum of an antitone convergent sequence equals its limit
    have h2 : ⨅ k : ℕ, alphaIicCE X hX_contract hX_meas hX_L2 (u (ns k) : ℝ) ω =
        alphaIicCE X hX_contract hX_meas hX_L2 t ω := by
      have h_bounded_below : BddBelow (Set.range
          (fun k => alphaIicCE X hX_contract hX_meas hX_L2 (u (ns k) : ℝ) ω)) := by
        use 0
        intro x ⟨k, hk⟩
        rw [← hk]
        exact h_bdd (ns k)
      -- For antitone bounded-below sequence, it converges to its infimum
      have h_conv_to_inf := tendsto_atTop_ciInf h_sub_anti h_bounded_below
      -- The limit is unique
      exact tendsto_nhds_unique h_conv_to_inf h_conv

    calc ⨅ n : ℕ, alphaIicCE X hX_contract hX_meas hX_L2 (u n : ℝ) ω
        ≤ ⨅ k : ℕ, alphaIicCE X hX_contract hX_meas hX_L2 (u (ns k) : ℝ) ω := h1
      _ = alphaIicCE X hX_contract hX_meas hX_L2 t ω := h2

  -- Step 4: Combine everything
  filter_upwards [h_infs_le_ae, h_inf_le_lim] with ω h_infs_le h_inf
  calc ⨅ q : { q : ℚ // t < ↑q }, alphaIicCE X hX_contract hX_meas hX_L2 (↑↑q) ω
      ≤ ⨅ n : ℕ, alphaIicCE X hX_contract hX_meas hX_L2 (u n : ℝ) ω := h_infs_le
    _ ≤ alphaIicCE X hX_contract hX_meas hX_L2 t ω := h_inf

/-- **Right-continuity of alphaIicCE at rationals.**

For each rational q, the infimum from the right equals the value:
`⨅ r > q (rational), alphaIicCE r = alphaIicCE q` a.e.

**Proof strategy:**
- alphaIicCE is monotone (increasing in t)
- For rₙ ↓ q, the indicators 1_{Iic rₙ} ↓ 1_{Iic q} pointwise
- By dominated convergence: E[1_{Iic rₙ}(X₀)|tail] → E[1_{Iic q}(X₀)|tail] in L¹
- For monotone sequences, L¹ convergence implies a.e. convergence
- So alphaIicCE rₙ → alphaIicCE q a.e. for any sequence rₙ ↓ q
- This means ⨅ r > q, alphaIicCE r = alphaIicCE q a.e. -/
lemma alphaIicCE_iInf_rat_gt_eq
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ) :
    ∀ᵐ ω ∂μ, ∀ q : ℚ, ⨅ r : Set.Ioi q,
        alphaIicCE X hX_contract hX_meas hX_L2 (r : ℝ) ω =
        alphaIicCE X hX_contract hX_meas hX_L2 (q : ℝ) ω := by
  -- Set up tail σ-algebra infrastructure
  have hm_le : TailSigma.tailSigma X ≤ (inferInstance : MeasurableSpace Ω) :=
    TailSigma.tailSigma_le X hX_meas
  haveI : Fact (TailSigma.tailSigma X ≤ (inferInstance : MeasurableSpace Ω)) := ⟨hm_le⟩

  -- Use ae_all_iff to reduce to proving for each rational q
  rw [ae_all_iff]
  intro q

  -- Filter on monotonicity and boundedness
  have h_mono_ae : ∀ᵐ ω ∂μ, ∀ r s : ℚ, r ≤ s →
      alphaIicCE X hX_contract hX_meas hX_L2 (r : ℝ) ω ≤
      alphaIicCE X hX_contract hX_meas hX_L2 (s : ℝ) ω := by
    rw [ae_all_iff]; intro r
    rw [ae_all_iff]; intro s
    by_cases hrs : r ≤ s
    · have h_le : (r : ℝ) ≤ (s : ℝ) := Rat.cast_le.mpr hrs
      filter_upwards [alphaIicCE_mono X hX_contract hX_meas hX_L2 (r : ℝ) (s : ℝ) h_le] with ω hω
      intro _; exact hω
    · exact ae_of_all μ (fun ω h_contra => absurd h_contra hrs)

  have h_bdd_ae : ∀ᵐ ω ∂μ, ∀ r : ℚ,
      0 ≤ alphaIicCE X hX_contract hX_meas hX_L2 (r : ℝ) ω ∧
      alphaIicCE X hX_contract hX_meas hX_L2 (r : ℝ) ω ≤ 1 := by
    rw [ae_all_iff]; intro r
    exact alphaIicCE_nonneg_le_one X hX_contract hX_meas hX_L2 (r : ℝ)

  -- Get the right-continuity property at this specific rational q
  have h_right_cont_ae : ∀ᵐ ω ∂μ, ⨅ r : {r : ℚ // (q : ℝ) < r},
      alphaIicCE X hX_contract hX_meas hX_L2 (r : ℝ) ω ≤
      alphaIicCE X hX_contract hX_meas hX_L2 (q : ℝ) ω :=
    alphaIicCE_right_continuous_at X hX_contract hX_meas hX_L2 (q : ℝ)

  filter_upwards [h_mono_ae, h_bdd_ae, h_right_cont_ae] with ω h_mono h_bdd h_right_cont

  -- At this ω, alphaIicCE is monotone and bounded in [0,1]
  -- The infimum of a monotone function from the right equals the value
  -- by right-continuity of CDFs

  apply le_antisymm
  · -- ⨅ r > q, alphaIicCE r ω ≤ alphaIicCE q ω (right-continuity)
    -- Key: for CDF functions, the infimum from the right equals the value
    -- Because the measure of the singleton {q} has measure zero for continuous distributions,
    -- the limit from the right equals the value

    -- Use that alphaIicCE comes from indicators which are right-continuous
    -- As r ↓ q, 1_{Iic r} ↓ 1_{Iic q} pointwise, so E[...|tail] ↓ as well

    -- Monotone decreasing: for r > q, alphaIicCE r ω ≥ alphaIicCE q ω
    -- The infimum is achieved in the limit, which equals alphaIicCE q ω

    -- Take rational sequence rₙ = q + 1/(n+1) decreasing to q
    -- The infimum is the limit of alphaIicCE rₙ ω
    -- By CDF right-continuity, this limit equals alphaIicCE q ω

    -- For bounded monotone functions, the infimum over r > q equals lim_{r → q⁺}
    -- Since alphaIicCE is bounded in [0,1], the limit exists

    -- Use ciInf_le with witness r = q + 1/(n+1) for any n,
    -- then take limit as n → ∞

    -- Actually, we use the property that for any ε > 0, there exists r > q such that
    -- alphaIicCE r ω < alphaIicCE q ω + ε

    -- Since monotonicity gives alphaIicCE r ω ≥ alphaIicCE q ω for all r > q,
    -- and the function is bounded, the infimum equals the greatest lower bound

    -- For right-continuous CDFs (which alphaIicCE is, by construction from indicators),
    -- lim_{r → q⁺} F(r) = F(q)

    -- The key insight: alphaIicCE at rational r equals the conditional probability
    -- P(X₀ ≤ r | tail). For probability CDFs, the right limit equals the value.

    -- Let's use the bound directly: alphaIicCE r ω ≤ 1 for all r
    -- And alphaIicCE r ω is decreasing as r decreases toward q
    -- So ⨅ r > q, alphaIicCE r ω ≥ alphaIicCE q ω (obvious)
    -- For the reverse, we need that there's no jump at q

    -- Since alphaIicCE is monotone and bounded, for any sequence rₙ ↓ q:
    -- alphaIicCE rₙ ω → ⨅ r > q, alphaIicCE r ω

    -- By the L¹ convergence of conditional expectations (dominated convergence),
    -- there exists a subsequence where alphaIicCE rₙ ω → alphaIicCE q ω

    -- Combined with monotonicity, the full sequence converges to alphaIicCE q ω

    -- Therefore ⨅ r > q, alphaIicCE r ω = alphaIicCE q ω

    -- Nonempty for the infimum
    have h_nonempty : Nonempty (Set.Ioi q) := ⟨⟨q + 1, by simp⟩⟩

    -- Bounded below by 0
    have h_bdd_below : BddBelow (Set.range fun r : Set.Ioi q =>
        alphaIicCE X hX_contract hX_meas hX_L2 (r : ℝ) ω) := by
      use 0
      intro x hx
      obtain ⟨r, rfl⟩ := hx
      exact (h_bdd r).1

    -- The infimum is at least the value (by monotonicity)
    have h_inf_ge : ⨅ r : Set.Ioi q, alphaIicCE X hX_contract hX_meas hX_L2 (r : ℝ) ω ≥
        alphaIicCE X hX_contract hX_meas hX_L2 (q : ℝ) ω := by
      apply le_ciInf
      intro ⟨r, hr⟩
      exact h_mono q r (le_of_lt hr)

    -- For the upper bound, we use that alphaIicCE is right-continuous
    -- This follows from the fact that it's the conditional CDF, which is right-continuous

    -- Key: alphaIicCE r ≤ 1 for all r, and alphaIicCE r decreases as r → q⁺
    -- Since the function is bounded and monotone, the infimum is achieved

    -- For a decreasing net bounded below, the infimum is the limit
    -- lim_{r → q⁺} alphaIicCE r = ⨅ r > q, alphaIicCE r

    -- And for conditional CDFs, lim_{r → q⁺} P(X₀ ≤ r | tail) = P(X₀ ≤ q | tail)

    -- The hard direction: ⨅ r > q, alphaIicCE r ω ≤ alphaIicCE q ω
    -- This is right-continuity of CDFs.
    --
    -- Mathematical proof:
    -- 1. For sequence rₙ = q + 1/n, we have rₙ ↓ q
    -- 2. 1_{Iic rₙ}(x) ↓ 1_{Iic q}(x) for all x (decreasing indicators)
    -- 3. By dominated convergence for conditional expectations:
    --    E[1_{Iic rₙ}(X₀)|tail] → E[1_{Iic q}(X₀)|tail] in L¹
    -- 4. For monotone decreasing sequences, L¹ convergence implies a.e. convergence
    -- 5. Therefore alphaIicCE rₙ ω → alphaIicCE q ω for a.e. ω
    -- 6. The infimum equals this limit, so ⨅ r > q = alphaIicCE q

    -- Since alphaIicCE is monotone in t and bounded in [0,1]:
    -- - The infimum from the right exists and equals the limit from the right
    -- - For CDFs, the limit from the right equals the value (right-continuity)

    -- The key insight is that h_inf_ge shows ⨅ ≥ value (by monotonicity),
    -- and we need ⨅ ≤ value (by right-continuity of CDF).
    -- Combined, they give equality.

    -- For now, since the proper dominated convergence proof is complex,
    -- we use that alphaIicCE is a CDF and CDFs are right-continuous.
    -- The proof would formally use tendsto_condExpL1_of_dominated_convergence.
    -- See mathlib's IsRatCondKernelCDFAux.iInf_rat_gt_eq for the pattern.

    -- Use the right-continuity property from h_right_cont
    -- The infimum over Set.Ioi q is ≤ infimum over {r : ℚ // (q : ℝ) < r}
    -- because Set.Ioi q ⊆ {r : ℚ // (q : ℝ) < r} (they're actually equal)

    -- Nonempty instances for the infima
    haveI : Nonempty { r : ℚ // (q : ℝ) < r } :=
      ⟨⟨q + 1, by simp [Rat.cast_add, Rat.cast_one]⟩⟩

    calc ⨅ r : Set.Ioi q, alphaIicCE X hX_contract hX_meas hX_L2 (r : ℝ) ω
        ≤ ⨅ r : {r : ℚ // (q : ℝ) < r}, alphaIicCE X hX_contract hX_meas hX_L2 (r : ℝ) ω := by
          apply le_ciInf
          intro ⟨r, hr⟩
          have hr' : q < r := by exact_mod_cast hr
          have h_bdd_below : BddBelow (Set.range fun s : Set.Ioi q =>
              alphaIicCE X hX_contract hX_meas hX_L2 (s : ℝ) ω) := by
            use 0
            intro x hx
            obtain ⟨s, rfl⟩ := hx
            exact (h_bdd s.val).1
          exact ciInf_le h_bdd_below ⟨r, hr'⟩
      _ ≤ alphaIicCE X hX_contract hX_meas hX_L2 (q : ℝ) ω := h_right_cont

  · -- alphaIicCE q ω ≤ ⨅ r > q, alphaIicCE r ω (by monotonicity)
    apply le_ciInf
    intro ⟨r, hr⟩
    exact h_mono q r (le_of_lt hr)

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

/-!
## Bridge Lemma: Integral against directing measure equals conditional expectation

This is the key Kallenberg insight: the directing measure ν(ω) is the conditional distribution
of X₀ given the tail σ-algebra. Therefore:

  ∫ f dν(ω) = E[f(X₀) | tail](ω)  a.e.

**Proof Strategy:**
1. **Base case (Iic indicators):** By Stieltjes construction,
   `∫ 1_{Iic t} dν(ω) = alphaIic t ω = alphaIicCE t ω = E[1_{Iic t}(X₀)|tail](ω)` a.e.

2. **Extension:** Iic sets form a π-system generating the Borel σ-algebra.
   By measure extensionality, two probability measures agreeing on Iic agree everywhere.
   The same linearity/continuity argument extends to all bounded measurable f.

This lemma is the bridge that allows us to go from:
- `cesaro_to_condexp_L2`: α = E[f(X₀)|tail]
to:
- `directing_measure_integral`: α = ∫f dν

by transitivity.
-/

/-- **Base case:** For Iic indicators, the directing measure integral equals alphaIicCE.

This follows from:
1. Stieltjes construction: `∫ 1_{Iic t} dν(ω) = (ν(Iic t)).toReal`
2. Measure value: `(ν(Iic t)).toReal = stieltjesOfMeasurableRat t`
3. Stieltjes extension: `stieltjesOfMeasurableRat t = alphaIic t` a.e.
4. Identification: `alphaIic t =ᵐ alphaIicCE t` -/
lemma directing_measure_integral_Iic_ae_eq_alphaIicCE
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ)
    (t : ℝ) :
    (fun ω => ∫ x, (Set.Iic t).indicator (fun _ => (1:ℝ)) x
        ∂(directing_measure X hX_contract hX_meas hX_L2 ω))
      =ᵐ[μ] alphaIicCE X hX_contract hX_meas hX_L2 t := by
  -- Step 1: Simplify integral to measure value
  have h_integral_eq : ∀ ω, ∫ x, (Set.Iic t).indicator (fun _ => (1 : ℝ)) x
      ∂(directing_measure X hX_contract hX_meas hX_L2 ω) =
      (directing_measure X hX_contract hX_meas hX_L2 ω (Set.Iic t)).toReal := by
    intro ω
    rw [MeasureTheory.integral_indicator measurableSet_Iic]
    simp only [MeasureTheory.integral_const, smul_eq_mul, mul_one]
    rw [Measure.real_def, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]

  -- Step 2: The measure on Iic t equals the Stieltjes function value
  have h_meas_eq : ∀ ω, (directing_measure X hX_contract hX_meas hX_L2 ω (Set.Iic t)).toReal =
      (ProbabilityTheory.stieltjesOfMeasurableRat
        (alphaIicRat X hX_contract hX_meas hX_L2)
        (measurable_alphaIicRat X hX_contract hX_meas hX_L2) ω) t := by
    intro ω
    unfold directing_measure
    rw [ProbabilityTheory.measure_stieltjesOfMeasurableRat_Iic]
    have h_nonneg : 0 ≤ (ProbabilityTheory.stieltjesOfMeasurableRat
          (alphaIicRat X hX_contract hX_meas hX_L2)
          (measurable_alphaIicRat X hX_contract hX_meas hX_L2) ω) t :=
      ProbabilityTheory.stieltjesOfMeasurableRat_nonneg _ _ _
    exact ENNReal.toReal_ofReal h_nonneg

  -- Step 3: Combine and use identification with alphaIicCE
  -- The Stieltjes extension equals alphaIic a.e., and alphaIic =ᵐ alphaIicCE

  -- We need to filter on the set where IsRatStieltjesPoint alphaIicRat ω holds.
  -- This requires: monotonicity, limits at ±∞, and right-continuity at all rationals.

  -- Get monotonicity of alphaIic at all rational pairs
  have h_mono_ae : ∀ᵐ ω ∂μ, ∀ q r : ℚ, q ≤ r →
      alphaIic X hX_contract hX_meas hX_L2 (q : ℝ) ω ≤
      alphaIic X hX_contract hX_meas hX_L2 (r : ℝ) ω := by
    rw [ae_all_iff]; intro q
    rw [ae_all_iff]; intro r
    by_cases hqr : q ≤ r
    · have h_le : (q : ℝ) ≤ (r : ℝ) := Rat.cast_le.mpr hqr
      filter_upwards [alphaIic_ae_eq_alphaIicCE X hX_contract hX_meas hX_L2 (q : ℝ),
                      alphaIic_ae_eq_alphaIicCE X hX_contract hX_meas hX_L2 (r : ℝ),
                      alphaIicCE_mono X hX_contract hX_meas hX_L2 (q : ℝ) (r : ℝ) h_le]
        with ω hq hr hCE_mono
      intro _
      rw [hq, hr]
      exact hCE_mono
    · exact ae_of_all μ (fun ω h_contra => absurd h_contra hqr)

  -- Get limits at ±∞ (along integers, which implies along rationals by monotonicity)
  have h_bot_ae : ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ =>
      alphaIic X hX_contract hX_meas hX_L2 (-(n : ℝ)) ω) atTop (𝓝 0) :=
    alphaIic_ae_tendsto_zero_at_bot X hX_contract hX_meas hX_L2

  have h_top_ae : ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ =>
      alphaIic X hX_contract hX_meas hX_L2 (n : ℝ) ω) atTop (𝓝 1) :=
    alphaIic_ae_tendsto_one_at_top X hX_contract hX_meas hX_L2

  -- Also filter on alphaIic = alphaIicCE at all rationals (countable ae union)
  have h_ae_all_rationals : ∀ᵐ ω ∂μ, ∀ q : ℚ,
      alphaIic X hX_contract hX_meas hX_L2 (q : ℝ) ω =
      alphaIicCE X hX_contract hX_meas hX_L2 (q : ℝ) ω := by
    rw [ae_all_iff]
    intro q
    exact alphaIic_ae_eq_alphaIicCE X hX_contract hX_meas hX_L2 (q : ℝ)

  -- Filter on alphaIicCE_mono at (t, q) for all rationals q > t
  have h_mono_t_rational : ∀ᵐ ω ∂μ, ∀ q : ℚ, t < q →
      alphaIicCE X hX_contract hX_meas hX_L2 t ω ≤
      alphaIicCE X hX_contract hX_meas hX_L2 (q : ℝ) ω := by
    rw [ae_all_iff]
    intro q
    by_cases htq : t < q
    · have h_le : t ≤ (q : ℝ) := le_of_lt htq
      filter_upwards [alphaIicCE_mono X hX_contract hX_meas hX_L2 t (q : ℝ) h_le] with ω hω
      intro _
      exact hω
    · exact ae_of_all μ (fun ω h_contra => absurd h_contra htq)

  -- Filter on all necessary conditions (including right-continuity at t and all rationals)
  filter_upwards [alphaIic_ae_eq_alphaIicCE X hX_contract hX_meas hX_L2 t,
                  h_mono_ae, h_bot_ae, h_top_ae, h_ae_all_rationals, h_mono_t_rational,
                  alphaIicCE_right_continuous_at X hX_contract hX_meas hX_L2 t,
                  alphaIicCE_iInf_rat_gt_eq X hX_contract hX_meas hX_L2]
    with ω h_ae h_mono h_bot h_top h_ae_rat h_mono_t_rat h_right_cont h_iInf_rat_gt_CE
  rw [h_integral_eq, h_meas_eq]
  -- Need: stieltjesOfMeasurableRat alphaIicRat ω t = alphaIicCE t ω
  -- By h_ae: alphaIic t ω = alphaIicCE t ω
  rw [← h_ae]

  -- The Stieltjes function is defined via toRatCDF.
  -- At rational points, stieltjesOfMeasurableRat equals toRatCDF.
  -- toRatCDF uses alphaIicRat when IsRatStieltjesPoint holds, else defaultRatCDF.

  -- Show that IsRatStieltjesPoint alphaIicRat ω holds for this ω.
  -- We verify the conditions using h_mono, h_bot, h_top.
  have h_alphaIicRat_mono : Monotone (alphaIicRat X hX_contract hX_meas hX_L2 ω) := by
    intro q r hqr
    unfold alphaIicRat
    exact h_mono q r hqr

  -- For limits at ±∞ along rationals, use monotonicity + integer limits
  have h_alphaIicRat_tendsto_top : Tendsto (alphaIicRat X hX_contract hX_meas hX_L2 ω)
      atTop (𝓝 1) := by
    -- alphaIicRat is monotone and bounded above by 1
    -- The integer subsequence converges to 1, so the whole sequence does
    -- Use tendsto_atTop_isLUB with the fact that 1 is the supremum
    apply tendsto_atTop_isLUB h_alphaIicRat_mono
    -- Need to show 1 is the LUB of the range
    -- Since alphaIicRat is monotone, bounded by 1, and the integer sequence → 1,
    -- the sup is 1.
    constructor
    · -- 1 is an upper bound
      rintro _ ⟨q, rfl⟩
      unfold alphaIicRat alphaIic
      -- max 0 (min 1 x) ≤ 1 always holds
      exact max_le zero_le_one (min_le_left _ _)
    · -- 1 is the least upper bound
      intro b hb
      -- b ≥ alphaIicRat n for all n, so b ≥ lim alphaIicRat n = 1
      by_contra h_not
      push_neg at h_not
      have hε : 1 - b > 0 := by linarith
      -- Since alphaIicRat n → 1, for large n we have alphaIicRat n > b
      have h_nat : Tendsto (fun n : ℕ => alphaIicRat X hX_contract hX_meas hX_L2 ω (n : ℚ))
          atTop (𝓝 1) := by
        unfold alphaIicRat
        simp only [Rat.cast_natCast]
        exact h_top
      rw [Metric.tendsto_atTop] at h_nat
      obtain ⟨N, hN⟩ := h_nat (1 - b) hε
      have h_contra := hb (Set.mem_range.mpr ⟨N, rfl⟩)
      specialize hN N le_rfl
      rw [Real.dist_eq] at hN
      have h_abs : |alphaIicRat X hX_contract hX_meas hX_L2 ω N - 1| < 1 - b := hN
      have h_lower : alphaIicRat X hX_contract hX_meas hX_L2 ω N ≥ 0 := by
        unfold alphaIicRat alphaIic
        -- 0 ≤ max 0 (min 1 x) always holds
        exact le_max_left 0 _
      have h_upper : alphaIicRat X hX_contract hX_meas hX_L2 ω N ≤ 1 := by
        unfold alphaIicRat alphaIic
        exact max_le zero_le_one (min_le_left _ _)
      rw [abs_sub_lt_iff] at h_abs
      linarith

  have h_alphaIicRat_tendsto_bot : Tendsto (alphaIicRat X hX_contract hX_meas hX_L2 ω)
      atBot (𝓝 0) := by
    -- Similar argument using monotonicity and GLB at -∞
    apply tendsto_atBot_isGLB h_alphaIicRat_mono
    -- Need to show 0 is the GLB of the range
    constructor
    · -- 0 is a lower bound
      rintro _ ⟨q, rfl⟩
      unfold alphaIicRat alphaIic
      -- 0 ≤ max 0 (min 1 x) always holds
      exact le_max_left 0 _
    · -- 0 is the greatest lower bound
      intro b hb
      by_contra h_not
      push_neg at h_not
      have hε : b > 0 := h_not
      -- Since alphaIicRat (-n) → 0, for large n we have alphaIicRat (-n) < b
      have h_nat : Tendsto (fun n : ℕ => alphaIicRat X hX_contract hX_meas hX_L2 ω (-(n : ℚ)))
          atTop (𝓝 0) := by
        unfold alphaIicRat
        simp only [Rat.cast_neg, Rat.cast_natCast]
        exact h_bot
      rw [Metric.tendsto_atTop] at h_nat
      obtain ⟨N, hN⟩ := h_nat b hε
      have h_contra := hb (Set.mem_range.mpr ⟨-(N : ℚ), rfl⟩)
      specialize hN N le_rfl
      rw [Real.dist_eq, abs_sub_comm] at hN
      have h_lower : alphaIicRat X hX_contract hX_meas hX_L2 ω (-(N : ℚ)) ≥ 0 := by
        unfold alphaIicRat alphaIic
        -- 0 ≤ max 0 (min 1 x) always holds
        exact le_max_left 0 _
      have h_abs : |alphaIicRat X hX_contract hX_meas hX_L2 ω (-(N : ℚ)) - 0| < b := by
        rwa [abs_sub_comm] at hN
      simp only [sub_zero, abs_of_nonneg h_lower] at h_abs
      linarith

  -- Right-continuity at rationals for alphaIicRat.
  -- This is a key property that follows from alphaIicCE being right-continuous
  -- (as a conditional expectation of right-continuous indicators).
  have h_iInf_rat_gt : ∀ q : ℚ, ⨅ r : Set.Ioi q,
      alphaIicRat X hX_contract hX_meas hX_L2 ω r = alphaIicRat X hX_contract hX_meas hX_L2 ω q := by
    intro q
    -- By monotonicity, the infimum is a limit from the right.
    -- For CDFs, right-continuity says this limit equals the value.
    apply le_antisymm
    · -- iInf ≤ value: Use h_iInf_rat_gt_CE and the identification h_ae_rat.
      -- alphaIicRat ω r = alphaIic (r : ℝ) ω = alphaIicCE (r : ℝ) ω for rational r.
      -- h_iInf_rat_gt_CE q says: ⨅ r > q, alphaIicCE r ω = alphaIicCE q ω
      -- Convert between alphaIicRat and alphaIicCE using h_ae_rat.
      unfold alphaIicRat
      -- Now goal is: ⨅ r : Set.Ioi q, alphaIic (r : ℝ) ω ≤ alphaIic (q : ℝ) ω
      rw [h_ae_rat q]
      -- Goal: ⨅ r : Set.Ioi q, alphaIic (r : ℝ) ω ≤ alphaIicCE (q : ℝ) ω
      have h_eq : ⨅ r : Set.Ioi q, alphaIic X hX_contract hX_meas hX_L2 (r : ℝ) ω =
          ⨅ r : Set.Ioi q, alphaIicCE X hX_contract hX_meas hX_L2 (r : ℝ) ω := by
        congr 1
        ext ⟨r, hr⟩
        exact h_ae_rat r
      rw [h_eq, h_iInf_rat_gt_CE q]
    · -- value ≤ iInf: use monotonicity
      apply le_ciInf
      intro ⟨r, hr⟩
      exact h_alphaIicRat_mono (le_of_lt hr)

  -- Now we know IsRatStieltjesPoint holds, so toRatCDF = alphaIicRat
  have h_isRSP : ProbabilityTheory.IsRatStieltjesPoint
      (alphaIicRat X hX_contract hX_meas hX_L2) ω :=
    ⟨h_alphaIicRat_mono, h_alphaIicRat_tendsto_top, h_alphaIicRat_tendsto_bot, h_iInf_rat_gt⟩

  -- Use toRatCDF_of_isRatStieltjesPoint: when IsRatStieltjesPoint holds, toRatCDF = f
  -- Then stieltjesOfMeasurableRat at t equals the infimum over rationals > t
  -- which by h_iInf_rat_gt equals alphaIicRat restricted to t
  -- But we need the value at real t, not rational t.

  -- The Stieltjes function at real t is defined as inf over rationals > t.
  -- stieltjesOfMeasurableRat f hf ω t = ⨅ q > t, toRatCDF f ω q
  -- Since IsRatStieltjesPoint holds: = ⨅ q > t, f ω q = ⨅ q > t, alphaIicRat ω q

  -- By right-continuity of alphaIic (which follows from being a CDF):
  -- ⨅ q > t, alphaIic q ω = alphaIic t ω

  -- The Stieltjes function equals its value via the iInf_rat_gt characterization
  have h_stieltjes_eq : (ProbabilityTheory.stieltjesOfMeasurableRat
        (alphaIicRat X hX_contract hX_meas hX_L2)
        (measurable_alphaIicRat X hX_contract hX_meas hX_L2) ω) t =
      ⨅ q : {q : ℚ // t < q}, alphaIicRat X hX_contract hX_meas hX_L2 ω q := by
    rw [← StieltjesFunction.iInf_rat_gt_eq]
    congr 1
    funext q
    rw [ProbabilityTheory.stieltjesOfMeasurableRat_eq]
    rw [ProbabilityTheory.toRatCDF_of_isRatStieltjesPoint h_isRSP]

  rw [h_stieltjes_eq]
  unfold alphaIicRat
  -- Now we need: ⨅ q > t, alphaIic q ω = alphaIic t ω

  -- Strategy: Use h_ae_rat to transfer to alphaIicCE, then use right-continuity.
  -- ⨅ q > t, alphaIic q ω = ⨅ q > t, alphaIicCE q ω  (by h_ae_rat)
  -- = alphaIicCE t ω  (by right-continuity of alphaIicCE)
  -- = alphaIic t ω   (by h_ae)

  -- Step 1: Rewrite the infimum using h_ae_rat
  have h_infimum_eq : (⨅ q : {q : ℚ // t < q}, alphaIic X hX_contract hX_meas hX_L2 (q : ℝ) ω) =
      ⨅ q : {q : ℚ // t < q}, alphaIicCE X hX_contract hX_meas hX_L2 (q : ℝ) ω := by
    congr 1
    ext ⟨q, _⟩
    exact h_ae_rat q

  rw [h_infimum_eq]

  -- Step 2: Show ⨅ q > t, alphaIicCE q ω = alphaIicCE t ω (right-continuity of alphaIicCE)
  -- alphaIicCE is the conditional expectation of the indicator 1_{Iic t}(X₀).
  -- As t → t₀⁺, the indicator 1_{Iic t} ↓ 1_{Iic t₀} pointwise (since Iic t ↓ Iic t₀).
  -- By monotone convergence for conditional expectations:
  -- E[1_{Iic t}(X₀) | tail] → E[1_{Iic t₀}(X₀) | tail] a.e.

  -- For this specific ω, we need: ⨅ q > t, alphaIicCE q ω = alphaIicCE t ω.
  -- This is the pointwise right-continuity of alphaIicCE.

  -- Actually, we filtered on conditions for alphaIicCE at rationals and at t,
  -- but not directly on right-continuity. Let's prove it using monotonicity.

  -- alphaIicCE is monotone a.e. We use the rational monotonicity we have.
  -- For q > t (rational), alphaIicCE t ω ≤ alphaIicCE q ω (by monotonicity).
  -- So alphaIicCE t ω ≤ ⨅ q > t, alphaIicCE q ω.
  -- The other direction (⨅ ≤ value) requires right-continuity.

  have h_nonempty : Nonempty {q : ℚ // t < q} := by
    -- Find a rational greater than t
    obtain ⟨q, hq⟩ := exists_rat_gt t
    exact ⟨⟨q, hq⟩⟩

  apply le_antisymm
  · -- ⨅ q > t, alphaIicCE q ω ≤ alphaIicCE t ω
    -- This is the "hard" direction requiring right-continuity.
    -- Use that the infimum of a monotone decreasing sequence converging to t
    -- equals the limit, which is the value at t for right-continuous functions.

    -- The set {q : ℚ // t < q} has infimum t.
    -- For monotone alphaIicCE, ⨅ q > t, alphaIicCE q = lim_{q → t⁺} alphaIicCE q.
    -- Right-continuity would give lim_{q → t⁺} alphaIicCE q = alphaIicCE t.

    -- For now, we use the key fact that alphaIicCE is bounded in [0,1] and monotone,
    -- so the infimum exists. The infimum equals the value at t by right-continuity
    -- of CDFs built from L¹ limits.

    -- Use the right-continuity lemma (filtered on via h_right_cont)
    calc ⨅ q : {q : ℚ // t < q}, alphaIicCE X hX_contract hX_meas hX_L2 (q : ℝ) ω
        ≤ alphaIicCE X hX_contract hX_meas hX_L2 t ω := h_right_cont
      _ = alphaIic X hX_contract hX_meas hX_L2 t ω := h_ae.symm

  · -- alphaIic t ω ≤ ⨅ q > t, alphaIicCE q ω
    -- By monotonicity: for q > t, alphaIicCE t ω ≤ alphaIicCE q ω.
    -- And alphaIic t ω = alphaIicCE t ω by h_ae.
    -- So alphaIic t ω ≤ ⨅ q > t, alphaIicCE q ω.
    rw [h_ae]
    apply le_ciInf
    intro ⟨q, hq⟩
    -- Need: alphaIicCE t ω ≤ alphaIicCE q ω where t < q
    -- This follows from h_mono_t_rat!
    exact h_mono_t_rat q hq

/-! ### Helper Lemmas for Monotone Class Extension

The following lemmas build up the π-λ argument needed for `directing_measure_integral_eq_condExp`.
Each phase is factored out as a separate lemma with its own sorry to be filled.

**Phase A**: Indicators of Borel sets → tail-AEStronglyMeasurable
**Phase B**: Simple functions → tail-AEStronglyMeasurable (via linearity)
**Phase C**: Bounded measurable functions → tail-AEStronglyMeasurable (via DCT + limits)
-/

/-- **Phase A:** For all Borel sets s, ω ↦ ∫ 1_s dν(ω) is tail-AEStronglyMeasurable.

The π-λ argument:
1. Base case: `{Iic t | t ∈ ℝ}` is a π-system generating Borel ℝ
2. For Iic t: uses `directing_measure_integral_Iic_ae_eq_alphaIicCE` + `stronglyMeasurable_condExp`
3. For ∅: integral is 0 (constant)
4. For complement: ∫ 1_{sᶜ} dν = 1 - ∫ 1_s dν (probability measure)
5. For disjoint unions: ∫ 1_{⋃ fn} dν = ∑' ∫ 1_{fn n} dν (σ-additivity)
6. Apply `MeasurableSpace.induction_on_inter` with `borel_eq_generateFrom_Iic`
-/
lemma integral_indicator_borel_tailAEStronglyMeasurable
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ)
    (s : Set ℝ) (hs : MeasurableSet s) :
    @AEStronglyMeasurable Ω ℝ _ (TailSigma.tailSigma X) _
      (fun ω => ∫ x, s.indicator (fun _ => (1:ℝ)) x
        ∂(directing_measure X hX_contract hX_meas hX_L2 ω)) μ := by
  classical
  -- Define the class of "good" sets G
  let G : Set (Set ℝ) := {t | MeasurableSet t ∧
    @AEStronglyMeasurable Ω ℝ _ (TailSigma.tailSigma X) _
      (fun ω => ∫ x, t.indicator (fun _ => (1:ℝ)) x
        ∂(directing_measure X hX_contract hX_meas hX_L2 ω)) μ}

  -- Step 1: G contains the π-system of half-lines {Iic t}
  have h_pi : ∀ t : ℝ, Set.Iic t ∈ G := by
    intro t
    constructor
    · exact measurableSet_Iic
    · -- By directing_measure_integral_Iic_ae_eq_alphaIicCE:
      -- ∫ 1_{Iic t} dν(ω) =ᵐ alphaIicCE t ω
      -- alphaIicCE t is tail-StronglyMeasurable (it's a condExp)
      have h_ae := directing_measure_integral_Iic_ae_eq_alphaIicCE X hX_contract hX_meas hX_L2 t
      have h_tail_sm : @StronglyMeasurable Ω ℝ _ (TailSigma.tailSigma X)
          (alphaIicCE X hX_contract hX_meas hX_L2 t) := by
        unfold alphaIicCE
        exact stronglyMeasurable_condExp
      exact AEStronglyMeasurable.congr h_tail_sm.aestronglyMeasurable h_ae.symm

  -- Step 2: G is a Dynkin system (λ-system)
  have h_empty : ∅ ∈ G := by
    constructor
    · exact MeasurableSet.empty
    · simp only [Set.indicator_empty, integral_zero]
      exact aestronglyMeasurable_const

  have h_compl : ∀ t ∈ G, tᶜ ∈ G := by
    intro t ⟨ht_meas, ht_aesm⟩
    constructor
    · exact ht_meas.compl
    · -- ∫ 1_{tᶜ} dν = ∫ (1 - 1_t) dν = 1 - ∫ 1_t dν (since ν is probability measure)
      have h_eq : ∀ ω, ∫ x, tᶜ.indicator (fun _ => (1:ℝ)) x
          ∂(directing_measure X hX_contract hX_meas hX_L2 ω) =
          1 - ∫ x, t.indicator (fun _ => (1:ℝ)) x
            ∂(directing_measure X hX_contract hX_meas hX_L2 ω) := by
        intro ω
        haveI hprob := directing_measure_isProbabilityMeasure X hX_contract hX_meas hX_L2 ω
        -- 1_{tᶜ} = 1 - 1_t
        have h_ind_compl : ∀ x, tᶜ.indicator (fun _ => (1:ℝ)) x =
            1 - t.indicator (fun _ => (1:ℝ)) x := by
          intro x
          by_cases hx : x ∈ t
          · simp [Set.indicator_of_mem hx, Set.indicator_of_not_mem (Set.not_mem_compl_iff.mpr hx)]
          · simp [Set.indicator_of_not_mem hx, Set.indicator_of_mem (Set.mem_compl hx)]
        simp_rw [h_ind_compl]
        rw [integral_sub (integrable_const 1), integral_const, measureReal_univ_eq_one, one_smul]
        exact (integrable_const 1).indicator ht_meas
      simp_rw [h_eq]
      exact aestronglyMeasurable_const.sub ht_aesm

  have h_iUnion : ∀ (f : ℕ → Set ℝ), (∀ i j, i ≠ j → Disjoint (f i) (f j)) →
      (∀ n, f n ∈ G) → (⋃ n, f n) ∈ G := by
    intro f hdisj hf
    constructor
    · exact MeasurableSet.iUnion (fun n => (hf n).1)
    · -- ∫ 1_{⋃ fn} dν = ∑' n, ∫ 1_{fn n} dν
      -- Partial sums are tail-AEStronglyMeasurable, converge pointwise to tsum
      -- Use aestronglyMeasurable_of_tendsto_ae
      have h_eq : ∀ ω, ∫ x, (⋃ n, f n).indicator (fun _ => (1:ℝ)) x
          ∂(directing_measure X hX_contract hX_meas hX_L2 ω) =
          ∑' n, ∫ x, (f n).indicator (fun _ => (1:ℝ)) x
            ∂(directing_measure X hX_contract hX_meas hX_L2 ω) := by
        intro ω
        haveI hprob := directing_measure_isProbabilityMeasure X hX_contract hX_meas hX_L2 ω
        -- indicator of union = sum of indicators for disjoint sets
        have h_ind_union : ∀ x, (⋃ n, f n).indicator (fun _ => (1:ℝ)) x =
            ∑' n, (f n).indicator (fun _ => (1:ℝ)) x := by
          intro x
          by_cases hx : x ∈ ⋃ n, f n
          · obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
            rw [Set.indicator_of_mem hx]
            -- x is in exactly one f n due to disjointness
            have h_unique : ∀ m, m ≠ n → x ∉ f m := by
              intro m hm hxm
              exact (hdisj n m (Ne.symm hm)).ne_of_mem hn hxm rfl
            rw [tsum_eq_single n]
            · simp [Set.indicator_of_mem hn]
            · intro m hm; simp [Set.indicator_of_not_mem (h_unique m hm)]
          · simp only [Set.indicator_of_not_mem hx]
            have : ∀ n, x ∉ f n := fun n hn => hx (Set.mem_iUnion.mpr ⟨n, hn⟩)
            simp [Set.indicator_of_not_mem (this _)]
        simp_rw [h_ind_union]
        -- integral of tsum = tsum of integrals (for nonneg functions)
        rw [integral_tsum]
        · exact fun n => (measurable_const.indicator (hf n).1).aestronglyMeasurable
        · -- Show ∑' i, ∫⁻ ‖1_{fi}‖ dν ≠ ⊤
          -- Each indicator has norm at most 1, and disjoint sets sum to at most 1
          have h_le_one : ∑' i, ∫⁻ a, ‖(f i).indicator (fun _ => (1:ℝ)) a‖ₑ
              ∂(directing_measure X hX_contract hX_meas hX_L2 ω) ≤ 1 := by
            have h_eq_meas : ∀ i, ∫⁻ a, ‖(f i).indicator (fun _ => (1:ℝ)) a‖ₑ
                ∂(directing_measure X hX_contract hX_meas hX_L2 ω)
                = directing_measure X hX_contract hX_meas hX_L2 ω (f i) := by
              intro i
              have h1 : ∫⁻ a, ‖(f i).indicator (fun _ => (1:ℝ)) a‖ₑ
                    ∂(directing_measure X hX_contract hX_meas hX_L2 ω)
                  = ∫⁻ a, (f i).indicator 1 a
                    ∂(directing_measure X hX_contract hX_meas hX_L2 ω) := by
                apply lintegral_congr; intro a
                simp only [Set.indicator, Real.enorm_eq_ofReal_abs, Pi.one_apply]
                split_ifs <;> simp
              rw [h1, lintegral_indicator_one (hf i).1]
            simp_rw [h_eq_meas]
            -- For disjoint measurable sets, sum = measure of union
            have hdisj' : Pairwise (Function.onFun Disjoint f) := fun i j hij => hdisj i j hij
            have hmeas : ∀ i, MeasurableSet (f i) := fun i => (hf i).1
            calc ∑' i, directing_measure X hX_contract hX_meas hX_L2 ω (f i)
                = directing_measure X hX_contract hX_meas hX_L2 ω (⋃ i, f i) :=
                  (measure_iUnion hdisj' hmeas).symm
              _ ≤ 1 := prob_le_one
          exact ne_top_of_le_ne_top ENNReal.one_ne_top h_le_one
      -- Now show the AEStronglyMeasurable property
      -- Key: partial sums ∑_{i<N} ∫ 1_{fi} dν are tail-AESM, converge to tsum
      let partialSum (N : ℕ) (ω : Ω) : ℝ := ∑ n ∈ Finset.range N,
        ∫ x, (f n).indicator (fun _ => (1:ℝ)) x
          ∂(directing_measure X hX_contract hX_meas hX_L2 ω)
      have h_partial_aesm : ∀ N, @AEStronglyMeasurable Ω ℝ _ (TailSigma.tailSigma X) _
          (partialSum N) μ := by
        intro N
        -- Use induction on N to build up the sum
        induction N with
        | zero =>
          -- partialSum 0 = 0, which is a constant
          have h_zero : partialSum 0 = fun _ => 0 := by
            funext ω
            show ∑ n ∈ Finset.range 0, _ = 0
            simp only [Finset.range_zero, Finset.sum_empty]
          rw [h_zero]
          exact aestronglyMeasurable_const
        | succ n ih =>
          -- partialSum (n+1) = partialSum n + (term at n)
          have h_succ : partialSum (n + 1) = fun ω => partialSum n ω +
              ∫ x, (f n).indicator (fun _ => (1:ℝ)) x
                ∂(directing_measure X hX_contract hX_meas hX_L2 ω) := by
            funext ω
            show ∑ k ∈ Finset.range (n + 1), _ = ∑ k ∈ Finset.range n, _ + _
            simp only [Finset.sum_range_succ]
          rw [h_succ]
          exact ih.add (hf n).2
      -- Partial sums converge pointwise to the full sum
      have h_tendsto : ∀ ω, Filter.Tendsto (fun N => partialSum N ω) Filter.atTop
          (nhds (∑' n, ∫ x, (f n).indicator (fun _ => (1:ℝ)) x
            ∂(directing_measure X hX_contract hX_meas hX_L2 ω))) := by
        intro ω
        haveI hprob := directing_measure_isProbabilityMeasure X hX_contract hX_meas hX_L2 ω
        -- Each term is nonnegative and bounded by 1
        have h_nonneg : ∀ n, 0 ≤ ∫ x, (f n).indicator (fun _ => (1:ℝ)) x
            ∂(directing_measure X hX_contract hX_meas hX_L2 ω) := by
          intro n
          apply integral_nonneg
          intro x; exact Set.indicator_nonneg (fun _ _ => zero_le_one) x
        -- For disjoint sets, partial sums ≤ 1 (probability measure)
        have h_partial_le : ∀ N, ∑ n ∈ Finset.range N, ∫ x, (f n).indicator (fun _ => (1:ℝ)) x
            ∂(directing_measure X hX_contract hX_meas hX_L2 ω) ≤ 1 := by
          intro N
          calc ∑ n ∈ Finset.range N, ∫ x, (f n).indicator (fun _ => (1:ℝ)) x
                ∂(directing_measure X hX_contract hX_meas hX_L2 ω)
            = ∫ x, ∑ n ∈ Finset.range N, (f n).indicator (fun _ => (1:ℝ)) x
                ∂(directing_measure X hX_contract hX_meas hX_L2 ω) := by
                rw [integral_finset_sum]
                intro i _
                exact (integrable_const 1).indicator (hf i).1
            _ ≤ ∫ _, 1 ∂(directing_measure X hX_contract hX_meas hX_L2 ω) := by
                apply integral_mono
                · apply integrable_finset_sum
                  intro i _
                  exact (integrable_const 1).indicator (hf i).1
                · exact integrable_const 1
                · intro x
                  -- Sum of disjoint indicators ≤ 1
                  have : ∑ n ∈ Finset.range N, (f n).indicator (fun _ => (1:ℝ)) x ≤ 1 := by
                    by_cases hx : ∃ n ∈ Finset.range N, x ∈ f n
                    · obtain ⟨m, hm_mem, hxm⟩ := hx
                      rw [Finset.sum_eq_single m]
                      · simp [Set.indicator_of_mem hxm]
                      · intro n hn hn_ne
                        have hne : m ≠ n := Ne.symm hn_ne
                        have hdisj_mn := hdisj m n hne
                        rw [Set.indicator_of_notMem]
                        exact Set.disjoint_left.mp hdisj_mn hxm
                      · intro hm_not; exact absurd hm_mem hm_not
                    · push_neg at hx
                      have h_zero : ∀ n ∈ Finset.range N, (f n).indicator (fun _ => (1:ℝ)) x = 0 :=
                        fun n hn => Set.indicator_of_notMem (hx n hn) _
                      rw [Finset.sum_eq_zero h_zero]
                      exact zero_le_one
                  exact this
            _ = 1 := by simp [measureReal_univ_eq_one]
        have h_summable : Summable (fun n => ∫ x, (f n).indicator (fun _ => (1:ℝ)) x
            ∂(directing_measure X hX_contract hX_meas hX_L2 ω)) :=
          summable_of_sum_range_le h_nonneg h_partial_le
        exact h_summable.hasSum.tendsto_sum_nat
      -- Apply aestronglyMeasurable_of_tendsto_ae
      have h_ae_tendsto : ∀ᵐ ω ∂μ, Filter.Tendsto (fun N => partialSum N ω) Filter.atTop
          (nhds (∑' n, ∫ x, (f n).indicator (fun _ => (1:ℝ)) x
            ∂(directing_measure X hX_contract hX_meas hX_L2 ω))) :=
        ae_of_all _ h_tendsto
      -- Construct AEStronglyMeasurable directly
      -- Key insight: partialSum n → tsum pointwise, and each partialSum n is tail-AESM
      -- Use ambient aestronglyMeasurable_of_tendsto_ae to get ambient AESM for the limit
      -- Then use the tail-AESM property of partialSum to extract a tail-SM witness
      have h_partial_ambient : ∀ n, AEStronglyMeasurable (partialSum n) μ := by
        intro n
        -- Each h_partial_aesm n is tail-AESM, which implies ambient-AESM
        -- tail-AESM has a tail-SM witness, and tail-SM implies ambient-SM
        exact (h_partial_aesm n).mono (TailSigma.tailSigma_le X hX_meas)
      have h_tsum_ambient : AEStronglyMeasurable
          (fun ω => ∑' n, ∫ x, (f n).indicator (fun _ => (1:ℝ)) x
            ∂(directing_measure X hX_contract hX_meas hX_L2 ω)) μ :=
        aestronglyMeasurable_of_tendsto_ae Filter.atTop h_partial_ambient h_ae_tendsto
      -- Now we need to show tail-AESM, not just ambient-AESM
      -- Key: the limit function equals ∑' n, ∫ ... which we can show is tail-AESM
      -- by using that each term is tail-AESM and taking the tsum
      have h_tsum_aesm : @AEStronglyMeasurable Ω ℝ _ (TailSigma.tailSigma X) _
            (fun ω => ∑' n, ∫ x, (f n).indicator (fun _ => (1:ℝ)) x
              ∂(directing_measure X hX_contract hX_meas hX_L2 ω)) μ := by
        -- Use that partial sums are tail-AESM and converge ae to get tail-AESM limit
        -- Get the tail-SM ae-representatives for each partial sum
        let g_n (n : ℕ) : Ω → ℝ := (h_partial_aesm n).mk (partialSum n)
        have hg_n_sm : ∀ n, @StronglyMeasurable Ω ℝ _ (TailSigma.tailSigma X) (g_n n) :=
          fun n => (h_partial_aesm n).stronglyMeasurable_mk
        have hg_n_ae : ∀ n, partialSum n =ᶠ[ae μ] g_n n := fun n => (h_partial_aesm n).ae_eq_mk
        -- Define the limit using the ae-representatives
        -- g_n converge ae to the tsum (since partialSum n → tsum and partialSum n =ᵐ g_n)
        have h_g_tendsto : ∀ᵐ ω ∂μ, Filter.Tendsto (fun n => g_n n ω) Filter.atTop
            (nhds (∑' k, ∫ x, (f k).indicator (fun _ => (1:ℝ)) x
              ∂(directing_measure X hX_contract hX_meas hX_L2 ω))) := by
          have h_ae_eq_all : ∀ᵐ ω ∂μ, ∀ n, g_n n ω = partialSum n ω := by
            rw [ae_all_iff]
            intro n
            exact (hg_n_ae n).symm
          filter_upwards [h_ae_eq_all] with ω h_eq
          simp_rw [h_eq]
          exact h_tendsto ω
        -- Use exists_stronglyMeasurable_limit_of_tendsto_ae on the g_n sequence
        have h_ae_exists : ∀ᵐ ω ∂μ, ∃ l, Filter.Tendsto (fun n => g_n n ω) Filter.atTop (nhds l) := by
          filter_upwards [h_g_tendsto] with ω hω
          exact ⟨_, hω⟩
        -- The g_n are ambient-AESM (since tail-SM implies ambient-AESM)
        have hg_n_ambient : ∀ n, AEStronglyMeasurable (g_n n) μ := by
          intro n
          exact (hg_n_sm n).aestronglyMeasurable.mono (TailSigma.tailSigma_le X hX_meas)
        -- Get the strongly measurable limit
        obtain ⟨g_lim, hg_lim_sm, hg_lim_tendsto⟩ :=
          exists_stronglyMeasurable_limit_of_tendsto_ae hg_n_ambient h_ae_exists
        -- g_lim is ambient-SM. We need to show it equals the tsum ae and is tail-AESM
        -- The limit of g_n equals tsum ae
        have h_lim_eq_tsum : g_lim =ᶠ[ae μ]
            (fun ω => ∑' k, ∫ x, (f k).indicator (fun _ => (1:ℝ)) x
              ∂(directing_measure X hX_contract hX_meas hX_L2 ω)) := by
          filter_upwards [hg_lim_tendsto, h_g_tendsto] with ω hω1 hω2
          exact tendsto_nhds_unique hω1 hω2
        -- We need ∃ h, tail-SM h ∧ tsum =ᵐ h
        -- Use limUnder which is the pointwise limit - StronglyMeasurable.limUnder shows
        -- that the pointwise limit of tail-SM functions is tail-SM
        let g_tail : Ω → ℝ := fun ω => limUnder atTop (fun n => g_n n ω)
        have hg_tail_sm : @StronglyMeasurable Ω ℝ _ (TailSigma.tailSigma X) g_tail :=
          @StronglyMeasurable.limUnder ℕ Ω ℝ (TailSigma.tailSigma X) _ _ _ atTop _
            (fun n => g_n n) _ hg_n_sm
        -- g_tail equals tsum ae (since g_n → tsum ae, and limUnder captures this limit)
        have hg_tail_eq_tsum : g_tail =ᶠ[ae μ]
            (fun ω => ∑' k, ∫ x, (f k).indicator (fun _ => (1:ℝ)) x
              ∂(directing_measure X hX_contract hX_meas hX_L2 ω)) := by
          filter_upwards [h_g_tendsto] with ω hω
          exact hω.limUnder_eq
        refine ⟨g_tail, hg_tail_sm, hg_tail_eq_tsum.symm⟩
      exact AEStronglyMeasurable.congr h_tsum_aesm (ae_of_all _ (fun ω => (h_eq ω).symm))

  -- Step 3: Apply π-λ theorem
  let S : Set (Set ℝ) := Set.range (Set.Iic : ℝ → Set ℝ)
  have h_gen : (inferInstance : MeasurableSpace ℝ) = MeasurableSpace.generateFrom S :=
    @borel_eq_generateFrom_Iic ℝ _ _ _ _
  have h_pi_S : IsPiSystem S := by
    intro u hu v hv _
    obtain ⟨s, rfl⟩ := hu
    obtain ⟨t, rfl⟩ := hv
    use min s t
    exact Set.Iic_inter_Iic.symm

  have h_induction : ∀ t (htm : MeasurableSet t), t ∈ G := fun t htm =>
    MeasurableSpace.induction_on_inter h_gen h_pi_S
      h_empty
      (fun u ⟨r, hr⟩ => hr ▸ h_pi r)
      (fun u hum hu => h_compl u hu)
      (fun f hdisj hfm hf => h_iUnion f hdisj hf)
      t htm

  exact (h_induction s hs).2

/-- **Phase B:** For simple functions, the integral is tail-AEStronglyMeasurable.

Simple functions are finite linear combinations of indicator functions.
Uses `Finset.aestronglyMeasurable_sum` and scalar multiplication. -/
lemma integral_simpleFunc_tailAEStronglyMeasurable
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ)
    (φ : SimpleFunc ℝ ℝ) :
    @AEStronglyMeasurable Ω ℝ _ (TailSigma.tailSigma X) _
      (fun ω => ∫ x, φ x ∂(directing_measure X hX_contract hX_meas hX_L2 ω)) μ := by
  -- SimpleFunc integral: ∫ φ dν = ∑ c ∈ φ.range, ν.real(φ⁻¹'{c}) • c
  -- For each c: ν.real(φ⁻¹'{c}) = ∫ 1_{φ⁻¹'{c}} dν, which is tail-AESM by A1
  -- c • (tail-AESM) is tail-AESM
  -- Finite sum of tail-AESM is tail-AESM

  -- The integral equals a finite sum over the range
  have h_eq : ∀ ω, ∫ x, φ x ∂(directing_measure X hX_contract hX_meas hX_L2 ω) =
      ∑ c ∈ φ.range, (directing_measure X hX_contract hX_meas hX_L2 ω).real (φ ⁻¹' {c}) • c := by
    intro ω
    haveI hprob := directing_measure_isProbabilityMeasure X hX_contract hX_meas hX_L2 ω
    -- φ is integrable on any probability measure (simple functions are bounded)
    have h_int : Integrable (⇑φ) (directing_measure X hX_contract hX_meas hX_L2 ω) :=
      SimpleFunc.integrable_of_isFiniteMeasure φ
    exact SimpleFunc.integral_eq_sum φ h_int

  -- Rewrite using h_eq
  have h_aesm : @AEStronglyMeasurable Ω ℝ _ (TailSigma.tailSigma X) _
      (fun ω => ∑ c ∈ φ.range,
        (directing_measure X hX_contract hX_meas hX_L2 ω).real (φ ⁻¹' {c}) • c) μ := by
    -- Need to help Lean see the eta-expanded form for Finset.aestronglyMeasurable_sum
    -- Convert fun ω => ∑ c ∈ s, f c ω  to  ∑ c ∈ s, (fun ω => f c ω)
    have h_eq_form : (fun ω => ∑ c ∈ φ.range,
        (directing_measure X hX_contract hX_meas hX_L2 ω).real (φ ⁻¹' {c}) • c) =
        ∑ c ∈ φ.range, fun ω =>
          (directing_measure X hX_contract hX_meas hX_L2 ω).real (φ ⁻¹' {c}) • c := by
      ext ω
      exact (Finset.sum_apply ω φ.range _).symm
    rw [h_eq_form]
    refine Finset.aestronglyMeasurable_sum φ.range ?_
    intro c _
    -- Need to show: ω ↦ ν(ω).real(φ⁻¹'{c}) • c is tail-AESM
    -- ν(ω).real(s) = ∫ 1_s dν(ω) for probability measures
    have h_preimage_meas : MeasurableSet (φ ⁻¹' {c}) := SimpleFunc.measurableSet_preimage φ {c}

    -- ω ↦ ν(ω).real(φ⁻¹'{c}) = ∫ 1_{φ⁻¹'{c}} dν(ω) is tail-AESM by A1
    have h_real_eq : ∀ ω, (directing_measure X hX_contract hX_meas hX_L2 ω).real (φ ⁻¹' {c}) =
        ∫ x, (φ ⁻¹' {c}).indicator (fun _ => (1:ℝ)) x
          ∂(directing_measure X hX_contract hX_meas hX_L2 ω) := by
      intro ω
      haveI hprob := directing_measure_isProbabilityMeasure X hX_contract hX_meas hX_L2 ω
      -- integral of indicator = measure (for probability measures)
      rw [integral_indicator_one h_preimage_meas]

    have h_term_aesm : @AEStronglyMeasurable Ω ℝ _ (TailSigma.tailSigma X) _
        (fun ω => (directing_measure X hX_contract hX_meas hX_L2 ω).real (φ ⁻¹' {c})) μ := by
      have := integral_indicator_borel_tailAEStronglyMeasurable X hX_contract hX_meas hX_L2
        (φ ⁻¹' {c}) h_preimage_meas
      exact AEStronglyMeasurable.congr this (ae_of_all _ (fun ω => (h_real_eq ω).symm))

    -- c • (tail-AESM) is tail-AESM
    exact h_term_aesm.const_smul c

  exact AEStronglyMeasurable.congr h_aesm (ae_of_all _ (fun ω => (h_eq ω).symm))

/-- **Phase C:** For bounded measurable f, the integral is tail-AEStronglyMeasurable.

Uses `SimpleFunc.approxOn` to approximate f by simple functions.
Takes limit via `aestronglyMeasurable_of_tendsto_ae` + DCT. -/
lemma integral_bounded_measurable_tailAEStronglyMeasurable
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ)
    (f : ℝ → ℝ) (hf_meas : Measurable f) (hf_bdd : ∃ M, ∀ x, |f x| ≤ M) :
    @AEStronglyMeasurable Ω ℝ _ (TailSigma.tailSigma X) _
      (fun ω => ∫ x, f x ∂(directing_measure X hX_contract hX_meas hX_L2 ω)) μ := by
  -- Get the bound M (ensure M ≥ 0)
  obtain ⟨M, hM⟩ := hf_bdd
  obtain ⟨M', hM'_nonneg, hM'⟩ : ∃ M' : ℝ, 0 ≤ M' ∧ ∀ x, |f x| ≤ M' := by
    use max M 0
    exact ⟨le_max_right M 0, fun x => (hM x).trans (le_max_left M 0)⟩

  -- The range of f is in Set.Icc (-M') M'
  have hf_range : ∀ x, f x ∈ Set.Icc (-M') M' := by
    intro x
    rw [Set.mem_Icc]
    exact abs_le.mp (hM' x)

  -- Set.Icc (-M') M' is nonempty (contains 0 when M' ≥ 0)
  have h0_mem : (0 : ℝ) ∈ Set.Icc (-M') M' := by
    rw [Set.mem_Icc]
    exact ⟨by linarith, hM'_nonneg⟩

  -- Approximate f by simple functions using approxOn
  let φ : ℕ → SimpleFunc ℝ ℝ := SimpleFunc.approxOn f hf_meas (Set.Icc (-M') M') 0 h0_mem

  -- Each φ n has values in Set.Icc (-M') M'
  have hφ_range : ∀ n x, φ n x ∈ Set.Icc (-M') M' := by
    intro n x
    exact SimpleFunc.approxOn_mem hf_meas h0_mem n x

  -- φ n → f pointwise (since f x ∈ closure (Icc (-M') M') = Icc (-M') M')
  have hφ_tendsto : ∀ x, Filter.Tendsto (fun n => φ n x) Filter.atTop (nhds (f x)) := by
    intro x
    apply SimpleFunc.tendsto_approxOn hf_meas h0_mem
    -- f x ∈ closure (Icc (-M') M') = Icc (-M') M' (closed set)
    rw [IsClosed.closure_eq (isClosed_Icc)]
    exact hf_range x

  -- Each ∫ φ_n dν(ω) is tail-AESM by Phase B
  have hφ_aesm : ∀ n, @AEStronglyMeasurable Ω ℝ _ (TailSigma.tailSigma X) _
      (fun ω => ∫ x, φ n x ∂(directing_measure X hX_contract hX_meas hX_L2 ω)) μ := by
    intro n
    exact integral_simpleFunc_tailAEStronglyMeasurable X hX_contract hX_meas hX_L2 (φ n)

  -- ∫ φ_n dν(ω) → ∫ f dν(ω) for each ω (by DCT on ν(ω))
  have h_int_tendsto : ∀ ω, Filter.Tendsto
      (fun n => ∫ x, φ n x ∂(directing_measure X hX_contract hX_meas hX_L2 ω))
      Filter.atTop
      (nhds (∫ x, f x ∂(directing_measure X hX_contract hX_meas hX_L2 ω))) := by
    intro ω
    haveI hprob := directing_measure_isProbabilityMeasure X hX_contract hX_meas hX_L2 ω
    -- Apply DCT with bound M' (constant, hence integrable)
    apply tendsto_integral_of_dominated_convergence (fun _ => M')
    · intro n
      exact (SimpleFunc.measurable (φ n)).aestronglyMeasurable
    · exact integrable_const M'
    · intro n
      filter_upwards with x
      rw [Real.norm_eq_abs]
      have := hφ_range n x
      rw [Set.mem_Icc] at this
      exact abs_le.mpr this
    · filter_upwards with x
      exact hφ_tendsto x

  -- Apply aestronglyMeasurable_of_tendsto_ae
  exact aestronglyMeasurable_of_tendsto_ae (μ := μ) Filter.atTop hφ_aesm (ae_of_all μ h_int_tendsto)

/-- **Set integral equality for Iic indicators.**

Base case: For Iic indicators, set integral equality follows from
`directing_measure_integral_Iic_ae_eq_alphaIicCE` + `setIntegral_condExp`. -/
lemma setIntegral_directing_measure_indicator_Iic_eq
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ)
    (t : ℝ) (A : Set Ω)
    (hA : @MeasurableSet Ω (TailSigma.tailSigma X) A)
    (hμA : μ A < ⊤) :
    ∫ ω in A, (∫ x, (Set.Iic t).indicator (fun _ => (1:ℝ)) x
        ∂(directing_measure X hX_contract hX_meas hX_L2 ω)) ∂μ
      = ∫ ω in A, (Set.Iic t).indicator (fun _ => (1:ℝ)) (X 0 ω) ∂μ := by
  -- Set up σ-algebra facts
  have hm_le : TailSigma.tailSigma X ≤ (inferInstance : MeasurableSpace Ω) :=
    TailSigma.tailSigma_le X hX_meas
  haveI : SigmaFinite (μ.trim hm_le) := inferInstance

  -- Step 1: ∫ 1_{Iic t} dν(ω) =ᵐ alphaIicCE t ω
  have h_ae := directing_measure_integral_Iic_ae_eq_alphaIicCE X hX_contract hX_meas hX_L2 t

  -- Step 2: ∫_A (∫ 1_{Iic t} dν) dμ = ∫_A alphaIicCE t dμ
  -- Use setIntegral_congr_ae
  have hA_ambient : MeasurableSet A := hm_le A hA
  have h_step2 : ∫ ω in A, (∫ x, (Set.Iic t).indicator (fun _ => (1:ℝ)) x
      ∂(directing_measure X hX_contract hX_meas hX_L2 ω)) ∂μ =
      ∫ ω in A, alphaIicCE X hX_contract hX_meas hX_L2 t ω ∂μ := by
    apply setIntegral_congr_ae hA_ambient
    filter_upwards [h_ae] with ω hω _
    exact hω

  -- Step 3: ∫_A alphaIicCE t dμ = ∫_A 1_{Iic t}(X₀) dμ
  -- alphaIicCE t = μ[1_{Iic t} ∘ X 0 | tail], so by setIntegral_condExp
  have h_step3 : ∫ ω in A, alphaIicCE X hX_contract hX_meas hX_L2 t ω ∂μ =
      ∫ ω in A, (Set.Iic t).indicator (fun _ => (1:ℝ)) (X 0 ω) ∂μ := by
    unfold alphaIicCE
    -- Convert composition form to lambda form
    simp only [indIic, Function.comp_def]
    -- Need to show the indicator function is integrable
    have h_int : Integrable (fun ω => (Set.Iic t).indicator (fun _ => (1:ℝ)) (X 0 ω)) μ := by
      apply Integrable.indicator
      · exact integrable_const 1
      · exact measurableSet_Iic.preimage (hX_meas 0)
    rw [setIntegral_condExp hm_le h_int hA]

  rw [h_step2, h_step3]

/-- **Set integral equality for Borel indicator functions.**

Extended from Iic indicators via π-λ argument. -/
lemma setIntegral_directing_measure_indicator_eq
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ)
    (s : Set ℝ) (hs : MeasurableSet s)
    (A : Set Ω) (hA : @MeasurableSet Ω (TailSigma.tailSigma X) A) (hμA : μ A < ⊤) :
    ∫ ω in A, (∫ x, s.indicator (fun _ => (1:ℝ)) x
        ∂(directing_measure X hX_contract hX_meas hX_L2 ω)) ∂μ
      = ∫ ω in A, s.indicator (fun _ => (1:ℝ)) (X 0 ω) ∂μ := by
  classical
  have hm_le : TailSigma.tailSigma X ≤ (inferInstance : MeasurableSpace Ω) :=
    TailSigma.tailSigma_le X hX_meas
  have hA_ambient : MeasurableSet A := hm_le A hA

  -- Define G = {t | MeasurableSet t ∧ set integral equality holds}
  let G : Set (Set ℝ) := {t | MeasurableSet t ∧
    ∫ ω in A, (∫ x, t.indicator (fun _ => (1:ℝ)) x
        ∂(directing_measure X hX_contract hX_meas hX_L2 ω)) ∂μ
      = ∫ ω in A, t.indicator (fun _ => (1:ℝ)) (X 0 ω) ∂μ}

  -- Step 1: G contains {Iic t}
  have h_pi : ∀ t : ℝ, Set.Iic t ∈ G := fun t => ⟨measurableSet_Iic,
    setIntegral_directing_measure_indicator_Iic_eq X hX_contract hX_meas hX_L2 t A hA hμA⟩

  -- Step 2: G is a Dynkin system
  have h_empty : ∅ ∈ G := by
    constructor
    · exact MeasurableSet.empty
    · simp only [Set.indicator_empty, integral_zero]

  have h_compl : ∀ t ∈ G, tᶜ ∈ G := by
    intro t ⟨ht_meas, ht_eq⟩
    constructor
    · exact ht_meas.compl
    · -- LHS: ∫_A (∫ 1_{tᶜ} dν) dμ = ∫_A (1 - ∫ 1_t dν) dμ = ∫_A 1 dμ - ∫_A (∫ 1_t dν) dμ
      -- RHS: ∫_A 1_{tᶜ}(X₀) dμ = ∫_A (1 - 1_t(X₀)) dμ = ∫_A 1 dμ - ∫_A 1_t(X₀) dμ
      -- By ht_eq, LHS = RHS
      have h_lhs_eq : ∫ ω in A, (∫ x, tᶜ.indicator (fun _ => (1:ℝ)) x
          ∂(directing_measure X hX_contract hX_meas hX_L2 ω)) ∂μ =
          ∫ ω in A, (1 : ℝ) ∂μ - ∫ ω in A, (∫ x, t.indicator (fun _ => (1:ℝ)) x
            ∂(directing_measure X hX_contract hX_meas hX_L2 ω)) ∂μ := by
        -- ∫ 1_{tᶜ} dν = 1 - ∫ 1_t dν (since ν is probability measure)
        have h_compl_eq : ∀ ω, ∫ x, tᶜ.indicator (fun _ => (1:ℝ)) x
            ∂(directing_measure X hX_contract hX_meas hX_L2 ω) =
            1 - ∫ x, t.indicator (fun _ => (1:ℝ)) x
              ∂(directing_measure X hX_contract hX_meas hX_L2 ω) := by
          intro ω
          haveI hprob := directing_measure_isProbabilityMeasure X hX_contract hX_meas hX_L2 ω
          have h_ind_compl : ∀ x, tᶜ.indicator (fun _ => (1:ℝ)) x =
              1 - t.indicator (fun _ => (1:ℝ)) x := by
            intro x
            by_cases hx : x ∈ t
            · simp [Set.indicator_of_mem hx, Set.indicator_of_not_mem (Set.not_mem_compl_iff.mpr hx)]
            · simp [Set.indicator_of_not_mem hx, Set.indicator_of_mem (Set.mem_compl hx)]
          simp_rw [h_ind_compl]
          rw [integral_sub (integrable_const 1), integral_const, measureReal_univ_eq_one, one_smul]
          exact (integrable_const 1).indicator ht_meas
        simp_rw [h_compl_eq]
        rw [integral_sub, integral_const]
        · exact (integrable_const 1).integrableOn
        · -- Need integrability of ω ↦ ∫ 1_t dν(ω) on A
          apply Integrable.integrableOn
          apply Integrable.mono' (integrable_const 1)
          · exact integral_indicator_borel_tailAEStronglyMeasurable X hX_contract hX_meas hX_L2 t ht_meas
              |>.mono hm_le
          · filter_upwards with ω
            rw [Real.norm_eq_abs]
            haveI hprob := directing_measure_isProbabilityMeasure X hX_contract hX_meas hX_L2 ω
            calc |∫ x, t.indicator (fun _ => (1:ℝ)) x
                ∂(directing_measure X hX_contract hX_meas hX_L2 ω)|
              ≤ ∫ x, |t.indicator (fun _ => (1:ℝ)) x|
                  ∂(directing_measure X hX_contract hX_meas hX_L2 ω) := abs_integral_le_integral_abs
              _ ≤ ∫ _, 1 ∂(directing_measure X hX_contract hX_meas hX_L2 ω) := by
                  apply integral_mono_of_nonneg
                  · exact ae_of_all _ (fun _ => abs_nonneg _)
                  · exact integrable_const 1
                  · exact ae_of_all _ (fun x => by
                      simp only [Set.indicator_apply]
                      split_ifs <;> simp)
              _ = 1 := by simp [measureReal_univ_eq_one]
      have h_rhs_eq : ∫ ω in A, tᶜ.indicator (fun _ => (1:ℝ)) (X 0 ω) ∂μ =
          ∫ ω in A, (1 : ℝ) ∂μ - ∫ ω in A, t.indicator (fun _ => (1:ℝ)) (X 0 ω) ∂μ := by
        have h_ind_compl : ∀ ω, tᶜ.indicator (fun _ => (1:ℝ)) (X 0 ω) =
            1 - t.indicator (fun _ => (1:ℝ)) (X 0 ω) := by
          intro ω
          by_cases hx : X 0 ω ∈ t
          · simp [Set.indicator_of_mem hx, Set.indicator_of_not_mem (Set.not_mem_compl_iff.mpr hx)]
          · simp [Set.indicator_of_not_mem hx, Set.indicator_of_mem (Set.mem_compl hx)]
        simp_rw [h_ind_compl]
        rw [integral_sub, integral_const]
        · exact (integrable_const 1).integrableOn
        · apply Integrable.integrableOn
          exact (integrable_const 1).indicator (ht_meas.preimage (hX_meas 0))
      rw [h_lhs_eq, h_rhs_eq, ht_eq]

  have h_iUnion : ∀ (f : ℕ → Set ℝ), (∀ i j, i ≠ j → Disjoint (f i) (f j)) →
      (∀ n, f n ∈ G) → (⋃ n, f n) ∈ G := by
    intro f hdisj hf
    constructor
    · exact MeasurableSet.iUnion (fun n => (hf n).1)
    · -- LHS: ∫_A (∫ 1_{⋃ fn} dν) dμ = ∫_A (∑' ∫ 1_{fn} dν) dμ = ∑' ∫_A (∫ 1_{fn} dν) dμ
      -- RHS: ∫_A 1_{⋃ fn}(X₀) dμ = ∫_A (∑' 1_{fn}(X₀)) dμ = ∑' ∫_A 1_{fn}(X₀) dμ
      -- By (hf n).2, each term is equal, hence sums are equal
      have h_lhs_eq : ∫ ω in A, (∫ x, (⋃ n, f n).indicator (fun _ => (1:ℝ)) x
          ∂(directing_measure X hX_contract hX_meas hX_L2 ω)) ∂μ =
          ∑' n, ∫ ω in A, (∫ x, (f n).indicator (fun _ => (1:ℝ)) x
            ∂(directing_measure X hX_contract hX_meas hX_L2 ω)) ∂μ := by
        -- First rewrite the inner integral as a tsum
        have h_inner_eq : ∀ ω, ∫ x, (⋃ n, f n).indicator (fun _ => (1:ℝ)) x
            ∂(directing_measure X hX_contract hX_meas hX_L2 ω) =
            ∑' n, ∫ x, (f n).indicator (fun _ => (1:ℝ)) x
              ∂(directing_measure X hX_contract hX_meas hX_L2 ω) := by
          intro ω
          haveI hprob := directing_measure_isProbabilityMeasure X hX_contract hX_meas hX_L2 ω
          have h_ind_union : ∀ x, (⋃ n, f n).indicator (fun _ => (1:ℝ)) x =
              ∑' n, (f n).indicator (fun _ => (1:ℝ)) x := by
            intro x
            by_cases hx : x ∈ ⋃ n, f n
            · obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
              rw [Set.indicator_of_mem hx]
              have h_unique : ∀ m, m ≠ n → x ∉ f m := by
                intro m hm hxm; exact (hdisj n m (Ne.symm hm)).ne_of_mem hn hxm rfl
              rw [tsum_eq_single n]
              · simp [Set.indicator_of_mem hn]
              · intro m hm; simp [Set.indicator_of_not_mem (h_unique m hm)]
            · simp only [Set.indicator_of_not_mem hx]
              have : ∀ n, x ∉ f n := fun n hn => hx (Set.mem_iUnion.mpr ⟨n, hn⟩)
              simp [Set.indicator_of_not_mem (this _)]
          simp_rw [h_ind_union]
          rw [integral_tsum]
          · exact fun n => (measurable_const.indicator (hf n).1).aestronglyMeasurable
          · intro n; exact (integrable_const 1).indicator (hf n).1
        simp_rw [h_inner_eq]
        -- Now we need: ∫_A (∑' fn) dμ = ∑' ∫_A fn dμ
        rw [integral_tsum]
        · intro n
          exact integral_indicator_borel_tailAEStronglyMeasurable X hX_contract hX_meas hX_L2
            (f n) (hf n).1 |>.mono hm_le |>.restrict
        · intro n
          apply Integrable.integrableOn
          apply Integrable.mono' (integrable_const 1)
          · exact integral_indicator_borel_tailAEStronglyMeasurable X hX_contract hX_meas hX_L2
              (f n) (hf n).1 |>.mono hm_le
          · filter_upwards with ω
            rw [Real.norm_eq_abs]
            haveI hprob := directing_measure_isProbabilityMeasure X hX_contract hX_meas hX_L2 ω
            calc |∫ x, (f n).indicator (fun _ => (1:ℝ)) x
                ∂(directing_measure X hX_contract hX_meas hX_L2 ω)|
              ≤ ∫ _, 1 ∂(directing_measure X hX_contract hX_meas hX_L2 ω) := by
                  rw [abs_le]; constructor
                  · calc -∫ x, (f n).indicator (fun _ => (1:ℝ)) x
                        ∂(directing_measure X hX_contract hX_meas hX_L2 ω)
                      ≤ 0 := by
                          simp only [neg_nonpos]
                          exact integral_nonneg (fun x => Set.indicator_nonneg (fun _ _ => zero_le_one) x)
                      _ ≤ ∫ _, 1 ∂(directing_measure X hX_contract hX_meas hX_L2 ω) :=
                          integral_nonneg (fun _ => zero_le_one)
                  · apply integral_mono
                    · exact (integrable_const 1).indicator (hf n).1
                    · exact integrable_const 1
                    · intro x; exact Set.indicator_le_self' (fun _ _ => zero_le_one) x
              _ = 1 := by simp [measureReal_univ_eq_one]

      have h_rhs_eq : ∫ ω in A, (⋃ n, f n).indicator (fun _ => (1:ℝ)) (X 0 ω) ∂μ =
          ∑' n, ∫ ω in A, (f n).indicator (fun _ => (1:ℝ)) (X 0 ω) ∂μ := by
        have h_ind_union : ∀ ω, (⋃ n, f n).indicator (fun _ => (1:ℝ)) (X 0 ω) =
            ∑' n, (f n).indicator (fun _ => (1:ℝ)) (X 0 ω) := by
          intro ω
          by_cases hx : X 0 ω ∈ ⋃ n, f n
          · obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
            rw [Set.indicator_of_mem hx]
            have h_unique : ∀ m, m ≠ n → X 0 ω ∉ f m := by
              intro m hm hxm; exact (hdisj n m (Ne.symm hm)).ne_of_mem hn hxm rfl
            rw [tsum_eq_single n]
            · simp [Set.indicator_of_mem hn]
            · intro m hm; simp [Set.indicator_of_not_mem (h_unique m hm)]
          · simp only [Set.indicator_of_not_mem hx]
            have : ∀ n, X 0 ω ∉ f n := fun n hn => hx (Set.mem_iUnion.mpr ⟨n, hn⟩)
            simp [Set.indicator_of_not_mem (this _)]
        simp_rw [h_ind_union]
        rw [integral_tsum]
        · intro n
          exact ((measurable_const.indicator (hf n).1).comp (hX_meas 0)).aestronglyMeasurable.restrict
        · intro n
          apply Integrable.integrableOn
          exact (integrable_const 1).indicator ((hf n).1.preimage (hX_meas 0))

      rw [h_lhs_eq, h_rhs_eq]
      congr 1
      ext n
      exact (hf n).2

  -- Step 3: Apply π-λ theorem
  let S : Set (Set ℝ) := Set.range (Set.Iic : ℝ → Set ℝ)
  have h_gen : (inferInstance : MeasurableSpace ℝ) = MeasurableSpace.generateFrom S :=
    @borel_eq_generateFrom_Iic ℝ _ _ _ _
  have h_pi_S : IsPiSystem S := by
    intro u hu v hv _
    obtain ⟨r, rfl⟩ := hu
    obtain ⟨t, rfl⟩ := hv
    use min r t
    exact Set.Iic_inter_Iic.symm

  have h_induction : ∀ t (htm : MeasurableSet t), t ∈ G := fun t htm =>
    MeasurableSpace.induction_on_inter h_gen h_pi_S
      h_empty
      (fun u ⟨r, hr⟩ => hr ▸ h_pi r)
      (fun u hum hu => h_compl u hu)
      (fun f hdisj hfm hf => h_iUnion f hdisj hf)
      t htm

  exact (h_induction s hs).2

/-- **Set integral equality for bounded measurable functions.**

This is the key equality needed for `ae_eq_condExp_of_forall_setIntegral_eq`. -/
lemma setIntegral_directing_measure_bounded_measurable_eq
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ)
    (f : ℝ → ℝ) (hf_meas : Measurable f) (hf_bdd : ∃ M, ∀ x, |f x| ≤ M)
    (A : Set Ω) (hA : @MeasurableSet Ω (TailSigma.tailSigma X) A) (hμA : μ A < ⊤) :
    ∫ ω in A, (∫ x, f x ∂(directing_measure X hX_contract hX_meas hX_L2 ω)) ∂μ
      = ∫ ω in A, f (X 0 ω) ∂μ := by
  -- Get the bound M (ensure M ≥ 0)
  obtain ⟨M, hM⟩ := hf_bdd
  obtain ⟨M', hM'_nonneg, hM'⟩ : ∃ M' : ℝ, 0 ≤ M' ∧ ∀ x, |f x| ≤ M' := by
    use max M 0
    exact ⟨le_max_right M 0, fun x => (hM x).trans (le_max_left M 0)⟩

  have hm_le : TailSigma.tailSigma X ≤ (inferInstance : MeasurableSpace Ω) :=
    TailSigma.tailSigma_le X hX_meas
  have hA_ambient : MeasurableSet A := hm_le A hA

  -- The range of f is in Set.Icc (-M') M'
  have hf_range : ∀ x, f x ∈ Set.Icc (-M') M' := by
    intro x
    rw [Set.mem_Icc]
    exact abs_le.mp (hM' x)

  have h0_mem : (0 : ℝ) ∈ Set.Icc (-M') M' := by
    rw [Set.mem_Icc]; exact ⟨by linarith, hM'_nonneg⟩

  -- Approximate f by simple functions
  let φ : ℕ → SimpleFunc ℝ ℝ := SimpleFunc.approxOn f hf_meas (Set.Icc (-M') M') 0 h0_mem

  have hφ_range : ∀ n x, φ n x ∈ Set.Icc (-M') M' := fun n x =>
    SimpleFunc.approxOn_mem hf_meas h0_mem n x

  have hφ_tendsto : ∀ x, Filter.Tendsto (fun n => φ n x) Filter.atTop (nhds (f x)) := by
    intro x
    apply SimpleFunc.tendsto_approxOn hf_meas h0_mem
    rw [IsClosed.closure_eq (isClosed_Icc)]
    exact hf_range x

  -- LHS: ∫_A (∫ φ_n dν) dμ → ∫_A (∫ f dν) dμ
  have h_lhs_tendsto : Filter.Tendsto
      (fun n => ∫ ω in A, (∫ x, φ n x ∂(directing_measure X hX_contract hX_meas hX_L2 ω)) ∂μ)
      Filter.atTop
      (nhds (∫ ω in A, (∫ x, f x ∂(directing_measure X hX_contract hX_meas hX_L2 ω)) ∂μ)) := by
    -- Apply DCT with bound M' (set integrals are definitionally restricted integrals)
    apply tendsto_integral_of_dominated_convergence (fun _ => M')
    · intro n
      exact integral_simpleFunc_tailAEStronglyMeasurable X hX_contract hX_meas hX_L2 (φ n)
        |>.mono hm_le |>.restrict
    · exact (integrable_const M').integrableOn
    · intro n
      filter_upwards with ω
      rw [Real.norm_eq_abs]
      haveI hprob := directing_measure_isProbabilityMeasure X hX_contract hX_meas hX_L2 ω
      -- |∫ φ_n dν| ≤ M' (since |φ_n| ≤ M' and ν is prob measure)
      calc |∫ x, φ n x ∂(directing_measure X hX_contract hX_meas hX_L2 ω)|
        ≤ ∫ x, |φ n x| ∂(directing_measure X hX_contract hX_meas hX_L2 ω) := abs_integral_le_integral_abs
        _ ≤ ∫ _, M' ∂(directing_measure X hX_contract hX_meas hX_L2 ω) := by
            apply integral_mono_of_nonneg
            · exact ae_of_all _ (fun _ => abs_nonneg _)
            · exact integrable_const M'
            · filter_upwards with x
              have := hφ_range n x
              rw [Set.mem_Icc] at this
              exact abs_le.mpr this
        _ = M' := by simp [measureReal_univ_eq_one]
    · filter_upwards with ω
      -- ∫ φ_n dν(ω) → ∫ f dν(ω) by DCT on ν(ω)
      haveI hprob := directing_measure_isProbabilityMeasure X hX_contract hX_meas hX_L2 ω
      apply tendsto_integral_of_dominated_convergence (fun _ => M')
      · intro n; exact (SimpleFunc.measurable (φ n)).aestronglyMeasurable
      · exact integrable_const M'
      · intro n; filter_upwards with x
        rw [Real.norm_eq_abs]
        have := hφ_range n x
        rw [Set.mem_Icc] at this
        exact abs_le.mpr this
      · filter_upwards with x; exact hφ_tendsto x

  -- RHS: ∫_A φ_n(X₀) dμ → ∫_A f(X₀) dμ
  have h_rhs_tendsto : Filter.Tendsto
      (fun n => ∫ ω in A, (φ n) (X 0 ω) ∂μ)
      Filter.atTop
      (nhds (∫ ω in A, f (X 0 ω) ∂μ)) := by
    -- Apply DCT with bound M' (set integrals are definitionally restricted integrals)
    apply tendsto_integral_of_dominated_convergence (fun _ => M')
    · intro n
      exact ((SimpleFunc.measurable (φ n)).comp (hX_meas 0)).aestronglyMeasurable.restrict
    · exact (integrable_const M').integrableOn
    · intro n
      filter_upwards with ω
      rw [Real.norm_eq_abs]
      have := hφ_range n (X 0 ω)
      rw [Set.mem_Icc] at this
      exact abs_le.mpr this
    · filter_upwards with ω
      exact hφ_tendsto (X 0 ω)

  -- For each n, LHS_n = RHS_n
  have h_eq_n : ∀ n, ∫ ω in A, (∫ x, φ n x ∂(directing_measure X hX_contract hX_meas hX_L2 ω)) ∂μ
      = ∫ ω in A, (φ n) (X 0 ω) ∂μ := by
    intro n
    -- SimpleFunc integral is finite sum of indicator integrals
    -- Use setIntegral_directing_measure_indicator_eq + linearity
    have h_sf_eq : ∀ ω, ∫ x, φ n x ∂(directing_measure X hX_contract hX_meas hX_L2 ω) =
        ∑ c ∈ (φ n).range, (directing_measure X hX_contract hX_meas hX_L2 ω).real ((φ n) ⁻¹' {c}) • c := by
      intro ω
      haveI hprob := directing_measure_isProbabilityMeasure X hX_contract hX_meas hX_L2 ω
      have h_int : Integrable (⇑(φ n)) (directing_measure X hX_contract hX_meas hX_L2 ω) := by
        apply SimpleFunc.integrable; intro c _; exact measure_ne_top _ _
      exact SimpleFunc.integral_eq_sum (φ n) h_int
    have h_rhs_sf_eq : ∀ ω, (φ n) (X 0 ω) =
        ∑ c ∈ (φ n).range, ((φ n) ⁻¹' {c}).indicator (fun _ => c) (X 0 ω) := by
      intro ω
      simp only [Finset.sum_indicator_eq_sum_filter]
      simp only [Finset.filter_eq', Finset.mem_range]
      by_cases h : (φ n) (X 0 ω) ∈ (φ n).range
      · simp [h]
      · simp only [h, ↓reduceIte, Finset.sum_empty]
        exfalso; exact h (SimpleFunc.mem_range_self (φ n) (X 0 ω))
    -- Both sides are sums; equality term by term
    simp_rw [h_sf_eq, h_rhs_sf_eq]
    rw [integral_finset_sum, integral_finset_sum]
    · congr 1
      ext c
      -- Need: ∫_A ν(ω).real((φ n)⁻¹'{c}) • c dμ = ∫_A 1_{(φ n)⁻¹'{c}}(X₀) • c dμ
      simp only [smul_eq_mul]
      rw [integral_mul_right, integral_mul_right]
      congr 1
      -- ∫_A ν(ω).real((φ n)⁻¹'{c}) dμ = ∫_A 1_{(φ n)⁻¹'{c}}(X₀) dμ
      have h_preimage_meas : MeasurableSet ((φ n) ⁻¹' {c}) := SimpleFunc.measurableSet_preimage (φ n) {c}
      have h_real_eq_ind : ∀ ω, (directing_measure X hX_contract hX_meas hX_L2 ω).real ((φ n) ⁻¹' {c}) =
          ∫ x, ((φ n) ⁻¹' {c}).indicator (fun _ => (1:ℝ)) x
            ∂(directing_measure X hX_contract hX_meas hX_L2 ω) := by
        intro ω
        haveI hprob := directing_measure_isProbabilityMeasure X hX_contract hX_meas hX_L2 ω
        rw [integral_indicator_one h_preimage_meas]
      simp_rw [h_real_eq_ind]
      have h_ind_X0 : ∀ ω, ((φ n) ⁻¹' {c}).indicator (fun _ => c) (X 0 ω) =
          c * ((φ n) ⁻¹' {c}).indicator (fun _ => (1:ℝ)) (X 0 ω) := by
        intro ω
        by_cases hω : X 0 ω ∈ (φ n) ⁻¹' {c}
        · simp [Set.indicator_of_mem hω]
        · simp [Set.indicator_of_not_mem hω]
      simp_rw [h_ind_X0, integral_mul_left]
      ring_nf
      exact setIntegral_directing_measure_indicator_eq X hX_contract hX_meas hX_L2
        ((φ n) ⁻¹' {c}) h_preimage_meas A hA hμA
    · intro c _
      apply Integrable.integrableOn
      exact (integrable_const c).indicator (h_preimage_meas.preimage (hX_meas 0))
    · intro c _
      apply Integrable.integrableOn
      apply Integrable.smul
      apply Integrable.mono' (integrable_const 1)
      · exact integral_indicator_borel_tailAEStronglyMeasurable X hX_contract hX_meas hX_L2
          ((φ n) ⁻¹' {c}) (SimpleFunc.measurableSet_preimage (φ n) {c}) |>.mono hm_le
      · filter_upwards with ω
        rw [Real.norm_eq_abs]
        haveI hprob := directing_measure_isProbabilityMeasure X hX_contract hX_meas hX_L2 ω
        calc |(directing_measure X hX_contract hX_meas hX_L2 ω).real ((φ n) ⁻¹' {c})|
          ≤ 1 := by
            rw [abs_le]
            constructor
            · calc -(directing_measure X hX_contract hX_meas hX_L2 ω).real ((φ n) ⁻¹' {c})
                ≤ 0 := by simp [measureReal_nonneg]
                _ ≤ 1 := zero_le_one
            · exact measureReal_le_one ((φ n) ⁻¹' {c})

  -- Since limits are unique and h_eq_n holds for all n, the limits are equal
  exact tendsto_nhds_unique h_lhs_tendsto (h_rhs_tendsto.congr (fun n => (h_eq_n n).symm))

/-- **Main bridge lemma:** For any bounded measurable f, the integral against directing_measure
equals the conditional expectation E[f(X₀)|tail].

This is the Kallenberg identification: ν(ω) is the conditional distribution of X₀ given tail. -/
lemma directing_measure_integral_eq_condExp
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ)
    (f : ℝ → ℝ) (hf_meas : Measurable f) (hf_bdd : ∃ M, ∀ x, |f x| ≤ M) :
    (fun ω => ∫ x, f x ∂(directing_measure X hX_contract hX_meas hX_L2 ω))
      =ᵐ[μ] μ[fun ω => f (X 0 ω) | TailSigma.tailSigma X] := by
  -- PROOF STRATEGY: Monotone class extension from Iic to bounded measurable
  --
  -- === STEP 1: Base case for Iic indicators ===
  -- For f = 1_{Iic t}, we need: ∫ 1_{Iic t} dν(ω) =ᵐ E[1_{Iic t}(X₀)|tail](ω)
  --
  -- - LHS: By directing_measure_integral_Iic_ae_eq_alphaIicCE, ∫ 1_{Iic t} dν(ω) =ᵐ αIicCE t ω
  -- - RHS: By definition of αIicCE, αIicCE t ω = μ[1_{Iic t} ∘ X 0 | TailSigma.tailSigma X](ω)
  -- - Result: LHS =ᵐ αIicCE t =ᵐ RHS ✓
  --
  -- === STEP 2: Extend to Ioc indicators ===
  -- For f = 1_{Ioc a b} = 1_{Iic b} - 1_{Iic a} (when a < b):
  -- - ∫ 1_{Ioc a b} dν(ω) = ∫ 1_{Iic b} dν - ∫ 1_{Iic a} dν  (linearity of integral)
  -- - E[1_{Ioc a b}(X₀)|tail] = E[1_{Iic b}(X₀)|tail] - E[1_{Iic a}(X₀)|tail]  (condExp_sub)
  -- - By Step 1, both pairs are a.e. equal → 1_{Ioc a b} works ✓
  --
  -- === STEP 3: Extend to simple functions ===
  -- Simple functions are finite linear combinations of Ioc indicators.
  -- By linearity of both operations (integral_add, integral_smul, condExp_add, condExp_smul),
  -- the result holds for all simple functions ✓
  --
  -- === STEP 4: Extend to bounded measurable ===
  -- For bounded measurable f with |f| ≤ M:
  -- - Use SimpleFunc.approxOn (or MeasureTheory.Lp.simpleFunc_approximation) to get
  --   simple functions s_n → f pointwise with |s_n| ≤ M
  -- - For LHS: Apply MeasureTheory.tendsto_integral_of_dominated_convergence
  --   (dominating function is M, bound by boundedness)
  -- - For RHS: Apply MeasureTheory.tendsto_condExpL1_of_dominated_convergence
  --   (same dominating function)
  -- - Both sides converge in L¹, and by Step 3 they're a.e. equal for each s_n
  -- - By L¹ limit uniqueness, the limits are a.e. equal ✓
  --
  -- Key mathlib lemmas:
  -- - directing_measure_integral_Iic_ae_eq_alphaIicCE (base case, exists above)
  -- - MeasureTheory.condExp_sub, MeasureTheory.condExp_smul (linearity)
  -- - MeasureTheory.SimpleFunc.approxOn (approximation by simple functions)
  -- - MeasureTheory.tendsto_integral_of_dominated_convergence (DCT for integrals)
  -- - MeasureTheory.tendsto_condExpL1_of_dominated_convergence (DCT for condExp)
  --
  -- ═══════════════════════════════════════════════════════════════════════════════
  -- PROOF STRATEGY: Conditional distribution uniqueness
  --
  -- The directing measure ν(ω) is constructed so that its CDF equals αIicCE:
  --   (ν(ω))(Iic t) = αIicCE t ω = E[1_{Iic t}(X₀)|tail](ω) a.e.
  --
  -- Since measures on ℝ are uniquely determined by their CDFs, and the conditional
  -- distribution of X₀ given tail is uniquely characterized by the same CDF values,
  -- we have ν(ω) = P_{X₀|tail}(ω) as measures for a.e. ω.
  --
  -- Therefore, for any bounded measurable f:
  --   ∫ f dν(ω) = E[f(X₀)|tail](ω) a.e.
  --
  -- The proof involves:
  -- 1. Base case: For Iic indicators, directing_measure_integral_Iic_ae_eq_alphaIicCE
  --    gives ∫ 1_{Iic t} dν(ω) =ᵐ αIicCE t ω = E[1_{Iic t}(X₀)|tail](ω)
  --
  -- 2. Extension: For general bounded measurable f, use:
  --    - Step functions approximation (via Ioc indicators)
  --    - Linearity of both ∫ · dν and E[·|tail]
  --    - Dominated convergence to pass to limit
  --
  -- OR use the uniqueness of conditional expectation:
  -- If h is m-measurable and ∫_A h dμ = ∫_A f(X₀) dμ for all m-measurable A,
  -- then h =ᵐ E[f(X₀)|m].
  --
  -- The key is showing ∫_A (∫ f dν) dμ = ∫_A f(X₀) dμ via Fubini and the
  -- conditional distribution property.
  -- ═══════════════════════════════════════════════════════════════════════════════
  --
  -- MATHEMATICAL CONTENT (to be formalized):
  --
  -- The proof requires showing that ν(ω) is the regular conditional distribution
  -- of X₀ given the tail σ-algebra. This follows from:
  -- 1. CDF agreement: For all t, (ν(ω))(Iic t) = E[1_{Iic t}(X₀)|tail](ω) a.e.
  -- 2. Measures are determined by CDFs (uniqueness)
  -- 3. Integration against measures determined by CDFs
  --
  -- The formalization uses ae_eq_condExp_of_forall_setIntegral_eq and requires:
  -- 1. Measurability of ω ↦ ∫ f dν(ω) w.r.t. tail σ-algebra
  -- 2. Set integral equality: ∫_A (∫ f dν) dμ = ∫_A f(X₀) dμ for tail-measurable A
  -- 3. Monotone class extension from Iic indicators to bounded measurable functions

  -- Set up the sub-σ-algebra and sigma-finiteness
  have hm_le : TailSigma.tailSigma X ≤ (inferInstance : MeasurableSpace Ω) :=
    TailSigma.tailSigma_le X hX_meas
  haveI hm_fact : Fact (TailSigma.tailSigma X ≤ (inferInstance : MeasurableSpace Ω)) := ⟨hm_le⟩
  haveI hσ : SigmaFinite (μ.trim hm_le) := inferInstance

  -- Get the bound M (ensure M ≥ 0)
  obtain ⟨M, hM⟩ := hf_bdd
  obtain ⟨M', hM'_nonneg, hM'⟩ : ∃ M' : ℝ, 0 ≤ M' ∧ ∀ x, |f x| ≤ M' := by
    use max M 0
    exact ⟨le_max_right M 0, fun x => (hM x).trans (le_max_left M 0)⟩

  -- Define g = fun ω => ∫ x, f x ∂ν(ω)
  let g : Ω → ℝ := fun ω => ∫ x, f x ∂(directing_measure X hX_contract hX_meas hX_L2 ω)

  -- f ∘ X 0 is integrable (bounded function composed with measurable map)
  have hfX0_int : Integrable (fun ω => f (X 0 ω)) μ := by
    refine Integrable.mono' (integrable_const M') ?_ ?_
    · exact (hf_meas.comp (hX_meas 0)).aestronglyMeasurable
    · filter_upwards with ω; rw [Real.norm_eq_abs]; exact hM' (X 0 ω)

  -- g is bounded by M' (since ν(ω) is a probability measure)
  have hg_bdd : ∀ ω, |g ω| ≤ M' := by
    intro ω
    haveI : IsProbabilityMeasure (directing_measure X hX_contract hX_meas hX_L2 ω) :=
      directing_measure_isProbabilityMeasure X hX_contract hX_meas hX_L2 ω
    calc |g ω| = |∫ x, f x ∂(directing_measure X hX_contract hX_meas hX_L2 ω)| := rfl
      _ ≤ ∫ x, |f x| ∂(directing_measure X hX_contract hX_meas hX_L2 ω) :=
          abs_integral_le_integral_abs
      _ ≤ ∫ x, M' ∂(directing_measure X hX_contract hX_meas hX_L2 ω) := by
          apply integral_mono_of_nonneg
          · exact ae_of_all _ (fun _ => abs_nonneg _)
          · exact integrable_const M'
          · exact ae_of_all _ hM'
      _ = M' := by simp only [integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul]

  -- g is AEStronglyMeasurable w.r.t. ambient σ-algebra
  -- Uses monotone class theorem: measurability extends from Iic indicators to bounded measurable f.
  -- First prove tail-AEStronglyMeasurable (hgm), then get ambient from it
  -- Key insight: alphaIicCE t is strongly measurable w.r.t. tail σ-algebra (it's a condExp)
  -- So ∫ 1_{Iic t} dν(ω) =ᵐ alphaIicCE t ω is tail-AEStronglyMeasurable
  -- Extend to bounded measurable f via step function approximation + limits

  have hgm_early : @AEStronglyMeasurable Ω ℝ _ (TailSigma.tailSigma X) _ g μ :=
    -- Use the factored-out helper lemma for Phase C (which builds on Phases A and B)
    integral_bounded_measurable_tailAEStronglyMeasurable X hX_contract hX_meas hX_L2 f hf_meas hf_bdd

  -- Ambient AEStronglyMeasurable follows from tail via .mono
  have hg_asm : AEStronglyMeasurable g μ := AEStronglyMeasurable.mono hm_le hgm_early

  -- g is integrable (bounded and measurable on probability space)
  have hg_int : Integrable g μ := by
    refine Integrable.mono' (integrable_const M') hg_asm ?_
    filter_upwards with ω; rw [Real.norm_eq_abs]; exact hg_bdd ω

  -- Apply ae_eq_condExp_of_forall_setIntegral_eq
  -- The theorem says: if g is tail-AEStronglyMeasurable and has the same set integrals as f ∘ X 0
  -- on all tail-measurable sets, then g =ᵐ μ[f ∘ X 0 | tail].
  -- Our goal is g =ᵐ μ[f ∘ X 0 | tail] where g = fun ω => ∫ f dν(ω).
  refine ae_eq_condExp_of_forall_setIntegral_eq hm_le hfX0_int ?hg_int_finite ?hg_eq ?hgm

  case hg_int_finite =>
    intro s _ _; exact hg_int.integrableOn

  case hgm =>
    -- ae_eq_condExp_of_forall_setIntegral_eq needs tail-AEStronglyMeasurable
    -- This is exactly what hgm_early provides.
    exact hgm_early

  case hg_eq =>
    -- The key: ∫_A g dμ = ∫_A f(X₀) dμ for tail-measurable A with μ A < ∞
    intro A hA hμA
    -- Use the factored-out helper lemma for set integral equality
    exact setIntegral_directing_measure_bounded_measurable_eq
      X hX_contract hX_meas hX_L2 f hf_meas hf_bdd A hA hμA

/-- **Simplified directing measure integral via identification chain.**

This lemma proves that the L¹ limit α equals ∫f dν a.e. using the Kallenberg identification chain:
1. α = E[f(X₀)|tail]  (from `cesaro_to_condexp_L2`)
2. E[f(X₀)|tail] = ∫f dν  (from `directing_measure_integral_eq_condExp`)
3. Therefore α = ∫f dν by transitivity

This approach bypasses the Ioc/step function decomposition entirely, giving a much simpler proof.

**Key insight:** By uniqueness of L¹ limits, the L¹ limit from `weighted_sums_converge_L1`
equals the L² limit from `cesaro_to_condexp_L2` (since L² convergence implies L¹ on prob spaces).
-/
lemma directing_measure_integral_via_chain
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
  -- Get α from weighted_sums_converge_L1
  obtain ⟨alpha, hα_meas, hα_L1, hα_conv⟩ :=
    weighted_sums_converge_L1 X hX_contract hX_meas hX_L2 f hf_meas hf_bdd
  refine ⟨alpha, hα_meas, hα_L1, hα_conv, ?_⟩

  -- ═══════════════════════════════════════════════════════════════════════════════
  -- IDENTIFICATION CHAIN: α = E[f(X₀)|tail] = ∫f dν
  -- ═══════════════════════════════════════════════════════════════════════════════

  -- Step 1: Get α_f from cesaro_to_condexp_L2 with identification
  -- α_f =ᵐ E[f(X₀)|tail]
  -- Note: cesaro_to_condexp_L2 requires |f x| ≤ 1, so we need to rescale if M > 1
  obtain ⟨M, hM⟩ := hf_bdd
  by_cases hM_zero : M = 0
  · -- If M = 0, then f = 0, so both α and ∫f dν are 0 a.e.
    have hf_zero : ∀ x, f x = 0 := fun x => by
      have := hM x
      rw [hM_zero] at this
      exact abs_nonpos_iff.mp this

    -- Show ∫f dν = 0 for all ω (deterministic, not just a.e.)
    have h_integral_zero : ∀ ω, ∫ x, f x ∂(directing_measure X hX_contract hX_meas hX_L2 ω) = 0 := by
      intro ω
      simp only [hf_zero, integral_zero]

    -- Show alpha = 0 a.e. from L¹ convergence
    -- When f = 0, Cesàro averages are 0, so ∫|0 - alpha| < ε for all ε > 0
    -- This implies ∫|alpha| = 0, hence alpha = 0 a.e.
    have h_alpha_zero_ae : alpha =ᵐ[μ] 0 := by
      -- The Cesàro sum is 0 when f = 0
      have h_cesaro_zero : ∀ (n : ℕ) (m : ℕ) ω,
          (1/(m:ℝ)) * ∑ k : Fin m, f (X (n + k.val + 1) ω) = 0 := by
        intro n m ω
        simp only [hf_zero, Finset.sum_const_zero, mul_zero]
      -- From hα_conv with n = 0, ε = 1/k: ∫|0 - alpha| < 1/k for large m
      -- Taking limit: ∫|alpha| ≤ 0, so ∫|alpha| = 0
      have h_int_abs_alpha_eq_zero : ∫ ω, |alpha ω| ∂μ = 0 := by
        apply le_antisymm _ (integral_nonneg (fun _ => abs_nonneg _))
        -- For any ε > 0, ∫|alpha| < ε (using hα_conv with cesaro = 0)
        by_contra h_pos
        push_neg at h_pos
        have hε : (0 : ℝ) < ∫ ω, |alpha ω| ∂μ := h_pos
        obtain ⟨M_idx, hM_idx⟩ := hα_conv 0 (∫ ω, |alpha ω| ∂μ) hε
        specialize hM_idx M_idx (le_refl _)
        have h_simp : ∀ ω', |(1 / (M_idx : ℝ)) * ∑ k : Fin M_idx, f (X (0 + k.val + 1) ω') - alpha ω'|
            = |alpha ω'| := by
          intro ω'
          rw [h_cesaro_zero 0 M_idx ω', zero_sub, abs_neg]
        simp_rw [h_simp] at hM_idx
        linarith
      -- ∫|alpha| = 0 implies alpha = 0 a.e.
      -- Use: integral_eq_zero_iff_of_nonneg_ae
      have h_abs_nonneg : (0 : Ω → ℝ) ≤ᵐ[μ] (fun ω => |alpha ω|) :=
        ae_of_all μ (fun ω => abs_nonneg (alpha ω))
      have h_abs_int : Integrable (fun ω => |alpha ω|) μ :=
        (memLp_one_iff_integrable.mp hα_L1).norm
      rw [integral_eq_zero_iff_of_nonneg_ae h_abs_nonneg h_abs_int] at h_int_abs_alpha_eq_zero
      exact h_int_abs_alpha_eq_zero.mono (fun ω hω => abs_eq_zero.mp hω)

    -- Combine: alpha = 0 = ∫f dν a.e.
    filter_upwards [h_alpha_zero_ae] with ω hω
    simp only [hω, h_integral_zero ω, Pi.zero_apply]

  · -- M > 0 case
    have hM_pos : 0 < M := lt_of_le_of_ne (abs_nonneg (f 0) |>.trans (hM 0)) (Ne.symm hM_zero)

    -- Rescale f to g = f/M so |g| ≤ 1
    let g : ℝ → ℝ := fun x => f x / M
    have hg_meas : Measurable g := hf_meas.div_const M
    have hg_bdd : ∀ x, |g x| ≤ 1 := fun x => by
      simp only [g, abs_div]
      have hM_abs : |M| = M := abs_of_pos hM_pos
      rw [hM_abs]
      calc |f x| / M ≤ M / M := div_le_div_of_nonneg_right (hM x) (le_of_lt hM_pos)
        _ = 1 := div_self (ne_of_gt hM_pos)

    -- Apply cesaro_to_condexp_L2 to g
    obtain ⟨α_g, hα_g_L2, hα_g_tail, hα_g_conv, hα_g_eq⟩ :=
      cesaro_to_condexp_L2 hX_contract hX_meas g hg_meas hg_bdd

    -- α_g = E[g(X₀)|tail] = E[(f/M)(X₀)|tail] = (1/M) * E[f(X₀)|tail]
    -- So: E[f(X₀)|tail] = M * α_g

    -- Chain:
    -- 1. alpha =ᵐ M * α_g  (by uniqueness of limits for f = M * g)
    -- 2. M * α_g =ᵐ M * E[g(X₀)|tail] = E[f(X₀)|tail]  (by linearity of condExp)
    -- 3. E[f(X₀)|tail] =ᵐ ∫f dν  (by directing_measure_integral_eq_condExp)

    -- Bridge lemma: E[f(X₀)|tail] =ᵐ ∫f dν
    have h_bridge : (fun ω => ∫ x, f x ∂(directing_measure X hX_contract hX_meas hX_L2 ω))
        =ᵐ[μ] μ[fun ω => f (X 0 ω) | TailSigma.tailSigma X] :=
      directing_measure_integral_eq_condExp X hX_contract hX_meas hX_L2 f hf_meas ⟨M, hM⟩

    -- ═══════════════════════════════════════════════════════════════════════════════
    -- KEY STEP: alpha =ᵐ E[f(X₀)|tail] via L¹ uniqueness
    -- ═══════════════════════════════════════════════════════════════════════════════
    --
    -- The identification chain connects three quantities a.e.:
    --   alpha = E[f(X₀)|tail] = ∫f dν
    --
    -- Direct approach: Both alpha and E[f|tail] are L¹ limits of shifted f-averages.
    -- - alpha → from hα_conv (L¹ limit of shifted f-averages at indices n+1,...,n+m)
    -- - E[f(X₀)|tail] → from cesaro_convergence_all_shifts (same averages)
    -- By L¹ uniqueness, alpha =ᵐ E[f(X₀)|tail].
    --
    -- Note: We use the rescaled function g = f/M with |g| ≤ 1 since
    -- cesaro_convergence_all_shifts requires the bound |g| ≤ 1.
    -- Then we scale back: M * (g-averages) = f-averages.

    -- Step 1: Show alpha =ᵐ E[f(X₀)|tail] using L¹ uniqueness directly
    -- Both limits are a.e. equal to the unique L¹ limit of shifted f-averages
    have h_alpha_eq_condExp : alpha =ᵐ[μ] μ[f ∘ X 0 | TailSigma.tailSigma X] := by
      -- PROOF: Use condExp_smul and the identification from cesaro_to_condexp_L2
      --
      -- We have from cesaro_to_condexp_L2:
      --   α_g =ᵐ μ[g ∘ X 0 | tail]    where g = f/M
      --
      -- By condExp_smul: μ[M • (g ∘ X 0) | tail] = M • μ[g ∘ X 0 | tail]
      -- Since f = M * g: μ[f ∘ X 0 | tail] = M * μ[g ∘ X 0 | tail] =ᵐ M * α_g
      --
      -- The L¹ uniqueness argument:
      -- - f-averages = M * g-averages (algebra)
      -- - g-averages → α_g in L² (from cesaro_to_condexp_L2, via L² convergence)
      -- - L² convergence ⟹ L¹ convergence on probability spaces
      -- - So M * g-averages = f-averages → M * α_g in L¹
      -- - But hα_conv says f-averages → alpha in L¹
      -- - By uniqueness of L¹ limits: alpha =ᵐ M * α_g
      --
      -- Conclusion: alpha =ᵐ M * α_g =ᵐ M * μ[g ∘ X 0 | tail] = μ[f ∘ X 0 | tail]

      -- Step 1a: Show μ[f ∘ X 0 | tail] = M * μ[g ∘ X 0 | tail]
      have hm_le := TailSigma.tailSigma_le X hX_meas
      have h_condExp_f_eq : μ[f ∘ X 0 | TailSigma.tailSigma X]
          =ᵐ[μ] fun ω => M * μ[g ∘ X 0 | TailSigma.tailSigma X] ω := by
        -- f x = M * g x (since g x = f x / M and M > 0)
        have h_f_eq_Mg : ∀ x, f x = M * g x := fun x => by
          simp only [g]
          field_simp [ne_of_gt hM_pos]
        -- f ∘ X 0 = (M • g) ∘ X 0 (pointwise)
        have h_comp_eq : (f ∘ X 0) = fun ω => M * g (X 0 ω) := by
          ext ω
          simp only [Function.comp_apply, h_f_eq_Mg]
        -- Use condExp linearity: E[M * h | m] = M * E[h | m]
        have h_ae : μ[fun ω => M * g (X 0 ω) | TailSigma.tailSigma X]
            =ᵐ[μ] fun ω => M * μ[g ∘ X 0 | TailSigma.tailSigma X] ω := by
          -- Use condExp_smul with appropriate coercions
          have h_smul := condExp_smul M (g ∘ X 0) (m := TailSigma.tailSigma X) (μ := μ)
          simp only [smul_eq_mul, Pi.smul_apply] at h_smul
          convert h_smul using 2 <;> ext ω <;> ring
        calc μ[f ∘ X 0 | TailSigma.tailSigma X]
            = μ[fun ω => M * g (X 0 ω) | TailSigma.tailSigma X] := by rw [h_comp_eq]
          _ =ᵐ[μ] fun ω => M * μ[g ∘ X 0 | TailSigma.tailSigma X] ω := h_ae

      -- Step 1b: Show alpha =ᵐ M * α_g by L¹ uniqueness
      -- Both are L¹ limits of f-averages (which equal M * g-averages)
      have h_alpha_eq_M_alpha_g : alpha =ᵐ[μ] fun ω => M * α_g ω := by
        -- Strategy: Both alpha and M * α_g are L¹ limits of the same sequence:
        --   A m ω := m⁻¹ * ∑ k : Fin m, f (X (k.val + 1) ω)
        -- The indices match:
        --   - hα_conv 0: uses X (0 + k.val + 1) = X (k.val + 1), indices 1, 2, ..., m
        --   - cesaro_convergence_all_shifts with n=1: uses X (1+k), indices 1, 2, ..., m
        -- By L¹ uniqueness, alpha =ᵐ M * α_g.

        -- Define the averaging sequence with matching indices
        let A : ℕ → Ω → ℝ := fun m ω => (1/(m:ℝ)) * ∑ k : Fin m, f (X (k.val + 1) ω)

        -- From hα_conv 0: A → alpha in L¹
        have hA_to_alpha : ∀ ε > 0, ∃ M_idx : ℕ, ∀ m ≥ M_idx,
            ∫ ω, |A m ω - alpha ω| ∂μ < ε := by
          intro ε hε
          obtain ⟨M_idx, hM_idx⟩ := hα_conv 0 ε hε
          use M_idx
          intro m hm
          convert hM_idx m hm using 2
          ext ω
          simp only [A, zero_add]

        -- From cesaro_convergence_all_shifts with n=1: g-averages → E[g∘X 0|tail] in L¹
        have hg_cesaro : ∀ ε > 0, ∃ M_idx : ℕ, ∀ m ≥ M_idx,
            ∫ ω, |(1/(m:ℝ)) * ∑ k : Fin m, g (X (1+k) ω) -
                 μ[g ∘ X 0 | TailSigma.tailSigma X] ω| ∂μ < ε := by
          intro ε hε
          exact cesaro_convergence_all_shifts X hX_contract hX_meas g hg_meas hg_bdd 1 ε hε

        -- Reindex: X(1+k) = X(k.val+1) for k : Fin m
        have hg_cesaro' : ∀ ε > 0, ∃ M_idx : ℕ, ∀ m ≥ M_idx,
            ∫ ω, |(1/(m:ℝ)) * ∑ k : Fin m, g (X (k.val+1) ω) -
                 μ[g ∘ X 0 | TailSigma.tailSigma X] ω| ∂μ < ε := by
          intro ε hε
          obtain ⟨M_idx, hM_idx⟩ := hg_cesaro ε hε
          use M_idx
          intro m hm
          convert hM_idx m hm using 3
          ext k
          ring_nf

        -- Since α_g =ᵐ E[g∘X 0|tail], we have ∫ |α_g - E[g∘X 0|tail]| = 0
        have hα_g_diff_zero : ∫ ω, |α_g ω - μ[g ∘ X 0 | TailSigma.tailSigma X] ω| ∂μ = 0 := by
          have h_ae := hα_g_eq
          rw [integral_eq_zero_iff_of_nonneg_ae (ae_of_all μ (fun _ => abs_nonneg _))]
          · filter_upwards [h_ae] with ω hω
            simp only [hω, sub_self, abs_zero]
          · -- Integrability: α_g - condExp is in L¹
            have hα_g_int : Integrable α_g μ := hα_g_L2.integrable one_le_two
            have hcond_int : Integrable (μ[g ∘ X 0 | TailSigma.tailSigma X]) μ :=
              integrable_condExp
            exact (hα_g_int.sub hcond_int).norm

        -- Triangle inequality: g-averages → α_g in L¹
        have hg_to_alpha_g : ∀ ε > 0, ∃ M_idx : ℕ, ∀ m ≥ M_idx,
            ∫ ω, |(1/(m:ℝ)) * ∑ k : Fin m, g (X (k.val+1) ω) - α_g ω| ∂μ < ε := by
          intro ε hε
          obtain ⟨M_idx, hM_idx⟩ := hg_cesaro' ε hε
          use M_idx
          intro m hm
          calc ∫ ω, |(1/(m:ℝ)) * ∑ k : Fin m, g (X (k.val+1) ω) - α_g ω| ∂μ
              ≤ ∫ ω, (|(1/(m:ℝ)) * ∑ k : Fin m, g (X (k.val+1) ω) -
                      μ[g ∘ X 0 | TailSigma.tailSigma X] ω| +
                     |μ[g ∘ X 0 | TailSigma.tailSigma X] ω - α_g ω|) ∂μ := by
                  apply integral_mono_of_nonneg (ae_of_all μ (fun _ => abs_nonneg _))
                  · apply Integrable.add
                    · have hg_avg_meas : Measurable (fun ω => (1/(m:ℝ)) * ∑ k : Fin m, g (X (k.val+1) ω)) := by
                        apply Measurable.const_mul
                        apply Finset.measurable_sum
                        intro k _
                        exact hg_meas.comp (hX_meas (k.val + 1))
                      have hg_avg_bdd : ∀ ω, |(1/(m:ℝ)) * ∑ k : Fin m, g (X (k.val+1) ω)| ≤ 1 := by
                        intro ω
                        by_cases hm : m = 0
                        · simp [hm]
                        · calc |(1/(m:ℝ)) * ∑ k : Fin m, g (X (k.val+1) ω)|
                              ≤ (m:ℝ)⁻¹ * ∑ k : Fin m, |g (X (k.val+1) ω)| := by
                                rw [one_div, abs_mul, abs_of_pos (by positivity : (m:ℝ)⁻¹ > 0)]
                                gcongr; exact Finset.abs_sum_le_sum_abs _ _
                            _ ≤ (m:ℝ)⁻¹ * ∑ k : Fin m, (1:ℝ) := by
                                gcongr with k _; exact hg_bdd _
                            _ = 1 := by simp [Finset.sum_const, Finset.card_fin]; field_simp [hm]
                      refine (Integrable.of_bound hg_avg_meas 1 (ae_of_all μ hg_avg_bdd)).sub integrable_condExp |>.norm
                    · refine (integrable_condExp.sub (hα_g_L2.integrable one_le_two)).norm
                  · apply ae_of_all μ
                    intro ω
                    calc |(1/(m:ℝ)) * ∑ k : Fin m, g (X (k.val+1) ω) - α_g ω|
                        = |((1/(m:ℝ)) * ∑ k : Fin m, g (X (k.val+1) ω) -
                            μ[g ∘ X 0 | TailSigma.tailSigma X] ω) +
                           (μ[g ∘ X 0 | TailSigma.tailSigma X] ω - α_g ω)| := by ring_nf
                      _ ≤ _ := abs_add _ _
            _ = ∫ ω, |(1/(m:ℝ)) * ∑ k : Fin m, g (X (k.val+1) ω) -
                      μ[g ∘ X 0 | TailSigma.tailSigma X] ω| ∂μ +
                ∫ ω, |μ[g ∘ X 0 | TailSigma.tailSigma X] ω - α_g ω| ∂μ := by
                  apply integral_add
                  · have hg_avg_meas : Measurable (fun ω => (1/(m:ℝ)) * ∑ k : Fin m, g (X (k.val+1) ω)) := by
                      apply Measurable.const_mul
                      apply Finset.measurable_sum
                      intro k _
                      exact hg_meas.comp (hX_meas (k.val + 1))
                    have hg_avg_bdd : ∀ ω, |(1/(m:ℝ)) * ∑ k : Fin m, g (X (k.val+1) ω)| ≤ 1 := by
                      intro ω
                      by_cases hm : m = 0
                      · simp [hm]
                      · calc |(1/(m:ℝ)) * ∑ k : Fin m, g (X (k.val+1) ω)|
                            ≤ (m:ℝ)⁻¹ * ∑ k : Fin m, |g (X (k.val+1) ω)| := by
                              rw [one_div, abs_mul, abs_of_pos (by positivity : (m:ℝ)⁻¹ > 0)]
                              gcongr; exact Finset.abs_sum_le_sum_abs _ _
                          _ ≤ (m:ℝ)⁻¹ * ∑ k : Fin m, (1:ℝ) := by
                              gcongr with k _; exact hg_bdd _
                          _ = 1 := by simp [Finset.sum_const, Finset.card_fin]; field_simp [hm]
                    exact (Integrable.of_bound hg_avg_meas 1 (ae_of_all μ hg_avg_bdd)).sub integrable_condExp |>.norm
                  · exact (integrable_condExp.sub (hα_g_L2.integrable one_le_two)).norm
            _ = ∫ ω, |(1/(m:ℝ)) * ∑ k : Fin m, g (X (k.val+1) ω) -
                      μ[g ∘ X 0 | TailSigma.tailSigma X] ω| ∂μ + 0 := by
                  congr 1
                  convert hα_g_diff_zero using 2
                  ext ω
                  rw [abs_sub_comm]
            _ < ε := by simp; exact hM_idx m hm

        -- Scaling: f-averages = M * g-averages
        have hfg_scaling : ∀ m ω, A m ω = M * ((1/(m:ℝ)) * ∑ k : Fin m, g (X (k.val+1) ω)) := by
          intro m ω
          simp only [A, g]
          by_cases hm : m = 0
          · simp [hm]
          · rw [mul_comm M, ← mul_assoc]
            congr 1
            rw [Finset.mul_sum]
            congr 1
            ext k
            field_simp [ne_of_gt hM_pos]

        -- Therefore: A → M * α_g in L¹
        have hA_to_M_alpha_g : ∀ ε > 0, ∃ M_idx : ℕ, ∀ m ≥ M_idx,
            ∫ ω, |A m ω - M * α_g ω| ∂μ < ε := by
          intro ε hε
          have hε' : 0 < ε / (|M| + 1) := by positivity
          obtain ⟨M_idx, hM_idx⟩ := hg_to_alpha_g (ε / (|M| + 1)) hε'
          use M_idx
          intro m hm
          calc ∫ ω, |A m ω - M * α_g ω| ∂μ
              = ∫ ω, |M * ((1/(m:ℝ)) * ∑ k : Fin m, g (X (k.val+1) ω)) - M * α_g ω| ∂μ := by
                  congr 1; ext ω; rw [hfg_scaling]
            _ = ∫ ω, |M| * |(1/(m:ℝ)) * ∑ k : Fin m, g (X (k.val+1) ω) - α_g ω| ∂μ := by
                  congr 1; ext ω; rw [← mul_sub, abs_mul]
            _ = |M| * ∫ ω, |(1/(m:ℝ)) * ∑ k : Fin m, g (X (k.val+1) ω) - α_g ω| ∂μ := by
                  rw [integral_mul_left]
            _ < |M| * (ε / (|M| + 1)) := by
                  gcongr; exact hM_idx m hm
            _ < (|M| + 1) * (ε / (|M| + 1)) := by
                  gcongr; linarith
            _ = ε := by field_simp

        -- Convert to TendstoInMeasure and apply uniqueness
        -- Both A → alpha and A → M * α_g in L¹

        -- First convert L¹ convergence to eLpNorm convergence
        have hA_meas : ∀ m, Measurable (A m) := fun m => by
          apply Measurable.const_mul
          apply Finset.measurable_sum
          intro k _
          exact hf_meas.comp (hX_meas (k.val + 1))

        have hA_bdd : ∀ m ω, |A m ω| ≤ M := fun m ω => by
          simp only [A]
          by_cases hm : m = 0
          · simp [hm]; exact abs_nonneg _ |>.trans (hM 0)
          · calc |(1/(m:ℝ)) * ∑ k : Fin m, f (X (k.val+1) ω)|
                ≤ (m:ℝ)⁻¹ * ∑ k : Fin m, |f (X (k.val+1) ω)| := by
                    rw [one_div, abs_mul, abs_of_pos (by positivity : (m:ℝ)⁻¹ > 0)]
                    gcongr; exact Finset.abs_sum_le_sum_abs _ _
              _ ≤ (m:ℝ)⁻¹ * ∑ k : Fin m, M := by
                    gcongr with k _; exact hM _
              _ = M := by simp [Finset.sum_const, Finset.card_fin]; field_simp [hm]

        have hAalpha_integrable : ∀ m, Integrable (fun ω => A m ω - alpha ω) μ := fun m =>
          (Integrable.of_bound (hA_meas m) M (ae_of_all μ (hA_bdd m))).sub
            (hα_L1.integrable)

        have hAMalpha_g_integrable : ∀ m, Integrable (fun ω => A m ω - M * α_g ω) μ := fun m =>
          (Integrable.of_bound (hA_meas m) M (ae_of_all μ (hA_bdd m))).sub
            ((hα_g_L2.integrable one_le_two).const_mul M)

        have hA_tendsto_alpha : Tendsto (fun m => ∫ ω, |A m ω - alpha ω| ∂μ) atTop (𝓝 0) := by
          rw [Metric.tendsto_atTop]
          intro ε hε
          obtain ⟨M_idx, hM_idx⟩ := hA_to_alpha ε hε
          use M_idx
          intro m hm
          rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg (fun ω => abs_nonneg _))]
          exact hM_idx m hm

        have hA_tendsto_M_alpha_g : Tendsto (fun m => ∫ ω, |A m ω - M * α_g ω| ∂μ) atTop (𝓝 0) := by
          rw [Metric.tendsto_atTop]
          intro ε hε
          obtain ⟨M_idx, hM_idx⟩ := hA_to_M_alpha_g ε hε
          use M_idx
          intro m hm
          rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg (fun ω => abs_nonneg _))]
          exact hM_idx m hm

        have halpha_eLpNorm : Tendsto (fun m => eLpNorm (fun ω => A m ω - alpha ω) 1 μ) atTop (𝓝 0) := by
          rw [ENNReal.tendsto_nhds_zero]
          intro ε hε
          rw [Metric.tendsto_atTop] at hA_tendsto_alpha
          by_cases h_top : ε = ⊤
          · simp [h_top]
          · have ε_pos : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' h_top
            obtain ⟨M_idx, hM_idx⟩ := hA_tendsto_alpha ε.toReal ε_pos
            refine Filter.eventually_atTop.mpr ⟨M_idx, fun m hm => ?_⟩
            rw [Exchangeability.Probability.IntegrationHelpers.eLpNorm_one_eq_integral_abs (hAalpha_integrable m)]
            rw [← ENNReal.ofReal_toReal h_top]
            rw [ENNReal.ofReal_le_ofReal_iff ε_pos.le]
            have := hM_idx m hm
            rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg (fun ω => abs_nonneg _))] at this
            exact this.le

        have hM_alpha_g_eLpNorm : Tendsto (fun m => eLpNorm (fun ω => A m ω - M * α_g ω) 1 μ) atTop (𝓝 0) := by
          rw [ENNReal.tendsto_nhds_zero]
          intro ε hε
          rw [Metric.tendsto_atTop] at hA_tendsto_M_alpha_g
          by_cases h_top : ε = ⊤
          · simp [h_top]
          · have ε_pos : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' h_top
            obtain ⟨M_idx, hM_idx⟩ := hA_tendsto_M_alpha_g ε.toReal ε_pos
            refine Filter.eventually_atTop.mpr ⟨M_idx, fun m hm => ?_⟩
            rw [Exchangeability.Probability.IntegrationHelpers.eLpNorm_one_eq_integral_abs (hAMalpha_g_integrable m)]
            rw [← ENNReal.ofReal_toReal h_top]
            rw [ENNReal.ofReal_le_ofReal_iff ε_pos.le]
            have := hM_idx m hm
            rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg (fun ω => abs_nonneg _))] at this
            exact this.le

        -- Convert to TendstoInMeasure
        have halpha_meas_conv : TendstoInMeasure μ A atTop alpha := by
          apply tendstoInMeasure_of_tendsto_eLpNorm (p := 1) one_ne_zero
          · intro m; exact (hA_meas m).aestronglyMeasurable
          · exact hα_meas.aestronglyMeasurable
          · exact halpha_eLpNorm

        have hM_alpha_g_meas_conv : TendstoInMeasure μ A atTop (fun ω => M * α_g ω) := by
          apply tendstoInMeasure_of_tendsto_eLpNorm (p := 1) one_ne_zero
          · intro m; exact (hA_meas m).aestronglyMeasurable
          · exact aestronglyMeasurable_const.mul hα_g_L2.aestronglyMeasurable
          · exact hM_alpha_g_eLpNorm

        -- Apply uniqueness
        exact tendstoInMeasure_ae_unique halpha_meas_conv hM_alpha_g_meas_conv

      -- Step 1c: Combine: alpha =ᵐ M * α_g =ᵐ M * μ[g|tail] = μ[f|tail]
      calc alpha =ᵐ[μ] fun ω => M * α_g ω := h_alpha_eq_M_alpha_g
        _ =ᵐ[μ] fun ω => M * μ[g ∘ X 0 | TailSigma.tailSigma X] ω := by
            filter_upwards [hα_g_eq] with ω hω
            simp only [hω]
        _ =ᵐ[μ] μ[f ∘ X 0 | TailSigma.tailSigma X] := h_condExp_f_eq.symm

    -- Step 2: Combine with bridge lemma: alpha =ᵐ ∫f dν
    exact h_alpha_eq_condExp.trans h_bridge.symm

end Exchangeability.DeFinetti.ViaL2
