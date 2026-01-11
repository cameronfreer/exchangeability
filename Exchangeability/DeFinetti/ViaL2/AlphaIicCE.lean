/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Exchangeability.DeFinetti.ViaL2.AlphaIic
import Exchangeability.Probability.IntegrationHelpers

/-!
# Canonical Conditional Expectation Version of Alpha_Iic

This file defines `alphaIicCE`, the canonical conditional expectation version of
the CDF-building function `alphaIic`. This is the "best" representative of the
L¹ equivalence class, with good a.e. properties.

## Main definitions

* `alphaIicCE`: Conditional expectation `E[1_{(-∞,t]}(X₀) | tail σ-algebra]`

## Main results

* `alphaIicCE_measurable`: `alphaIicCE` is measurable
* `alphaIicCE_mono`: `alphaIicCE` is monotone in t (a.e.)
* `alphaIicCE_nonneg_le_one`: `0 ≤ alphaIicCE ≤ 1` (a.e.)
* `alphaIicCE_right_continuous_at`: Right-continuity at any real t (a.e.)
* `alphaIicCE_iInf_rat_gt_eq`: Right-continuity at rationals (a.e.)

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
@[nolint unusedArguments]
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

Note: Previously had BorelSpace typeclass instance resolution issues.
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

Note: Uses dominated convergence for conditional expectations.
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

end Exchangeability.DeFinetti.ViaL2
