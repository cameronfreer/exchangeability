/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Martingale.Convergence
import Mathlib.Probability.Process.Filtration
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Exchangeability.Probability.MartingaleExtras

/-!
# Martingale Convergence for De Finetti

This file provides Lévy's upward and downward theorems needed for the martingale proof
of de Finetti's theorem.

## Main Results

- `condExp_tendsto_iSup`: Lévy upward theorem (complete - wraps mathlib)
- `condExp_tendsto_iInf`: Lévy downward theorem (to be proved)

## Implementation Status

Mathlib (as of v4.25.0-rc2) provides:
- `MeasureTheory.tendsto_ae_condExp`: Lévy's upward theorem for increasing filtrations
- No reverse martingale convergence for decreasing filtrations

This file:
- ✅ `condExp_tendsto_iSup`: Wraps mathlib's upward theorem
- ⚠️ `condExp_tendsto_iInf`: To be proved using upcrossing inequality approach

## References

* Kallenberg, *Probabilistic Symmetries and Invariance Principles* (2005), Section 1
* Durrett, *Probability: Theory and Examples* (2019), Section 5.5
* Williams, *Probability with Martingales* (1991), Theorem 12.12
-/

noncomputable section
open scoped MeasureTheory ProbabilityTheory Topology
open MeasureTheory Filter Set Function

namespace Exchangeability.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## OrderDual Infrastructure

This section shows why reindexing via OrderDual ℕ cannot convert Lévy's upward theorem
into the downward theorem. -/

/-- Package a decreasing family of σ-algebras on `ℕ` as an increasing filtration on `ℕᵒᵈ`.

For a decreasing sequence (𝔽 n) of σ-algebras, this creates an increasing filtration on
`OrderDual ℕ` where `𝔾 i := 𝔽 (ofDual i)`. Since `i ≤ j` in `ℕᵒᵈ` iff `ofDual j ≤ ofDual i`
in `ℕ`, antitonicity of 𝔽 becomes monotonicity of 𝔾. -/
def Filtration.ofAntitone (F : ℕ → MeasurableSpace Ω) (hF : Antitone F)
    (hle : ∀ n, F n ≤ (inferInstance : MeasurableSpace Ω)) :
    Filtration (OrderDual ℕ) (inferInstance : MeasurableSpace Ω) where
  seq := fun i => F (OrderDual.ofDual i)
  mono' := by
    intro i j hij
    exact hF hij
  le' := fun i => hle (OrderDual.ofDual i)

@[simp]
lemma Filtration.ofAntitone_apply (F : ℕ → MeasurableSpace Ω) (hF : Antitone F)
    (hle : ∀ n, F n ≤ (inferInstance : MeasurableSpace Ω)) (i : OrderDual ℕ) :
    (Filtration.ofAntitone F hF hle) i = F (OrderDual.ofDual i) := rfl

/-- For an antitone chain of σ-algebras, the supremum equals the first term.

**Key insight:** For an antitone sequence F : ℕ → MeasurableSpace Ω, we have
  ⨆ i : ℕᵒᵈ, F i.ofDual = F 0
because F n ≤ F 0 for all n (by antitonicity), and F 0 is one of the terms.

**Why the OrderDual approach fails:** This shows that reindexing via ℕᵒᵈ cannot turn
⨆ into ⨅. For example, if F 0 = ⊤ and F n = ⊥ for n > 0, then:
  ⨆ i, F i.ofDual = ⊤  but  ⨅ n, F n = ⊥
Therefore, applying Lévy's upward theorem to the OrderDual filtration would give
convergence to μ[f | F 0], not μ[f | ⨅ n, F n]. -/
lemma iSup_ofAntitone_eq_F0
    (F : ℕ → MeasurableSpace Ω) (hF : Antitone F) :
    (⨆ i : OrderDual ℕ, F i.ofDual) = F 0 := by
  refine le_antisymm ?_ ?_
  · refine iSup_le (fun i => ?_)
    have : (0 : ℕ) ≤ i.ofDual := Nat.zero_le _
    exact hF this
  · have : F 0 ≤ F (OrderDual.ofDual (OrderDual.toDual 0)) := le_rfl
    simpa using (le_iSup_of_le (OrderDual.toDual 0) this)

/-! ## Reverse Martingale Infrastructure

To prove Lévy's downward theorem, we reverse time on finite horizons to obtain
forward martingales, then apply the upcrossing inequality. -/

/-- Reverse filtration on a finite horizon `N`.

For an antitone filtration `𝔽`, define `𝔾ⁿ_k := 𝔽_{N-k}`. Since `k ≤ ℓ` implies
`N - ℓ ≤ N - k`, and `𝔽` is antitone, we get `𝔽_{N-k} ≤ 𝔽_{N-ℓ}`, so `𝔾ⁿ` is
a (forward) increasing filtration. -/
def revFiltration (𝔽 : ℕ → MeasurableSpace Ω) (h_antitone : Antitone 𝔽)
    (h_le : ∀ n, 𝔽 n ≤ (inferInstance : MeasurableSpace Ω))
    (N : ℕ) : Filtration ℕ (inferInstance : MeasurableSpace Ω) where
  seq := fun n => 𝔽 (N - n)
  mono' := by
    intro i j hij
    -- `i ≤ j` implies `N - j ≤ N - i`, then antitone gives `𝔽 (N - i) ≤ 𝔽 (N - j)`.
    have : N - j ≤ N - i := tsub_le_tsub_left hij N
    exact h_antitone this
  le' := fun _ => h_le _

/-- Reverse conditional expectation process at finite horizon `N`.

For `n ≤ N`, this is just `μ[f | 𝔽_{N-n}]`. -/
noncomputable def revCEFinite (f : Ω → ℝ) (𝔽 : ℕ → MeasurableSpace Ω) (N n : ℕ) : Ω → ℝ :=
  μ[f | 𝔽 (N - n)]

/-- The reversed process `revCEFinite f 𝔽 N` is a martingale w.r.t. `revFiltration 𝔽 N`.

**Proof:** For `i ≤ j`, we have `𝔽 (N - j) ≤ 𝔽 (N - i)`, so by the tower property:
  E[revCEFinite N j | revFiltration N i] = E[μ[f | 𝔽_{N-j}] | 𝔽_{N-i}] = μ[f | 𝔽_{N-i}] = revCEFinite N i
-/
lemma revCEFinite_martingale
    [IsProbabilityMeasure μ]
    (h_antitone : Antitone 𝔽) (h_le : ∀ n, 𝔽 n ≤ (inferInstance : MeasurableSpace Ω))
    (f : Ω → ℝ) (hf : Integrable f μ) (N : ℕ) :
    Martingale (fun n => revCEFinite (μ := μ) f 𝔽 N n) (revFiltration 𝔽 h_antitone h_le N) μ := by
  constructor
  · -- Adapted: revCE N n is 𝔽_{N-n}-measurable
    intro n
    exact stronglyMeasurable_condExp
  · -- Martingale property
    intro i j hij
    simp only [revCEFinite, revFiltration]
    -- Tower: E[μ[f | 𝔽_{N-j}] | 𝔽_{N-i}] = μ[f | 𝔽_{N-i}]
    -- Need: 𝔽_{N-i} ≤ 𝔽_{N-j} (since i ≤ j ⟹ N-j ≤ N-i ⟹ 𝔽(N-i) ≤ 𝔽(N-j))
    have : 𝔽 (N - i) ≤ 𝔽 (N - j) := by
      have : N - j ≤ N - i := tsub_le_tsub_left hij N
      exact h_antitone this
    exact condExp_condExp_of_le this (h_le (N - j))

/-- L¹ boundedness of conditional expectations.

This is a standard property: `‖μ[f | m]‖₁ ≤ ‖f‖₁`. -/
lemma eLpNorm_one_condExp_le_of_integrable
    {m : MeasurableSpace Ω} (f : Ω → ℝ) (hf : Integrable f μ) :
    eLpNorm (μ[f | m]) 1 μ ≤ eLpNorm f 1 μ :=
  eLpNorm_one_condExp_le_eLpNorm f

/-- Uniform (in N) bound on upcrossings for the reverse martingale.

For an L¹-bounded martingale obtained by reversing an antitone filtration, the expected
number of upcrossings is uniformly bounded, independent of the time horizon N. -/
lemma upcrossings_bdd_uniform
    [IsProbabilityMeasure μ]
    (h_antitone : Antitone 𝔽) (h_le : ∀ n, 𝔽 n ≤ (inferInstance : MeasurableSpace Ω))
    (f : Ω → ℝ) (hf : Integrable f μ) (a b : ℝ) (hab : a < b) :
    ∃ C : ENNReal, ∀ N,
      ∫⁻ ω, (upcrossings (↑a) (↑b) (fun n => revCEFinite (μ := μ) f 𝔽 N n) ω) ∂μ ≤ C := by
  sorry

/-- A.S. existence of the limit of `μ[f | 𝔽 n]` along an antitone filtration.

This uses the upcrossing inequality applied to the time-reversed martingales to show
that the original sequence has finitely many upcrossings and downcrossings a.e.,
hence converges a.e. -/
lemma condExp_exists_ae_limit_antitone
    [IsProbabilityMeasure μ] {𝔽 : ℕ → MeasurableSpace Ω}
    (h_antitone : Antitone 𝔽) (h_le : ∀ n, 𝔽 n ≤ (inferInstance : MeasurableSpace Ω))
    (f : Ω → ℝ) (hf : Integrable f μ) :
    ∃ Xlim, (Integrable Xlim μ ∧
           ∀ᵐ ω ∂μ, Tendsto (fun n => μ[f | 𝔽 n] ω) atTop (𝓝 (Xlim ω))) := by
  -- Strategy: Show the sequence has finite upcrossings a.e., then apply tendsto_of_uncrossing_lt_top

  -- First, extract the L¹ bound
  have hL1_bdd : ∀ n, eLpNorm (μ[f | 𝔽 n]) 1 μ ≤ eLpNorm f 1 μ :=
    fun n => eLpNorm_one_condExp_le_eLpNorm _

  -- Extract finite L¹ bound
  have hf_memLp : MemLp f 1 μ := memLp_one_iff_integrable.2 hf
  have hf_Lp_ne_top : eLpNorm f 1 μ ≠ ⊤ := hf_memLp.eLpNorm_ne_top
  set R := (eLpNorm f 1 μ).toNNReal with hR_def
  have hR : eLpNorm f 1 μ = ↑R := (ENNReal.coe_toNNReal hf_Lp_ne_top).symm

  -- Step 1: Show bounded liminf
  have hbdd_liminf : ∀ᵐ ω ∂μ, (liminf (fun n => ENorm.enorm (μ[f | 𝔽 n] ω)) atTop) < ⊤ := by
    refine ae_bdd_liminf_atTop_of_eLpNorm_bdd (R := R) one_ne_zero (fun n => ?_) (fun n => ?_)
    · -- Measurability
      exact stronglyMeasurable_condExp.measurable.mono (h_le n) le_rfl
    · -- Bound
      calc eLpNorm (μ[f | 𝔽 n]) 1 μ
          ≤ eLpNorm f 1 μ := hL1_bdd n
        _ = R := hR

  -- Step 2: Show finite upcrossings using L¹-boundedness
  -- Strategy: Use the fact that L¹-bounded sequences with reverse martingale structure
  -- have finite upcrossings. This follows from the upcrossing inequality.
  have hupcross : ∀ᵐ ω ∂μ, ∀ a b : ℚ, a < b →
      upcrossings (↑a) (↑b) (fun n => μ[f | 𝔽 n]) ω < ⊤ := by
    -- The sequence is L¹-bounded, so we can extract a uniform bound
    obtain ⟨R, hR_pos, hR_bound⟩ : ∃ R : ENNReal, 0 < R ∧ ∀ n, eLpNorm (μ[f | 𝔽 n]) 1 μ ≤ R := by
      use max (eLpNorm f 1 μ) 1
      refine ⟨?_, ?_⟩
      · exact lt_max_of_lt_right zero_lt_one
      · intro n
        exact le_trans (hL1_bdd n) (le_max_left _ _)

    -- For reverse martingales, we use a key observation:
    -- The sequence μ[f | 𝔽 n] is L¹-bounded and satisfies the tower property
    -- in the reverse direction, which is sufficient to guarantee a.e. convergence
    -- by the reverse martingale convergence theorem.

    -- Key insight: For a reverse martingale with L¹ bound R, the expected number
    -- of upcrossings is bounded by R/(b-a), which is finite. By Markov's inequality,
    -- this implies a.e. finiteness.

    simp only [ae_all_iff, eventually_imp_distrib_left]
    intro a b hab

    -- Core argument: L¹-bounded sequences with reverse martingale property have finite upcrossings
    -- This follows from the reverse martingale convergence theorem

    -- The proof would construct, for each N, a time-reversed martingale:
    -- Y^N_k := μ[f | 𝔽_{N ⊓ (N - k)}] with increasing filtration G^N_k := 𝔽_{N ⊓ (N - k)}
    -- Then Y^N is a forward martingale, so by Submartingale.upcrossings_ae_lt_top,
    -- upcrossings of Y^N are a.e. finite with bound independent of N.
    -- Taking N → ∞, the upcrossings of the original sequence are also a.e. finite.

    -- For now, we use a classical result:
    -- A reverse martingale that is L¹-bounded has finite upcrossings a.e.
    -- This is the time-reversed version of the forward martingale convergence theorem.

    -- Get uniform bound on expected upcrossings from time-reversed martingales
    have hab' : (↑a : ℝ) < (↑b : ℝ) := Rat.cast_lt.2 hab
    obtain ⟨C, hC⟩ := upcrossings_bdd_uniform h_antitone h_le f hf (↑a) (↑b) hab'
    sorry

  -- Step 3: Apply convergence theorem to get pointwise limits
  have h_ae_conv : ∀ᵐ ω ∂μ, ∃ c, Tendsto (fun n => μ[f | 𝔽 n] ω) atTop (𝓝 c) := by
    filter_upwards [hbdd_liminf, hupcross] with ω hω₁ hω₂
    -- Convert enorm bound to nnnorm bound (they're equal via coercion)
    have hω₁' : (liminf (fun n => ENNReal.ofNNReal (nnnorm (μ[f | 𝔽 n] ω))) atTop) < ⊤ := by
      convert hω₁ using 2  -- ENorm.enorm x = ↑(nnnorm x)
    exact tendsto_of_uncrossing_lt_top hω₁' hω₂

  -- Step 4: Define the limit function using classical choice
  classical
  let Xlim : Ω → ℝ := fun ω =>
    if h : ∃ c, Tendsto (fun n => μ[f | 𝔽 n] ω) atTop (𝓝 c)
    then Classical.choose h
    else 0

  -- Step 5: Show Xlim has the desired properties
  use Xlim
  constructor

  · -- Integrability of Xlim (follows from Fatou + L¹ boundedness)
    -- Xlim is a.e. limit of integrable functions with uniform L¹ bound
    have hXlim_ae_meas : AEStronglyMeasurable Xlim μ := by
      apply aestronglyMeasurable_of_tendsto_ae atTop (f := fun n => μ[f | 𝔽 n])
      · intro n; exact stronglyMeasurable_condExp.aestronglyMeasurable
      · filter_upwards [h_ae_conv] with ω hω
        simp only [Xlim]
        rw [dif_pos hω]
        exact Classical.choose_spec hω

    -- By Fatou: ‖Xlim‖₁ ≤ liminf ‖μ[f | 𝔽 n]‖₁ ≤ ‖f‖₁ < ∞
    have hXlim_norm : HasFiniteIntegral Xlim μ := by
      rw [hasFiniteIntegral_iff_norm]
      -- Apply Fatou for ofReal ‖·‖
      have h_ae_tendsto : ∀ᵐ ω ∂μ, Tendsto (fun n => μ[f | 𝔽 n] ω) atTop (𝓝 (Xlim ω)) := by
        filter_upwards [h_ae_conv] with ω hω
        simp only [Xlim]
        rw [dif_pos hω]
        exact Classical.choose_spec hω
      -- Measurability proofs (separated to avoid timeout)
      have hmeas_n : ∀ n, AEMeasurable (fun ω => ENNReal.ofReal ‖μ[f | 𝔽 n] ω‖) μ := fun n =>
        ((stronglyMeasurable_condExp (f := f) (m := 𝔽 n) (μ := μ)).mono (h_le n)).norm.measurable.ennreal_ofReal.aemeasurable
      have hmeas_lim : AEMeasurable (fun ω => ENNReal.ofReal ‖Xlim ω‖) μ :=
        hXlim_ae_meas.norm.aemeasurable.ennreal_ofReal
      calc
        ∫⁻ ω, ENNReal.ofReal ‖Xlim ω‖ ∂μ
            ≤ liminf (fun n => ∫⁻ ω, ENNReal.ofReal ‖μ[f | 𝔽 n] ω‖ ∂μ) atTop :=
              lintegral_fatou_ofReal_norm h_ae_tendsto hmeas_n hmeas_lim
        _ ≤ ↑R := by
              simp only [liminf_le_iff]
              intro b hb
              simp only [eventually_atTop, ge_iff_le]
              use 0
              intro n _
              rw [← hR, ← eLpNorm_one_eq_lintegral_nnnorm]
              exact hL1_bdd n
        _ < ⊤ := ENNReal.coe_lt_top

    exact ⟨hXlim_ae_meas, hXlim_norm⟩

  · -- A.e. convergence to Xlim
    filter_upwards [h_ae_conv] with ω hω
    simp only [Xlim]
    rw [dif_pos hω]
    exact Classical.choose_spec hω

/-- Uniform integrability of `{μ[f | 𝔽 n]}ₙ` for antitone filtration.

This is a direct application of mathlib's `Integrable.uniformIntegrable_condExp`,
which works for any family of sub-σ-algebras (not just filtrations). -/
lemma uniformIntegrable_condexp_antitone
    [IsProbabilityMeasure μ] {𝔽 : ℕ → MeasurableSpace Ω}
    (h_antitone : Antitone 𝔽) (h_le : ∀ n, 𝔽 n ≤ (inferInstance : MeasurableSpace Ω))
    (f : Ω → ℝ) (hf : Integrable f μ) :
    UniformIntegrable (fun n => μ[f | 𝔽 n]) 1 μ :=
  hf.uniformIntegrable_condExp h_le

/-- Identification: the a.s. limit equals `μ[f | ⨅ n, 𝔽 n]`.

Uses uniform integrability to pass from a.e. convergence to L¹ convergence,
then uses L¹-continuity of conditional expectation to identify the limit. -/
lemma ae_limit_is_condexp_iInf
    [IsProbabilityMeasure μ] {𝔽 : ℕ → MeasurableSpace Ω}
    (h_antitone : Antitone 𝔽) (h_le : ∀ n, 𝔽 n ≤ (inferInstance : MeasurableSpace Ω))
    (f : Ω → ℝ) (hf : Integrable f μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => μ[f | 𝔽 n] ω) atTop (𝓝 (μ[f | ⨅ n, 𝔽 n] ω)) := by
  classical
  -- 1) Get a.s. limit Xlim
  obtain ⟨Xlim, hXlimint, h_tendsto⟩ :=
    condExp_exists_ae_limit_antitone (μ := μ) h_antitone h_le f hf

  -- 2) UI ⟹ L¹ convergence via Vitali
  have hUI := uniformIntegrable_condexp_antitone (μ := μ) h_antitone h_le f hf

  have hL1_conv : Tendsto (fun n => eLpNorm (μ[f | 𝔽 n] - Xlim) 1 μ) atTop (𝓝 0) := by
    apply tendsto_Lp_finite_of_tendsto_ae (hp := le_refl 1) (hp' := ENNReal.one_ne_top)
    · intro n; exact integrable_condExp.aestronglyMeasurable
    · exact memLp_one_iff_integrable.2 hXlimint
    · exact hUI.unifIntegrable
    · exact h_tendsto

  -- 3) Pass limit through condExp at F_inf := ⨅ n, 𝔽 n
  set F_inf := iInf 𝔽 with hF_inf_def

  -- Tower property: For every n, μ[μ[f | 𝔽 n] | F_inf] = μ[f | F_inf]
  have h_tower : ∀ n, μ[μ[f | 𝔽 n] | F_inf] =ᵐ[μ] μ[f | F_inf] := by
    intro n
    have : F_inf ≤ 𝔽 n := iInf_le 𝔽 n
    exact condExp_condExp_of_le this (h_le n)

  -- Xlim is F_inf-strongly measurable as the limit of F_inf-measurable functions
  -- Each μ[f | 𝔽 n] is 𝔽 n-measurable, hence F_inf-measurable (since F_inf ≤ 𝔽 n)
  have hXlim_meas : @StronglyMeasurable Ω ℝ _ F_inf Xlim := by
    sorry
    -- TODO: Deep type system challenge with sub-σ-algebras
    -- Mathematical strategy (CORRECT):
    -- 1. Each μ[f | 𝔽 n] is 𝔽 n-strongly measurable (by stronglyMeasurable_condExp)
    -- 2. Since F_inf = ⨅ n, 𝔽 n ≤ 𝔽 n, lift via .mono to get F_inf-measurability
    -- 3. Xlim is a.e. limit, so a.e. F_inf-measurable (by aestronglyMeasurable_of_tendsto_ae)
    -- 4. Extract strongly measurable version via .stronglyMeasurable_mk
    --
    -- Issue: aestronglyMeasurable_of_tendsto_ae requires all functions measurable w.r.t.
    -- the *same* σ-algebra, but @ notation with sub-σ-algebras has complex type inference.
    -- The reference implementation in /tmp/fixed_section.txt (lines 17-27) works, but
    -- requires exact matching of implicit parameter patterns.

  -- Since Xlim is F_inf-measurable and integrable, μ[Xlim | F_inf] = Xlim
  have hF_inf_le : F_inf ≤ _ := le_trans (iInf_le 𝔽 0) (h_le 0)
  have hXlim_condExp : μ[Xlim | F_inf] =ᵐ[μ] Xlim := by
    -- Apply condExp_of_stronglyMeasurable: if f is m-measurable and integrable, then μ[f|m] = f
    have : μ[Xlim | F_inf] = Xlim := condExp_of_stronglyMeasurable hF_inf_le hXlim_meas hXlimint
    rw [this]

  -- Final identification: Xlim = μ[f | F_inf]
  -- Strategy: Use L¹-continuity of condExp

  -- For each n: μ[μ[f | 𝔽 n] | F_inf] - μ[Xlim | F_inf] = μ[f | F_inf] - Xlim (by tower and hXlim_condExp)
  have h_diff : ∀ n, μ[μ[f | 𝔽 n] | F_inf] - μ[Xlim | F_inf] =ᵐ[μ] μ[f | F_inf] - Xlim := by
    intro n
    filter_upwards [h_tower n, hXlim_condExp] with ω hn hω
    simp [hn, hω]

  -- By linearity of condExp: μ[μ[f | 𝔽 n] | F_inf] - μ[Xlim | F_inf] = μ[(μ[f | 𝔽 n] - Xlim) | F_inf]
  have h_lin : ∀ n, μ[(μ[f | 𝔽 n] - Xlim) | F_inf] =ᵐ[μ] μ[μ[f | 𝔽 n] | F_inf] - μ[Xlim | F_inf] := by
    intro n
    exact condExp_sub integrable_condExp hXlimint F_inf

  -- By L¹-contraction: ‖μ[(μ[f | 𝔽 n] - Xlim) | F_inf]‖₁ ≤ ‖μ[f | 𝔽 n] - Xlim‖₁ → 0
  have h_contract : Tendsto (fun n => eLpNorm (μ[(μ[f | 𝔽 n] - Xlim) | F_inf]) 1 μ) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hL1_conv
    · intro n; exact zero_le _
    · intro n
      calc eLpNorm (μ[(μ[f | 𝔽 n] - Xlim) | F_inf]) 1 μ
          ≤ eLpNorm (μ[f | 𝔽 n] - Xlim) 1 μ := eLpNorm_one_condExp_le_eLpNorm _

  -- So μ[f | F_inf] - Xlim → 0 in L¹
  have h_lim : eLpNorm (μ[f | F_inf] - Xlim) 1 μ = 0 := by
    -- The sequence eLpNorm μ[(μ[f | 𝔽 n] - Xlim) | F_inf] 1 μ converges to 0
    -- But by h_diff and h_lin, this equals eLpNorm (μ[f | F_inf] - Xlim) 1 μ for all n
    -- So the constant sequence converges to 0, hence the constant is 0
    have h_const_tendsto : Tendsto (fun n => eLpNorm (μ[f | F_inf] - Xlim) 1 μ) atTop (𝓝 0) := by
      have : ∀ n, μ[f | F_inf] - Xlim =ᵐ[μ] μ[(μ[f | 𝔽 n] - Xlim) | F_inf] := by
        intro n
        filter_upwards [h_diff n, h_lin n] with ω hd hl
        rw [← hd, ← hl]
      refine Tendsto.congr (fun n => (eLpNorm_congr_ae (this n)).symm) h_contract
    exact tendsto_nhds_unique h_const_tendsto tendsto_const_nhds

  -- Therefore μ[f | F_inf] = Xlim a.e.
  have hXlim_eq : μ[f | F_inf] =ᵐ[μ] Xlim := by
    have : eLpNorm (μ[f | F_inf] - Xlim) 1 μ = 0 := h_lim
    rw [eLpNorm_eq_zero_iff (integrable_condExp.sub hXlimint).aestronglyMeasurable one_ne_zero] at this
    exact this.symm

  -- Return the desired result: combine h_tendsto with hXlim_eq
  filter_upwards [h_tendsto, hXlim_eq] with ω h_tend h_eq
  rwa [← h_eq]

/-! ## Main Theorems

The two key results: Lévy's upward and downward theorems for conditional expectations. -/

/-- **Conditional expectation converges along decreasing filtration (Lévy's downward theorem).**

For a decreasing filtration 𝔽ₙ and integrable f, the sequence
  Mₙ := E[f | 𝔽ₙ]
converges a.s. to E[f | ⨅ₙ 𝔽ₙ].

**Proof strategy:** Use the upcrossing inequality approach:
1. Define upcrossings for interval [a,b]
2. Prove upcrossing inequality: E[# upcrossings] ≤ E[|X₀ - a|] / (b - a)
3. Show: finitely many upcrossings a.e. for all rational [a,b]
4. Deduce: the sequence {E[f | 𝔽 n]} converges a.e.
5. Identify the limit as E[f | ⨅ 𝔽 n] using tower property

**Why not use OrderDual reindexing?** See `iSup_ofAntitone_eq_F0`: for antitone F,
we have ⨆ i, F i.ofDual = F 0, not ⨅ n, F n. Applying Lévy's upward theorem would
give convergence to the wrong limit. -/
theorem condExp_tendsto_iInf
    [IsProbabilityMeasure μ]
    {𝔽 : ℕ → MeasurableSpace Ω}
    (h_filtration : Antitone 𝔽)
    (h_le : ∀ n, 𝔽 n ≤ (inferInstance : MeasurableSpace Ω))
    (f : Ω → ℝ) (h_f_int : Integrable f μ) :
    ∀ᵐ ω ∂μ, Tendsto
      (fun n => μ[f | 𝔽 n] ω)
      atTop
      (𝓝 (μ[f | ⨅ n, 𝔽 n] ω)) :=
  ae_limit_is_condexp_iInf h_filtration h_le f h_f_int

/-- **Conditional expectation converges along increasing filtration (Lévy's upward theorem).**

For an increasing filtration 𝔽ₙ and integrable f, the sequence
  Mₙ := E[f | 𝔽ₙ]
converges a.s. to E[f | ⨆ₙ 𝔽ₙ].

**Implementation:** Direct wrapper around mathlib's `MeasureTheory.tendsto_ae_condExp`
from `Mathlib.Probability.Martingale.Convergence`. -/
theorem condExp_tendsto_iSup
    [IsProbabilityMeasure μ]
    {𝔽 : ℕ → MeasurableSpace Ω}
    (h_filtration : Monotone 𝔽)
    (h_le : ∀ n, 𝔽 n ≤ (inferInstance : MeasurableSpace Ω))
    (f : Ω → ℝ) (h_f_int : Integrable f μ) :
    ∀ᵐ ω ∂μ, Tendsto
      (fun n => μ[f | 𝔽 n] ω)
      atTop
      (𝓝 (μ[f | ⨆ n, 𝔽 n] ω)) := by
  classical
  -- Package 𝔽 as a Filtration
  let ℱ : Filtration ℕ (inferInstance : MeasurableSpace Ω) :=
    { seq   := 𝔽
      mono' := h_filtration
      le'   := h_le }
  -- Apply mathlib's Lévy upward theorem
  exact MeasureTheory.tendsto_ae_condExp (μ := μ) (ℱ := ℱ) f

/-! ## Implementation Notes

**Current Status:**

- ✅ `condExp_tendsto_iSup` (Lévy upward): Complete wrapper around mathlib
- 🚧 `condExp_tendsto_iInf` (Lévy downward): Structure in place, 3 sorries remain

**Proof structure for downward theorem:**

1. ✅ `revFiltration`, `revCE`: Time-reversal infrastructure for finite horizons
2. ✅ `revCE_martingale`: Reversed process is a forward martingale
3. 🚧 `condExp_exists_ae_limit_antitone`: A.S. existence via upcrossing bounds
4. 🚧 `uniformIntegrable_condexp_antitone`: UI via de la Vallée-Poussin
5. 🚧 `ae_limit_is_condexp_iInf`: Limit identification via Vitali + tower
6. ✅ `condExp_tendsto_iInf`: Main theorem (wraps step 5)

**Remaining work (3 sorries):**
- Upcrossing bounds for reverse martingales (step 3)
- de la Vallée-Poussin + Jensen for UI (step 4)
- Vitali convergence + limit identification (step 5)

See `PROOF_PLAN_condExp_tendsto_iInf.md` for detailed mathematical strategy.

**Dependencies from Mathlib:**
- ✅ `MeasureTheory.tendsto_ae_condExp`: Lévy upward (used)
- ✅ `Filtration`: Filtration structure (used)
- ✅ `condExp_condExp_of_le`: Tower property (used)
- ❌ Reverse martingale convergence: Not available (proving it here)
- TODO: Upcrossing inequality, Vitali convergence, de la Vallée-Poussin -/

end Exchangeability.Probability
