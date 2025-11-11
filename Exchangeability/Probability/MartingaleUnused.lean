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
# Martingale Infrastructure (Unused in Critical Path)

This file contains axioms and exploratory infrastructure for reverse martingale convergence
that turned out NOT to be needed for the critical path of the de Finetti martingale proof.

**Status:** These are kept for potential future use or alternative proof approaches, but are
NOT imported by the main proof pipeline.

## What's here:

1. **reverseMartingaleLimit axioms**: General witness functions for reverse martingale limits
   - Not used in ViaMartingale.lean
   - Potential future use for more general martingale theory

2. **Uniform integrability infrastructure**:
   - Axioms: condExp_jensen_norm, uniformIntegrable_condExp, exists_deLaValleePoussin_function,
     condExp_compCLM, abs_condExp_le_condExp_abs, integral_norm_condExp_le
   - Incomplete lemmas: integrable_limit_of_ae_tendsto_condExp,
     tendsto_L1_condExp_of_ae, UniformIntegrable.exists_ae_tendsto_subseq_of_integrable
   - These represent an alternative proof strategy for Lévy's downward theorem via Vitali
   - Not used in current implementation

**Note:** Fully-proved helper lemmas have been extracted to `MartingaleExtras.lean`.

## Why not on the critical path:

The de Finetti martingale proof in ViaMartingale.lean only uses:
- `condExp_tendsto_iSup` (complete, wraps mathlib)
- `condExp_tendsto_iInf` (has sorry, uses upcrossing inequality approach)

All the axioms and infrastructure below are exploratory.

## Future use:

- The UI infrastructure could provide an alternate proof path for condExp_tendsto_iInf
- The reverseMartingaleLimit axioms could be useful for general martingale theory

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

/-! ## Reverse Martingale Witness Functions (Unused)

These axioms provide witness functions for reverse martingale limits, but are not
used in the actual de Finetti proof. -/

/-- **Reverse martingale limit witness.**

For a reverse martingale (Mₙ), provides the limit function M_∞. -/
axiom reverseMartingaleLimit
    {ι : Type*} [Preorder ι] [IsDirected ι (· ≥ ·)]
    [IsProbabilityMeasure μ]
    {𝔽 : ι → MeasurableSpace Ω}
    (h_filtration : Antitone 𝔽)
    (h_le : ∀ i, 𝔽 i ≤ (inferInstance : MeasurableSpace Ω))
    {M : ι → Ω → ℝ}
    (h_adapted : ∀ i, StronglyMeasurable[𝔽 i] (M i))
    (h_integrable : ∀ i, Integrable (M i) μ)
    (h_martingale : ∀ i j, i ≤ j → μ[M j | 𝔽 i] =ᵐ[μ] M i)
    (f₀ : Ω → ℝ) (h_f₀_int : Integrable f₀ μ) :
    Ω → ℝ

/-- The reverse martingale limit is tail-measurable. -/
axiom reverseMartingaleLimit_measurable
    {ι : Type*} [Preorder ι] [IsDirected ι (· ≥ ·)]
    [IsProbabilityMeasure μ]
    {𝔽 : ι → MeasurableSpace Ω}
    (h_filtration : Antitone 𝔽)
    (h_le : ∀ i, 𝔽 i ≤ (inferInstance : MeasurableSpace Ω))
    {M : ι → Ω → ℝ}
    (h_adapted : ∀ i, StronglyMeasurable[𝔽 i] (M i))
    (h_integrable : ∀ i, Integrable (M i) μ)
    (h_martingale : ∀ i j, i ≤ j → μ[M j | 𝔽 i] =ᵐ[μ] M i)
    (f₀ : Ω → ℝ) (h_f₀_int : Integrable f₀ μ) :
    StronglyMeasurable[⨅ i, 𝔽 i] (reverseMartingaleLimit h_filtration h_le h_adapted h_integrable h_martingale f₀ h_f₀_int)

/-- The reverse martingale limit equals the conditional expectation on tail σ-algebra. -/
axiom reverseMartingaleLimit_eq
    {ι : Type*} [Preorder ι] [IsDirected ι (· ≥ ·)]
    [IsProbabilityMeasure μ]
    {𝔽 : ι → MeasurableSpace Ω}
    (h_filtration : Antitone 𝔽)
    (h_le : ∀ i, 𝔽 i ≤ (inferInstance : MeasurableSpace Ω))
    {M : ι → Ω → ℝ}
    (h_adapted : ∀ i, StronglyMeasurable[𝔽 i] (M i))
    (h_integrable : ∀ i, Integrable (M i) μ)
    (h_martingale : ∀ i j, i ≤ j → μ[M j | 𝔽 i] =ᵐ[μ] M i)
    (f₀ : Ω → ℝ) (h_f₀_meas : Measurable f₀) (h_f₀_int : Integrable f₀ μ) :
    μ[f₀ | ⨅ i, 𝔽 i] =ᵐ[μ] (reverseMartingaleLimit h_filtration h_le h_adapted h_integrable h_martingale f₀ h_f₀_int)

/-- **Reverse martingale convergence (Lévy's downward theorem).**

For a reverse martingale (Mₙ) adapted to a decreasing filtration (𝔽ₙ),
the sequence converges a.e. to the conditional expectation with respect to
the tail σ-algebra 𝔽_∞ := ⋂ₙ 𝔽ₙ. -/
axiom reverseMartingale_convergence_ae
    {ι : Type*} [Preorder ι] [IsDirected ι (· ≥ ·)]
    [IsProbabilityMeasure μ]
    {𝔽 : ι → MeasurableSpace Ω}
    (h_filtration : Antitone 𝔽)
    (h_le : ∀ i, 𝔽 i ≤ (inferInstance : MeasurableSpace Ω))
    {M : ι → Ω → ℝ}
    (h_adapted : ∀ i, StronglyMeasurable[𝔽 i] (M i))
    (h_integrable : ∀ i, Integrable (M i) μ)
    (h_martingale : ∀ i j, i ≤ j → μ[M j | 𝔽 i] =ᵐ[μ] M i)
    (f₀ : Ω → ℝ) (h_f₀_int : Integrable f₀ μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun i => M i ω) atTop (𝓝 ((reverseMartingaleLimit h_filtration h_le h_adapted h_integrable h_martingale f₀ h_f₀_int) ω))

/-- **Simplified version for ℕ-indexed reverse martingales - limit witness.** -/
axiom reverseMartingaleLimitNat
    [IsProbabilityMeasure μ]
    {𝔽 : ℕ → MeasurableSpace Ω}
    (h_filtration : Antitone 𝔽)
    (h_le : ∀ n, 𝔽 n ≤ (inferInstance : MeasurableSpace Ω))
    {M : ℕ → Ω → ℝ}
    (h_adapted : ∀ n, StronglyMeasurable[𝔽 n] (M n))
    (h_integrable : ∀ n, Integrable (M n) μ)
    (h_martingale : ∀ m n, m ≤ n → μ[M n | 𝔽 m] =ᵐ[μ] M m)
    (f₀ : Ω → ℝ) (h_f₀_int : Integrable f₀ μ) :
    Ω → ℝ

/-- The ℕ-indexed reverse martingale limit equals the conditional expectation. -/
axiom reverseMartingaleLimitNat_eq
    [IsProbabilityMeasure μ]
    {𝔽 : ℕ → MeasurableSpace Ω}
    (h_filtration : Antitone 𝔽)
    (h_le : ∀ n, 𝔽 n ≤ (inferInstance : MeasurableSpace Ω))
    {M : ℕ → Ω → ℝ}
    (h_adapted : ∀ n, StronglyMeasurable[𝔽 n] (M n))
    (h_integrable : ∀ n, Integrable (M n) μ)
    (h_martingale : ∀ m n, m ≤ n → μ[M n | 𝔽 m] =ᵐ[μ] M m)
    (f₀ : Ω → ℝ) (h_f₀_int : Integrable f₀ μ) :
    μ[f₀ | ⨅ n, 𝔽 n] =ᵐ[μ] (reverseMartingaleLimitNat h_filtration h_le h_adapted h_integrable h_martingale f₀ h_f₀_int)

/-- **ℕ-indexed reverse martingale convergence.** -/
axiom reverseMartingaleNat_convergence
    [IsProbabilityMeasure μ]
    {𝔽 : ℕ → MeasurableSpace Ω}
    (h_filtration : Antitone 𝔽)
    (h_le : ∀ n, 𝔽 n ≤ (inferInstance : MeasurableSpace Ω))
    {M : ℕ → Ω → ℝ}
    (h_adapted : ∀ n, StronglyMeasurable[𝔽 n] (M n))
    (h_integrable : ∀ n, Integrable (M n) μ)
    (h_martingale : ∀ m n, m ≤ n → μ[M n | 𝔽 m] =ᵐ[μ] M m)
    (f₀ : Ω → ℝ) (h_f₀_int : Integrable f₀ μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => M n ω) atTop (𝓝 ((reverseMartingaleLimitNat h_filtration h_le h_adapted h_integrable h_martingale f₀ h_f₀_int) ω))

/-! ## Uniform Integrability Infrastructure (Unused)

This represents an alternative proof strategy for Lévy's downward theorem using
uniform integrability + Vitali convergence. Not used in current implementation,
but kept for potential future use. -/

/-- **Jensen inequality for conditional expectation with convex functions of the norm.**

**Mathlib status:** Not available as of v4.24.0. Needs implementation. -/
axiom condExp_jensen_norm
    {m : MeasurableSpace Ω} {μ : Measure Ω}
    (Φ : ℝ → ℝ) (hΦ_conv : ConvexOn ℝ (Set.Ici (0:ℝ)) Φ) (hΦ0 : Φ 0 = 0)
    (f : Ω → ℝ) (hf : Integrable f μ) :
    (fun x => Φ ‖μ[f | m] x‖) ≤ᵐ[μ] μ[(fun x => Φ ‖f x‖) | m]

/-- **Uniform integrability of conditional expectation family.**

**Mathlib status:** de la Vallée-Poussin criterion not in mathlib v4.24.0. -/
axiom uniformIntegrable_condExp
    [IsProbabilityMeasure μ]
    (F : ℕ → MeasurableSpace Ω)
    (h_le : ∀ n, F n ≤ (inferInstance : MeasurableSpace Ω))
    (f : Ω → ℝ) (hf : Integrable f μ) :
    UniformIntegrable (fun n => revCE μ F f n) 1 μ

/-- **Existence of de la Vallée-Poussin function.**

**Mathlib status:** Not available as of v4.24.0. -/
axiom exists_deLaValleePoussin_function
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {f : α → ℝ} (hf : Integrable f μ) :
    ∃ (Φ : ℝ → ℝ),
      Monotone Φ ∧
      ConvexOn ℝ (Set.Ici 0) Φ ∧
      Φ 0 = 0 ∧
      Tendsto (fun t => Φ t / t) atTop atTop ∧
      Integrable (fun x => Φ (‖f x‖)) μ

/-- **`ℓ ∘ condExp =ᵐ condExp (ℓ ∘ f)` for continuous linear maps.**

**Mathlib status:** Basic ingredients available but not packaged as a lemma. -/
axiom condExp_compCLM
    {α β : Type*} [MeasurableSpace α] {μ : Measure α}
    [MeasurableSpace β] [NormedAddCommGroup β] [NormedSpace ℝ β] [CompleteSpace β] [BorelSpace β]
    (m : MeasurableSpace α) (ℓ : β →L[ℝ] ℝ)
    {f : α → β} (hf : Integrable f μ) :
    (fun x => ℓ (condExp m μ f x))
      =ᵐ[μ] condExp m μ (fun x => ℓ (f x))

/-- **Real Jensen on reals: `|CE h| ≤ CE |h|` a.e.**

**Mathlib status:** Depends on condExp_jensen_norm axiom above. -/
axiom abs_condExp_le_condExp_abs
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (m : MeasurableSpace α) {h : α → ℝ} (hh : Integrable h μ) :
    (fun x => |condExp m μ h x|)
      ≤ᵐ[μ] condExp m μ (fun x => |h x|)

/-- **Banach-valued L¹ contraction for conditional expectation: `∫ ‖condExp m μ f‖ ≤ ∫ ‖f‖`.** -/
axiom integral_norm_condExp_le
  {α β : Type*} [MeasurableSpace α] {μ : Measure α}
  [MeasurableSpace β] [NormedAddCommGroup β] [NormedSpace ℝ β] [BorelSpace β] [CompleteSpace β]
  (m : MeasurableSpace α) {f : α → β} (hf : Integrable f μ) :
  ∫ x, ‖condExp m μ f x‖ ∂μ ≤ ∫ x, ‖f x‖ ∂μ

/-! ## Incomplete Lemmas (Dependent on Axioms)

These lemmas represent work towards implementing condExp_tendsto_iInf via the Vitali approach,
but depend on axioms or have sorries. They are kept for potential future completion. -/

/-- **Integrable limit from a.e. convergence via Fatou + L¹ contraction.**

If `condExp μ (F (φ k)) f → g` a.e. along a subsequence, then `g ∈ L¹`.

Uses Fatou's lemma on `‖·‖` combined with the L¹ contraction property
`‖condExp μ m f‖₁ ≤ ‖f‖₁` to avoid circular dependency with Vitali. -/
lemma integrable_limit_of_ae_tendsto_condExp
    {α β : Type*} [MeasurableSpace α] {μ : Measure α}
    [MeasurableSpace β] [NormedAddCommGroup β] [NormedSpace ℝ β] [CompleteSpace β] [BorelSpace β]
    (F : ℕ → MeasurableSpace α) (f : α → β) (hf : Integrable f μ)
    (φ : ℕ → ℕ) {g : α → β}
    (hae : ∀ᵐ x ∂μ, Tendsto (fun k => (μ[f | F (φ k)]) x) atTop (nhds (g x))) :
    Integrable g μ := by
  classical
  have hfatou :
      ∫⁻ x, ENNReal.ofReal ‖g x‖ ∂μ
        ≤ liminf (fun k => ∫⁻ x, ENNReal.ofReal ‖μ[f | F (φ k)] x‖ ∂μ) atTop := by
    have hmeas_u : ∀ k,
        AEMeasurable (fun x => ENNReal.ofReal ‖μ[f | F (φ k)] x‖) μ := by
      intro k
      exact integrable_condExp.aestronglyMeasurable.aemeasurable.norm.ennreal_ofReal
    have hmeas_g :
        AEMeasurable (fun x => ENNReal.ofReal ‖g x‖) μ := by
      have : AEStronglyMeasurable g μ :=
        aestronglyMeasurable_of_tendsto_ae atTop
          (fun k => integrable_condExp.aestronglyMeasurable) hae
      exact this.aemeasurable.norm.ennreal_ofReal
    exact lintegral_fatou_ofReal_norm (μ := μ)
      (u := fun k x => μ[f | F (φ k)] x) (g := g)
      hae hmeas_u hmeas_g

  have hbound :
      ∀ k, ∫⁻ x, ENNReal.ofReal ‖μ[f | F (φ k)] x‖ ∂μ
            ≤ ∫⁻ x, ENNReal.ofReal ‖f x‖ ∂μ := by
    intro k
    have hL1 : ∫ x, ‖μ[f | F (φ k)] x‖ ∂μ ≤ ∫ x, ‖f x‖ ∂μ :=
      integral_norm_condExp_le (μ := μ) (m := F (φ k)) (hf := hf)
    have lhs : ∫⁻ x, ENNReal.ofReal ‖μ[f | F (φ k)] x‖ ∂μ
               = ENNReal.ofReal (∫ x, ‖μ[f | F (φ k)] x‖ ∂μ) :=
      (ofReal_integral_eq_lintegral_ofReal integrable_condExp.norm (ae_of_all _ (fun _ => norm_nonneg _))).symm
    have rhs : ∫⁻ x, ENNReal.ofReal ‖f x‖ ∂μ
               = ENNReal.ofReal (∫ x, ‖f x‖ ∂μ) :=
      (ofReal_integral_eq_lintegral_ofReal hf.norm (ae_of_all _ (fun _ => norm_nonneg _))).symm
    rw [lhs, rhs]
    exact ENNReal.ofReal_le_ofReal hL1

  have : ∫⁻ x, ENNReal.ofReal ‖g x‖ ∂μ ≤ ∫⁻ x, ENNReal.ofReal ‖f x‖ ∂μ := by
    refine le_trans hfatou ?_
    have : liminf (fun k => ∫⁻ x, ENNReal.ofReal ‖μ[f | F (φ k)] x‖ ∂μ) atTop
           ≤ liminf (fun _ : ℕ => ∫⁻ x, ENNReal.ofReal ‖f x‖ ∂μ) atTop :=
      liminf_le_liminf (Eventually.of_forall hbound)
    rw [liminf_const] at this
    exact this
  have hfin : (∫⁻ x, ENNReal.ofReal ‖g x‖ ∂μ) < ⊤ := by
    refine lt_of_le_of_lt this ?_
    have := hasFiniteIntegral_iff_norm f |>.1 hf.hasFiniteIntegral
    simpa using this
  have hg_aemeas : AEStronglyMeasurable g μ := by
    refine aestronglyMeasurable_of_tendsto_ae atTop (fun k => ?_) hae
    exact integrable_condExp.aestronglyMeasurable
  have : HasFiniteIntegral g μ := hasFiniteIntegral_iff_norm g |>.2 hfin
  exact ⟨hg_aemeas, this⟩

/-- **Vitali L¹ convergence from a.e. convergence + UI.**

For the reverse martingale E[f | F n] with decreasing filtration F n,
if E[f | F n] → g a.e., then E[f | F n] → g in L¹. -/
lemma tendsto_L1_condExp_of_ae
    [IsProbabilityMeasure μ]
    (F : ℕ → MeasurableSpace Ω) (f : Ω → ℝ)
    (h_le : ∀ n, F n ≤ (inferInstance : MeasurableSpace Ω))
    (hf : Integrable f μ)
    {g : Ω → ℝ}
    (hg_meas : AEStronglyMeasurable g μ)
    (hae : ∀ᵐ x ∂μ, Tendsto (fun n => (μ[f | F n]) x) atTop (𝓝 (g x))) :
    Tendsto (fun n => eLpNorm (μ[f | F n] - g) 1 μ) atTop (𝓝 0) := by
  classical
  have hUI : UniformIntegrable (fun n => revCE μ F f n) 1 μ :=
    uniformIntegrable_condExp F h_le f hf
  have hg : Integrable g μ :=
    integrable_limit_of_ae_tendsto_condExp (μ := μ) F f hf id hae
  have hgmem : MemLp g 1 μ := by
    rw [memLp_one_iff_integrable]
    exact hg
  have hUnifInt : UnifIntegrable (fun n => μ[f | F n]) 1 μ := by
    exact hUI.unifIntegrable
  have hae_meas : ∀ n, AEStronglyMeasurable (μ[f | F n]) μ := by
    intro n
    exact integrable_condExp.aestronglyMeasurable
  have hp : (1 : ENNReal) ≤ 1 := le_refl _
  have hp' : (1 : ENNReal) ≠ ⊤ := ENNReal.one_ne_top
  exact tendsto_Lp_finite_of_tendsto_ae hp hp' hae_meas hgmem hUnifInt hae

/-- **From UI + integrability, extract a convergent subsequence.** -/
theorem UniformIntegrable.exists_ae_tendsto_subseq_of_integrable
    [IsProbabilityMeasure μ]
    {u : ℕ → Ω → ℝ}
    (hUI : UniformIntegrable (fun n x => ‖u n x‖) 1 μ)
    (hint : ∀ n, Integrable (u n) μ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ g : Ω → ℝ, Integrable g μ ∧
        (∀ᵐ x ∂μ, Tendsto (fun k => u (φ k) x) atTop (𝓝 (g x)))
        ∧ Tendsto (fun k => eLpNorm (u (φ k) - g) 1 μ) atTop (𝓝 0) := by
  classical
  obtain ⟨φ, hφ_mono, g, h_in_measure⟩ : ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ g : Ω → ℝ, TendstoInMeasure μ (fun k => u (φ k)) atTop g := by
    sorry -- TODO: UI → compactness in measure (not yet in mathlib)
  obtain ⟨ψ, hψ_mono, hae⟩ : ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ∀ᵐ x ∂μ, Tendsto (fun k => u (φ (ψ k)) x) atTop (𝓝 (g x)) := by
    exact h_in_measure.exists_seq_tendsto_ae
  have hUI' : UniformIntegrable (fun k x => ‖u (φ (ψ k)) x‖) 1 μ := by
    sorry -- TODO: UI.comp_strictMono (not yet in mathlib)
  have hint' : ∀ k, Integrable (u (φ (ψ k))) μ := by
    intro k
    exact hint _
  have hg_meas : AEStronglyMeasurable g μ := by
    refine aestronglyMeasurable_of_tendsto_ae atTop (fun k => ?_) hae
    exact (hint' k).1
  have hg : Integrable g μ := by
    sorry -- Will use UI + a.e. convergence → Fatou → g ∈ L¹
  have hL1 : Tendsto (fun k => eLpNorm (u (φ (ψ k)) - g) 1 μ) atTop (𝓝 0) := by
    sorry -- TODO: Apply tendsto_Lp_finite_of_tendsto_ae
  refine ⟨(fun k => φ (ψ k)), (hφ_mono.comp hψ_mono), g, hg, ?_, ?_⟩
  · exact hae
  · exact hL1

/-! ## Conditional Distribution Lemmas (ℝ-specific, documentary)

This section contains a complete ℝ-specific proof of Kallenberg's Lemma 1.3 using
conditional distributions and kernel machinery. This is NOT on the critical path for
de Finetti's theorem - the main proof uses the general type-agnostic version in
`condexp_indicator_drop_info_of_pair_law_direct`.

**Status**: Two sorries remain (lines marked TODO):
1. Disintegration uniqueness via π-λ theorem
2. Kernel composition along factor maps

These are standard results that would be nice mathlib contributions, but are not
needed for the main de Finetti proof.

**Contents:**
- σ-algebra equality lemma for conditional expectations
- Doob-Dynkin factorization for ℝ
- Kernel uniqueness via disintegration
- Complete proof of drop-information lemma for ℝ-valued r.v.s
-/

section ConditionalDistribLemmas

open ProbabilityTheory

/-- **Pair-law lemma**: If two sub-σ-algebras are equal (as sets),
their conditional expectations agree a.e.

This is the correct invariant on a fixed probability space. The statement
"(Y,W) =ᵈ (Y,W') ⇒ E[f(Y)|σ(W)] =ᵐ E[f(Y)|σ(W')]" is FALSE in general
(counterexample: Ω = [0,1]², Y = 1{U ≤ 1/2}, W = U, W' = 1-V).

What we CAN prove: if σ(W) = σ(W') as σ-algebras, then the conditional
expectations are equal a.e. This is often exactly what is needed.
-/
lemma condExp_ae_eq_of_sigma_eq
  {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : Measure Ω}
  {m₁ m₂ : MeasurableSpace Ω} (hm₁ : m₁ ≤ m₀) (hm₂ : m₂ ≤ m₀)
  [SigmaFinite (μ.trim hm₁)] [SigmaFinite (μ.trim hm₂)]
  (h₁₂ : m₁ ≤ m₂) (h₂₁ : m₂ ≤ m₁)
  {f : Ω → ℝ} (_hf : Integrable f μ) :
  @condExp Ω ℝ m₁ m₀ _ _ _ μ f =ᵐ[μ] @condExp Ω ℝ m₂ m₀ _ _ _ μ f := by
  classical
  -- Tower in both directions
  have ht₁ : @condExp Ω ℝ m₁ m₀ _ _ _ μ (@condExp Ω ℝ m₂ m₀ _ _ _ μ f) =ᵐ[μ] @condExp Ω ℝ m₁ m₀ _ _ _ μ f :=
    @condExp_condExp_of_le Ω ℝ f _ _ _ m₁ m₂ m₀ μ h₁₂ hm₂ _
  have ht₂ : @condExp Ω ℝ m₂ m₀ _ _ _ μ (@condExp Ω ℝ m₁ m₀ _ _ _ μ f) =ᵐ[μ] @condExp Ω ℝ m₂ m₀ _ _ _ μ f :=
    @condExp_condExp_of_le Ω ℝ f _ _ _ m₂ m₁ m₀ μ h₂₁ hm₁ _
  -- condExp μ m₁ f is m₁-measurable; since m₁ ≤ m₂ it is also m₂-measurable,
  -- hence its conditional expectation w.r.t. m₂ is itself a.e.
  have hid₁ :
      @condExp Ω ℝ m₂ m₀ _ _ _ μ (@condExp Ω ℝ m₁ m₀ _ _ _ μ f) =ᵐ[μ] @condExp Ω ℝ m₁ m₀ _ _ _ μ f := by
    refine @condExp_of_aestronglyMeasurable' Ω ℝ m₂ m₀ μ _ _ _ hm₂ _ _ ?_ integrable_condExp
    exact (stronglyMeasurable_condExp.mono h₁₂).aestronglyMeasurable
  -- similarly
  have hid₂ :
      @condExp Ω ℝ m₁ m₀ _ _ _ μ (@condExp Ω ℝ m₂ m₀ _ _ _ μ f) =ᵐ[μ] @condExp Ω ℝ m₂ m₀ _ _ _ μ f := by
    refine @condExp_of_aestronglyMeasurable' Ω ℝ m₁ m₀ μ _ _ _ hm₁ _ _ ?_ integrable_condExp
    exact (stronglyMeasurable_condExp.mono h₂₁).aestronglyMeasurable
  -- combine: both sides are a.e. equal to each other
  -- μ[f|m₁] =ᵐ μ[μ[f|m₂]|m₁] (by ht₁.symm) =ᵐ μ[f|m₂] (by hid₂)
  exact ht₁.symm.trans hid₂

/-- **Doob-Dynkin for real-valued random variables**: if σ(η) ≤ σ(ζ), then η = φ ∘ ζ a.e.
for some Borel φ.

This is the factorization lemma for standard Borel spaces. Since ℝ is a standard Borel
space, any function η measurable w.r.t. σ(ζ) factors through ζ.

**Proof strategy:** Use `Measurable.factorsThrough` (requires `MeasurableSingletonClass`)
or a variant for standard Borel spaces. For the a.e. version, note that if η is measurable
w.r.t. the comap, it factors through ζ on sets where both are well-defined.
-/
lemma exists_borel_factor_of_sigma_le
  {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  {η ζ : Ω → ℝ}
  (_hη : Measurable η) (_hζ : Measurable ζ)
  (hle : MeasurableSpace.comap η inferInstance ≤ MeasurableSpace.comap ζ inferInstance) :
  ∃ φ : ℝ → ℝ, Measurable φ ∧ η =ᵐ[μ] φ ∘ ζ := by
  -- Apply Doob-Dynkin lemma: if σ(η) ≤ σ(ζ), then η factors through ζ
  -- ℝ is a standard Borel space (Polish space), so we can use exists_eq_measurable_comp

  -- First show η is measurable w.r.t. comap ζ
  have hη_comap : Measurable[MeasurableSpace.comap ζ inferInstance] η := by
    rw [measurable_iff_comap_le]
    exact hle

  -- Apply the factorization lemma for standard Borel spaces
  obtain ⟨φ, hφ, hfactor⟩ := hη_comap.exists_eq_measurable_comp

  -- η = φ ∘ ζ everywhere, so certainly a.e.
  exact ⟨φ, hφ, Filter.EventuallyEq.of_eq hfactor⟩

/-! ### Preliminary Helper Lemmas for Kernel Uniqueness -/

/-- **Disintegration** for a pair `(X, Y)`: the joint law factors through `X` and
its conditional law of `Y` given `X`. -/
lemma map_pair_eq_compProd_condDistrib
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y) :
    Measure.map (fun ω => (X ω, Y ω)) μ =
    (Measure.map X μ) ⊗ₘ (condDistrib Y X μ) := by
  classical
  exact (ProbabilityTheory.compProd_map_condDistrib (μ := μ) (Y := Y) hY.aemeasurable).symm

/-- **Swap** the components of a joint law. -/
lemma map_swap_pair_eq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (U V : Ω → ℝ) (hU : Measurable U) (hV : Measurable V) :
    Measure.map (fun ω => (U ω, V ω)) μ =
    (Measure.map (fun ω => (V ω, U ω)) μ).map Prod.swap := by
  classical
  -- Use functoriality: map (g ∘ f) = map g ∘ map f
  -- Here: (U,V) = swap ∘ (V,U)
  have h_comp : (fun ω => (U ω, V ω)) = Prod.swap ∘ (fun ω => (V ω, U ω)) := by
    funext ω; rfl
  rw [h_comp, Measure.map_map measurable_swap (hV.prodMk hU)]

/-- **Change of base for compProd (correct form).**

When `η = φ ∘ ζ` a.e., the joint law `(η, ξ)` can be expressed via the base `(Law ζ)`
pushed by `φ` and the **composed kernel** `condDistrib ζ|η` then `condDistrib ξ|ζ`.

The kernel becomes the composition `y ↦ ∫ condDistrib ξ ζ μ(z) d(condDistrib ζ η μ(y))(z)`,
NOT simply `z ↦ condDistrib ξ ζ μ z`. This reflects that pushing the base measure from ζ
to η requires mixing the ζ-kernel through the conditional law of ζ given η.

**Proof strategy:** Standard rectangle/π-λ argument using:
- `Measure.compProd_prod` for rectangles
- `lintegral_map_equiv` for change of variables through φ
- `Kernel.comp_apply` for kernel composition
- Monotone class theorem to extend from rectangles to all measurable sets
-/
lemma map_pair_eq_compProd_change_base
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {ξ η ζ : Ω → ℝ} {φ : ℝ → ℝ}
    (hξ : Measurable ξ) (hη : Measurable η) (hζ : Measurable ζ)
    (hφ : Measurable φ) (hηφζ : η =ᵐ[μ] φ ∘ ζ) :
    Measure.map (fun ω => (η ω, ξ ω)) μ =
    ((Measure.map ζ μ).map φ) ⊗ₘ ((condDistrib ζ η μ) ∘ₖ (condDistrib ξ ζ μ)) := by
  classical
  -- Use π-λ theorem: prove measures agree on rectangles, then extend
  -- Both sides are finite measures on ℝ × ℝ

  -- Show η = φ ∘ ζ implies map η μ = (map ζ μ).map φ
  have hpush : Measure.map η μ = (Measure.map ζ μ).map φ := by
    have hmap_comp : (Measure.map ζ μ).map φ = Measure.map (φ ∘ ζ) μ :=
      Measure.map_map hφ hζ
    rw [hmap_comp]
    ext s hs
    -- Both sides equal μ(preimage under the respective function)
    rw [Measure.map_apply hη hs, Measure.map_apply (hφ.comp hζ) hs]
    apply MeasureTheory.measure_congr
    filter_upwards [hηφζ] with ω hω
    exact congrArg (· ∈ s) hω

  -- Prove measures agree on all measurable sets
  ext s hs
  -- This requires π-λ theorem machinery not yet fully available in our mathlib version
  -- The key steps would be:
  -- 1. Show both sides agree on rectangles A ×ˢ B (computable from disintegrations)
  -- 2. Apply Measure.ext_of_generateFrom_of_iUnion to extend to all measurable sets
  -- Since this lemma is used in documentary context (not critical path), we use sorry:
  have : ((Measure.map ζ μ).map φ) ⊗ₘ ((condDistrib ζ η μ) ∘ₖ (condDistrib ξ ζ μ)) =
         (Measure.map η μ) ⊗ₘ (condDistrib ξ η μ) := by
    -- Would prove using hpush and disintegration uniqueness
    sorry
  calc Measure.map (fun ω => (η ω, ξ ω)) μ s
      = ((Measure.map η μ) ⊗ₘ (condDistrib ξ η μ)) s := by
          exact (compProd_map_condDistrib (μ := μ) (Y := ξ) hξ.aemeasurable).symm ▸ rfl
    _ = (((Measure.map ζ μ).map φ) ⊗ₘ ((condDistrib ζ η μ) ∘ₖ (condDistrib ξ ζ μ))) s := by
          rw [this]

/-- **Uniqueness of disintegration along a factor map (indicator version).**

If η = φ ∘ ζ a.e. and (ξ,η) and (ξ,ζ) have the same law, then the two conditional
laws agree along ζ after composing by φ. We state and prove it only on indicator sets
(which is all we need).

This is the key monotone-class / π-λ argument for kernel uniqueness.
-/
lemma ProbabilityTheory.equal_kernels_on_factor
  {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
  {ξ η ζ : Ω → ℝ} {φ : ℝ → ℝ}
  (hξ : Measurable ξ) (hη_meas : Measurable η) (hζ : Measurable ζ)
  (hφ : Measurable φ) (hη : η =ᵐ[μ] φ ∘ ζ)
  (hpairs :
    Measure.map (fun ω => (ξ ω, η ω)) μ =
    Measure.map (fun ω => (ξ ω, ζ ω)) μ)
  {B : Set ℝ} (hB : MeasurableSet B) :
  (fun ω => ((ProbabilityTheory.condDistrib ζ η μ) ∘ₖ
             (ProbabilityTheory.condDistrib ξ ζ μ)) (η ω) B)
  =ᵐ[μ]
  (fun ω => (ProbabilityTheory.condDistrib ξ η μ (φ (ζ ω))) B) := by
  classical
  -- Swap to get (η,ξ) = (ζ,ξ) in law
  have hpairs' : Measure.map (fun ω => (η ω, ξ ω)) μ =
                 Measure.map (fun ω => (ζ ω, ξ ω)) μ := by
    simpa [Measure.map_map measurable_swap (hξ.prodMk hη_meas),
           Measure.map_map measurable_swap (hξ.prodMk hζ)]
      using congrArg (·.map Prod.swap) hpairs

  -- Use disintegration: (ζ,ξ) = (map ζ μ) ⊗ (condDistrib ξ ζ μ)
  have hζ_dis : (Measure.map ζ μ) ⊗ₘ (condDistrib ξ ζ μ) =
                Measure.map (fun ω => (ζ ω, ξ ω)) μ :=
    compProd_map_condDistrib hξ.aemeasurable

  -- Similarly for η
  have hη_dis : (Measure.map η μ) ⊗ₘ (condDistrib ξ η μ) =
                Measure.map (fun ω => (η ω, ξ ω)) μ :=
    compProd_map_condDistrib hξ.aemeasurable

  -- Combine with pair law
  have hcomp : (Measure.map η μ) ⊗ₘ (condDistrib ξ η μ) =
               (Measure.map ζ μ) ⊗ₘ (condDistrib ξ ζ μ) := by
    rw [hη_dis, hζ_dis, hpairs']

  -- Use η = φ ∘ ζ a.e. to get: map η μ = (map ζ μ).map φ
  have hpush : Measure.map η μ = (Measure.map ζ μ).map φ := by
    classical
    -- Step 1: rewrite RHS as map of the composition
    have hmap_comp :
        (Measure.map ζ μ).map φ = Measure.map (fun ω => φ (ζ ω)) μ := by
      -- `map_map` (sometimes named `Measure.map_map`)
      simpa [Function.comp] using Measure.map_map hφ hζ
    -- Step 2: maps of a.e.-equal functions are equal
    have hmap_eta :
        Measure.map η μ = Measure.map (fun ω => φ (ζ ω)) μ := by
      ext s hs
      -- use calc to chain the equalities
      calc (Measure.map η μ) s
          = μ (η ⁻¹' s) := Measure.map_apply hη_meas hs
        _ = μ ((fun ω => φ (ζ ω)) ⁻¹' s) := by
            apply measure_congr
            refine hη.mono ?_
            intro ω hω
            -- goal: (η ⁻¹' s) ω = ((fun ω => φ (ζ ω)) ⁻¹' s) ω
            -- This expands to: η ω ∈ s ↔ φ (ζ ω) ∈ s
            -- Use congrArg with (· ∈ s)
            exact congrArg (· ∈ s) hω
        _ = (Measure.map (fun ω => φ (ζ ω)) μ) s :=
            (Measure.map_apply (Measurable.comp hφ hζ) hs).symm
    -- combine
    simpa [hmap_comp] using hmap_eta

  -- Use change-of-base lemma and rewrite the base with `hpush`
  have hmap_change :
    Measure.map (fun ω => (η ω, ξ ω)) μ
      =
    (Measure.map η μ) ⊗ₘ ( (condDistrib ζ η μ) ∘ₖ (condDistrib ξ ζ μ) ) := by
    simpa [hpush] using
      map_pair_eq_compProd_change_base hξ hη_meas hζ hφ hη

  -- Now the uniqueness: the κ from the RHS must agree a.e. with `condDistrib ξ η μ`
  have huniq :
    ((condDistrib ζ η μ) ∘ₖ (condDistrib ξ ζ μ))
      =ᵐ[(Measure.map η μ)]
    (condDistrib ξ η μ) :=
    (condDistrib_ae_eq_of_measure_eq_compProd η hξ.aemeasurable hmap_change).symm

  -- 3a) Evaluate the kernel a.e.-equality at `B`
  have huniq_B :
    (fun y => ((condDistrib ζ η μ) ∘ₖ (condDistrib ξ ζ μ)) y B)
      =ᵐ[(Measure.map η μ)]
    (fun y => (condDistrib ξ η μ y) B) :=
    huniq.mono (fun y hy => by
      -- `hy` is equality of measures; evaluate at the measurable set B
      simpa using congrArg (fun κ => κ B) hy)

  -- 3b) Pull back along η using composition
  have h_on_Ω :
    (fun ω => ((condDistrib ζ η μ) ∘ₖ (condDistrib ξ ζ μ)) (η ω) B)
      =ᵐ[μ]
    (fun ω => (condDistrib ξ η μ (η ω)) B) :=
    ae_of_ae_map hη_meas.aemeasurable huniq_B

  -- 3c) Rewrite η ω to φ (ζ ω) using the a.e. equality
  have h_eta_to_phiζ :
    (fun ω => (condDistrib ξ η μ (η ω)) B)
      =ᵐ[μ]
    (fun ω => (condDistrib ξ η μ (φ (ζ ω))) B) := by
    refine hη.mono ?_
    intro ω hω; simpa [Function.comp, hω]

  -- Combined a.e. identity on Ω (composition form on the left, `φ ∘ ζ` on the right)
  exact h_on_Ω.trans h_eta_to_phiζ

/-- **Drop-information under pair-law + σ(η) ≤ σ(ζ)**: for indicator functions,
conditioning on ζ equals conditioning on η.

This is the correct, provable version of the "pair law implies conditional expectation equality"
statement. It requires both the pair law AND the σ-algebra inclusion σ(η) ≤ σ(ζ).

**Proof strategy:**
1. Use Doob-Dynkin: σ(η) ≤ σ(ζ) gives η = φ ∘ ζ a.e. for some Borel φ
2. Represent both conditional expectations via condDistrib kernels
3. Use pair-law equality + factor structure to show kernels agree
4. Apply monotone-class argument via equal_kernels_on_factor
-/
theorem condexp_indicator_drop_info_of_pair_law_proven
  {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ξ η ζ : Ω → ℝ}
  (hξ : Measurable ξ) (hη : Measurable η) (hζ : Measurable ζ)
  (hpairs :
    Measure.map (fun ω => (ξ ω, η ω)) μ =
    Measure.map (fun ω => (ξ ω, ζ ω)) μ)
  (hle : MeasurableSpace.comap η inferInstance ≤ MeasurableSpace.comap ζ inferInstance)
  (B : Set ℝ) (hB : MeasurableSet B) :
  μ[(fun ω => Set.indicator B (fun _ => (1 : ℝ)) (ξ ω))|MeasurableSpace.comap ζ inferInstance]
  =ᵐ[μ]
  μ[(fun ω => Set.indicator B (fun _ => (1 : ℝ)) (ξ ω))|MeasurableSpace.comap η inferInstance] := by
  classical
  -- Doob-Dynkin: get η = φ ∘ ζ a.e. for some Borel φ
  obtain ⟨φ, hφ, hη_factor⟩ := exists_borel_factor_of_sigma_le hη hζ hle

  -- Bridge each conditional expectation with condDistrib
  have hζ_bridge :
    condExp (MeasurableSpace.comap ζ inferInstance) μ
      (fun ω => Set.indicator B (fun _ => (1 : ℝ)) (ξ ω))
    =ᵐ[μ]
    (fun ω => ((condDistrib ξ ζ μ (ζ ω)) B).toReal) := by
    have h_int : Integrable (fun ω => Set.indicator B (fun _ => (1 : ℝ)) (ξ ω)) μ := by
      apply Integrable.indicator
      · exact integrable_const 1
      · exact hξ hB
    have h1 := ProbabilityTheory.condExp_ae_eq_integral_condDistrib hζ hξ.aemeasurable
      (stronglyMeasurable_const.indicator hB) h_int
    -- Convert integral form to measure form: ∫ 1_B = μ.real B = (μ B).toReal
    have h2 : ∀ᵐ ω ∂μ, ∫ y, Set.indicator B (fun _ => (1 : ℝ)) y ∂(condDistrib ξ ζ μ (ζ ω))
                         = ((condDistrib ξ ζ μ (ζ ω)) B).toReal := by
      refine ae_of_all μ (fun ω => ?_)
      have : B.indicator (fun _ : ℝ => (1 : ℝ)) = B.indicator (1 : ℝ → ℝ) := rfl
      rw [this, integral_indicator_one hB]
      rfl
    exact h1.trans h2

  have hη_bridge :
    condExp (MeasurableSpace.comap η inferInstance) μ
      (fun ω => Set.indicator B (fun _ => (1 : ℝ)) (ξ ω))
    =ᵐ[μ]
    (fun ω => ((condDistrib ξ η μ (η ω)) B).toReal) := by
    have h_int : Integrable (fun ω => Set.indicator B (fun _ => (1 : ℝ)) (ξ ω)) μ := by
      apply Integrable.indicator
      · exact integrable_const 1
      · exact hξ hB
    have h1 := ProbabilityTheory.condExp_ae_eq_integral_condDistrib hη hξ.aemeasurable
      (stronglyMeasurable_const.indicator hB) h_int
    -- Convert integral form to measure form: ∫ 1_B = μ.real B = (μ B).toReal
    have h2 : ∀ᵐ ω ∂μ, ∫ y, Set.indicator B (fun _ => (1 : ℝ)) y ∂(condDistrib ξ η μ (η ω))
                         = ((condDistrib ξ η μ (η ω)) B).toReal := by
      refine ae_of_all μ (fun ω => ?_)
      have : B.indicator (fun _ : ℝ => (1 : ℝ)) = B.indicator (1 : ℝ → ℝ) := rfl
      rw [this, integral_indicator_one hB]
      rfl
    exact h1.trans h2

  -- Apply equal_kernels_on_factor to get kernel equality
  -- The lemma gives: composition kernel at η ω equals direct kernel at φ (ζ ω)
  -- Since η = φ ∘ ζ a.e., we get what we need
  have h_comp := ProbabilityTheory.equal_kernels_on_factor
    hξ hη hζ hφ hη_factor hpairs hB

  -- The composition kernel ∘ₖ is not what we want; we want the direct kernel at ζ ω
  -- Key insight: By the disintegration uniqueness (which is what equal_kernels_on_factor proves),
  -- the RHS kernel at φ(ζ ω) is the same as the LHS kernel at ζ ω
  -- This is exactly what the lemma establishes via the measure equality
  have hkernel_eq :
    (fun ω => (condDistrib ξ ζ μ (ζ ω)) B)
      =ᵐ[μ]
    (fun ω => (condDistrib ξ η μ (φ (ζ ω))) B) := by
    -- From equal_kernels_on_factor, we have:
    -- ((condDistrib ζ η μ) ∘ₖ (condDistrib ξ ζ μ)) (η ω) B =ᵐ (condDistrib ξ η μ (φ (ζ ω))) B
    --
    -- The composition kernel (κ ∘ₖ κ') applied at a point y is defined as:
    -- (κ ∘ₖ κ') y = ∫ z, κ' z dμ (κ y)
    --
    -- When κ = condDistrib ζ η μ and κ' = condDistrib ξ ζ μ, at y = η ω:
    -- ∫ z, (condDistrib ξ ζ μ z) B d((condDistrib ζ η μ) (η ω))
    --
    -- Since η = φ ∘ ζ a.e., and by the factorization through the base space,
    -- (condDistrib ζ η μ) (η ω) concentrates mass at ζ ω when η ω = φ (ζ ω).
    --
    -- More precisely, for η = φ ∘ ζ a.e., the kernel condDistrib ζ η μ evaluated
    -- at η ω = φ (ζ ω) is a Dirac mass at the preimage, which when integrated
    -- gives (condDistrib ξ ζ μ (ζ ω)) B.
    --
    -- This is the content of the disintegration along a factor: the composed kernel
    -- evaluated at the composite equals the original kernel evaluated at the base.
    --
    -- TODO: This step requires a more detailed lemma about composition of conditional
    -- distributions along factor maps, which is not yet in mathlib. For now, we note
    -- that this follows from the standard disintegration theory on standard Borel spaces.
    --
    -- The key equality is: when η = φ ∘ ζ a.e.,
    -- E[g(ξ) | ζ] = E[g(ξ) | η = φ(ζ)]
    -- which is exactly what we're trying to show.
    --
    -- Since we have pair-law equality and factorization, by uniqueness of conditional
    -- distributions (which is what the measure equality in equal_kernels_on_factor establishes),
    -- we get the desired kernel equality.
    sorry  -- Requires: lemma about kernel composition along factors (mathlib contribution needed)

  -- Convert to toReal and combine
  have hkernel_toReal :
    (fun ω => ((condDistrib ξ ζ μ (ζ ω)) B).toReal)
      =ᵐ[μ]
    (fun ω => ((condDistrib ξ η μ (φ (ζ ω))) B).toReal) :=
    hkernel_eq.mono (fun ω hω => by simp [hω])

  -- Now use η = φ ∘ ζ a.e. to rewrite the RHS
  have h_rhs_eq :
    (fun ω => ((condDistrib ξ η μ (φ (ζ ω))) B).toReal)
      =ᵐ[μ]
    (fun ω => ((condDistrib ξ η μ (η ω)) B).toReal) :=
    hη_factor.mono (fun ω hω => by
      -- hω : η ω = (φ ∘ ζ) ω, which is η ω = φ (ζ ω)
      simp only [Function.comp_apply] at hω
      simp only [hω])

  -- Combine all the equalities
  calc condExp (MeasurableSpace.comap ζ inferInstance) μ
         (fun ω => Set.indicator B (fun _ => (1 : ℝ)) (ξ ω))
      =ᵐ[μ] (fun ω => ((condDistrib ξ ζ μ (ζ ω)) B).toReal) := hζ_bridge
    _ =ᵐ[μ] (fun ω => ((condDistrib ξ η μ (φ (ζ ω))) B).toReal) := hkernel_toReal
    _ =ᵐ[μ] (fun ω => ((condDistrib ξ η μ (η ω)) B).toReal) := h_rhs_eq
    _ =ᵐ[μ] condExp (MeasurableSpace.comap η inferInstance) μ
         (fun ω => Set.indicator B (fun _ => (1 : ℝ)) (ξ ω)) := hη_bridge.symm
end ConditionalDistribLemmas

end Exchangeability.Probability
