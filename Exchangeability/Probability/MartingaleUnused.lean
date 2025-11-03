/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Martingale.Convergence
import Mathlib.Probability.Process.Filtration
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

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

2. **Helper definitions**: revCE, revCE_tower, revCE_L1_bdd
   - Support the unused reverseMartingaleLimit axioms
   - Specific to reverse martingale sequences

3. **Uniform integrability infrastructure**:
   - Axioms: condExp_jensen_norm, uniformIntegrable_condExp, exists_deLaValleePoussin_function,
     condExp_compCLM, abs_condExp_le_condExp_abs, integral_norm_condExp_le
   - Complete lemmas: lintegral_fatou_ofReal_norm, integrable_limit_of_ae_tendsto_condExp,
     tendsto_L1_condExp_of_ae, UniformIntegrable.exists_ae_tendsto_subseq_of_integrable
   - These represent an alternative proof strategy for Lévy's downward theorem via Vitali
   - Not used in current implementation

## Why not on the critical path:

The de Finetti martingale proof in ViaMartingale.lean only uses:
- `condExp_tendsto_iSup` (complete, wraps mathlib)
- `condExp_tendsto_iInf` (has sorry, uses upcrossing inequality approach)

All the axioms and infrastructure below are exploratory.

## Future use:

- The UI infrastructure could provide an alternate proof path for condExp_tendsto_iInf
- The reverseMartingaleLimit axioms could be useful for general martingale theory
- Some complete lemmas (like integrable_limit_of_ae_tendsto_condExp) are reusable

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

/-! ## Helper Definitions (Unused)

These support the unused reverseMartingaleLimit axioms above. -/

/-- Reverse martingale along a decreasing chain: `X n := condExp μ (F n) f`. -/
def revCE (μ : Measure Ω) (F : ℕ → MeasurableSpace Ω) (f : Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  μ[f | F n]

/-- Tower property in the reverse direction: for `m ≥ n`, `E[X_n | F_m] = X_m`. -/
lemma revCE_tower
    [IsProbabilityMeasure μ]
    {F : ℕ → MeasurableSpace Ω} (hF : Antitone F)
    (h_le : ∀ n, F n ≤ (inferInstance : MeasurableSpace Ω))
    (f : Ω → ℝ) {n m : ℕ} (hmn : n ≤ m) :
    μ[revCE μ F f n | F m] =ᵐ[μ] revCE μ F f m := by
  simp only [revCE]
  exact condExp_condExp_of_le (hF hmn) (h_le n)

/-- L¹ boundedness of the reverse martingale. -/
lemma revCE_L1_bdd
    [IsProbabilityMeasure μ]
    {F : ℕ → MeasurableSpace Ω}
    (h_le : ∀ n, F n ≤ (inferInstance : MeasurableSpace Ω))
    (f : Ω → ℝ) (hf : Integrable f μ) :
    ∀ n, eLpNorm (revCE μ F f n) 1 μ ≤ eLpNorm f 1 μ := by
  intro n
  simp only [revCE]
  exact eLpNorm_one_condExp_le_eLpNorm f

/-! ## Uniform Integrability Infrastructure (Unused)

This represents an alternative proof strategy for Lévy's downward theorem using
uniform integrability + Vitali convergence. Not used in current implementation,
but kept for potential future use. -/

/-- From the de la Vallée-Poussin tail condition `Φ(t)/t → ∞`, extract a threshold `R > 0`
such that `t ≤ Φ t` for all `t ≥ R`. -/
lemma deLaValleePoussin_eventually_ge_id
    (Φ : ℝ → ℝ)
    (hΦ_tail : Tendsto (fun t : ℝ => Φ t / t) atTop atTop) :
    ∃ R > 0, ∀ ⦃t⦄, t ≥ R → t ≤ Φ t := by
  have h := (tendsto_atTop_atTop.1 hΦ_tail) 1
  rcases h with ⟨R, hR⟩
  refine ⟨max R 1, by positivity, ?_⟩
  intro t ht
  have ht' : t ≥ R := le_trans (le_max_left _ _) ht
  have hΦ_ge : Φ t / t ≥ 1 := hR t ht'
  have hpos : 0 < t := by linarith [le_max_right R 1]
  have : 1 ≤ Φ t / t := hΦ_ge
  calc t = t * 1 := by ring
       _ ≤ t * (Φ t / t) := by exact mul_le_mul_of_nonneg_left this (le_of_lt hpos)
       _ = Φ t := by field_simp

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

/-! ## Complete Lemmas (Unused but Reusable)

These lemmas are fully proved and could be useful for implementing condExp_tendsto_iInf
via the Vitali approach. -/

/-- Fatou on `ENNReal.ofReal ∘ ‖·‖` along an a.e. pointwise limit. -/
lemma lintegral_fatou_ofReal_norm
  {α β : Type*} [MeasurableSpace α] {μ : Measure α}
  [MeasurableSpace β] [NormedAddCommGroup β] [BorelSpace β]
  {u : ℕ → α → β} {g : α → β}
  (hae : ∀ᵐ x ∂μ, Tendsto (fun n => u n x) atTop (nhds (g x)))
  (hu_meas : ∀ n, AEMeasurable (fun x => ENNReal.ofReal ‖u n x‖) μ)
  (hg_meas : AEMeasurable (fun x => ENNReal.ofReal ‖g x‖) μ) :
  ∫⁻ x, ENNReal.ofReal ‖g x‖ ∂μ
    ≤ liminf (fun n => ∫⁻ x, ENNReal.ofReal ‖u n x‖ ∂μ) atTop := by
  have hae_ofReal :
      ∀ᵐ x ∂μ,
        Tendsto (fun n => ENNReal.ofReal ‖u n x‖) atTop
                (nhds (ENNReal.ofReal ‖g x‖)) :=
    hae.mono (fun x hx =>
      ((ENNReal.continuous_ofReal.comp continuous_norm).tendsto _).comp hx)
  calc ∫⁻ x, ENNReal.ofReal ‖g x‖ ∂μ
      = ∫⁻ x, liminf (fun n => ENNReal.ofReal ‖u n x‖) atTop ∂μ :=
          lintegral_congr_ae (hae_ofReal.mono fun x hx => hx.liminf_eq.symm)
    _ ≤ liminf (fun n => ∫⁻ x, ENNReal.ofReal ‖u n x‖ ∂μ) atTop :=
          lintegral_liminf_le' hu_meas

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

end Exchangeability.Probability
