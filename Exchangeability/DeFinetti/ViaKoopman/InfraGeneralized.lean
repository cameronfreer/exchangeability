/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Exchangeability.DeFinetti.ViaKoopman.InfraCore
import Exchangeability.DeFinetti.ViaKoopman.InfraLagConstancy

/-! # Generalized Lag-Constancy and Two-Sided Infrastructure

This file contains advanced infrastructure for the Koopman-based de Finetti proof:
- Two-sided extension lemmas for bi-infinite path spaces
- `condexp_precomp_iterate_eq_twosided` - CE invariance under two-sided shifts
- `condexp_lag_constant_product` - Generalized lag constancy for products
- `condexp_lag_constant_product_general` - Full generalization at arbitrary coordinates
- Conditional expectation helper lemmas (L¹-Lipschitz, pullout)

All lemmas in this file are proved (no sorries).

**Extracted from**: Infrastructure.lean (Part 3/3)
**Status**: Complete (no sorries in proofs)
-/

open Filter MeasureTheory

noncomputable section

namespace Exchangeability.DeFinetti.ViaKoopman

open MeasureTheory Filter Topology ProbabilityTheory
open Exchangeability.Ergodic
open Exchangeability.PathSpace
open scoped BigOperators RealInnerProductSpace

variable {α : Type*} [MeasurableSpace α]

-- Short notation for shift-invariant σ-algebra (used throughout this file)
local notation "mSI" => shiftInvariantSigma (α := α)

/-- The comap of shiftInvariantSigma along restrictNonneg is contained in shiftInvariantSigmaℤ.

This follows from the fact that preimages of shift-invariant sets are shiftℤ-invariant,
using `restrictNonneg_shiftℤ : restrictNonneg (shiftℤ ω) = shift (restrictNonneg ω)`. -/
lemma comap_restrictNonneg_shiftInvariantSigma_le :
    MeasurableSpace.comap (restrictNonneg (α := α)) (shiftInvariantSigma (α := α))
      ≤ shiftInvariantSigmaℤ (α := α) := by
  intro t ht
  -- t is of the form restrictNonneg⁻¹' s for some s ∈ shiftInvariantSigma
  rcases ht with ⟨s, hs, rfl⟩
  -- hs : isShiftInvariant s, i.e., MeasurableSet s ∧ shift⁻¹' s = s
  constructor
  · -- Measurability: restrictNonneg⁻¹' s is measurable
    exact measurable_restrictNonneg hs.1
  · -- Shift-invariance: shiftℤ⁻¹' (restrictNonneg⁻¹' s) = restrictNonneg⁻¹' s
    ext ω
    simp only [Set.mem_preimage]
    -- Goal: shiftℤ ω ∈ restrictNonneg⁻¹' s ↔ ω ∈ restrictNonneg⁻¹' s
    -- i.e., restrictNonneg (shiftℤ ω) ∈ s ↔ restrictNonneg ω ∈ s
    rw [restrictNonneg_shiftℤ]
    -- Now: shift (restrictNonneg ω) ∈ s ↔ restrictNonneg ω ∈ s
    -- This follows from s being shift-invariant
    have h_inv : shift ⁻¹' s = s := hs.2
    rw [← Set.mem_preimage, h_inv]

/-- Pulling an almost-everywhere equality back along the natural extension.

**Proof**: Uses `ae_map_iff` from mathlib: since `μ = map restrictNonneg ext.μhat`,
we have `(∀ᵐ ω ∂μ, F ω = G ω) ↔ (∀ᵐ ωhat ∂ext.μhat, F (restrictNonneg ωhat) = G (restrictNonneg ωhat))`.
The hypothesis `h` gives the RHS, so we conclude the LHS. -/
lemma naturalExtension_pullback_ae
    {μ : Measure (Ω[α])} [IsProbabilityMeasure μ] [StandardBorelSpace α]
    (ext : NaturalExtensionData (μ := μ))
    {F G : Ω[α] → ℝ} (hF : AEMeasurable F μ) (hG : AEMeasurable G μ)
    (h : (fun ωhat => F (restrictNonneg (α := α) ωhat))
        =ᵐ[ext.μhat]
        (fun ωhat => G (restrictNonneg (α := α) ωhat))) :
    F =ᵐ[μ] G := by
  haveI := ext.μhat_isProb
  rw [ae_pullback_iff (restrictNonneg (α := α)) measurable_restrictNonneg
    ext.restrict_pushforward hF hG]
  exact h

/-- Two-sided version of `condexp_precomp_iterate_eq`.

**Proof strategy**: For any k iterations of shiftℤ, the conditional expectation
is unchanged because:
1. shiftℤ^[k] is measure-preserving (composition of measure-preserving maps)
2. shiftℤ^[k] leaves shiftInvariantSigmaℤ-measurable sets invariant
3. Set-integrals over invariant sets are preserved by measure-preserving maps -/
lemma condexp_precomp_iterate_eq_twosided
    {μhat : Measure (Ωℤ[α])} [IsProbabilityMeasure μhat]
    (hσ : MeasurePreserving (shiftℤ (α := α)) μhat μhat) {k : ℕ}
    {f : Ωℤ[α] → ℝ} (hf : Integrable f μhat) :
    μhat[(fun ω => f ((shiftℤ (α := α))^[k] ω))
        | shiftInvariantSigmaℤ (α := α)]
      =ᵐ[μhat] μhat[f | shiftInvariantSigmaℤ (α := α)] := by
  -- Key property: shiftInvariantSigmaℤ-measurable sets are shiftℤ-invariant by definition
  have h_inv : ∀ s, MeasurableSet[shiftInvariantSigmaℤ (α := α)] s →
      (shiftℤ (α := α)) ⁻¹' s = s := fun s hs => hs.2
  -- Proof by induction on k
  induction k with
  | zero => simp
  | succ k ih =>
    -- f ∘ shiftℤ^[k+1] = (f ∘ shiftℤ^[k]) ∘ shiftℤ
    have h_comp : (fun ω => f ((shiftℤ (α := α))^[k+1] ω)) =
        (fun ω => f ((shiftℤ (α := α))^[k] ω)) ∘ (shiftℤ (α := α)) := by
      ext ω
      simp only [Function.comp_apply]
      -- Goal: f (shiftℤ^[k+1] ω) = f (shiftℤ^[k] (shiftℤ ω))
      -- Use: shiftℤ^[k+1] ω = shiftℤ^[k] (shiftℤ ω) by iterate_succ_apply
      rw [Function.iterate_succ_apply]
    -- shiftℤ^[k] is measure-preserving
    have hσ_k : MeasurePreserving ((shiftℤ (α := α))^[k]) μhat μhat := hσ.iterate k
    -- f ∘ shiftℤ^[k] is integrable
    have hf_k : Integrable (fun ω => f ((shiftℤ (α := α))^[k] ω)) μhat := by
      have : (fun ω => f ((shiftℤ (α := α))^[k] ω)) = f ∘ ((shiftℤ (α := α))^[k]) := rfl
      rw [this, hσ_k.integrable_comp hf.aestronglyMeasurable]
      exact hf
    -- Use uniqueness of conditional expectation for the base step
    have h_base : μhat[(fun ω => f ((shiftℤ (α := α))^[k] ω)) ∘ (shiftℤ (α := α))
        | shiftInvariantSigmaℤ (α := α)]
          =ᵐ[μhat] μhat[(fun ω => f ((shiftℤ (α := α))^[k] ω))
              | shiftInvariantSigmaℤ (α := α)] := by
      symm
      apply MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq
        (shiftInvariantSigmaℤ_le (α := α))
      -- Integrability of f ∘ shiftℤ^[k] ∘ shiftℤ
      · rw [hσ.integrable_comp hf_k.aestronglyMeasurable]
        exact hf_k
      -- IntegrableOn for the condExp
      · intro s _ _
        exact MeasureTheory.integrable_condExp.integrableOn
      -- Set integral equality: ∫_s E[g|m] = ∫_s g ∘ T when T⁻¹' s = s
      · intro s hs hμs
        -- First use setIntegral_condExp: ∫_s E[g|m] dμ = ∫_s g dμ
        rw [MeasureTheory.setIntegral_condExp (shiftInvariantSigmaℤ_le (α := α)) hf_k hs]
        -- Now show: ∫_s g dμ = ∫_s (g ∘ T) dμ using T⁻¹'s = s and MeasurePreserving
        let g := fun ω => f ((shiftℤ (α := α))^[k] ω)
        have h_s_inv : (shiftℤ (α := α)) ⁻¹' s = s := h_inv s hs
        -- Apply setIntegral_map_preimage in reverse with h_s_inv
        have h_map_eq : Measure.map (shiftℤ (α := α)) μhat = μhat := hσ.map_eq
        rw [← MeasureTheory.setIntegral_map_preimage (shiftℤ (α := α)) measurable_shiftℤ h_map_eq
            g s (shiftInvariantSigmaℤ_le (α := α) s hs) hf_k.aemeasurable]
        -- Now goal: ∫_s g = ∫_{T⁻¹'s} (g ∘ T), rewrite T⁻¹'s = s
        rw [h_s_inv]
      -- AE strong measurability
      · exact MeasureTheory.stronglyMeasurable_condExp.aestronglyMeasurable
    -- Combine: E[f ∘ T^{k+1} | m] = E[(f ∘ T^k) ∘ T | m] = E[f ∘ T^k | m] = E[f | m]
    calc μhat[(fun ω => f ((shiftℤ (α := α))^[k+1] ω)) | shiftInvariantSigmaℤ (α := α)]
        = μhat[(fun ω => f ((shiftℤ (α := α))^[k] ω)) ∘ (shiftℤ (α := α))
            | shiftInvariantSigmaℤ (α := α)] := by rw [h_comp]
      _ =ᵐ[μhat] μhat[(fun ω => f ((shiftℤ (α := α))^[k] ω))
            | shiftInvariantSigmaℤ (α := α)] := h_base
      _ =ᵐ[μhat] μhat[f | shiftInvariantSigmaℤ (α := α)] := ih

/-- Invariance of conditional expectation under the inverse shift.

**Proof strategy**: Similar to `condexp_precomp_iterate_eq_twosided`, but using
that shiftℤInv also preserves the measure and leaves the invariant σ-algebra fixed. -/
lemma condexp_precomp_shiftℤInv_eq
    {μhat : Measure (Ωℤ[α])} [IsProbabilityMeasure μhat]
    (hσInv : MeasurePreserving (shiftℤInv (α := α)) μhat μhat)
    {f : Ωℤ[α] → ℝ} (hf : Integrable f μhat) :
    μhat[(fun ω => f (shiftℤInv (α := α) ω))
        | shiftInvariantSigmaℤ (α := α)]
      =ᵐ[μhat] μhat[f | shiftInvariantSigmaℤ (α := α)] := by
  -- Key property: shiftInvariantSigmaℤ-measurable sets are shiftℤInv-invariant too
  -- Proof: If shiftℤ⁻¹' s = s then shiftℤInv⁻¹' s = s (since they're inverses)
  have h_inv : ∀ s, MeasurableSet[shiftInvariantSigmaℤ (α := α)] s →
      (shiftℤInv (α := α)) ⁻¹' s = s := by
    intro s hs
    -- hs.2 gives shiftℤ⁻¹' s = s
    -- Need: shiftℤInv⁻¹' s = s, i.e., ∀ ω, shiftℤInv ω ∈ s ↔ ω ∈ s
    ext ω
    constructor
    · -- shiftℤInv ω ∈ s → ω ∈ s
      intro h
      -- shiftℤInv ω ∈ s means ω = shiftℤ (shiftℤInv ω) ∈ shiftℤ '' s
      -- Since shiftℤ⁻¹' s = s, we have shiftℤ '' s = s (bijection)
      have hω' : shiftℤ (α := α) (shiftℤInv (α := α) ω) ∈ shiftℤ (α := α) '' s :=
        Set.mem_image_of_mem _ h
      simp only [shiftℤ_comp_shiftℤInv] at hω'
      -- Use that shiftℤ '' s = s (from shiftℤ⁻¹' s = s and bijectivity)
      have h_surj : shiftℤ (α := α) '' s = s := by
        ext x
        simp only [Set.mem_image]
        constructor
        · rintro ⟨y, hy, rfl⟩
          -- y ∈ s, want shiftℤ y ∈ s
          -- hs.2 : shiftℤ⁻¹' s = s means y ∈ s ↔ y ∈ shiftℤ⁻¹' s ↔ shiftℤ y ∈ s
          have h : y ∈ shiftℤ (α := α) ⁻¹' s := by rw [hs.2]; exact hy
          exact Set.mem_preimage.mp h
        · intro hx
          use shiftℤInv (α := α) x
          constructor
          · rw [← hs.2]
            simp [shiftℤ_comp_shiftℤInv, hx]
          · simp
      rw [h_surj] at hω'
      exact hω'
    · -- ω ∈ s → shiftℤInv ω ∈ s
      intro h
      -- ω ∈ s and shiftℤ⁻¹' s = s means shiftℤ⁻¹ ω ∈ s
      -- shiftℤ⁻¹' s = s means: ∀ x, shiftℤ x ∈ s ↔ x ∈ s
      -- Apply with x = shiftℤInv ω: shiftℤ (shiftℤInv ω) ∈ s ↔ shiftℤInv ω ∈ s
      rw [← hs.2]
      simp [h]
  -- Now prove the main result using ae_eq_condExp_of_forall_setIntegral_eq
  have hf_inv : Integrable (fun ω => f (shiftℤInv (α := α) ω)) μhat := by
    exact (hσInv.integrable_comp hf.aestronglyMeasurable).mpr hf
  symm
  apply MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq
    (shiftInvariantSigmaℤ_le (α := α))
  -- Integrability
  · exact hf_inv
  -- IntegrableOn for the condExp
  · intro s _ _
    exact MeasureTheory.integrable_condExp.integrableOn
  -- Set integral equality
  · intro s hs hμs
    rw [MeasureTheory.setIntegral_condExp (shiftInvariantSigmaℤ_le (α := α)) hf hs]
    -- Need: ∫_s (f ∘ shiftℤInv) = ∫_s f
    have h_s_inv : (shiftℤInv (α := α)) ⁻¹' s = s := h_inv s hs
    -- Use measure-preserving property
    rw [← MeasureTheory.integral_indicator (shiftInvariantSigmaℤ_le (α := α) s hs)]
    rw [← MeasureTheory.integral_indicator (shiftInvariantSigmaℤ_le (α := α) s hs)]
    -- Rewrite indicator: (1_s · f) ∘ shiftℤInv vs 1_s · (f ∘ shiftℤInv)
    -- Since shiftℤInv⁻¹' s = s, we have 1_s (shiftℤInv ω) = 1_s ω
    have h_ind : ∀ ω, s.indicator (fun ω => f (shiftℤInv (α := α) ω)) ω =
        s.indicator f (shiftℤInv (α := α) ω) := by
      intro ω
      simp only [Set.indicator]
      split_ifs with h1 h2 h2
      · rfl
      · exfalso
        rw [← Set.mem_preimage, h_s_inv] at h2
        exact h2 h1
      · exfalso
        rw [← h_s_inv] at h1
        exact h1 (Set.mem_preimage.mpr h2)
      · rfl
    rw [show (∫ x, s.indicator (fun ω => f (shiftℤInv (α := α) ω)) x ∂μhat) =
        (∫ x, s.indicator f (shiftℤInv (α := α) x) ∂μhat)
      from MeasureTheory.integral_congr_ae (ae_of_all μhat h_ind)]
    -- Now use measure-preserving: ∫ g ∘ T dμ = ∫ g dμ
    -- Since hσInv.map_eq : μhat.map shiftℤInv = μhat,
    -- we have ∫ g ∘ shiftℤInv dμhat = ∫ g d(μhat.map shiftℤInv) = ∫ g dμhat
    -- This is exactly ∫ (s.indicator f) ∘ shiftℤInv dμhat = ∫ s.indicator f dμhat
    have h_map_eq : Measure.map (shiftℤInv (α := α)) μhat = μhat := hσInv.map_eq
    have h_ae : AEStronglyMeasurable (s.indicator f) μhat := by
      refine (hf.aestronglyMeasurable.indicator ?_)
      exact shiftInvariantSigmaℤ_le (α := α) s hs
    -- Convert h_ae to AEStronglyMeasurable for the map measure
    have h_ae_map : AEStronglyMeasurable (s.indicator f) (μhat.map (shiftℤInv (α := α))) := by
      rw [h_map_eq]; exact h_ae
    rw [← MeasureTheory.integral_map measurable_shiftℤInv.aemeasurable h_ae_map, h_map_eq]
  -- AE strong measurability
  · exact MeasureTheory.stronglyMeasurable_condExp.aestronglyMeasurable

/-- Helper: Integrability of a bounded function on a finite measure space. -/
private lemma integrable_of_bounded_helper {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {f : Ω → ℝ} (hf : Measurable f) (hbd : ∃ C, ∀ ω, |f ω| ≤ C) :
    Integrable f μ := by
  obtain ⟨C, hC⟩ := hbd
  exact ⟨hf.aestronglyMeasurable, HasFiniteIntegral.of_bounded (ae_of_all μ hC)⟩

/-- Helper: Integrability of a bounded product on a finite measure space. -/
private lemma integrable_of_bounded_mul_helper
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ] [Nonempty Ω]
    {φ ψ : Ω → ℝ}
    (hφ_meas : Measurable φ) (hφ_bd : ∃ Cφ, ∀ ω, |φ ω| ≤ Cφ)
    (hψ_meas : Measurable ψ) (hψ_bd : ∃ Cψ, ∀ ω, |ψ ω| ≤ Cψ) :
    Integrable (fun ω => φ ω * ψ ω) μ := by
  classical
  obtain ⟨Cφ, hCφ⟩ := hφ_bd
  obtain ⟨Cψ, hCψ⟩ := hψ_bd
  have hCφ_nonneg : 0 ≤ Cφ := by
    have h := hCφ (Classical.arbitrary Ω)
    exact (abs_nonneg _).trans h
  have hCψ_nonneg : 0 ≤ Cψ := by
    have h := hCψ (Classical.arbitrary Ω)
    exact (abs_nonneg _).trans h
  have h_bound : ∀ ω, |φ ω * ψ ω| ≤ Cφ * Cψ := by
    intro ω
    have hφ := hCφ ω
    have hψ := hCψ ω
    have hmul :=
      mul_le_mul hφ hψ (abs_nonneg _) hCφ_nonneg
    simpa [abs_mul] using hmul
  have h_meas : Measurable fun ω => φ ω * ψ ω := hφ_meas.mul hψ_meas
  exact integrable_of_bounded_helper h_meas ⟨Cφ * Cψ, h_bound⟩

/-- Integrability of `f * g` when `g` is integrable and `|f| ≤ C`.

This shows that multiplying an integrable function by a bounded function preserves integrability.
The bound `|f * g| ≤ C * |g|` follows from `|f| ≤ C`. -/
lemma Integrable.of_abs_bounded {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f g : Ω → ℝ} (hg : Integrable g μ) (C : ℝ) (hC : 0 ≤ C)
    (h_bound : ∀ ω, |f ω| ≤ C)
    (hfg_meas : AEStronglyMeasurable (fun ω => f ω * g ω) μ) :
    Integrable (fun ω => f ω * g ω) μ := by
  have h_norm_bound : ∀ᵐ ω ∂μ, ‖f ω * g ω‖ ≤ C * ‖g ω‖ := by
    apply Filter.Eventually.of_forall
    intro ω
    simp only [Real.norm_eq_abs]
    calc |f ω * g ω| = |f ω| * |g ω| := abs_mul _ _
      _ ≤ C * |g ω| := mul_le_mul_of_nonneg_right (h_bound ω) (abs_nonneg _)
  -- Use Integrable.mono' with dominating function C * |g|
  refine Integrable.mono' (hg.norm.const_mul C) hfg_meas ?_
  filter_upwards with ω
  simp only [Real.norm_eq_abs, Pi.mul_apply, abs_of_nonneg hC]
  calc |f ω * g ω| = |f ω| * |g ω| := abs_mul _ _
    _ ≤ C * |g ω| := mul_le_mul_of_nonneg_right (h_bound ω) (abs_nonneg _)

/-- **Generalized lag-constancy for products** (extends `condexp_lag_constant_from_exchangeability`).

For EXCHANGEABLE measures μ on path space, if P = ∏_{i<n} f_i(ω_i) is a product of
the first n coordinates and g : α → ℝ is bounded measurable, then for k ≥ n:
  CE[P · g(ω_{k+1}) | mSI] = CE[P · g(ω_k) | mSI]

**Proof**: Uses transposition τ = swap(k, k+1). Since k ≥ n, τ fixes all indices < n.
Therefore P is unchanged by reindex τ, while g(ω_{k+1}) becomes g(ω_k).
Exchangeability then gives the result.

**Key insight**: This generalizes the pair case where P = f(ω_0) and n = 1. -/
lemma condexp_lag_constant_product
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α]
    {μ : Measure (ℕ → α)} [IsProbabilityMeasure μ]
    (hExch : ∀ π : Equiv.Perm ℕ, Measure.map (Exchangeability.reindex π) μ = μ)
    (n : ℕ) (fs : Fin n → α → ℝ)
    (hfs_meas : ∀ i, Measurable (fs i))
    (hfs_bd : ∀ i, ∃ C, ∀ x, |fs i x| ≤ C)
    (g : α → ℝ) (hg_meas : Measurable g) (hg_bd : ∃ Cg, ∀ x, |g x| ≤ Cg)
    (k : ℕ) (hk : n ≤ k) :
    μ[(fun ω => (∏ i : Fin n, fs i (ω i)) * g (ω (k + 1))) | shiftInvariantSigma (α := α)]
      =ᵐ[μ]
    μ[(fun ω => (∏ i : Fin n, fs i (ω i)) * g (ω k)) | shiftInvariantSigma (α := α)] := by
  -- Define the transposition τ = swap k (k+1)
  let τ := Equiv.swap k (k + 1)
  -- Define the two functions
  let P : (ℕ → α) → ℝ := fun ω => ∏ i : Fin n, fs i (ω i)
  let F := fun ω : ℕ → α => P ω * g (ω (k + 1))
  let G := fun ω : ℕ → α => P ω * g (ω k)

  -- Key fact 1: τ fixes all indices < n (since k ≥ n implies k, k+1 > n-1)
  have hτ_fix : ∀ i : Fin n, τ (i : ℕ) = i := by
    intro i
    have hi : (i : ℕ) < n := Fin.is_lt i
    have hik : (i : ℕ) ≠ k := by omega
    have hik1 : (i : ℕ) ≠ k + 1 := by omega
    exact Equiv.swap_apply_of_ne_of_ne hik hik1

  -- Key fact 2: P ∘ reindex τ = P (product unchanged since τ fixes all indices < n)
  have hP_inv : (P ∘ Exchangeability.reindex τ) = P := by
    ext ω
    simp only [Function.comp_apply, P, Exchangeability.reindex]
    apply Finset.prod_congr rfl
    intro i _
    -- Goal: fs i (ω (τ ↑i)) = fs i (ω ↑i)
    -- From hτ_fix: τ ↑i = ↑i
    simp only [hτ_fix i]

  -- Key fact 3: F ∘ reindex τ = G
  have hFG : F ∘ Exchangeability.reindex τ = G := by
    ext ω
    simp only [Function.comp_apply, F, G, Exchangeability.reindex]
    congr 1
    · -- P part: unchanged
      apply Finset.prod_congr rfl
      intro i _
      -- Need: fs i (ω (τ i)) = fs i (ω i)
      -- Since τ fixes i: τ (i : ℕ) = i
      show fs i (ω (τ i)) = fs i (ω i)
      rw [hτ_fix i]
    · -- g part: ω (τ (k+1)) = ω k
      rw [Equiv.swap_apply_right]

  -- Key fact 4: μ.map (reindex τ) = μ (exchangeability)
  have hμ_inv : Measure.map (Exchangeability.reindex τ) μ = μ := hExch τ

  -- Both F and G are integrable (products of bounded measurable functions)
  have hP_meas : Measurable P :=
    Finset.measurable_prod _ (fun i _ => (hfs_meas i).comp (measurable_pi_apply (i : ℕ)))

  -- Bound for the product P
  let CP := ∏ i : Fin n, (hfs_bd i).choose
  have hCP : ∀ ω, |P ω| ≤ CP := fun ω => by
    calc |P ω| = |∏ i : Fin n, fs i (ω i)| := rfl
      _ = ∏ i : Fin n, |fs i (ω i)| := Finset.abs_prod _ _
      _ ≤ ∏ i : Fin n, (hfs_bd i).choose := by
          apply Finset.prod_le_prod
          · intro i _; exact abs_nonneg _
          · intro i _; exact (hfs_bd i).choose_spec (ω i)

  obtain ⟨Cg, hCg⟩ := hg_bd

  have hF_meas : Measurable F := hP_meas.mul (hg_meas.comp (measurable_pi_apply (k + 1)))
  have hG_meas : Measurable G := hP_meas.mul (hg_meas.comp (measurable_pi_apply k))

  have hCP_nonneg : 0 ≤ CP := by
    -- CP = ∏ (hfs_bd i).choose ≥ 0 since each bound is ≥ 0
    -- Each (hfs_bd i).choose bounds |fs i x| ≥ 0, so it must be ≥ 0
    -- Need some element of α to instantiate x
    haveI : Nonempty (ℕ → α) := ProbabilityMeasure.nonempty ⟨μ, inferInstance⟩
    have ω : ℕ → α := Classical.choice ‹Nonempty (ℕ → α)›
    apply Finset.prod_nonneg
    intro i _
    exact le_trans (abs_nonneg _) ((hfs_bd i).choose_spec (ω 0))

  have hF_bd : ∀ ω, ‖F ω‖ ≤ CP * Cg := fun ω => by
    simp only [Real.norm_eq_abs]
    calc |F ω| = |P ω * g (ω (k + 1))| := rfl
      _ = |P ω| * |g (ω (k + 1))| := abs_mul _ _
      _ ≤ CP * Cg := mul_le_mul (hCP _) (hCg _) (abs_nonneg _) hCP_nonneg

  have hG_bd : ∀ ω, ‖G ω‖ ≤ CP * Cg := fun ω => by
    simp only [Real.norm_eq_abs]
    calc |G ω| = |P ω * g (ω k)| := rfl
      _ = |P ω| * |g (ω k)| := abs_mul _ _
      _ ≤ CP * Cg := mul_le_mul (hCP _) (hCg _) (abs_nonneg _) hCP_nonneg

  have hF_int : Integrable F μ := Integrable.of_bound hF_meas.aestronglyMeasurable (CP * Cg)
    (Filter.Eventually.of_forall hF_bd)
  have hG_int : Integrable G μ := Integrable.of_bound hG_meas.aestronglyMeasurable (CP * Cg)
    (Filter.Eventually.of_forall hG_bd)

  -- Strategy: Show ∫_s F = ∫_s G for all s ∈ mSI, then μ[F|mSI] = μ[G|mSI]
  have hτ_meas : Measurable (Exchangeability.reindex (α := α) τ) :=
    Exchangeability.measurable_reindex (α := α) (π := τ)

  have h_int_eq : ∀ s, MeasurableSet[shiftInvariantSigma (α := α)] s → μ s < ⊤ →
      ∫ ω in s, F ω ∂μ = ∫ ω in s, G ω ∂μ := fun s hs _ => by
    have hs_inv : isShiftInvariant (α := α) s := (mem_shiftInvariantSigma_iff (α := α)).mp hs
    exact setIntegral_eq_of_reindex_eq τ hμ_inv F G hFG hF_meas s hs_inv.1
      (reindex_swap_preimage_shiftInvariant k s hs_inv)

  -- Show ∫_s (F - G) = 0 for all s ∈ mSI
  have h_diff_zero : ∀ s, MeasurableSet[shiftInvariantSigma (α := α)] s → μ s < ⊤ →
      ∫ ω in s, (F - G) ω ∂μ = 0 := fun s hs hμs => by
    simp only [Pi.sub_apply, integral_sub hF_int.integrableOn hG_int.integrableOn,
               h_int_eq s hs hμs, sub_self]

  exact condExp_ae_eq_of_setIntegral_diff_eq_zero hF_int hG_int h_diff_zero

/-- **Generalized lag constancy for products at arbitrary coordinates**.

This extends `condexp_lag_constant_product` to products at general coordinates k_0, ..., k_{n-1}.
For j, j+1 both larger than all k_i, the transposition τ = swap(j, j+1) fixes all coordinates
in the product, so the conditional expectation is unchanged.

**Key observation**: If M = max(k_i) + 1, then for all j ≥ M:
- τ = swap(j, j+1) fixes all indices 0, 1, ..., j-1
- In particular, τ fixes all k_i (since k_i < M ≤ j)
- Therefore P ∘ reindex τ = P
- And the lag constancy argument applies -/
lemma condexp_lag_constant_product_general
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α]
    {μ : Measure (ℕ → α)} [IsProbabilityMeasure μ]
    (hExch : ∀ π : Equiv.Perm ℕ, Measure.map (Exchangeability.reindex π) μ = μ)
    (n : ℕ) (fs : Fin n → α → ℝ) (coords : Fin n → ℕ)
    (hfs_meas : ∀ i, Measurable (fs i))
    (hfs_bd : ∀ i, ∃ C, ∀ x, |fs i x| ≤ C)
    (g : α → ℝ) (hg_meas : Measurable g) (hg_bd : ∃ Cg, ∀ x, |g x| ≤ Cg)
    (j : ℕ) (hj : ∀ i : Fin n, coords i < j) :
    μ[(fun ω => (∏ i : Fin n, fs i (ω (coords i))) * g (ω (j + 1))) | shiftInvariantSigma (α := α)]
      =ᵐ[μ]
    μ[(fun ω => (∏ i : Fin n, fs i (ω (coords i))) * g (ω j)) | shiftInvariantSigma (α := α)] := by
  -- Define the transposition τ = swap j (j+1)
  let τ := Equiv.swap j (j + 1)
  -- Define the product P at coordinates
  let P : (ℕ → α) → ℝ := fun ω => ∏ i : Fin n, fs i (ω (coords i))
  let F := fun ω : ℕ → α => P ω * g (ω (j + 1))
  let G := fun ω : ℕ → α => P ω * g (ω j)

  -- Key fact 1: τ fixes all coords(i) (since coords(i) < j and τ swaps j, j+1)
  have hτ_fix : ∀ i : Fin n, τ (coords i) = coords i := by
    intro i
    have hi : coords i < j := hj i
    have hne1 : coords i ≠ j := by omega
    have hne2 : coords i ≠ j + 1 := by omega
    exact Equiv.swap_apply_of_ne_of_ne hne1 hne2

  -- Key fact 2: P ∘ reindex τ = P (product unchanged since τ fixes all coords)
  have hP_inv : (P ∘ Exchangeability.reindex τ) = P := by
    ext ω
    simp only [Function.comp_apply, P, Exchangeability.reindex]
    apply Finset.prod_congr rfl
    intro i _
    simp only [hτ_fix i]

  -- Key fact 3: τ(j+1) = j and τ(j) = j+1
  have hτ_j1 : τ (j + 1) = j := Equiv.swap_apply_right j (j + 1)
  have hτ_j : τ j = j + 1 := Equiv.swap_apply_left j (j + 1)

  -- Key fact 4: F ∘ reindex τ = G
  have hFG : (F ∘ Exchangeability.reindex τ) = G := by
    ext ω
    simp only [Function.comp_apply, F, G, Exchangeability.reindex]
    congr 1
    · -- P part
      simp only [P]
      apply Finset.prod_congr rfl
      intro i _
      show fs i (ω (τ (coords i))) = fs i (ω (coords i))
      rw [hτ_fix i]
    · -- g part
      show g (ω (τ (j + 1))) = g (ω j)
      rw [hτ_j1]

  -- Integrability bounds
  have hP_bd : ∃ Cp, ∀ ω, |P ω| ≤ Cp := by
    choose Cs hCs using hfs_bd
    use ∏ i : Fin n, Cs i
    intro ω
    calc |P ω| = |∏ i : Fin n, fs i (ω (coords i))| := rfl
      _ = ∏ i : Fin n, |fs i (ω (coords i))| := Finset.abs_prod _ _
      _ ≤ ∏ i : Fin n, Cs i := by
          apply Finset.prod_le_prod
          · intro i _; exact abs_nonneg _
          · intro i _; exact hCs i (ω (coords i))

  obtain ⟨Cp, hCp⟩ := hP_bd
  obtain ⟨Cg, hCg⟩ := hg_bd

  have hP_meas : Measurable P := by
    apply Finset.measurable_prod
    intro i _
    exact (hfs_meas i).comp (measurable_pi_apply (coords i))

  have hCp_nonneg : 0 ≤ Cp := by
    haveI : Nonempty (ℕ → α) := ProbabilityMeasure.nonempty ⟨μ, inferInstance⟩
    have ω : ℕ → α := Classical.choice ‹Nonempty (ℕ → α)›
    exact le_trans (abs_nonneg _) (hCp ω)

  have hF_meas : Measurable F := hP_meas.mul (hg_meas.comp (measurable_pi_apply (j + 1)))
  have hF_bd : ∀ ω, ‖F ω‖ ≤ Cp * Cg := fun ω => by
    simp only [Real.norm_eq_abs, F]
    calc |P ω * g (ω (j + 1))| = |P ω| * |g (ω (j + 1))| := abs_mul _ _
      _ ≤ Cp * Cg := mul_le_mul (hCp _) (hCg _) (abs_nonneg _) hCp_nonneg
  have hF_int : Integrable F μ := Integrable.of_bound hF_meas.aestronglyMeasurable (Cp * Cg)
    (Filter.Eventually.of_forall hF_bd)

  have hG_meas : Measurable G := hP_meas.mul (hg_meas.comp (measurable_pi_apply j))
  have hG_bd : ∀ ω, ‖G ω‖ ≤ Cp * Cg := fun ω => by
    simp only [Real.norm_eq_abs, G]
    calc |P ω * g (ω j)| = |P ω| * |g (ω j)| := abs_mul _ _
      _ ≤ Cp * Cg := mul_le_mul (hCp _) (hCg _) (abs_nonneg _) hCp_nonneg
  have hG_int : Integrable G μ := Integrable.of_bound hG_meas.aestronglyMeasurable (Cp * Cg)
    (Filter.Eventually.of_forall hG_bd)

  -- μ.map (reindex τ) = μ (exchangeability)
  have hμ_inv : Measure.map (Exchangeability.reindex τ) μ = μ := hExch τ

  -- Now apply the exchange argument (same pattern as condexp_lag_constant_product)
  have h_int_eq : ∀ s, MeasurableSet[shiftInvariantSigma (α := α)] s → μ s < ⊤ →
      ∫ ω in s, F ω ∂μ = ∫ ω in s, G ω ∂μ := fun s hs _ => by
    have hs_inv : isShiftInvariant (α := α) s := (mem_shiftInvariantSigma_iff (α := α)).mp hs
    exact setIntegral_eq_of_reindex_eq τ hμ_inv F G hFG hF_meas s hs_inv.1
      (reindex_swap_preimage_shiftInvariant j s hs_inv)

  have h_diff_zero : ∀ (s : Set (ℕ → α)), MeasurableSet[shiftInvariantSigma (α := α)] s
      → μ s < ⊤ →
      ∫ ω in s, (F - G) ω ∂μ = 0 := fun s hs hμs => by
    simp only [Pi.sub_apply, integral_sub hF_int.integrableOn hG_int.integrableOn,
               h_int_eq s hs hμs, sub_self]

  exact condExp_ae_eq_of_setIntegral_diff_eq_zero hF_int hG_int h_diff_zero


/-! ### Conditional Expectation Helper Lemmas

These lemmas support the L¹ Cesàro convergence framework. -/

/-- If `Z` is a.e.-bounded and measurable and `Y` is integrable,
    then `Z*Y` is integrable (finite measure suffices). -/
lemma integrable_mul_of_ae_bdd_left
    {μ : Measure (Ω[α])} [IsFiniteMeasure μ]
    {Z Y : Ω[α] → ℝ}
    (hZ : Measurable Z) (hZ_bd : ∃ C, ∀ᵐ ω ∂μ, |Z ω| ≤ C)
    (hY : Integrable Y μ) :
    Integrable (Z * Y) μ := by
  obtain ⟨C, hC⟩ := hZ_bd
  have hZ_norm : ∀ᵐ ω ∂μ, ‖Z ω‖ ≤ C := by
    filter_upwards [hC] with ω hω
    rwa [Real.norm_eq_abs]
  exact Integrable.bdd_mul' hY hZ.aestronglyMeasurable hZ_norm

/-- Conditional expectation is L¹-Lipschitz: moving the integrand changes the CE by at most
the L¹ distance. This is a standard property following from Jensen's inequality. -/
lemma condExp_L1_lipschitz
    {μ : Measure (Ω[α])} [IsProbabilityMeasure μ]
    {Z W : Ω[α] → ℝ} (hZ : Integrable Z μ) (hW : Integrable W μ) :
    ∫ ω, |μ[Z | shiftInvariantSigma (α := α)] ω - μ[W | shiftInvariantSigma (α := α)] ω| ∂μ
      ≤ ∫ ω, |Z ω - W ω| ∂μ := by
  have h_sub : μ[(Z - W) | shiftInvariantSigma]
              =ᵐ[μ] μ[Z | shiftInvariantSigma] - μ[W | shiftInvariantSigma] :=
    condExp_sub hZ hW shiftInvariantSigma
  calc ∫ ω, |μ[Z | shiftInvariantSigma] ω - μ[W | shiftInvariantSigma] ω| ∂μ
      = ∫ ω, |μ[(Z - W) | shiftInvariantSigma] ω| ∂μ := by
          refine integral_congr_ae ?_
          filter_upwards [h_sub] with ω hω
          simp [hω]
    _ ≤ ∫ ω, |Z ω - W ω| ∂μ := integral_abs_condExp_le (Z - W)

/-- Pull-out property: if Z is measurable w.r.t. the conditioning σ-algebra and a.e.-bounded,
then CE[Z·Y | mSI] = Z·CE[Y | mSI] a.e. This is the standard "taking out what is known". -/
lemma condExp_mul_pullout
    {μ : Measure (Ω[α])} [IsProbabilityMeasure μ]
    {Z Y : Ω[α] → ℝ}
    (hZ_meas : Measurable[shiftInvariantSigma (α := α)] Z)
    (hZ_bd : ∃ C, ∀ᵐ ω ∂μ, |Z ω| ≤ C)
    (hY : Integrable Y μ) :
    μ[Z * Y | shiftInvariantSigma (α := α)] =ᵐ[μ] Z * μ[Y | shiftInvariantSigma (α := α)] := by
  have hZ_aesm : AEStronglyMeasurable[shiftInvariantSigma (α := α)] Z μ :=
    hZ_meas.aestronglyMeasurable
  have hZY_int : Integrable (Z * Y) μ := by
    have hZ_meas_ambient : Measurable Z := by
      apply Measurable.mono hZ_meas
      · exact shiftInvariantSigma_le (α := α)
      · exact le_rfl
    exact integrable_mul_of_ae_bdd_left hZ_meas_ambient hZ_bd hY
  exact MeasureTheory.condExp_mul_of_aestronglyMeasurable_left
    (μ := μ) (m := shiftInvariantSigma (α := α)) hZ_aesm hZY_int hY



end Exchangeability.DeFinetti.ViaKoopman
