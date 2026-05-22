/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Exchangeability.DeFinetti.ViaKoopman.InfraCore

/-! # Lag-Constancy Infrastructure for ViaKoopman Proof

This file contains lag-constancy lemmas for the Koopman-based de Finetti proof:
- `condexp_pullback_factor` - CE pullback along factor maps
- LagConstancyProof section with permutation lemmas
- `setIntegral_eq_of_reindex_eq` - Set integral equality via reindexing
- `condExp_ae_eq_of_setIntegral_diff_eq_zero` - CE equality from set integral equality
- `condexp_lag_constant_from_exchangeability` - Main lag-constancy result

All lemmas in this file are proved (no sorries).

**Extracted from**: Infrastructure.lean (Part 2/3)
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

/-- **Factor-map pullback for conditional expectation**.

If `g : Ω' → Ω` is a factor map (i.e., `map g μ' = μ`), then conditional expectation
pulls back correctly: `CE[H | 𝒢] ∘ g = CE[H ∘ g | comap g 𝒢]` a.e.

This is the key lemma for transporting conditional expectations between spaces. -/
lemma condexp_pullback_factor
    {Ω Ω' : Type*} [inst : MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} [IsFiniteMeasure μ] {μ' : Measure Ω'} [IsFiniteMeasure μ']
    (g : Ω' → Ω) (hg : Measurable g) (hpush : Measure.map g μ' = μ)
    {H : Ω → ℝ} (hH : Integrable H μ)
    (m : MeasurableSpace Ω) (hm : m ≤ inst) :
    (fun ω' => μ[H | m] (g ω'))
      =ᵐ[μ'] μ'[(H ∘ g) | MeasurableSpace.comap g m] := by
  classical

  -- 1) Set-integral equality on every comap set
  have h_sets :
      ∀ s, MeasurableSet[MeasurableSpace.comap g m] s →
        ∫ x in s, (μ[H | m] ∘ g) x ∂ μ' = ∫ x in s, (H ∘ g) x ∂ μ' := by
    intro s hs
    rcases hs with ⟨B, hBm, rfl⟩
    -- lift measurability from m to ambient inst
    have hBm' : @MeasurableSet Ω inst B := hm B hBm
    -- a.e.-measurability for the integrands (under μ)
    -- Lift stronglyMeasurable from m to inst using hm : m ≤ inst
    have hCE_ae : AEMeasurable (condExp m μ H) μ :=
      (stronglyMeasurable_condExp.mono hm).aestronglyMeasurable.aemeasurable
    have hH_ae : AEMeasurable H μ := hH.aestronglyMeasurable.aemeasurable
    -- Three-step calc: change variables, apply CE property, change back
    calc
      ∫ x in g ⁻¹' B, (condExp m μ H ∘ g) x ∂ μ'
          = ∫ x in B, condExp m μ H x ∂ μ := by
            -- ★ explicit instance-locked change of variables
            exact
              @MeasureTheory.setIntegral_map_preimage Ω Ω' inst _ μ μ' g hg hpush
                (condExp m μ H) B hBm' hCE_ae
      _ = ∫ x in B, H x ∂ μ := by
            -- ★ explicit instance-locked CE property on m
            -- Provide `SigmaFinite (μ.trim hm)` if your build doesn't infer it automatically from finiteness.
            -- You can move this `haveI` up if you prefer a global instance.
            haveI : SigmaFinite (μ.trim hm) := inferInstance
            exact
              @MeasureTheory.setIntegral_condExp' Ω inst μ m hm _ B (by simpa using hBm) H hH
      _ = ∫ x in g ⁻¹' B, (H ∘ g) x ∂ μ' := by
            -- ★ explicit instance-locked change of variables (back)
            exact
              (@MeasureTheory.setIntegral_map_preimage Ω Ω' inst _ μ μ' g hg hpush
                H B hBm' hH_ae).symm

  -- 2) Uniqueness of the conditional expectation on `m.comap g`
  have hm' : MeasurableSpace.comap g m ≤ ‹MeasurableSpace Ω'› := by
    intro s hs
    rcases hs with ⟨B, hBm, rfl⟩
    -- Lift measurability from m to ambient inst, then apply preimage
    have hB_inst : @MeasurableSet Ω inst B := hm B hBm
    exact hB_inst.preimage hg
  -- Integrability of the pulled-back function (no instance shenanigans)
  have hHg' : Integrable (H ∘ g) μ' :=
    @integrable_comp_of_pushforward Ω Ω' inst _ μ μ' g H hg hpush hH

  -- Apply uniqueness of conditional expectation: we want to show (μ[H | m] ∘ g) = μ'[H ∘ g | comap g m]
  -- The lemma signature is: ae_eq_condExp_of_forall_setIntegral_eq (hf : Integrable f) ... : g =ᵐ[μ] μ[f | m]
  -- So f = H ∘ g (the integrable function we're taking condExp of)
  -- And g = μ[H | m] ∘ g (the function we're claiming equals the condExp)
  refine ae_eq_condExp_of_forall_setIntegral_eq (μ := μ') (m := MeasurableSpace.comap g m) (hm := hm') hHg' ?_ ?_ ?_
  -- 1) IntegrableOn for (μ[H | m] ∘ g) on finite measure comap sets
  · intro s hs hμs
    -- μ[H | m] ∘ g is integrable because μ[H | m] is integrable
    have : Integrable (μ[H | m]) μ := integrable_condExp
    exact (@integrable_comp_of_pushforward Ω Ω' inst _ μ μ' g (μ[H | m]) hg hpush this).integrableOn
  -- 2) Integral equality (h_sets but with added finite measure hypothesis)
  · intro s hs _
    exact h_sets s hs
  -- 3) AEStronglyMeasurable for (μ[H | m] ∘ g) with respect to comap g m
  · -- Key: g is measurable from (Ω', comap g m) to (Ω, m) by definition of comap
    have hf_meas_comap : @Measurable Ω' Ω (MeasurableSpace.comap g m) m g :=
      fun s hs => ⟨s, hs, rfl⟩
    -- condExp m μ H is strongly measurable w.r.t. m
    have h_sm : StronglyMeasurable[m] (condExp m μ H) := stronglyMeasurable_condExp
    -- Composition preserves strong measurability
    have h_comp_sm : StronglyMeasurable[MeasurableSpace.comap g m] (condExp m μ H ∘ g) :=
      h_sm.comp_measurable hf_meas_comap
    exact h_comp_sm.aestronglyMeasurable

/-! ### Lag-Constancy from Exchangeability: The Transposition Argument

This section proves that exchangeability implies lag-constancy for conditional
expectations. The proof uses Kallenberg's transposition argument:

1. For k ≥ 1, the transposition τ = swap(k, k+1) fixes index 0
2. Exchangeability gives measure invariance under reindex τ
3. Shift-invariant sets are preserved by reindex τ (they depend only on tails)
4. Therefore CE[f(ω₀)·g(ω_{k+1}) | ℐ] = CE[f(ω₀)·g(ω_k) | ℐ]

**Key lemmas:**
- `shift_reindex_swap_eq`: For m > k+1, shift^m ∘ reindex τ = shift^m
- `reindex_swap_preimage_shiftInvariant`: Shift-invariant sets are τ-invariant
- `condexp_lag_constant_from_exchangeability`: The main result
-/

section LagConstancyProof

variable {α : Type*} [MeasurableSpace α]

omit [MeasurableSpace α] in
/-- Shift^m applied to reindex (swap k (k+1)) ω equals shift^m applied to ω when m > k + 1.

This is because the swap only affects coordinates k and k+1, which are "shifted away"
after m iterations of shift when m > k + 1. -/
-- Helper: iterated shift satisfies shift^[j] ξ n = ξ (n + j)
private lemma shift_iterate_apply (j n : ℕ) (ξ : ℕ → α) :
    ((shift (α := α))^[j] ξ) n = ξ (n + j) := by
  induction j generalizing n with
  | zero => simp
  | succ j ih =>
    simp only [Function.iterate_succ', Function.comp_apply, shift_apply, ih]; ring_nf

omit [MeasurableSpace α] in
private lemma shift_iterate_reindex_swap_eq (k m : ℕ) (hm : k + 1 < m) (ω : ℕ → α) :
    shift^[m] (Exchangeability.reindex (Equiv.swap k (k + 1)) ω) = shift^[m] ω := by
  ext n; rw [shift_iterate_apply, shift_iterate_apply, Exchangeability.reindex_apply,
    Equiv.swap_apply_of_ne_of_ne (by omega : n + m ≠ k) (by omega : n + m ≠ k + 1)]

/-- Preimages of shift-invariant sets under reindex (swap k (k+1)) are the same set.

**Proof strategy**: A set s is shift-invariant iff membership depends only on tails.
Since swap k (k+1) only affects coordinates k and k+1, for any n > k+1,
the n-tail of ω equals the n-tail of (reindex τ ω). By shift-invariance,
membership in s is determined by any tail, hence ω ∈ s ↔ (reindex τ ω) ∈ s. -/
lemma reindex_swap_preimage_shiftInvariant (k : ℕ) (s : Set (ℕ → α))
    (hs : isShiftInvariant (α := α) s) :
    (Exchangeability.reindex (Equiv.swap k (k + 1))) ⁻¹' s = s := by
  ext ω
  simp only [Set.mem_preimage]
  -- Use that s is shift-invariant: ω ∈ s ↔ shift^[m] ω ∈ s for any m
  obtain ⟨_, hs_shift⟩ := hs
  -- Key: shift⁻¹' s = s means ω ∈ s ↔ shift ω ∈ s, hence ω ∈ s ↔ shift^m ω ∈ s
  have h_iter : ∀ m, (shift (α := α))^[m] ⁻¹' s = s := by
    intro m
    induction m with
    | zero => simp
    | succ n ih =>
      calc shift^[n + 1] ⁻¹' s = shift^[n] ⁻¹' (shift ⁻¹' s) := by
              simp only [Function.iterate_succ', Set.preimage_comp]
        _ = shift^[n] ⁻¹' s := by rw [hs_shift]
        _ = s := ih
  -- Choose m = k + 2 > k + 1
  have hm : k + 1 < k + 2 := Nat.lt_succ_self _
  -- The key: shift^[k+2] (reindex τ ω) = shift^[k+2] ω
  have h_eq := shift_iterate_reindex_swap_eq k (k + 2) hm ω
  -- Use that s is shift^[k+2]-invariant: ω ∈ s ↔ shift^[k+2] ω ∈ s
  have h_iter_k2 := h_iter (k + 2)
  -- ω ∈ shift^[m] ⁻¹' s ↔ shift^[m] ω ∈ s, and h_iter_k2 says shift^[k+2] ⁻¹' s = s
  -- h_iter_k2 means: ξ ∈ s ↔ ξ ∈ shift^[k+2] ⁻¹' s ↔ shift^[k+2] ξ ∈ s
  -- Transport membership through shift^[k+2] using shift-invariance
  constructor <;> intro h <;> (rw [← h_iter_k2, Set.mem_preimage] at h ⊢; first | rwa [← h_eq] | rwa [h_eq])


omit [MeasurableSpace α] in
private lemma product_reindex_swap_eq (f g : α → ℝ) (k : ℕ) (hk : 0 < k) :
    (fun ω => f (ω 0) * g (ω (k + 1))) ∘ Exchangeability.reindex (Equiv.swap k (k + 1))
    = fun ω => f (ω 0) * g (ω k) := by
  ext ω; simp only [Function.comp_apply, Exchangeability.reindex_apply,
    Equiv.swap_apply_of_ne_of_ne (by omega : (0 : ℕ) ≠ k) (by omega : (0 : ℕ) ≠ k + 1),
    Equiv.swap_apply_right]

end LagConstancyProof

/-- For exchangeable measures, set integrals are equal for functions that agree on reindexing.
This is a key step in proving lag-constancy: ∫_s F = ∫_s G when F ∘ reindex τ = G
and the set s is shift-invariant (hence also reindex-invariant). -/
@[nolint unusedArguments]
lemma setIntegral_eq_of_reindex_eq
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α]
    {μ : Measure (ℕ → α)} [IsProbabilityMeasure μ]
    (τ : Equiv.Perm ℕ)
    (hμ_inv : Measure.map (Exchangeability.reindex τ) μ = μ)
    (F G : (ℕ → α) → ℝ)
    (hFG : F ∘ Exchangeability.reindex τ = G)
    (hF_meas : Measurable F)
    (s : Set (ℕ → α))
    (hs_meas : MeasurableSet s)
    (h_preimage : (Exchangeability.reindex τ) ⁻¹' s = s) :
    ∫ ω in s, F ω ∂μ = ∫ ω in s, G ω ∂μ := by
  have hτ_meas : Measurable (Exchangeability.reindex (α := α) τ) :=
    Exchangeability.measurable_reindex (α := α) (π := τ)
  have hF' : AEStronglyMeasurable F (Measure.map (Exchangeability.reindex τ) μ) := by
    rw [hμ_inv]; exact hF_meas.aestronglyMeasurable
  calc ∫ ω in s, F ω ∂μ
      = ∫ ω in s, F ω ∂(Measure.map (Exchangeability.reindex τ) μ) := by rw [hμ_inv]
    _ = ∫ ω in (Exchangeability.reindex τ) ⁻¹' s, F ((Exchangeability.reindex τ) ω) ∂μ :=
        setIntegral_map hs_meas hF' hτ_meas.aemeasurable
    _ = ∫ ω in s, F ((Exchangeability.reindex τ) ω) ∂μ := by rw [h_preimage]
    _ = ∫ ω in s, G ω ∂μ := by congr 1

/-- If ∫_s (F - G) = 0 for all s in sub-σ-algebra, then CE[F|m] = CE[G|m] a.e. -/
@[nolint unusedArguments]
lemma condExp_ae_eq_of_setIntegral_diff_eq_zero
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α]
    {μ : Measure (ℕ → α)} [IsProbabilityMeasure μ]
    {F G : (ℕ → α) → ℝ}
    (hF_int : Integrable F μ)
    (hG_int : Integrable G μ)
    (h_diff_zero : ∀ s, MeasurableSet[shiftInvariantSigma (α := α)] s → μ s < ⊤ →
        ∫ ω in s, (F - G) ω ∂μ = 0) :
    μ[F | shiftInvariantSigma (α := α)] =ᵐ[μ] μ[G | shiftInvariantSigma (α := α)] := by
  have hm := shiftInvariantSigma_le (α := α)
  have hFG_int : Integrable (F - G) μ := hF_int.sub hG_int
  -- Step 1: 0 =ᵐ CE[F-G|mSI] since both have same integrals over mSI-sets
  have h_zero_eq_ce : (0 : (ℕ → α) → ℝ) =ᵐ[μ] μ[F - G | shiftInvariantSigma (α := α)] :=
    ae_eq_condExp_of_forall_setIntegral_eq hm hFG_int
      (fun _ _ _ => integrableOn_zero)
      (fun s hs hμs => by simp only [Pi.zero_apply, integral_zero, h_diff_zero s hs hμs])
      aestronglyMeasurable_zero
  -- Step 2: CE[F-G|mSI] = 0 a.e.
  have h_ce_diff_zero : μ[F - G | shiftInvariantSigma (α := α)] =ᵐ[μ] 0 := h_zero_eq_ce.symm
  -- Step 3: CE[F-G|mSI] = CE[F|mSI] - CE[G|mSI] by linearity
  have h_ce_sub : μ[F - G | shiftInvariantSigma (α := α)] =ᵐ[μ]
      μ[F | shiftInvariantSigma (α := α)] - μ[G | shiftInvariantSigma (α := α)] :=
    condExp_sub hF_int hG_int (shiftInvariantSigma (α := α))
  -- Step 4: Combine to get CE[F|mSI] - CE[G|mSI] = 0, hence CE[F|mSI] = CE[G|mSI]
  have h_eq := h_ce_sub.symm.trans h_ce_diff_zero
  exact h_eq.mono fun ω hω => sub_eq_zero.mp hω

/-- **Lag-constancy from exchangeability via transpositions** (Kallenberg's approach).

For EXCHANGEABLE measures μ on path space, the conditional expectation
CE[f(ω₀)·g(ω_{k+1}) | ℐ] equals CE[f(ω₀)·g(ω_k) | ℐ] for k ≥ 1.

**Key insight**: This uses EXCHANGEABILITY (not just stationarity). The proof is:
1. Let τ be the transposition swapping indices k and k+1
2. Exchangeability gives: Measure.map (reindex τ) μ = μ
3. Since k ≥ 1, τ fixes 0: τ(0) = 0
4. Therefore: CE[f(ω₀)·g(ω_{k+1}) | ℐ] = CE[(f∘τ)(ω₀)·(g∘τ)(ω_{k+1}) | ℐ]
                                        = CE[f(ω₀)·g(ω_k) | ℐ]

**Why k ≥ 1 is required (CRITICAL)**:
- When k=0, τ = swap(0, 1) does NOT fix 0 (τ sends 0 ↦ 1)
- So (f∘τ)(ω₀) = f(ω₁) ≠ f(ω₀), breaking the argument
- Counterexample for k=0: i.i.d. Bernoulli(1/2):
  * CE[ω₀·ω₁ | ℐ] = E[ω₀]·E[ω₁] = 1/4
  * CE[ω₀² | ℐ] = E[ω₀²] = 1/2 (since ω₀ ∈ {0,1})
  * These are NOT equal!

**Why stationarity alone is NOT enough**: Stationary non-exchangeable processes
(Markov chains, AR processes) can have lag-dependent conditional correlations.
The transposition trick requires the FULL permutation invariance of exchangeability. -/
lemma condexp_lag_constant_from_exchangeability
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α]
    {μ : Measure (ℕ → α)} [IsProbabilityMeasure μ]
    (hExch : ∀ π : Equiv.Perm ℕ, Measure.map (Exchangeability.reindex π) μ = μ)
    (f g : α → ℝ)
    (hf_meas : Measurable f) (hf_bd : ∃ C, ∀ x, |f x| ≤ C)
    (hg_meas : Measurable g) (hg_bd : ∃ C, ∀ x, |g x| ≤ C)
    (k : ℕ) (hk : 0 < k) :
    μ[(fun ω => f (ω 0) * g (ω (k + 1))) | shiftInvariantSigma (α := α)]
      =ᵐ[μ]
    μ[(fun ω => f (ω 0) * g (ω k)) | shiftInvariantSigma (α := α)] := by
  -- Define the transposition τ = swap k (k+1)
  let τ := Equiv.swap k (k + 1)
  -- Define the two functions
  let F := fun ω : ℕ → α => f (ω 0) * g (ω (k + 1))
  let G := fun ω : ℕ → α => f (ω 0) * g (ω k)
  -- Key fact 1: F ∘ reindex τ = G
  have hFG : F ∘ Exchangeability.reindex τ = G := product_reindex_swap_eq f g k hk
  -- Key fact 2: μ.map (reindex τ) = μ (exchangeability)
  have hμ_inv : Measure.map (Exchangeability.reindex τ) μ = μ := hExch τ
  -- Key fact 3: reindex τ is measurable
  have hτ_meas : Measurable (Exchangeability.reindex (α := α) τ) :=
    Exchangeability.measurable_reindex (α := α) (π := τ)
  -- Both F and G are integrable (bounded measurable on probability space)
  obtain ⟨Cf, hCf⟩ := hf_bd
  obtain ⟨Cg, hCg⟩ := hg_bd
  have hF_meas : Measurable F := (hf_meas.comp (measurable_pi_apply 0)).mul
                                  (hg_meas.comp (measurable_pi_apply (k + 1)))
  have hG_meas : Measurable G := (hf_meas.comp (measurable_pi_apply 0)).mul
                                  (hg_meas.comp (measurable_pi_apply k))
  have hF_bd : ∀ ω, ‖F ω‖ ≤ Cf * Cg := fun ω => by
    simp only [Real.norm_eq_abs]
    calc |F ω| = |f (ω 0) * g (ω (k + 1))| := rfl
      _ = |f (ω 0)| * |g (ω (k + 1))| := abs_mul _ _
      _ ≤ Cf * Cg := mul_le_mul (hCf _) (hCg _) (abs_nonneg _)
                       (le_trans (abs_nonneg _) (hCf (ω 0)))
  have hG_bd : ∀ ω, ‖G ω‖ ≤ Cf * Cg := fun ω => by
    simp only [Real.norm_eq_abs]
    calc |G ω| = |f (ω 0) * g (ω k)| := rfl
      _ = |f (ω 0)| * |g (ω k)| := abs_mul _ _
      _ ≤ Cf * Cg := mul_le_mul (hCf _) (hCg _) (abs_nonneg _)
                       (le_trans (abs_nonneg _) (hCf (ω 0)))
  have hF_int : Integrable F μ := Integrable.of_bound hF_meas.aestronglyMeasurable (Cf * Cg)
    (Filter.Eventually.of_forall hF_bd)
  have hG_int : Integrable G μ := Integrable.of_bound hG_meas.aestronglyMeasurable (Cf * Cg)
    (Filter.Eventually.of_forall hG_bd)
  -- Strategy: Show ∫_s F = ∫_s G for all s ∈ mSI, then μ[F|mSI] = μ[G|mSI]
  have h_int_eq : ∀ s, MeasurableSet[shiftInvariantSigma (α := α)] s → μ s < ⊤ →
      ∫ ω in s, F ω ∂μ = ∫ ω in s, G ω ∂μ := fun s hs _ => by
    have hs_inv : isShiftInvariant (α := α) s := (mem_shiftInvariantSigma_iff (α := α)).mp hs
    exact setIntegral_eq_of_reindex_eq τ hμ_inv F G hFG hF_meas s hs_inv.1
      (reindex_swap_preimage_shiftInvariant k s hs_inv)
  -- Show ∫_s (F - G) = 0 for all s ∈ mSI, then use helper lemma
  have h_diff_zero : ∀ s, MeasurableSet[shiftInvariantSigma (α := α)] s → μ s < ⊤ →
      ∫ ω in s, (F - G) ω ∂μ = 0 := fun s hs hμs => by
    simp only [Pi.sub_apply, integral_sub hF_int.integrableOn hG_int.integrableOn,
               h_int_eq s hs hμs, sub_self]
  exact condExp_ae_eq_of_setIntegral_diff_eq_zero hF_int hG_int h_diff_zero

end Exchangeability.DeFinetti.ViaKoopman
