/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer, Claude (Anthropic)
-/
import Exchangeability.Tail.TailSigma
import Exchangeability.PathSpace.Shift
import Exchangeability.Contractability
import Exchangeability.Core
import Mathlib.MeasureTheory.PiSystem

/-!
# Shift Invariance of Tail σ-Algebra for Exchangeable Sequences

This file proves that for exchangeable (contractable) sequences, the tail σ-algebra
is shift-invariant. Specifically, for contractable sequences:

  ∫_A f(X_k) dμ = ∫_A f(X_0) dμ

for all k ∈ ℕ and tail-measurable sets A.

## Main results

* `tailSigma_shift_invariant_for_contractable`: The law of the shifted process equals
  the law of the original process.
* `setIntegral_comp_shift_eq`: Set integrals over tail-measurable sets are shift-invariant.

## Implementation notes

The proofs use the fact that exchangeability implies the measure is invariant under
permutations, and the tail σ-algebra "forgets" finite initial segments.

## References

- Kallenberg (2005), *Probabilistic Symmetries and Invariance Principles*, Chapter 1
- Fristedt-Gray (1997), *A Modern Approach to Probability Theory*, Section II.4
-/

open MeasureTheory
open Exchangeability.PathSpace (shift)
open Exchangeability.Tail

namespace Exchangeability.Tail.ShiftInvariance

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ## Shift Invariance of Tail σ-Algebra

The key insight: For exchangeable sequences, shifting indices doesn't affect events
that depend only on the "tail" of the sequence (events determined by the behavior
far out in the sequence).

Mathematically: If X is exchangeable and E ∈ tailSigma X, then:
  {ω : X₀(ω), X₁(ω), X₂(ω), ... ∈ E} = {ω : X₁(ω), X₂(ω), X₃(ω), ... ∈ E}

This is because permuting the first element doesn't affect tail events.
-/

/-- **Tail σ-algebra is shift-invariant for exchangeable sequences.**

For an exchangeable sequence X, the law of the shifted process equals the law
of the original process:

  Measure.map (fun ω i => X (1 + i) ω) μ = Measure.map (fun ω i => X i ω) μ

**Intuition:** Tail events depend only on the behavior "at infinity" - they don't
care about the first finitely many coordinates. Exchangeability means we can permute
finite initial segments without changing the distribution, so in particular we can
"drop" the first element.
-/
lemma tailSigma_shift_invariant_for_contractable
    (X : ℕ → Ω → α)
    (hX : Exchangeability.Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i)) :
    Measure.map (fun ω i => X (1 + i) ω) μ =
      Measure.map (fun ω i => X i ω) μ := by
  -- Use measure_eq_of_fin_marginals_eq_prob: two probability measures on ℕ → α
  -- are equal if all finite marginals agree

  -- Define the two measures on ℕ → α
  let ν₁ := Measure.map (fun ω i => X (1 + i) ω) μ
  let ν₂ := Measure.map (fun ω i => X i ω) μ

  -- Both are probability measures
  have h_meas_shifted : Measurable (fun ω i => X (1 + i) ω) :=
    measurable_pi_lambda _ (fun i => hX_meas (1 + i))
  have h_meas_orig : Measurable (fun ω i => X i ω) :=
    measurable_pi_lambda _ hX_meas
  haveI : IsProbabilityMeasure ν₁ := Measure.isProbabilityMeasure_map h_meas_shifted.aemeasurable
  haveI : IsProbabilityMeasure ν₂ := Measure.isProbabilityMeasure_map h_meas_orig.aemeasurable

  -- Apply finite marginals theorem
  apply Exchangeability.measure_eq_of_fin_marginals_eq_prob (α := α)

  -- For each n, show finite marginals agree
  intro n S hS

  -- Compute finite marginals via Measure.map_map
  have h_prefix_meas : Measurable (Exchangeability.prefixProj (α := α) n) :=
    Exchangeability.measurable_prefixProj (α := α) (n := n)

  -- LHS: Measure.map (prefixProj n) (Measure.map (fun ω i => X (1 + i) ω) μ)
  --    = Measure.map (prefixProj n ∘ (fun ω i => X (1 + i) ω)) μ
  --    = Measure.map (fun ω (i : Fin n) => X (1 + i) ω) μ
  rw [Measure.map_map h_prefix_meas h_meas_shifted]
  rw [Measure.map_map h_prefix_meas h_meas_orig]

  -- Now the goal is about Measure.map of two compositions
  -- Show they're equal function compositions
  have h_lhs : (Exchangeability.prefixProj (α := α) n ∘ fun ω i => X (1 + i) ω)
      = (fun ω (i : Fin n) => X (1 + i.val) ω) := by
    funext ω i
    simp only [Function.comp_apply, Exchangeability.prefixProj]
  have h_rhs : (Exchangeability.prefixProj (α := α) n ∘ fun ω i => X i ω)
      = (fun ω (i : Fin n) => X i.val ω) := by
    funext ω i
    simp only [Function.comp_apply, Exchangeability.prefixProj]

  rw [h_lhs, h_rhs]

  -- Now apply shift_segment_eq
  have h_shift := Exchangeability.Contractable.shift_segment_eq hX n 1
  -- h_shift : Measure.map (fun ω (i : Fin n) => X (1 + i.val) ω) μ =
  --           Measure.map (fun ω (i : Fin n) => X i.val ω) μ
  rw [h_shift]

/-- **Key helper: Integral equality on cylinder sets via contractability.**

For indices k+1 < N ≤ N+M (forming a strictly increasing sequence), the integral
∫_{C} f(X_{k+1}) dμ equals ∫_{C} f(X_0) dμ where C = {ω : (X_N(ω), ..., X_{N+M}(ω)) ∈ S}.

This follows because both sequences (k+1, N, ..., N+M) and (0, N, ..., N+M) are strictly
increasing, so by contractability both have the same law as (0, 1, ..., M+1). -/
private lemma setIntegral_cylinder_eq
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → α)
    (hX_contract : Exchangeability.Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (f : α → ℝ)
    (hf_meas : Measurable f)
    (_hf_int : Integrable (f ∘ X 0) μ)
    (k N M : ℕ) (hN : k + 1 < N)
    (S : Set (Fin (M + 2) → α)) (_hS : MeasurableSet S) :
    let C : Set Ω := {ω | (fun i => X (N + i.val) ω) ∈ S}
    ∫ ω in C, f (X (k + 1) ω) ∂μ = ∫ ω in C, f (X 0 ω) ∂μ := by
  -- Define the index sequences
  let σ : Fin (M + 3) → ℕ := fun i => if i.val = 0 then k + 1 else N + (i.val - 1)
  let τ : Fin (M + 3) → ℕ := fun i => if i.val = 0 then 0 else N + (i.val - 1)

  -- σ is strictly increasing
  have hσ_strictMono : StrictMono σ := by
    intro i j hij
    simp only [σ]
    by_cases hi : i.val = 0
    · simp only [hi, ↓reduceIte]
      have hj_pos : 0 < j.val := by omega
      simp only [Nat.ne_of_gt hj_pos, ↓reduceIte]
      omega
    · simp only [hi, ↓reduceIte]
      have hj_pos : 0 < j.val := by omega
      simp only [Nat.ne_of_gt hj_pos, ↓reduceIte]
      omega

  -- τ is strictly increasing
  have hτ_strictMono : StrictMono τ := by
    intro i j hij
    simp only [τ]
    by_cases hi : i.val = 0
    · simp only [hi, ↓reduceIte]
      have hj_pos : 0 < j.val := by omega
      simp only [Nat.ne_of_gt hj_pos, ↓reduceIte]
      omega
    · simp only [hi, ↓reduceIte]
      have hj_pos : 0 < j.val := by omega
      simp only [Nat.ne_of_gt hj_pos, ↓reduceIte]
      omega

  -- By contractability, both push-forward measures equal the reference measure
  have h_eq_σ := hX_contract (M + 3) σ hσ_strictMono
  have h_eq_τ := hX_contract (M + 3) τ hτ_strictMono

  -- Therefore σ and τ give the same push-forward measure
  have h_eq : Measure.map (fun ω i => X (σ i) ω) μ = Measure.map (fun ω i => X (τ i) ω) μ := by
    rw [h_eq_σ, h_eq_τ]

  -- Define the joint function g : (Fin (M+3) → α) → ℝ
  let g : (Fin (M + 3) → α) → ℝ := fun z =>
    f (z ⟨0, by omega⟩) * (S.indicator 1 (fun i : Fin (M + 2) => z ⟨i.val + 1, by omega⟩))

  -- Verify σ and τ agree on tail indices
  have h_agree : ∀ i : Fin (M + 2), σ ⟨i.val + 1, by omega⟩ = τ ⟨i.val + 1, by omega⟩ := by
    intro i
    simp only [σ, τ, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]

  let C' : Set Ω := {ω | (fun i => X (N + i.val) ω) ∈ S}
  have hC_C' : C' = {ω | (fun i => X (N + i.val) ω) ∈ S} := rfl

  have hσ_meas : Measurable (fun ω i => X (σ i) ω) :=
    measurable_pi_lambda _ (fun i => hX_meas (σ i))
  have hτ_meas : Measurable (fun ω i => X (τ i) ω) :=
    measurable_pi_lambda _ (fun i => hX_meas (τ i))

  have hσ_0 : σ ⟨0, by omega⟩ = k + 1 := by simp only [σ, ↓reduceIte]
  have hτ_0 : τ ⟨0, by omega⟩ = 0 := by simp only [τ, ↓reduceIte]

  have hσ_tail : ∀ i : Fin (M + 2), σ ⟨i.val + 1, by omega⟩ = N + i.val := by
    intro i
    simp only [σ, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]

  have hτ_tail : ∀ i : Fin (M + 2), τ ⟨i.val + 1, by omega⟩ = N + i.val := by
    intro i
    simp only [τ, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]

  have hS_σ : ∀ ω, ((fun i : Fin (M + 2) => X (σ ⟨i.val + 1, by omega⟩) ω) ∈ S) ↔ ω ∈ C' := by
    intro ω
    simp only [Set.mem_setOf_eq, C']
    constructor
    · intro h; convert h using 1
    · intro h; convert h using 1

  have hS_τ : ∀ ω, ((fun i : Fin (M + 2) => X (τ ⟨i.val + 1, by omega⟩) ω) ∈ S) ↔ ω ∈ C' := by
    intro ω
    simp only [Set.mem_setOf_eq, C']
    constructor
    · intro h; convert h using 1
    · intro h; convert h using 1

  have hg_σ : ∀ ω, g (fun i => X (σ i) ω) = f (X (k + 1) ω) * (C'.indicator 1 ω) := by
    intro ω
    simp only [g, hσ_0]
    by_cases hω : ω ∈ C'
    · have hS_mem : (fun i : Fin (M + 2) => X (σ ⟨i.val + 1, by omega⟩) ω) ∈ S := (hS_σ ω).mpr hω
      rw [Set.indicator_of_mem hω, Set.indicator_of_mem hS_mem]
      simp only [Pi.one_apply, mul_one]
    · have hS_nmem : (fun i : Fin (M + 2) => X (σ ⟨i.val + 1, by omega⟩) ω) ∉ S :=
        fun h => hω ((hS_σ ω).mp h)
      rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hS_nmem]

  have hg_τ : ∀ ω, g (fun i => X (τ i) ω) = f (X 0 ω) * (C'.indicator 1 ω) := by
    intro ω
    simp only [g, hτ_0]
    by_cases hω : ω ∈ C'
    · have hS_mem : (fun i : Fin (M + 2) => X (τ ⟨i.val + 1, by omega⟩) ω) ∈ S := (hS_τ ω).mpr hω
      rw [Set.indicator_of_mem hω, Set.indicator_of_mem hS_mem]
      simp only [Pi.one_apply, mul_one]
    · have hS_nmem : (fun i : Fin (M + 2) => X (τ ⟨i.val + 1, by omega⟩) ω) ∉ S :=
        fun h => hω ((hS_τ ω).mp h)
      rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hS_nmem]

  have hC'_meas : MeasurableSet C' := by
    apply MeasurableSet.preimage _hS
    exact measurable_pi_lambda _ (fun i => hX_meas (N + i.val))

  have h_ind_eq : ∀ (h : α → ℝ) (ω : Ω),
      C'.indicator (fun ω => h (X 0 ω)) ω = h (X 0 ω) * (C'.indicator 1 ω) := by
    intro h ω
    by_cases hω : ω ∈ C'
    · simp [Set.indicator_of_mem hω]
    · simp [Set.indicator_of_notMem hω]

  have h_ind_eq_k : ∀ (ω : Ω),
      C'.indicator (fun ω => f (X (k + 1) ω)) ω = f (X (k + 1) ω) * (C'.indicator 1 ω) := by
    intro ω
    by_cases hω : ω ∈ C'
    · simp [Set.indicator_of_mem hω]
    · simp [Set.indicator_of_notMem hω]

  calc ∫ ω in C', f (X (k + 1) ω) ∂μ
      = ∫ ω, C'.indicator (fun ω => f (X (k + 1) ω)) ω ∂μ := by
          rw [← integral_indicator hC'_meas]
    _ = ∫ ω, f (X (k + 1) ω) * (C'.indicator 1 ω) ∂μ := by
          apply integral_congr_ae
          filter_upwards with ω
          exact h_ind_eq_k ω
    _ = ∫ ω, g (fun i => X (σ i) ω) ∂μ := by
          apply integral_congr_ae
          filter_upwards with ω
          rw [hg_σ]
    _ = ∫ z, g z ∂(Measure.map (fun ω i => X (σ i) ω) μ) := by
          rw [integral_map hσ_meas.aemeasurable]
          apply Measurable.aestronglyMeasurable
          apply Measurable.mul
          · exact hf_meas.comp (measurable_pi_apply _)
          · apply Measurable.indicator measurable_const
            exact MeasurableSet.preimage _hS (measurable_pi_lambda _ (fun i => measurable_pi_apply _))
    _ = ∫ z, g z ∂(Measure.map (fun ω i => X (τ i) ω) μ) := by rw [h_eq]
    _ = ∫ ω, g (fun i => X (τ i) ω) ∂μ := by
          rw [← integral_map hτ_meas.aemeasurable]
          apply Measurable.aestronglyMeasurable
          apply Measurable.mul
          · exact hf_meas.comp (measurable_pi_apply _)
          · apply Measurable.indicator measurable_const
            exact MeasurableSet.preimage _hS (measurable_pi_lambda _ (fun i => measurable_pi_apply _))
    _ = ∫ ω, f (X 0 ω) * (C'.indicator 1 ω) ∂μ := by
          apply integral_congr_ae
          filter_upwards with ω
          rw [hg_τ]
    _ = ∫ ω, C'.indicator (fun ω => f (X 0 ω)) ω ∂μ := by
          apply integral_congr_ae
          filter_upwards with ω
          exact (h_ind_eq f ω).symm
    _ = ∫ ω in C', f (X 0 ω) ∂μ := by rw [← integral_indicator hC'_meas]

/-- **Key lemma: Set integrals over tail-measurable sets are shift-invariant.**

For a contractable sequence X and tail-measurable set A, the integral ∫_A f(X_k) dμ
does not depend on k. This follows from the measure-theoretic shift invariance:
- The law of the process (X_0, X_1, ...) on (ℕ → α) is shift-invariant
- Tail-measurable sets correspond to shift-invariant sets in path space
- The integral identity follows from measure invariance
-/
lemma setIntegral_comp_shift_eq
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → α)
    (hX_contract : Exchangeability.Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (f : α → ℝ)
    (hf_meas : Measurable f)
    {A : Set Ω}
    (hA : MeasurableSet[tailProcess X] A)
    (hf_int : Integrable (f ∘ X 0) μ)
    (k : ℕ) :
    ∫ ω in A, f (X k ω) ∂μ = ∫ ω in A, f (X 0 ω) ∂μ := by
  -- For k = 0, trivial
  cases k with
  | zero => rfl
  | succ k =>
    -- The measure equality from shift invariance
    have h_shift := tailSigma_shift_invariant_for_contractable X hX_contract hX_meas

    -- X_{k+1} and X_0 have the same distribution (from contractability)
    have hX_k1_eq_X0 : Measure.map (X (k + 1)) μ = Measure.map (X 0) μ := by
      have h1 := Exchangeability.Contractable.shift_segment_eq hX_contract 1 (k + 1)
      ext s hs
      let S : Set (Fin 1 → α) := {g | g 0 ∈ s}
      have hS : MeasurableSet S := measurable_pi_apply 0 hs
      have h_meas_k1 : Measurable (fun ω (i : Fin 1) => X ((k + 1) + i.val) ω) :=
        measurable_pi_lambda _ (fun i => hX_meas ((k + 1) + i.val))
      have h_meas_0 : Measurable (fun ω (i : Fin 1) => X i.val ω) :=
        measurable_pi_lambda _ (fun i => hX_meas i.val)
      rw [Measure.map_apply (hX_meas (k + 1)) hs, Measure.map_apply (hX_meas 0) hs]
      have h_pre_k1 : X (k + 1) ⁻¹' s = (fun ω (i : Fin 1) => X ((k + 1) + i.val) ω) ⁻¹' S := by
        ext ω
        simp only [Set.mem_preimage, Set.mem_setOf_eq, S, Fin.val_zero, add_zero]
      have h_pre_0 : X 0 ⁻¹' s = (fun ω (i : Fin 1) => X i.val ω) ⁻¹' S := by
        ext ω
        simp only [Set.mem_preimage, Set.mem_setOf_eq, S, Fin.val_zero]
      rw [h_pre_k1, h_pre_0]
      have h_eq := congrFun (congrArg (·.toOuterMeasure) h1) S
      simp only [Measure.coe_toOuterMeasure] at h_eq
      rw [Measure.map_apply h_meas_k1 hS, Measure.map_apply h_meas_0 hS] at h_eq
      exact h_eq

    -- Integrability transfer
    have hf_int_k1 : Integrable (f ∘ X (k + 1)) μ := by
      have hf_aesm : AEStronglyMeasurable f (Measure.map (X 0) μ) := hf_meas.aestronglyMeasurable
      have h_int_map : Integrable f (Measure.map (X 0) μ) :=
        (integrable_map_measure hf_aesm (hX_meas 0).aemeasurable).mpr hf_int
      rw [← hX_k1_eq_X0] at h_int_map
      exact (integrable_map_measure hf_meas.aestronglyMeasurable
        (hX_meas (k + 1)).aemeasurable).mp h_int_map

    -- A ∈ tailFamily X N for N = k + 2 > k + 1
    let N := k + 2
    have hN_gt : k + 1 < N := by omega
    have hA_tailFam : MeasurableSet[tailFamily X N] A := (tailProcess_le_tailFamily X N) A hA

    -- Full-space integral equality (needed for complement closure)
    have h_full : ∫ ω, f (X (k + 1) ω) ∂μ = ∫ ω, f (X 0 ω) ∂μ := by
      calc ∫ ω, f (X (k + 1) ω) ∂μ
          = ∫ x, f x ∂(Measure.map (X (k + 1)) μ) := by
              rw [integral_map (hX_meas (k + 1)).aemeasurable hf_meas.aestronglyMeasurable]
        _ = ∫ x, f x ∂(Measure.map (X 0) μ) := by rw [hX_k1_eq_X0]
        _ = ∫ ω, f (X 0 ω) ∂μ := by
              rw [← integral_map (hX_meas 0).aemeasurable hf_meas.aestronglyMeasurable]

    -- Define the coordinate σ-algebras
    let m : ℕ → MeasurableSpace Ω := fun j => MeasurableSpace.comap (fun ω => X (N + j) ω) inferInstance

    have h_tailFam_eq_iSup : tailFamily X N = ⨆ j, m j := by
      simp only [tailFamily, m]

    let π : Set (Set Ω) := piiUnionInter (fun j => {s | MeasurableSet[m j] s}) Set.univ

    have hπ_isPiSystem : IsPiSystem π := by
      exact isPiSystem_piiUnionInter (fun j => {s | MeasurableSet[m j] s})
        (fun j => @MeasurableSpace.isPiSystem_measurableSet Ω (m j)) Set.univ

    have h_gen : tailFamily X N = MeasurableSpace.generateFrom π := by
      rw [h_tailFam_eq_iSup]
      have := generateFrom_piiUnionInter_measurableSet m Set.univ
      simp only [Set.mem_univ, iSup_true] at this
      exact this.symm

    have h_meas_le : tailFamily X N ≤ (inferInstance : MeasurableSpace Ω) := by
      apply iSup_le
      intro j
      exact (hX_meas (N + j)).comap_le

    let P : (s : Set Ω) → MeasurableSet[tailFamily X N] s → Prop :=
      fun s _ => ∫ ω in s, f (X (k + 1) ω) ∂μ = ∫ ω in s, f (X 0 ω) ∂μ

    refine MeasurableSpace.induction_on_inter h_gen hπ_isPiSystem ?_ ?_ ?_ ?_ A hA_tailFam

    -- Case 1: Empty Set
    · simp only [setIntegral_empty]

    -- Case 2: Elements of π-System (Cylinder Sets)
    · intro t ht
      rcases ht with ⟨pt, _, ft, ht_m, rfl⟩

      by_cases hpt_empty : pt = ∅
      · simp only [hpt_empty, Finset.notMem_empty, Set.iInter_of_empty, Set.iInter_univ]
        simp only [setIntegral_univ]
        exact h_full

      let indices : List ℕ := pt.sort (· ≤ ·)
      have h_sorted : indices.SortedLT := pt.sortedLT_sort
      have h_nodup : indices.Nodup := pt.sort_nodup (· ≤ ·)
      have h_indices_ne : indices ≠ [] := by
        simp only [indices, ne_eq, List.eq_nil_iff_forall_not_mem]
        intro h
        apply hpt_empty
        ext x
        simp only [Finset.notMem_empty, iff_false]
        intro hx
        exact h x ((Finset.mem_sort _).mpr hx)

      let min_idx := indices.head h_indices_ne
      let d := pt.card
      have hd_pos : 0 < d := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hpt_empty)

      have h_len : indices.length = d := by
        simp only [indices, d, Finset.length_sort]

      let σ : Fin (d + 1) → ℕ := fun i =>
        if hi : i.val = 0 then k + 1
        else N + indices.get ⟨i.val - 1, by rw [h_len]; omega⟩

      let τ : Fin (d + 1) → ℕ := fun i =>
        if hi : i.val = 0 then 0
        else N + indices.get ⟨i.val - 1, by rw [h_len]; omega⟩

      have h_idx_sorted : ∀ i j : ℕ, (hi : i < d) → (hj : j < d) → i < j →
          indices.get ⟨i, by rw [h_len]; exact hi⟩ < indices.get ⟨j, by rw [h_len]; exact hj⟩ := by
        intro i j hi hj hij
        exact h_sorted.getElem_lt_getElem_iff.mpr hij

      have hσ_strictMono : StrictMono σ := by
        intro i j hij
        simp only [σ]
        by_cases hi : i.val = 0
        · simp only [hi, ↓reduceDIte]
          have hj_pos : 0 < j.val := by omega
          simp only [Nat.ne_of_gt hj_pos, ↓reduceDIte]
          omega
        · simp only [hi, ↓reduceDIte]
          have hj_pos : 0 < j.val := by omega
          simp only [Nat.ne_of_gt hj_pos, ↓reduceDIte]
          have h_ij : i.val - 1 < j.val - 1 := by omega
          have h_i_bd : i.val - 1 < d := by omega
          have h_j_bd : j.val - 1 < d := by omega
          have h1 := h_idx_sorted (i.val - 1) (j.val - 1) h_i_bd h_j_bd h_ij
          omega

      have hτ_strictMono : StrictMono τ := by
        intro i j hij
        simp only [τ]
        by_cases hi : i.val = 0
        · simp only [hi, ↓reduceDIte]
          have hj_pos : 0 < j.val := by omega
          simp only [Nat.ne_of_gt hj_pos, ↓reduceDIte]
          omega
        · simp only [hi, ↓reduceDIte]
          have hj_pos : 0 < j.val := by omega
          simp only [Nat.ne_of_gt hj_pos, ↓reduceDIte]
          have h_ij : i.val - 1 < j.val - 1 := by omega
          have h_i_bd : i.val - 1 < d := by omega
          have h_j_bd : j.val - 1 < d := by omega
          have h1 := h_idx_sorted (i.val - 1) (j.val - 1) h_i_bd h_j_bd h_ij
          omega

      have h_eq_σ := hX_contract (d + 1) σ hσ_strictMono
      have h_eq_τ := hX_contract (d + 1) τ hτ_strictMono
      have h_eq : Measure.map (fun ω i => X (σ i) ω) μ = Measure.map (fun ω i => X (τ i) ω) μ := by
        rw [h_eq_σ, h_eq_τ]

      have h_agree : ∀ i : Fin (d + 1), i.val ≠ 0 → σ i = τ i := by
        intro i hi
        simp only [σ, τ, hi, ↓reduceDIte]

      let C := ⋂ j ∈ pt, ft j

      have hC_meas : MeasurableSet C := by
        apply MeasurableSet.iInter
        intro j
        apply MeasurableSet.iInter
        intro hj
        have h1 : MeasurableSet[m j] (ft j) := ht_m j hj
        have h2 : m j ≤ tailFamily X N := le_iSup m j
        exact (h2.trans h_meas_le) (ft j) h1

      have hσ_0 : σ ⟨0, by omega⟩ = k + 1 := by simp only [σ, ↓reduceDIte]
      have hτ_0 : τ ⟨0, by omega⟩ = 0 := by simp only [τ, ↓reduceDIte]

      have hσ_meas : Measurable (fun ω i => X (σ i) ω) :=
        measurable_pi_lambda _ (fun i => hX_meas (σ i))
      have hτ_meas : Measurable (fun ω i => X (τ i) ω) :=
        measurable_pi_lambda _ (fun i => hX_meas (τ i))

      have hσ_succ : ∀ i : Fin d, σ ⟨i.val + 1, by omega⟩ =
          N + indices.get ⟨i.val, by rw [h_len]; exact i.isLt⟩ := by
        intro i
        simp only [σ, Nat.add_one_ne_zero, ↓reduceDIte, Nat.add_sub_cancel]

      have hτ_succ : ∀ i : Fin d, τ ⟨i.val + 1, by omega⟩ =
          N + indices.get ⟨i.val, by rw [h_len]; exact i.isLt⟩ := by
        intro i
        simp only [τ, Nat.add_one_ne_zero, ↓reduceDIte, Nat.add_sub_cancel]

      have h_preimage : ∀ j ∈ pt, ∃ (Tj : Set α), MeasurableSet Tj ∧
          ft j = (X (N + j))⁻¹' Tj := by
        intro j hj
        obtain ⟨Tj, hTj_meas, hTj_eq⟩ := MeasurableSpace.measurableSet_comap.mp (ht_m j hj)
        exact ⟨Tj, hTj_meas, hTj_eq.symm⟩

      choose Tj hTj using h_preimage

      let proj : (Fin (d + 1) → α) → (Fin d → α) := fun z i =>
        z ⟨i.val + 1, by omega⟩

      have hproj_meas : Measurable proj := by
        apply measurable_pi_lambda
        intro i
        exact measurable_pi_apply _

      have h_indices_mem : ∀ i : Fin d, indices.get ⟨i.val, by rw [h_len]; exact i.isLt⟩ ∈ pt := by
        intro i
        have hi_lt : i.val < indices.length := by rw [h_len]; exact i.isLt
        exact (Finset.mem_sort _).mp (List.get_mem indices ⟨i.val, hi_lt⟩)

      let S : Set (Fin d → α) := {y : Fin d → α | ∀ i : Fin d,
        y i ∈ Tj (indices.get ⟨i.val, by rw [h_len]; exact i.isLt⟩) (h_indices_mem i)}

      have hS_meas : MeasurableSet S := by
        have hS_eq : S = ⋂ i : Fin d, (fun y => y i) ⁻¹'
            Tj (indices.get ⟨i.val, by rw [h_len]; exact i.isLt⟩) (h_indices_mem i) := by
          ext y
          simp only [S, Set.mem_iInter, Set.mem_preimage, Set.mem_setOf_eq]
        rw [hS_eq]
        apply MeasurableSet.iInter
        intro i
        apply MeasurableSet.preimage (hTj _ (h_indices_mem i)).1
        exact measurable_pi_apply i

      have h_indices_surj : ∀ j ∈ pt, ∃ i : Fin d,
          indices.get ⟨i.val, by rw [h_len]; exact i.isLt⟩ = j := by
        intro j hj
        have h_mem_list : j ∈ indices := (Finset.mem_sort _).mpr hj
        obtain ⟨n, hn_eq⟩ := List.get_of_mem h_mem_list
        have hn_d : n.val < d := by rw [← h_len]; exact n.isLt
        exact ⟨⟨n.val, hn_d⟩, hn_eq⟩

      have h_C_iff_S : ∀ ω, ω ∈ C ↔ (fun i : Fin d =>
          X (σ ⟨i.val + 1, by omega⟩) ω) ∈ S := by
        intro ω
        constructor
        · intro hω
          simp only [S, Set.mem_setOf_eq]
          intro i
          have h_idx_mem := h_indices_mem i
          have hω_ft := (Set.mem_iInter.mp (Set.mem_iInter.mp hω
            (indices.get ⟨i.val, by rw [h_len]; exact i.isLt⟩))) h_idx_mem
          rw [(hTj _ h_idx_mem).2] at hω_ft
          simp only [Set.mem_preimage] at hω_ft
          rw [hσ_succ i]
          exact hω_ft
        · intro hS_mem
          simp only [C, Set.mem_iInter]
          intro j hj
          obtain ⟨i, hi_eq⟩ := h_indices_surj j hj
          rw [(hTj j hj).2]
          simp only [Set.mem_preimage]
          simp only [S, Set.mem_setOf_eq] at hS_mem
          subst hi_eq
          have h := hS_mem i
          simp only [hσ_succ] at h
          exact h

      have h_C_iff_S_τ : ∀ ω, ω ∈ C ↔ (fun i : Fin d =>
          X (τ ⟨i.val + 1, by omega⟩) ω) ∈ S := by
        intro ω
        rw [h_C_iff_S]
        suffices h : (fun i : Fin d => X (σ ⟨i.val + 1, by omega⟩) ω) =
                     (fun i : Fin d => X (τ ⟨i.val + 1, by omega⟩) ω) by
          rw [h]
        ext i
        rw [hσ_succ, hτ_succ]

      let g : (Fin (d + 1) → α) → ℝ := fun z =>
        f (z ⟨0, by omega⟩) * S.indicator 1 (proj z)

      have hg_meas : Measurable g := by
        apply Measurable.mul
        · exact hf_meas.comp (measurable_pi_apply _)
        · apply Measurable.indicator measurable_const
          exact hS_meas.preimage hproj_meas

      have hg_σ : ∀ ω, g (fun i => X (σ i) ω) =
          f (X (σ ⟨0, by omega⟩) ω) * C.indicator 1 ω := by
        intro ω
        simp only [g, proj]
        congr 1
        by_cases hC : ω ∈ C
        · have hS : (fun i : Fin d => X (σ ⟨i.val + 1, by omega⟩) ω) ∈ S :=
            (h_C_iff_S ω).mp hC
          simp only [Set.indicator_of_mem hS, Set.indicator_of_mem hC, Pi.one_apply]
        · have hS : (fun i : Fin d => X (σ ⟨i.val + 1, by omega⟩) ω) ∉ S :=
            fun h => hC ((h_C_iff_S ω).mpr h)
          simp only [Set.indicator_of_notMem hS, Set.indicator_of_notMem hC]

      have hg_τ : ∀ ω, g (fun i => X (τ i) ω) =
          f (X (τ ⟨0, by omega⟩) ω) * C.indicator 1 ω := by
        intro ω
        simp only [g, proj]
        congr 1
        by_cases hC : ω ∈ C
        · have hS : (fun i : Fin d => X (τ ⟨i.val + 1, by omega⟩) ω) ∈ S :=
            (h_C_iff_S_τ ω).mp hC
          simp only [Set.indicator_of_mem hS, Set.indicator_of_mem hC, Pi.one_apply]
        · have hS : (fun i : Fin d => X (τ ⟨i.val + 1, by omega⟩) ω) ∉ S :=
            fun h => hC ((h_C_iff_S_τ ω).mpr h)
          simp only [Set.indicator_of_notMem hS, Set.indicator_of_notMem hC]

      calc ∫ ω in C, f (X (k + 1) ω) ∂μ
          = ∫ ω, C.indicator (fun ω => f (X (k + 1) ω)) ω ∂μ := by
              rw [← integral_indicator hC_meas]
        _ = ∫ ω, f (X (σ ⟨0, by omega⟩) ω) * (C.indicator 1 ω) ∂μ := by
              apply integral_congr_ae
              filter_upwards with ω
              rw [hσ_0]
              by_cases hω : ω ∈ C
              · simp [Set.indicator_of_mem hω]
              · simp [Set.indicator_of_notMem hω]
        _ = ∫ ω, f (X (τ ⟨0, by omega⟩) ω) * (C.indicator 1 ω) ∂μ := by
              calc ∫ ω, f (X (σ ⟨0, by omega⟩) ω) * C.indicator 1 ω ∂μ
                  = ∫ ω, g (fun i => X (σ i) ω) ∂μ := by
                      apply integral_congr_ae
                      filter_upwards with ω
                      exact (hg_σ ω).symm
                _ = ∫ z, g z ∂(Measure.map (fun ω i => X (σ i) ω) μ) := by
                      rw [integral_map hσ_meas.aemeasurable hg_meas.aestronglyMeasurable]
                _ = ∫ z, g z ∂(Measure.map (fun ω i => X (τ i) ω) μ) := by rw [h_eq]
                _ = ∫ ω, g (fun i => X (τ i) ω) ∂μ := by
                      rw [← integral_map hτ_meas.aemeasurable hg_meas.aestronglyMeasurable]
                _ = ∫ ω, f (X (τ ⟨0, by omega⟩) ω) * C.indicator 1 ω ∂μ := by
                      apply integral_congr_ae
                      filter_upwards with ω
                      exact hg_τ ω
        _ = ∫ ω, C.indicator (fun ω => f (X 0 ω)) ω ∂μ := by
              apply integral_congr_ae
              filter_upwards with ω
              rw [hτ_0]
              by_cases hω : ω ∈ C
              · simp [Set.indicator_of_mem hω]
              · simp [Set.indicator_of_notMem hω]
        _ = ∫ ω in C, f (X 0 ω) ∂μ := by rw [← integral_indicator hC_meas]

    -- Case 3: Complement
    · intro t ht h_eq
      have h_meas_t : MeasurableSet t := h_meas_le t ht
      have hc1 := setIntegral_compl h_meas_t hf_int_k1
      have hc0 := setIntegral_compl h_meas_t hf_int
      simp only [Function.comp_apply] at hc1 hc0
      rw [hc1, hc0, h_full, h_eq]

    -- Case 4: Countable Disjoint Union
    · intro s h_disj h_meas h_eq
      have h_meas' : ∀ i, MeasurableSet (s i) := fun i => h_meas_le (s i) (h_meas i)
      have h_int_k1_on : IntegrableOn (fun ω => f (X (k + 1) ω)) (⋃ i, s i) μ :=
        hf_int_k1.integrableOn
      have h_int_0_on : IntegrableOn (fun ω => f (X 0 ω)) (⋃ i, s i) μ :=
        hf_int.integrableOn
      rw [integral_iUnion h_meas' h_disj h_int_k1_on]
      rw [integral_iUnion h_meas' h_disj h_int_0_on]
      congr 1
      ext i
      exact h_eq i

end Exchangeability.Tail.ShiftInvariance
