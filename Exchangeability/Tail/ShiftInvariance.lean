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
is shift-invariant, meaning:

  μ[f∘X_n | tailSigma X] = μ[f∘X_0 | tailSigma X]  a.e.

for all n ∈ ℕ.

## Main results

* `tailSigma_shift_invariant`: The tail σ-algebra is invariant under the shift operator
  for exchangeable sequences.
* `condExp_shift_eq_condExp`: Conditional expectations with respect to the tail σ-algebra
  are shift-invariant for exchangeable sequences.

## Implementation notes

This is the KEY infrastructure needed to:
1. Complete the asymptotic negligibility proof (generalize from n=0 to arbitrary n)
2. Provide an elegant alternative proof using shift invariance directly

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

/-- **BONUS THEOREM: Tail σ-algebra is shift-invariant for exchangeable sequences.**

For an exchangeable sequence X, events in the tail σ-algebra are invariant under
the shift operator. This means:

  E ∈ tailSigma X  ⟹  {ω : (shift (fun k => X k ω)) ∈ E} = {ω : (fun k => X k ω) ∈ E}

**Intuition:** Tail events depend only on the behavior "at infinity" - they don't
care about the first finitely many coordinates. Exchangeability means we can permute
finite initial segments without changing the distribution, so in particular we can
"drop" the first element.

**Proof strategy:**
1. Show that for any tail event E, we can approximate it by events that ignore
   the first n coordinates.
2. Use exchangeability to show that shifting doesn't affect such events.
3. Take limit as n → ∞.

**Status:** This is the key lemma we need. The proof requires careful use of:
- The definition of tail σ-algebra as ⨅ n, σ(X_n, X_{n+1}, ...)
- Exchangeability (or contractability) of the measure
- Approximation arguments for σ-algebras

For now, we leave this as sorry - proving it is the main technical work needed.
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
  -- PROOF STRATEGY:
  -- Define index sequences σ, τ : Fin (M+3) → ℕ where:
  --   σ(0) = k+1, σ(i+1) = N+i  (for i = 0, ..., M+1)
  --   τ(0) = 0,   τ(i+1) = N+i  (for i = 0, ..., M+1)
  -- Both are strictly increasing (since k+1 < N and 0 < N).
  -- By contractability, both Measure.map (fun ω i => X (σ i) ω) μ and
  -- Measure.map (fun ω i => X (τ i) ω) μ equal Measure.map (fun ω i => X i.val ω) μ.
  -- Therefore they're equal to each other.
  --
  -- Define g : (Fin (M+3) → α) → ℝ by g(z) = f(z 0) · S.indicator 1 (fun i => z ⟨i+1, _⟩).
  -- Then:
  --   ∫_C f(X_{k+1}) dμ = ∫ g(fun i => X (σ i) ω) dμ
  --                     = ∫ g dν₁  where ν₁ = (fun ω i => X (σ i) ω)_* μ
  --   ∫_C f(X_0) dμ     = ∫ g(fun i => X (τ i) ω) dμ
  --                     = ∫ g dν₂  where ν₂ = (fun ω i => X (τ i) ω)_* μ
  -- Since ν₁ = ν₂ by contractability, the integrals are equal.

  -- Define the index sequences
  let σ : Fin (M + 3) → ℕ := fun i => if i.val = 0 then k + 1 else N + (i.val - 1)
  let τ : Fin (M + 3) → ℕ := fun i => if i.val = 0 then 0 else N + (i.val - 1)

  -- σ is strictly increasing
  have hσ_strictMono : StrictMono σ := by
    intro i j hij
    simp only [σ]
    by_cases hi : i.val = 0
    · -- i.val = 0
      simp only [hi, ↓reduceIte]
      have hj_pos : 0 < j.val := by omega
      simp only [Nat.ne_of_gt hj_pos, ↓reduceIte]
      -- Need: k + 1 < N + (j.val - 1)
      omega
    · -- i.val > 0
      simp only [hi, ↓reduceIte]
      have hj_pos : 0 < j.val := by omega
      simp only [Nat.ne_of_gt hj_pos, ↓reduceIte]
      -- Need: N + (i.val - 1) < N + (j.val - 1)
      omega

  -- τ is strictly increasing
  have hτ_strictMono : StrictMono τ := by
    intro i j hij
    simp only [τ]
    by_cases hi : i.val = 0
    · -- i.val = 0
      simp only [hi, ↓reduceIte]
      have hj_pos : 0 < j.val := by omega
      simp only [Nat.ne_of_gt hj_pos, ↓reduceIte]
      -- Need: 0 < N + (j.val - 1), which is true since N > 0 (from hN)
      omega
    · -- i.val > 0
      simp only [hi, ↓reduceIte]
      have hj_pos : 0 < j.val := by omega
      simp only [Nat.ne_of_gt hj_pos, ↓reduceIte]
      -- Need: N + (i.val - 1) < N + (j.val - 1)
      omega

  -- By contractability, both push-forward measures equal the reference measure
  have h_eq_σ := hX_contract (M + 3) σ hσ_strictMono
  have h_eq_τ := hX_contract (M + 3) τ hτ_strictMono

  -- Therefore σ and τ give the same push-forward measure
  have h_eq : Measure.map (fun ω i => X (σ i) ω) μ = Measure.map (fun ω i => X (τ i) ω) μ := by
    rw [h_eq_σ, h_eq_τ]

  -- Now express the integrals using these measures
  -- The key is that σ and τ agree on indices 1, ..., M+2 (both give N, N+1, ..., N+M+1)
  -- and only differ at index 0 (σ gives k+1, τ gives 0)

  -- For the set C: ω ∈ C ↔ (fun i => X (N + i.val) ω) ∈ S
  --                     ↔ (fun i : Fin (M+2) => X (σ ⟨i+1, _⟩) ω) ∈ S  [since σ(i+1) = N+i]
  --                     ↔ (fun i : Fin (M+2) => X (τ ⟨i+1, _⟩) ω) ∈ S  [since τ(i+1) = N+i]

  -- Define the joint function g : (Fin (M+3) → α) → ℝ
  -- g(z) = f(z 0) · indicator for (z_1, z_2, ..., z_{M+2}) ∈ S
  let g : (Fin (M + 3) → α) → ℝ := fun z =>
    f (z ⟨0, by omega⟩) * (S.indicator 1 (fun i : Fin (M + 2) => z ⟨i.val + 1, by omega⟩))

  -- The integrals can be expressed as:
  -- ∫_C f(X_{k+1}) dμ = ∫ g(fun i => X (σ i) ω) dμ
  -- ∫_C f(X_0) dμ     = ∫ g(fun i => X (τ i) ω) dμ

  -- This follows because:
  -- 1. σ(0) = k+1 and τ(0) = 0, so z 0 is X_{k+1} vs X_0
  -- 2. σ(i+1) = τ(i+1) = N + i, so the indicator part is the same (both equal 1_C)

  -- Verify σ and τ agree on tail indices
  have h_agree : ∀ i : Fin (M + 2), σ ⟨i.val + 1, by omega⟩ = τ ⟨i.val + 1, by omega⟩ := by
    intro i
    simp only [σ, τ, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]

  -- Express C' (the actual set) in terms of σ (or equivalently τ)
  let C' : Set Ω := {ω | (fun i => X (N + i.val) ω) ∈ S}
  -- C' and C are definitionally equal since C is defined by let
  have hC_C' : C' = {ω | (fun i => X (N + i.val) ω) ∈ S} := rfl

  -- Now use the measure equality to relate the integrals
  -- The remaining step is to apply integral_map twice and use h_eq
  -- This is technically involved due to the indicator function handling

  -- For measurability of the maps
  have hσ_meas : Measurable (fun ω i => X (σ i) ω) :=
    measurable_pi_lambda _ (fun i => hX_meas (σ i))
  have hτ_meas : Measurable (fun ω i => X (τ i) ω) :=
    measurable_pi_lambda _ (fun i => hX_meas (τ i))

  -- The final step uses that g composed with the σ-indexed process equals
  -- the integrand on one side, and g composed with τ-indexed process equals
  -- the integrand on the other side. The measure equality gives the result.

  -- First show that σ(0) = k+1 and τ(0) = 0
  have hσ_0 : σ ⟨0, by omega⟩ = k + 1 := by simp only [σ, ↓reduceIte]
  have hτ_0 : τ ⟨0, by omega⟩ = 0 := by simp only [τ, ↓reduceIte]

  -- Show that σ and τ agree on indices 1, ..., M+2 (give N+i for index i+1)
  have hσ_tail : ∀ i : Fin (M + 2), σ ⟨i.val + 1, by omega⟩ = N + i.val := by
    intro i
    simp only [σ, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]

  have hτ_tail : ∀ i : Fin (M + 2), τ ⟨i.val + 1, by omega⟩ = N + i.val := by
    intro i
    simp only [τ, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]

  -- Key observation: σ-indexed tail is the same as C' membership condition
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

  -- Key: g composed with σ-indexed process gives f(X_{k+1}) * 1_C
  have hg_σ : ∀ ω, g (fun i => X (σ i) ω) = f (X (k + 1) ω) * (C'.indicator 1 ω) := by
    intro ω
    simp only [g, hσ_0]
    -- g's indicator is S.indicator on (fun i => X (σ ⟨i+1, _⟩) ω)
    -- C'.indicator is on ω
    -- They agree because (hS_σ ω)
    by_cases hω : ω ∈ C'
    · -- Both indicators are 1
      have hS_mem : (fun i : Fin (M + 2) => X (σ ⟨i.val + 1, by omega⟩) ω) ∈ S := (hS_σ ω).mpr hω
      rw [Set.indicator_of_mem hω, Set.indicator_of_mem hS_mem]
      simp only [Pi.one_apply, mul_one]
    · -- Both indicators are 0
      have hS_nmem : (fun i : Fin (M + 2) => X (σ ⟨i.val + 1, by omega⟩) ω) ∉ S :=
        fun h => hω ((hS_σ ω).mp h)
      rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hS_nmem]

  -- Similarly for τ
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

  -- The set C' is measurable (preimage of S under measurable map)
  have hC'_meas : MeasurableSet C' := by
    apply MeasurableSet.preimage _hS
    exact measurable_pi_lambda _ (fun i => hX_meas (N + i.val))

  -- Helper: indicator of f equals f * indicator of 1
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

  -- Express set integrals using indicator functions
  -- ∫_C f(X_{k+1}) dμ = ∫ f(X_{k+1}) * 1_C dμ = ∫ g(σ-process) dμ
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
  -- The proof uses path-space formulation:
  -- 1. Let π : Ω → (ℕ → α) be π(ω)_i = X_i(ω)
  -- 2. Let ν = π_* μ be the law on path space
  -- 3. A = π⁻¹(B) for some B in tailShift α (tail σ-algebra on path space)
  -- 4. By tailSigma_shift_invariant_for_contractable: T_* ν = ν where T is left shift
  -- 5. For B ∈ tailShift α: T⁻¹(B) = B (tail sets are shift-invariant)
  -- 6. ∫_B f(y_k) dν = ∫_B f((T^k y)_0) dν = ∫_B f(y_0) d((T^k)_* ν) = ∫_B f(y_0) dν

  -- Define the path map
  let π : Ω → (ℕ → α) := fun ω i => X i ω
  let ν := Measure.map π μ

  -- Measurability of π
  have hπ_meas : Measurable π := measurable_pi_lambda _ hX_meas

  -- The key insight: A ∈ tailProcess X = iInf (tailFamily X),
  -- so A ∈ tailFamily X N for all N, including N > k.
  -- For such N, the sequences (k, N, N+1, ...) and (0, N, N+1, ...)
  -- are both strictly increasing, so by contractability they have
  -- the same joint law. This implies the set integrals are equal.

  -- We prove directly that for any k, the integral equals the k=0 case.
  -- The argument uses contractability on finite-dimensional marginals.

  -- Strategy: A is in tailFamily X N for all N. For N > k, express the
  -- integral in terms of the joint distribution of (X_k, X_N, X_{N+1}, ...)
  -- and use contractability.

  -- For k = 0, trivial
  cases k with
  | zero => rfl
  | succ k =>
    -- Show ∫_A f(X(k+1)) = ∫_A f(X 0)
    -- A ∈ tailFamily X N for N = k + 2
    -- The sequences (k+1, k+2, k+3, ...) and (0, 1, 2, ...) are both strictly increasing
    -- So by contractability, Law(X(k+1), X(k+2), X(k+3), ...) = Law(X 0, X 1, X 2, ...)

    -- This means: for any bounded measurable g : (ℕ → α) → ℝ,
    -- ∫ g(X(k+1), X(k+2), ...) dμ = ∫ g(X 0, X 1, ...) dμ

    -- In particular, taking g(y) = f(y 0) · 1_{A'}(y) where A' = π(A) in path space:
    -- ∫_A f(X(k+1)) dμ = ∫_A f(X 0) dμ

    -- The measure equality from shift invariance
    have h_shift := tailSigma_shift_invariant_for_contractable X hX_contract hX_meas
    -- h_shift : Measure.map (fun ω i => X (1 + i) ω) μ = Measure.map (fun ω i => X i ω) μ

    -- By iterating shift invariance k+1 times, we get:
    -- Measure.map (fun ω i => X ((k+1) + i) ω) μ = Measure.map (fun ω i => X i ω) μ

    -- Since A is tail-measurable, it's determined by coordinates ≥ some N.
    -- Under the shift by k+1, the indicator becomes 1_A(shifted) which equals 1_A
    -- because tail events don't depend on finite initial segments.

    -- The formal argument:
    -- Let Φ_j : Ω → (ℕ → α) by Φ_j(ω)_i = X(j+i)(ω)
    -- Then A = Φ_0⁻¹(B) for some B ∈ tailShift α (tail σ-algebra on path space)
    -- By tailProcess_eq_comap_path or similar.

    -- For tail-measurable B:
    -- - B is shift-invariant: T⁻¹(B) = B
    -- - So Φ_j⁻¹(B) = Φ_0⁻¹(B) = A for all j

    -- Therefore:
    -- ∫_A f(X(k+1)) dμ = ∫_{Φ_0⁻¹(B)} f(X(k+1)) dμ
    --                  = ∫_B f(y_{k+1}) d(Φ_0_* μ)(y)
    --                  = ∫_B f((T^{k+1} y)_0) d(Φ_0_* μ)(y)
    --                  = ∫_B f(y_0) d((T^{k+1})_* Φ_0_* μ)(y)  [change of vars]
    --                  = ∫_B f(y_0) d(Φ_0_* μ)(y)  [since (T^{k+1})_* ν = ν]
    --                  = ∫_A f(X 0) dμ

    -- The change of variables for non-invertible T requires:
    -- For ν-integrable g and B with T⁻¹(B) = B:
    -- ∫_B g dν = ∫_B (g ∘ T) dν (when T_* ν = ν)

    -- Proof: ∫_B g dν = ∫_B g d(T_* ν) = ∫_{T⁻¹(B)} (g ∘ T) dν = ∫_B (g ∘ T) dν

    -- Alternative proof using finite-dimensional contractability directly:
    -- For A ∈ tailProcess X ⊆ tailFamily X N for any N, pick N = k + 2 > k + 1.
    -- A depends only on (X_N, X_{N+1}, ...).
    -- By contractability, for strictly increasing sequences of indices:
    --   Law(X_{k+1}, X_N, X_{N+1}, ..., X_{N+M}) = Law(X_0, X_1, ..., X_{M+1})
    --   Law(X_0, X_N, X_{N+1}, ..., X_{N+M}) = Law(X_0, X_1, ..., X_{M+1})
    -- These have the SAME law because both are strictly increasing sequences of length M+2.
    -- Therefore: ∫_A f(X_{k+1}) dμ = ∫_A f(X_0) dμ
    --
    -- Detailed argument:
    -- For any cylinder set C = {ω : (X_N(ω), ..., X_{N+M}(ω)) ∈ D} with N > k+1:
    --   ∫_C f(X_{k+1}) dμ = ∫ f(X_{k+1}) · 1_D(X_N, ..., X_{N+M}) dμ
    --                     = 𝔼[g(X_{k+1}, X_N, ..., X_{N+M})]
    --                     = 𝔼[g(X_0, X_1, ..., X_{M+1})]  (by contractability)
    --                     = 𝔼[g(X_0, X_N, ..., X_{N+M})]  (by contractability)
    --                     = ∫_C f(X_0) dμ
    -- where g(z_0, z_1, ...) = f(z_0) · 1_D(z_1, ..., z_{M+1}).
    --
    -- The equality extends to all sets in σ(X_N, X_{N+1}, ...) by π-λ theorem,
    -- and A ∈ tailFamily X N for N = k + 2 > k + 1.

    -- The formal implementation uses contractability for non-contiguous strictly increasing
    -- sequences combined with the π-λ theorem.

    -- Key insight: For N > k+1, the sequences (k+1, N, N+1, ..., N+M) and (0, N, N+1, ..., N+M)
    -- are both strictly increasing. By contractability, both have the same law as (0, 1, ..., M+1).
    -- Therefore they have the same joint law, which gives the integral equality on cylinder sets.

    -- For the π-λ extension: Define the property P(A) := "∫_A f(X_{k+1}) dμ = ∫_A f(X_0) dμ"
    -- P holds on cylinder sets (proved above), and P is preserved under:
    -- - Empty set (trivial)
    -- - Complements (by linearity of integral: ∫_{Aᶜ} = ∫ - ∫_A)
    -- - Disjoint unions (by additivity of set integral)
    -- Since cylinder sets form a π-system generating tailFamily X N, P holds everywhere.

    -- For now, we accept this as mathematically sound but technically involved to formalize.
    -- The key lemmas needed from mathlib:
    -- 1. `Contractable` definition for general strictly increasing sequences (we have this)
    -- 2. `induction_on_inter` for extending from π-systems (mathlib has this)
    -- 3. Set integral additivity on disjoint unions (mathlib has this)

    -- === DIRECT MEASURE-THEORETIC PROOF ===
    -- The proof uses the fact that the shifted process has the same law on path space.
    -- For tail-measurable sets, integrals can be computed via the path-space measure,
    -- and shift invariance of the path-space law implies the integral equality.

    -- Step 1: Prove single-coordinate distribution equality
    -- X_{k+1} and X_0 have the same distribution
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

    -- Step 2: Integrability transfer
    have hf_int_k1 : Integrable (f ∘ X (k + 1)) μ := by
      have hf_aesm : AEStronglyMeasurable f (Measure.map (X 0) μ) := hf_meas.aestronglyMeasurable
      have h_int_map : Integrable f (Measure.map (X 0) μ) :=
        (integrable_map_measure hf_aesm (hX_meas 0).aemeasurable).mpr hf_int
      rw [← hX_k1_eq_X0] at h_int_map
      exact (integrable_map_measure hf_meas.aestronglyMeasurable
        (hX_meas (k + 1)).aemeasurable).mp h_int_map

    -- Step 3: Use cylinder set equality for tail-measurable A
    -- A is in tailProcess X, hence in tailFamily X N for N = k + 2 > k + 1
    let N := k + 2
    have hN_gt : k + 1 < N := by omega

    -- A ∈ tailFamily X N since tailProcess X ≤ tailFamily X N
    have hA_tailFam : MeasurableSet[tailFamily X N] A := (tailProcess_le_tailFamily X N) A hA

    -- Step 4: The key insight is that for ANY cylinder C based at indices ≥ N,
    -- the integral equality holds by setIntegral_cylinder_eq.
    -- For a general tail-measurable set A ∈ tailFamily X N, we use the
    -- π-λ extension: tail-measurable sets are limits of cylinders,
    -- and the integral equality is preserved under limits by monotone convergence.

    -- For the full formal proof, we would apply the Dynkin system theorem.
    -- The property P(A) := "∫_A f(X_{k+1}) = ∫_A f(X_0)" is closed under:
    -- (1) Empty set: trivial
    -- (2) Complements: P(A) → P(Aᶜ) using full-space equality
    -- (3) Disjoint unions: by additivity of set integral
    -- And P holds on cylinder sets by setIntegral_cylinder_eq.

    -- For now, we use the measure-theoretic approach via path space.
    -- The shift-invariant law implies equal integrals over tail events.

    -- Path space measure and shift invariance
    let ν := Measure.map (fun ω i => X i ω) μ
    have h_shift := tailSigma_shift_invariant_for_contractable X hX_contract hX_meas

    -- The rigorous proof uses:
    -- 1. tailProcess X = comap π (tailShift α) when π is surjective
    -- 2. For B ∈ tailShift with ν shift-invariant: ∫_B g(y_k) dν = ∫_B g(y_0) dν
    -- 3. Translate back to Ω via the comap structure

    -- The cylinder approach already proved:
    -- For any cylinder C = {ω : (X_N, ..., X_{N+M}) ∈ S} with N > k+1:
    --   ∫_C f(X_{k+1}) dμ = ∫_C f(X_0) dμ
    -- This extends to all of tailFamily X N by the π-λ theorem.

    -- Direct application: A is in tailFamily X N, so the equality holds.
    -- The formal verification uses induction_on_inter, but the mathematical
    -- content is in setIntegral_cylinder_eq.

    -- === π-λ EXTENSION ===
    -- The key lemma setIntegral_cylinder_eq proves integral equality on cylinder sets.
    -- We extend to all of tailFamily X N via the Dynkin system theorem.
    --
    -- Structure:
    -- 1. Define the property P(A) := "∫_A f(X_{k+1}) = ∫_A f(X_0)"
    -- 2. P holds on cylinders (by setIntegral_cylinder_eq with generalized indices)
    -- 3. P is closed under: empty set, complements, disjoint unions
    -- 4. Cylinders form a π-system generating tailFamily X N
    -- 5. By induction_on_inter, P holds on all of tailFamily X N

    -- Key: the full-space integral equality (needed for complement closure)
    have h_full : ∫ ω, f (X (k + 1) ω) ∂μ = ∫ ω, f (X 0 ω) ∂μ := by
      -- By equal distribution: X_{k+1} =_d X_0
      calc ∫ ω, f (X (k + 1) ω) ∂μ
          = ∫ x, f x ∂(Measure.map (X (k + 1)) μ) := by
              rw [integral_map (hX_meas (k + 1)).aemeasurable hf_meas.aestronglyMeasurable]
        _ = ∫ x, f x ∂(Measure.map (X 0) μ) := by rw [hX_k1_eq_X0]
        _ = ∫ ω, f (X 0 ω) ∂μ := by
              rw [← integral_map (hX_meas 0).aemeasurable hf_meas.aestronglyMeasurable]

    -- The proof uses the fact that for tail-measurable A:
    -- A ∈ tailProcess X ⊆ tailFamily X N for N = k + 2
    -- The cylinder sets {ω | (X_N ω, ..., X_{N+M} ω) ∈ S} generate tailFamily X N
    -- and we've proved the integral equality on those cylinders.
    --
    -- The Dynkin system extension is standard:
    -- - Empty: ∫_∅ = 0 = ∫_∅ ✓
    -- - Complement: ∫_{Aᶜ} g = ∫ g - ∫_A g, so equal on Aᶜ if equal on A and full space ✓
    -- - Disjoint union: ∫_{⋃ Aᵢ} g = ∑ ∫_{Aᵢ} g, so preserved ✓
    --
    -- For the formal mathlib implementation, we would use induction_on_inter
    -- with the generating π-system and verify the Dynkin closure properties.
    --
    -- Technical note: The exact cylinder-based generating system for tailFamily X N
    -- is {π⁻¹(C) | C is a finite-coordinate cylinder in path space at indices ≥ N}.
    -- This forms a π-system (intersection of cylinders is a cylinder) and generates
    -- tailFamily X N by definition as iSup of coordinate comaps.

    -- === π-λ EXTENSION via induction_on_inter ===
    -- Structure: Apply MeasurableSpace.induction_on_inter
    -- - tailFamily X N = generateFrom (piiUnionInter ...) by generateFrom_piiUnionInter_measurableSet
    -- - piiUnionInter is a π-system by isPiSystem_piiUnionInter
    -- - Property "∫_A f(X_{k+1}) = ∫_A f(X_0)" is proved on generators and Dynkin-closed

    -- Define the coordinate σ-algebras
    let m : ℕ → MeasurableSpace Ω := fun j => MeasurableSpace.comap (fun ω => X (N + j) ω) inferInstance

    -- tailFamily X N = iSup m = ⨆ j ∈ Set.univ, m j
    have h_tailFam_eq_iSup : tailFamily X N = ⨆ j, m j := by
      simp only [tailFamily, m]

    -- The generating π-system
    let π : Set (Set Ω) := piiUnionInter (fun j => {s | MeasurableSet[m j] s}) Set.univ

    -- π is a π-system
    have hπ_isPiSystem : IsPiSystem π := by
      exact isPiSystem_piiUnionInter (fun j => {s | MeasurableSet[m j] s})
        (fun j => @MeasurableSpace.isPiSystem_measurableSet Ω (m j)) Set.univ

    -- tailFamily X N = generateFrom π
    have h_gen : tailFamily X N = MeasurableSpace.generateFrom π := by
      rw [h_tailFam_eq_iSup]
      have := generateFrom_piiUnionInter_measurableSet m Set.univ
      simp only [Set.mem_univ, iSup_true] at this
      exact this.symm

    -- Measurability wrt tailFamily X N implies measurability wrt the ambient space
    have h_meas_le : tailFamily X N ≤ (inferInstance : MeasurableSpace Ω) := by
      apply iSup_le
      intro j
      exact (hX_meas (N + j)).comap_le

    -- A is measurable in tailFamily X N (we proved hA_tailFam earlier)
    -- Express the proof goal using induction_on_inter

    -- The property we want to prove
    let P : (s : Set Ω) → MeasurableSet[tailFamily X N] s → Prop :=
      fun s _ => ∫ ω in s, f (X (k + 1) ω) ∂μ = ∫ ω in s, f (X 0 ω) ∂μ

    -- Apply induction_on_inter
    refine MeasurableSpace.induction_on_inter h_gen hπ_isPiSystem ?_ ?_ ?_ ?_ A hA_tailFam

    -- Case 1: Empty set
    · simp only [setIntegral_empty]

    -- Case 2: Basic (elements of the π-system)
    -- These are finite intersections of preimages: ⋂_{i ∈ p} {ω | X (N+kᵢ) ω ∈ Sᵢ}
    -- The integral equality follows from contractability (same argument as setIntegral_cylinder_eq)
    · intro t ht
      -- Extract the structure: t = ⋂_{j ∈ pt} ft j where ft j ∈ {s | MeasurableSet[m j] s}
      rcases ht with ⟨pt, _, ft, ht_m, rfl⟩

      -- If pt is empty, t = univ and we use h_full
      by_cases hpt_empty : pt = ∅
      · simp only [hpt_empty, Finset.notMem_empty, Set.iInter_of_empty, Set.iInter_univ]
        simp only [setIntegral_univ]
        exact h_full

      -- pt is nonempty, so t is a proper finite intersection
      -- Get the sorted list of indices in pt
      let indices : List ℕ := pt.sort (· ≤ ·)
      have h_sorted : indices.Sorted (· < ·) := Finset.sort_sorted_lt pt
      have h_nodup : indices.Nodup := Finset.sort_nodup (· ≤ ·) pt
      have h_indices_ne : indices ≠ [] := by
        simp only [indices, ne_eq, List.eq_nil_iff_forall_not_mem]
        intro h
        apply hpt_empty
        ext x
        simp only [Finset.notMem_empty, iff_false]
        intro hx
        exact h x ((Finset.mem_sort _).mpr hx)

      -- The minimum index in pt
      let min_idx := indices.head h_indices_ne

      -- Key fact: k + 1 < N ≤ N + min_idx, so prepending k+1 or 0 preserves strict monotonicity
      -- Since min_idx ≥ 0 and N = k + 2, we have N + min_idx ≥ k + 2 > k + 1 > 0

      -- The proof follows setIntegral_cylinder_eq but for non-consecutive indices.
      -- The key is that contractability works for ANY strictly increasing sequence.

      -- Let d = pt.card be the number of tail coordinates
      let d := pt.card
      have hd_pos : 0 < d := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hpt_empty)

      -- Get length of indices list
      have h_len : indices.length = d := by
        simp only [indices, d, Finset.length_sort]

      -- Define index functions from Fin (d + 1) → ℕ using List.get
      -- σ(0) = k + 1, σ(i+1) = N + indices[i]
      -- τ(0) = 0,     τ(i+1) = N + indices[i]

      -- Define σ : Fin (d + 1) → ℕ
      let σ : Fin (d + 1) → ℕ := fun i =>
        if hi : i.val = 0 then k + 1
        else N + indices.get ⟨i.val - 1, by rw [h_len]; omega⟩

      -- Define τ : Fin (d + 1) → ℕ
      let τ : Fin (d + 1) → ℕ := fun i =>
        if hi : i.val = 0 then 0
        else N + indices.get ⟨i.val - 1, by rw [h_len]; omega⟩

      -- The sorted indices are strictly increasing
      have h_idx_sorted : ∀ i j : ℕ, (hi : i < d) → (hj : j < d) → i < j →
          indices.get ⟨i, by rw [h_len]; exact hi⟩ < indices.get ⟨j, by rw [h_len]; exact hj⟩ := by
        intro i j hi hj hij
        exact List.Sorted.rel_get_of_lt h_sorted (by simp [hij])

      -- σ is strictly increasing
      have hσ_strictMono : StrictMono σ := by
        intro i j hij
        simp only [σ]
        by_cases hi : i.val = 0
        · -- i = 0, so σ(i) = k + 1
          simp only [hi, ↓reduceDIte]
          have hj_pos : 0 < j.val := by omega
          simp only [Nat.ne_of_gt hj_pos, ↓reduceDIte]
          -- Need: k + 1 < N + indices[j-1]
          -- We have k + 1 < N = k + 2, and N + _ ≥ N
          omega
        · -- i > 0
          simp only [hi, ↓reduceDIte]
          have hj_pos : 0 < j.val := by omega
          simp only [Nat.ne_of_gt hj_pos, ↓reduceDIte]
          -- Need: N + indices[i-1] < N + indices[j-1]
          have h_ij : i.val - 1 < j.val - 1 := by omega
          have h_i_bd : i.val - 1 < d := by omega
          have h_j_bd : j.val - 1 < d := by omega
          have h1 := h_idx_sorted (i.val - 1) (j.val - 1) h_i_bd h_j_bd h_ij
          omega

      -- τ is strictly increasing
      have hτ_strictMono : StrictMono τ := by
        intro i j hij
        simp only [τ]
        by_cases hi : i.val = 0
        · -- i = 0, so τ(i) = 0
          simp only [hi, ↓reduceDIte]
          have hj_pos : 0 < j.val := by omega
          simp only [Nat.ne_of_gt hj_pos, ↓reduceDIte]
          -- Need: 0 < N + indices[j-1], which is true since N > 0
          omega
        · -- i > 0
          simp only [hi, ↓reduceDIte]
          have hj_pos : 0 < j.val := by omega
          simp only [Nat.ne_of_gt hj_pos, ↓reduceDIte]
          -- Need: N + indices[i-1] < N + indices[j-1]
          have h_ij : i.val - 1 < j.val - 1 := by omega
          have h_i_bd : i.val - 1 < d := by omega
          have h_j_bd : j.val - 1 < d := by omega
          have h1 := h_idx_sorted (i.val - 1) (j.val - 1) h_i_bd h_j_bd h_ij
          omega

      -- By contractability, σ and τ give the same push-forward measure
      have h_eq_σ := hX_contract (d + 1) σ hσ_strictMono
      have h_eq_τ := hX_contract (d + 1) τ hτ_strictMono
      have h_eq : Measure.map (fun ω i => X (σ i) ω) μ = Measure.map (fun ω i => X (τ i) ω) μ := by
        rw [h_eq_σ, h_eq_τ]

      -- Key: σ and τ agree on non-zero indices (both give N + indices[i-1])
      have h_agree : ∀ i : Fin (d + 1), i.val ≠ 0 → σ i = τ i := by
        intro i hi
        simp only [σ, τ, hi, ↓reduceDIte]

      -- The set C := ⋂ j ∈ pt, ft j is determined by the tail coordinates.
      -- Since each ft j is measurable in comap (X (N + j)), membership in C
      -- depends only on (X (N + j₁) ω, ..., X (N + jₘ) ω) = tail of both processes.

      let C := ⋂ j ∈ pt, ft j

      -- C is measurable in the ambient space
      have hC_meas : MeasurableSet C := by
        apply MeasurableSet.iInter
        intro j
        apply MeasurableSet.iInter
        intro hj
        -- ht_m j hj : ft j ∈ {s | MeasurableSet[m j] s}
        -- This is MeasurableSet[m j] (ft j), and m j ≤ tailFamily X N ≤ inst
        have h1 : MeasurableSet[m j] (ft j) := ht_m j hj
        have h2 : m j ≤ tailFamily X N := le_iSup m j
        exact (h2.trans h_meas_le) (ft j) h1

      -- Define the joint function g : (Fin (d+1) → α) → ℝ
      -- g(z) = f(z 0) * indicator condition based on z 1, ..., z d
      --
      -- The indicator condition needs to match C membership.
      -- For ω, C membership depends on X (N + indices[0]) ω, ..., X (N + indices[d-1]) ω
      -- These are exactly X (σ (Fin.succ i)) ω = X (τ (Fin.succ i)) ω for i : Fin d.

      -- For the joint function, we need a set S ⊆ (Fin d → α) such that:
      -- ω ∈ C ↔ (fun i : Fin d => X (N + indices.get ⟨i, _⟩) ω) ∈ S

      -- Using measurableSet_comap: for each j ∈ pt, there exists Tⱼ with ft j = (X (N+j))⁻¹(Tⱼ)
      -- So C = ⋂ j ∈ pt, (X (N+j))⁻¹(Tⱼ) = (joint map)⁻¹(product of Tⱼ's)

      -- Rather than extracting Tⱼ explicitly, we define S implicitly:
      -- S := {y : Fin d → α | ∀ i, y i ∈ range of corresponding Tⱼ condition}

      -- For the proof, we use that the integrand is f(z 0) * 1_C(ω) where
      -- the indicator 1_C depends only on the tail coordinates.

      -- The key calculation follows setIntegral_cylinder_eq pattern.
      -- Both integrals equal ∫ g dν where ν = σ_*μ = τ_*μ and
      -- g extracts f(first coord) * indicator(tail coords).

      -- Now we define the joint function g and chain the integrals.
      -- This follows setIntegral_cylinder_eq (lines 355-389) exactly.

      -- First, verify σ(0) = k + 1 and τ(0) = 0
      have hσ_0 : σ ⟨0, by omega⟩ = k + 1 := by simp only [σ, ↓reduceDIte]
      have hτ_0 : τ ⟨0, by omega⟩ = 0 := by simp only [τ, ↓reduceDIte]

      -- The maps for measurability
      have hσ_meas : Measurable (fun ω i => X (σ i) ω) :=
        measurable_pi_lambda _ (fun i => hX_meas (σ i))
      have hτ_meas : Measurable (fun ω i => X (τ i) ω) :=
        measurable_pi_lambda _ (fun i => hX_meas (τ i))

      -- Key: The indicator 1_C depends only on tail coordinates (σ 1, ..., σ d = τ 1, ..., τ d)
      -- This is because C = ⋂ j ∈ pt, ft j and each ft j is determined by X (N + j),
      -- which corresponds to one of the tail coordinates.

      -- Define the joint function g : (Fin (d+1) → α) → ℝ
      -- g(z) = f(z 0) * indicator for the tail coordinates condition

      -- The indicator condition needs to express C membership via the indexed coordinates.
      -- For ω ∈ C: ∀ j ∈ pt, ω ∈ ft j, which depends on X (N + j) ω for j ∈ pt.
      -- These are exactly the tail coordinates σ(i+1) = τ(i+1) = N + indices[i].

      -- Rather than defining S explicitly, we use the equivalence:
      -- For the σ-process: C.indicator (fun ω => f(X_{k+1} ω)) ω = f(X_{k+1} ω) * 1_C(ω)
      -- For the τ-process: C.indicator (fun ω => f(X_0 ω)) ω = f(X_0 ω) * 1_C(ω)

      -- The proof uses that 1_C depends only on tail coords, which are same for σ and τ.

      -- Express set integrals as full integrals with indicator
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
        -- The key step: 1_C depends only on tail coordinates
        -- Both σ and τ give the same tail, so the indicator is the same
        -- This means: for any z, if z comes from σ-process or τ-process with same ω,
        -- the indicator value is the same.
        -- Therefore the integrands are related by the measure equality.
        _ = ∫ ω, f (X (τ ⟨0, by omega⟩) ω) * (C.indicator 1 ω) ∂μ := by
              -- The key insight: both integrals equal ∫ g dν where ν = σ_*μ = τ_*μ
              -- Since σ and τ only differ at index 0, and 1_C depends only on indices ≥ 1,
              -- we need to show the two integrals are equal via the measure equality h_eq.

              -- Step 1: Extract preimage sets for each ft j using measurableSet_comap
              -- For each j ∈ pt, ft j = (X (N + j))⁻¹' T_j for some measurable T_j
              have h_preimage : ∀ j ∈ pt, ∃ (Tj : Set α), MeasurableSet Tj ∧
                  ft j = (X (N + j))⁻¹' Tj := by
                intro j hj
                obtain ⟨Tj, hTj_meas, hTj_eq⟩ := MeasurableSpace.measurableSet_comap.mp (ht_m j hj)
                exact ⟨Tj, hTj_meas, hTj_eq.symm⟩

              -- Step 2: Use choice to get the family of preimage sets
              choose Tj hTj using h_preimage

              -- Step 3: Define the projection map from (Fin (d+1) → α) to (Fin d → α)
              let proj : (Fin (d + 1) → α) → (Fin d → α) := fun z i =>
                z ⟨i.val + 1, by omega⟩

              -- proj is measurable
              have hproj_meas : Measurable proj := by
                apply measurable_pi_lambda
                intro i
                exact measurable_pi_apply _

              -- Step 4: For each i : Fin d, get the index j = indices.get i ∈ pt
              -- and the corresponding set T_{indices.get i}

              -- Helper: indices.get maps Fin d into pt
              have h_indices_mem : ∀ i : Fin d, indices.get ⟨i.val, by rw [h_len]; exact i.isLt⟩ ∈ pt := by
                intro i
                have hi_lt : i.val < indices.length := by rw [h_len]; exact i.isLt
                exact (Finset.mem_sort _).mp (List.get_mem indices ⟨i.val, hi_lt⟩)

              -- Step 5: Define the set S in (Fin d → α)
              -- S = {y : Fin d → α | ∀ i : Fin d, y i ∈ T_{indices.get i}}
              let S : Set (Fin d → α) := {y : Fin d → α | ∀ i : Fin d,
                y i ∈ Tj (indices.get ⟨i.val, by rw [h_len]; exact i.isLt⟩) (h_indices_mem i)}

              -- S is measurable (finite intersection of preimages of measurable sets)
              -- S = ⋂ i : Fin d, (fun y => y i)⁻¹' (Tj ...)
              have hS_meas : MeasurableSet S := by
                -- Express S as an intersection
                have hS_eq : S = ⋂ i : Fin d, (fun y => y i) ⁻¹'
                    Tj (indices.get ⟨i.val, by rw [h_len]; exact i.isLt⟩) (h_indices_mem i) := by
                  ext y
                  simp only [S, Set.mem_iInter, Set.mem_preimage, Set.mem_setOf_eq]
                rw [hS_eq]
                apply MeasurableSet.iInter
                intro i
                apply MeasurableSet.preimage (hTj _ (h_indices_mem i)).1
                exact measurable_pi_apply i

              -- Step 6: Show the key equivalence: ω ∈ C ↔ proj (fun i => X (σ i) ω) ∈ S
              -- First, show that σ (Fin.succ i) = N + indices.get i for i : Fin d
              have hσ_succ : ∀ i : Fin d, σ ⟨i.val + 1, by omega⟩ =
                  N + indices.get ⟨i.val, by rw [h_len]; exact i.isLt⟩ := by
                intro i
                simp only [σ, Nat.add_one_ne_zero, ↓reduceDIte, Nat.add_sub_cancel]

              have hτ_succ : ∀ i : Fin d, τ ⟨i.val + 1, by omega⟩ =
                  N + indices.get ⟨i.val, by rw [h_len]; exact i.isLt⟩ := by
                intro i
                simp only [τ, Nat.add_one_ne_zero, ↓reduceDIte, Nat.add_sub_cancel]

              -- Helper: Every j ∈ pt corresponds to some i : Fin d with indices.get i = j
              have h_indices_surj : ∀ j ∈ pt, ∃ i : Fin d,
                  indices.get ⟨i.val, by rw [h_len]; exact i.isLt⟩ = j := by
                intro j hj
                have h_mem_list : j ∈ indices := (Finset.mem_sort _).mpr hj
                obtain ⟨n, hn_eq⟩ := List.get_of_mem h_mem_list
                -- n : Fin indices.length with indices.get n = j
                have hn_d : n.val < d := by rw [← h_len]; exact n.isLt
                exact ⟨⟨n.val, hn_d⟩, hn_eq⟩

              -- The key equivalence: membership in C is determined by the tail coordinates
              have h_C_iff_S : ∀ ω, ω ∈ C ↔ (fun i : Fin d =>
                  X (σ ⟨i.val + 1, by omega⟩) ω) ∈ S := by
                intro ω
                constructor
                · -- Forward: ω ∈ C → tail of σ-process is in S
                  intro hω
                  simp only [S, Set.mem_setOf_eq]
                  intro i
                  have h_idx_mem := h_indices_mem i
                  have hω_ft := (Set.mem_iInter.mp (Set.mem_iInter.mp hω
                    (indices.get ⟨i.val, by rw [h_len]; exact i.isLt⟩))) h_idx_mem
                  rw [(hTj _ h_idx_mem).2] at hω_ft
                  simp only [Set.mem_preimage] at hω_ft
                  rw [hσ_succ i]
                  exact hω_ft
                · -- Backward: tail of σ-process is in S → ω ∈ C
                  intro hS_mem
                  simp only [C, Set.mem_iInter]
                  intro j hj
                  obtain ⟨i, hi_eq⟩ := h_indices_surj j hj
                  rw [(hTj j hj).2]
                  simp only [Set.mem_preimage]
                  simp only [S, Set.mem_setOf_eq] at hS_mem
                  -- hS_mem i : X (σ ⟨↑i + 1, _⟩) ω ∈ Tj (indices.get ⟨↑i, _⟩) _
                  -- hi_eq : indices.get ⟨i.val, _⟩ = j
                  -- Goal: X (N + j) ω ∈ Tj j hj
                  subst hi_eq
                  have h := hS_mem i
                  simp only [hσ_succ] at h
                  exact h

              -- Same for τ (since σ and τ agree on tail indices)
              have h_C_iff_S_τ : ∀ ω, ω ∈ C ↔ (fun i : Fin d =>
                  X (τ ⟨i.val + 1, by omega⟩) ω) ∈ S := by
                intro ω
                rw [h_C_iff_S]
                -- The functions agree because σ and τ agree on non-zero indices
                suffices h : (fun i : Fin d => X (σ ⟨i.val + 1, by omega⟩) ω) =
                             (fun i : Fin d => X (τ ⟨i.val + 1, by omega⟩) ω) by
                  rw [h]
                ext i
                rw [hσ_succ, hτ_succ]

              -- Step 7: Define g : (Fin (d+1) → α) → ℝ
              let g : (Fin (d + 1) → α) → ℝ := fun z =>
                f (z ⟨0, by omega⟩) * S.indicator 1 (proj z)

              -- g is measurable
              have hg_meas : Measurable g := by
                apply Measurable.mul
                · exact hf_meas.comp (measurable_pi_apply _)
                · apply Measurable.indicator measurable_const
                  exact hS_meas.preimage hproj_meas

              -- Step 8: Show that g ∘ φ_σ gives the σ-integrand, g ∘ φ_τ gives the τ-integrand
              have hg_σ : ∀ ω, g (fun i => X (σ i) ω) =
                  f (X (σ ⟨0, by omega⟩) ω) * C.indicator 1 ω := by
                intro ω
                simp only [g, proj]
                congr 1
                -- Need: S.indicator 1 (fun i => X (σ ⟨↑i + 1, _⟩) ω) = C.indicator 1 ω
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
                -- Need: S.indicator 1 (fun i => X (τ ⟨↑i + 1, _⟩) ω) = C.indicator 1 ω
                by_cases hC : ω ∈ C
                · have hS : (fun i : Fin d => X (τ ⟨i.val + 1, by omega⟩) ω) ∈ S :=
                    (h_C_iff_S_τ ω).mp hC
                  simp only [Set.indicator_of_mem hS, Set.indicator_of_mem hC, Pi.one_apply]
                · have hS : (fun i : Fin d => X (τ ⟨i.val + 1, by omega⟩) ω) ∉ S :=
                    fun h => hC ((h_C_iff_S_τ ω).mpr h)
                  simp only [Set.indicator_of_notMem hS, Set.indicator_of_notMem hC]

              -- Step 9: Chain the integrals
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
      -- ∫_{tᶜ} g = ∫ g - ∫_t g
      -- ht : MeasurableSet[tailFamily X N] t, convert to ambient space using h_meas_le
      have h_meas_t : MeasurableSet t := h_meas_le t ht
      -- Use setIntegral_compl: ∫_tᶜ f = ∫ f - ∫_t f
      have hc1 := setIntegral_compl h_meas_t hf_int_k1
      have hc0 := setIntegral_compl h_meas_t hf_int
      simp only [Function.comp_apply] at hc1 hc0
      rw [hc1, hc0, h_full, h_eq]

    -- Case 4: Disjoint union
    · intro s h_disj h_meas h_eq
      -- ∫_{⋃ sᵢ} g = ∑ ∫_{sᵢ} g
      -- h_meas i : MeasurableSet[tailFamily X N] (s i), convert to ambient space using h_meas_le
      have h_meas' : ∀ i, MeasurableSet (s i) := fun i => h_meas_le (s i) (h_meas i)
      -- IntegrableOn on the union follows from integrability on the full space
      have h_int_k1_on : IntegrableOn (fun ω => f (X (k + 1) ω)) (⋃ i, s i) μ :=
        hf_int_k1.integrableOn
      have h_int_0_on : IntegrableOn (fun ω => f (X 0 ω)) (⋃ i, s i) μ :=
        hf_int.integrableOn
      rw [integral_iUnion h_meas' h_disj h_int_k1_on]
      rw [integral_iUnion h_meas' h_disj h_int_0_on]
      congr 1
      ext i
      exact h_eq i

/-- **Shift invariance of conditional expectation for contractable sequences (TODO).**

For a contractable sequence X and integrable function f, the conditional expectation
of f∘X_n given the tail σ-algebra does not depend on n.

This is a standard result in probability theory (see Kallenberg 2005, Theorem 1.2).
The proof requires ergodic theory machinery:
- The shifted process (X_n, X_{n+1}, ...) has the same tail σ-algebra as the original
- Conditional expectations are preserved under this identification
- Uses Contractable.shift_segment_eq as foundation

Currently left as sorry until the full ergodic theory infrastructure is developed.
-/
lemma condExp_shift_eq_condExp
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → α)
    (hX_contract : Exchangeability.Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (f : α → ℝ)
    (hf_meas : Measurable f)
    (hf_int : Integrable (f ∘ X 0) μ)
    (n : ℕ) :
    μ[f ∘ X n | Exchangeability.Tail.tailProcess X] =ᵐ[μ] μ[f ∘ X 0 | Exchangeability.Tail.tailProcess X] := by
  -- Strategy: Use uniqueness of conditional expectation.
  -- Both sides are AEStronglyMeasurable[tail] and integrable.
  -- For any tail-measurable set A with finite measure:
  --   ∫_A (μ[f∘Xₙ|tail]) dμ = ∫_A f∘Xₙ dμ  (by setIntegral_condExp)
  --   ∫_A (μ[f∘X₀|tail]) dμ = ∫_A f∘X₀ dμ  (by setIntegral_condExp)
  -- So we need: ∫_A f∘Xₙ dμ = ∫_A f∘X₀ dμ for tail-measurable A.
  -- This follows from contractability: for tail events, the shifted process
  -- has the same distribution as the original.

  -- For n = 0, this is trivial
  cases n with
  | zero => rfl
  | succ n =>
    -- The non-trivial case: show μ[f∘X(n+1)|tail] =ᵐ μ[f∘X₀|tail]
    -- Both are conditional expectations wrt the same σ-algebra

    -- Integrability of f ∘ X (n+1)
    have hf_int_n : Integrable (f ∘ X (n + 1)) μ := by
      -- By contractability, X (n+1) has the same distribution as X 0
      have h_shift := Exchangeability.Contractable.shift_segment_eq hX_contract 1 (n + 1)
      -- Measure.map (fun ω (i : Fin 1) => X ((n+1) + i.val) ω) μ =
      --   Measure.map (fun ω (i : Fin 1) => X i.val ω) μ
      -- This implies X (n+1) has same distribution as X 0
      -- So if f ∘ X 0 is integrable, so is f ∘ X (n+1)
      -- Use: Integrable.of_map with the equal measures
      have h_meas_comp : Measurable (f ∘ X (n + 1)) := hf_meas.comp (hX_meas (n + 1))
      -- The distributions are equal
      have h_map_eq : Measure.map (X (n + 1)) μ = Measure.map (X 0) μ := by
        have h1 := Exchangeability.Contractable.shift_segment_eq hX_contract 1 (n + 1)
        -- h1 : Measure.map (fun ω (i : Fin 1) => X ((n + 1) + i.val) ω) μ =
        --      Measure.map (fun ω (i : Fin 1) => X i.val ω) μ
        -- For Fin 1, i.val = 0 for any i, so these simplify
        ext s hs
        -- We need: μ (X (n+1) ⁻¹' s) = μ (X 0 ⁻¹' s)
        -- Define the cylinder set S := {f : Fin 1 → α | f 0 ∈ s}
        let S : Set (Fin 1 → α) := {f | f 0 ∈ s}
        have hS : MeasurableSet S := measurable_pi_apply 0 hs
        -- The two preimages relate via S
        have h_preimage_n1 : X (n + 1) ⁻¹' s = (fun ω (i : Fin 1) => X ((n + 1) + i.val) ω) ⁻¹' S := by
          ext ω
          simp only [Set.mem_preimage, Set.mem_setOf_eq, S]
          -- Need: X (n+1) ω ∈ s ↔ X ((n+1) + (0 : Fin 1).val) ω ∈ s
          simp only [Fin.val_zero, add_zero]
        have h_preimage_0 : X 0 ⁻¹' s = (fun ω (i : Fin 1) => X i.val ω) ⁻¹' S := by
          ext ω
          simp only [Set.mem_preimage, Set.mem_setOf_eq, S]
          -- Need: X 0 ω ∈ s ↔ X (0 : Fin 1).val ω ∈ s
          simp only [Fin.val_zero]
        -- Now use the equal measures
        have h_meas_n1 : Measurable (fun ω (i : Fin 1) => X ((n + 1) + i.val) ω) :=
          measurable_pi_lambda _ (fun i => hX_meas ((n + 1) + i.val))
        have h_meas_0 : Measurable (fun ω (i : Fin 1) => X i.val ω) :=
          measurable_pi_lambda _ (fun i => hX_meas i.val)
        rw [Measure.map_apply (hX_meas (n + 1)) hs, Measure.map_apply (hX_meas 0) hs]
        rw [h_preimage_n1, h_preimage_0]
        -- Now use h1 at S
        have h_eq := congrFun (congrArg (·.toOuterMeasure) h1) S
        simp only [Measure.coe_toOuterMeasure] at h_eq
        rw [Measure.map_apply h_meas_n1 hS, Measure.map_apply h_meas_0 hS] at h_eq
        exact h_eq
      -- Use integrable_map_measure to transfer integrability across equal measures
      -- Step 1: hf_int : Integrable (f ∘ X 0) μ
      -- Step 2: By integrable_map_measure, Integrable f (Measure.map (X 0) μ)
      -- Step 3: Since Measure.map (X (n+1)) μ = Measure.map (X 0) μ by h_map_eq,
      --         Integrable f (Measure.map (X (n+1)) μ)
      -- Step 4: By integrable_map_measure again, Integrable (f ∘ X (n+1)) μ
      have hf_aesm_0 : AEStronglyMeasurable f (Measure.map (X 0) μ) :=
        hf_meas.aestronglyMeasurable
      have h_int_map : Integrable f (Measure.map (X 0) μ) :=
        (integrable_map_measure hf_aesm_0 (hX_meas 0).aemeasurable).mpr hf_int
      rw [← h_map_eq] at h_int_map
      have hf_aesm_n1 : AEStronglyMeasurable f (Measure.map (X (n + 1)) μ) :=
        hf_meas.aestronglyMeasurable
      exact (integrable_map_measure hf_aesm_n1 (hX_meas (n + 1)).aemeasurable).mp h_int_map

    -- Apply uniqueness of conditional expectation
    -- We'll show μ[f ∘ X (n+1) | tail] satisfies the defining property of μ[f ∘ X 0 | tail]
    -- by showing ∫_A f(X(n+1)) dμ = ∫_A f(X 0) dμ for all tail-measurable A.

    -- The sub-σ-algebra condition
    have h_le : tailProcess X ≤ (inferInstance : MeasurableSpace Ω) := iInf_le_of_le 0 (by
      simp only [tailFamily]
      apply iSup_le
      intro k
      -- tailFamily uses X (0 + k), which equals X k
      have h_eq : (fun ω => X (0 + k) ω) = X k := by simp only [Nat.zero_add]
      rw [h_eq]
      exact (hX_meas k).comap_le)

    -- σ-finiteness of trimmed measure (automatic for probability measures)
    haveI h_finite : IsFiniteMeasure (μ.trim h_le) := by
      constructor
      rw [trim_measurableSet_eq h_le MeasurableSet.univ]
      exact measure_lt_top μ Set.univ
    haveI : SigmaFinite (μ.trim h_le) := @IsFiniteMeasure.toSigmaFinite _ _ _ h_finite

    -- Use ae_eq_condExp_of_forall_setIntegral_eq
    -- g = μ[f ∘ X (n+1) | tail], f = f ∘ X 0
    apply ae_eq_condExp_of_forall_setIntegral_eq h_le hf_int

    -- g is integrable on finite-measure tail-measurable sets
    · intro s hs hμs
      exact integrable_condExp.integrableOn

    -- The key: ∫_A condExp dμ = ∫_A f(X 0) dμ
    · intro s hs hμs
      -- LHS: by definition of condExp
      rw [setIntegral_condExp h_le hf_int_n hs]
      -- Now need: ∫_s f(X(n+1)) dμ = ∫_s f(X 0) dμ
      -- This follows from shift invariance on path space

      -- The key insight: both integrals are over a tail-measurable set,
      -- and by contractability, X_k has same distribution as X_0 for
      -- events that don't depend on finite initial segments.

      -- By the shift invariance lemma we proved:
      -- Measure.map (fun ω i => X (1+i) ω) μ = Measure.map (fun ω i => X i ω) μ

      -- For a tail-measurable set s, we use the fact that the set integral
      -- can be expressed via the path space measure.

      -- This is a deep result requiring careful path-space arguments.
      -- For now, we note that this follows from the established shift invariance
      -- but requires additional infrastructure to formalize completely.

      -- Apply the set integral shift invariance lemma
      exact setIntegral_comp_shift_eq X hX_contract hX_meas f hf_meas hs hf_int (n + 1)

    -- g is tail-measurable
    · exact stronglyMeasurable_condExp.aestronglyMeasurable

/-! ## Note on Cesàro Averages

The lemma `cesaro_convergence_all_shifts` showing that shifted Cesàro averages
`(1/m) ∑_{k=0}^{m-1} f(X_{n+k})` converge to `μ[f∘X₀ | tailSigma X]` for all `n ∈ ℕ`
is implemented in `Exchangeability.DeFinetti.ViaL2.CesaroConvergence`.

It was moved there to resolve a circular import: that file already imports this one,
so the proof (which uses `cesaro_to_condexp_L1` from CesaroConvergence) lives there.
-/

end Exchangeability.Tail.ShiftInvariance
