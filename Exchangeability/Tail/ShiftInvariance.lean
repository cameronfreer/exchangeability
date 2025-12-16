/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer, Claude (Anthropic)
-/
import Exchangeability.Tail.TailSigma
import Exchangeability.PathSpace.Shift
import Exchangeability.Contractability
import Exchangeability.Core

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

    -- Implementation note: The full formalization requires π-λ extension from cylinders.
    -- The key components already proved:
    -- ✓ setIntegral_cylinder_eq: Integral equality holds on finite-dimensional cylinders
    -- ✓ tailSigma_shift_invariant_for_contractable: Path space law is shift-invariant
    --
    -- Required infrastructure for π-λ extension:
    -- 1. Show tailFamily X N = generateFrom {cylinder sets based on (X_N, X_{N+1}, ...)}
    -- 2. Show cylinder sets form a π-system (closed under finite intersections)
    -- 3. Apply induction_on_inter with the λ-system defined by:
    --    P(A) := "∫_A f(X_{k+1}) dμ = ∫_A f(X_0) dμ"
    --    - P(∅): Both integrals are 0 ✓
    --    - P(A) → P(Aᶜ): By linearity ∫_{Aᶜ} = ∫_Ω - ∫_A
    --    - Disjoint union: ∫_{⋃ Aᵢ} = ∑ ∫_{Aᵢ} by countable additivity
    --
    -- The mathematical argument is sound; formal infrastructure is non-trivial.
    sorry

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

/-! ## Application to Cesàro Averages

This section shows how shift invariance immediately resolves the index mismatch
in the asymptotic negligibility proof.
-/

/-- **BONUS APPLICATION: All shifted Cesàro averages converge to the same limit.**

For an exchangeable sequence, the Cesàro averages starting at different indices
all converge to the same limit:

  (1/m) ∑_{k=0}^{m-1} f(X_{n+k})  →  μ[f∘X₀ | tailSigma X]  in L¹

for ALL n ∈ ℕ.

**This solves the n≠0 case!** We already proved it for n=0 using asymptotic negligibility.
Shift invariance shows that all starting indices give the same limit.

**Proof strategy:**
1. Apply cesaro_to_condexp_L1 for the n=0 case (already have this as axiom)
2. Use shift invariance to show μ[f∘X_n | tail] = μ[f∘X_0 | tail]
3. Conclude that the n≠0 case converges to the same limit

**Status:** This is the payoff! Once we prove shift invariance, this follows immediately.
-/
lemma cesaro_convergence_all_shifts
    (X : ℕ → Ω → α)
    (hX_contract : Exchangeability.Contractable μ X)
    (hX_meas : ∀ i, Measurable (X i))
    (f : α → ℝ)
    (hf_meas : Measurable f)
    (hf_bdd : ∀ x, |f x| ≤ 1)
    (n : ℕ) :
    ∀ ε > 0, ∃ M : ℕ, ∀ m ≥ M,
      ∫ ω, |(1/(m:ℝ)) * ∑ k : Fin m, f (X (n+k) ω) - μ[f ∘ X 0 | tailProcess X] ω| ∂μ < ε := by
  intro ε hε

  -- The key observation: by shift invariance,
  -- μ[f∘X_n | tail] = μ[f∘X_0 | tail]  a.e.

  -- Therefore, we can apply the axiom cesaro_to_condexp_L1 for the shifted sequence
  -- or alternatively, note that the limit is the same for all starting indices

  sorry -- TODO: Complete using shift invariance

end Exchangeability.Tail.ShiftInvariance
