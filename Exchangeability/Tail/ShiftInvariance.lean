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

    -- The formal implementation requires:
    -- 1. Showing tailProcess X ≤ comap π (tailShift α) (done in TailSigma.lean)
    -- 2. Showing B is T-invariant when A is tail-measurable
    -- 3. Change of variables formula

    -- TODO: Complete the formal proof using the above strategy
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
      rw [← Integrable.map_measure h_meas_comp.aemeasurable h_map_eq]
      exact hf_int.map (hX_meas 0)

    -- Apply uniqueness of conditional expectation
    -- We'll show μ[f ∘ X (n+1) | tail] satisfies the defining property of μ[f ∘ X 0 | tail]
    -- by showing ∫_A f(X(n+1)) dμ = ∫_A f(X 0) dμ for all tail-measurable A.

    -- The sub-σ-algebra condition
    have h_le : tailProcess X ≤ inferInstance := iInf_le_of_le 0 (by
      simp only [tailFamily]
      apply iSup_le
      intro k
      exact MeasurableSpace.comap_le_iff_le_map.mpr (hX_meas k).le)

    -- σ-finiteness of trimmed measure (automatic for probability measures)
    haveI : SigmaFinite (μ.trim h_le) := by
      have : IsFiniteMeasure (μ.trim h_le) := by
        constructor
        rw [trim_measurableSet_eq h_le MeasurableSet.univ]
        exact measure_lt_top μ Set.univ
      exact IsFiniteMeasure.toSigmaFinite

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
