/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Exchangeability.Tail.ShiftInvariantMeasure
import Mathlib.Probability.ConditionalExpectation

/-!
# Shift Invariance of Conditional Expectations for Exchangeable Sequences

This file proves that for exchangeable (contractable) sequences, the conditional expectation
of f∘X_n given the tail σ-algebra does not depend on n.

## Main results

* `condExp_shift_eq_condExp`: For a contractable sequence X and integrable function f,
  `μ[f ∘ X n | tail] =ᵐ[μ] μ[f ∘ X 0 | tail]` for all n.

## Implementation notes

The proof uses the uniqueness characterization of conditional expectation: both sides are
tail-measurable, integrable, and have equal set integrals over all tail-measurable sets.
The set integral equality follows from `setIntegral_comp_shift_eq`.

## References

- Kallenberg (2005), *Probabilistic Symmetries and Invariance Principles*, Theorem 1.2
-/

open MeasureTheory
open Exchangeability.Tail

namespace Exchangeability.Tail.ShiftInvariance

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **Shift invariance of conditional expectation for contractable sequences.**

For a contractable sequence X and integrable function f, the conditional expectation
of f∘X_n given the tail σ-algebra does not depend on n.

This is a standard result in probability theory (see Kallenberg 2005, Theorem 1.2).
The proof uses:
- The shifted process (X_n, X_{n+1}, ...) has the same tail σ-algebra as the original
- Conditional expectations are preserved under this identification
- Uses `setIntegral_comp_shift_eq` as foundation
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
      have h_meas_comp : Measurable (f ∘ X (n + 1)) := hf_meas.comp (hX_meas (n + 1))
      -- The distributions are equal
      have h_map_eq : Measure.map (X (n + 1)) μ = Measure.map (X 0) μ := by
        have h1 := Exchangeability.Contractable.shift_segment_eq hX_contract 1 (n + 1)
        ext s hs
        let S : Set (Fin 1 → α) := {f | f 0 ∈ s}
        have hS : MeasurableSet S := measurable_pi_apply 0 hs
        have h_preimage_n1 : X (n + 1) ⁻¹' s = (fun ω (i : Fin 1) => X ((n + 1) + i.val) ω) ⁻¹' S := by
          ext ω
          simp only [Set.mem_preimage, Set.mem_setOf_eq, S, Fin.val_zero, add_zero]
        have h_preimage_0 : X 0 ⁻¹' s = (fun ω (i : Fin 1) => X i.val ω) ⁻¹' S := by
          ext ω
          simp only [Set.mem_preimage, Set.mem_setOf_eq, S, Fin.val_zero]
        have h_meas_n1 : Measurable (fun ω (i : Fin 1) => X ((n + 1) + i.val) ω) :=
          measurable_pi_lambda _ (fun i => hX_meas ((n + 1) + i.val))
        have h_meas_0 : Measurable (fun ω (i : Fin 1) => X i.val ω) :=
          measurable_pi_lambda _ (fun i => hX_meas i.val)
        rw [Measure.map_apply (hX_meas (n + 1)) hs, Measure.map_apply (hX_meas 0) hs]
        rw [h_preimage_n1, h_preimage_0]
        have h_eq := congrFun (congrArg (·.toOuterMeasure) h1) S
        simp only [Measure.coe_toOuterMeasure] at h_eq
        rw [Measure.map_apply h_meas_n1 hS, Measure.map_apply h_meas_0 hS] at h_eq
        exact h_eq
      have hf_aesm_0 : AEStronglyMeasurable f (Measure.map (X 0) μ) :=
        hf_meas.aestronglyMeasurable
      have h_int_map : Integrable f (Measure.map (X 0) μ) :=
        (integrable_map_measure hf_aesm_0 (hX_meas 0).aemeasurable).mpr hf_int
      rw [← h_map_eq] at h_int_map
      have hf_aesm_n1 : AEStronglyMeasurable f (Measure.map (X (n + 1)) μ) :=
        hf_meas.aestronglyMeasurable
      exact (integrable_map_measure hf_aesm_n1 (hX_meas (n + 1)).aemeasurable).mp h_int_map

    -- Apply uniqueness of conditional expectation
    -- The sub-σ-algebra condition
    have h_le : tailProcess X ≤ (inferInstance : MeasurableSpace Ω) := iInf_le_of_le 0 (by
      simp only [tailFamily]
      apply iSup_le
      intro k
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
    apply ae_eq_condExp_of_forall_setIntegral_eq h_le hf_int

    -- g is integrable on finite-measure tail-measurable sets
    · intro s hs hμs
      exact integrable_condExp.integrableOn

    -- The key: ∫_A condExp dμ = ∫_A f(X 0) dμ
    · intro s hs hμs
      rw [setIntegral_condExp h_le hf_int_n hs]
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
