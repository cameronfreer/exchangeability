/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Exchangeability.Contractability
import Exchangeability.ConditionallyIID
import Exchangeability.DeFinetti.ViaKoopman
import Exchangeability.Bridge.CesaroToCondExp

/-!
# de Finetti's Theorem - Koopman/Ergodic Proof

This file provides the **completed Koopman proof** of de Finetti's theorem
using `ViaKoopman` which proves conditional i.i.d. via block averaging and
the Mean Ergodic Theorem.

This is **Kallenberg's "first proof"** (page 26), which uses the Mean Ergodic
Theorem applied to the Koopman operator on L²(μ).

## Proof architecture

The Koopman approach follows this structure:

1. **ViaKoopman**: Apply the Mean Ergodic Theorem to the Koopman operator
   U : L²(μ) → L²(μ) defined by (Uf)(ω) = f(shift(ω)).

   For contractable sequences, the shift operator preserves the measure μ
   (up to contractability), and ergodic theory gives convergence of
   Cesàro averages to the projection onto shift-invariant functions.

2. **Tail measurability**: The limit functions α_f are tail-measurable
   (shift-invariant functions live in the tail σ-algebra)

3. **CommonEnding.conditional_iid_from_directing_measure**: Given the family
   {α_f}, construct the directing measure ν and complete the proof

## Dependencies

This approach requires:
- Mean Ergodic Theorem from mathlib (heavy ergodic theory dependencies)
- Koopman operator theory
- Connection between contractability and shift-invariance

## References

* Kallenberg (2005), *Probabilistic Symmetries and Invariance Principles*,
  Theorem 1.1 (page 26), "First proof"
* Yosida (1980), *Functional Analysis*, Mean Ergodic Theorem
-/

noncomputable section
open scoped BigOperators MeasureTheory Topology Classical

namespace Exchangeability.DeFinetti

open MeasureTheory ProbabilityTheory
open Exchangeability (reindex pathLaw FullyExchangeable exchangeable_iff_fullyExchangeable
                      fullyExchangeable_iff_pathLaw_invariant Contractable contractable_of_exchangeable)
open Exchangeability.Bridge (μ_path pathify measurePreserving_shift_path)
open Exchangeability.PathSpace (shift)

variable {Ω : Type*} [MeasurableSpace Ω]

/-!
## Main theorems (Koopman proof)

These theorems connect the general theory to the classical de Finetti result.

**Status**: The Koopman proof uses the Mean Ergodic Theorem approach. The key insight is that
exchangeability implies full exchangeability (via `exchangeable_iff_fullyExchangeable`), which
gives path measure exchangeability needed for the ergodic machinery.
-/

lemma deFinetti_RyllNardzewski_equivalence_viaKoopman
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_meas : ∀ i, Measurable (X i)) :
    Contractable μ X ↔ Exchangeable μ X ∧ ConditionallyIID μ X := by
  constructor
  · -- Forward: Contractable → Exchangeable ∧ ConditionallyIID
    -- This is Kallenberg's "first proof" using disjoint-block averaging.
    -- Key insight: We prove ConditionallyIID FIRST, then derive Exchangeable from it.
    -- This avoids the circular dependency of trying to derive Exchangeability from
    -- Contractability directly (which IS de Finetti's theorem!).
    intro hContract
    -- Step 1: Push contractability to path space
    have hPathContract := pathSpace_contractable_of_contractable X hX_meas hContract
    -- Step 2: Get shift-preservation on path space
    have hσ := pathSpace_shift_preserving_of_contractable X hX_meas hContract
    haveI : IsProbabilityMeasure (μ_path μ X) :=
      Exchangeability.Bridge.isProbabilityMeasure_μ_path μ X hX_meas
    -- Step 3: Apply CONTRACTABLE theorem directly (NOT exchangeable_implies_ciid_modulo_bridge!)
    -- This uses conditionallyIID_bind_of_contractable which takes (hσ, hContract)
    -- without requiring exchangeability. The bridge condition extends from StrictMono
    -- to arbitrary Injective indices using sorting + product commutativity.
    have h_path_ciid : ConditionallyIID (μ_path μ X) (fun i (ω : ℕ → ℝ) => ω i) :=
      conditionallyIID_bind_of_contractable hσ hPathContract
    -- Step 4: Transfer from path space to original space
    have hCIID : ConditionallyIID μ X :=
      conditionallyIID_transfer X hX_meas h_path_ciid
    -- Step 5: Get Exchangeable from ConditionallyIID (the "obvious" direction per Kallenberg)
    have hExch : Exchangeable μ X := exchangeable_of_conditionallyIID hX_meas hCIID
    exact ⟨hExch, hCIID⟩
  · -- Backward: Exchangeable ∧ ConditionallyIID → Contractable
    intro ⟨hExch, _hCIID⟩
    exact contractable_of_exchangeable hExch hX_meas

/-- **De Finetti's Theorem (Koopman proof)**: Exchangeable ⇒ ConditionallyIID.

**Reference**: Kallenberg (2005), Theorem 1.1 (page 26), "First proof".

**Proof**: Direct proof using the Mean Ergodic Theorem approach:
1. Get contractability from exchangeability (for shift invariance)
2. Get path exchangeability from exchangeability (via fullyExchangeable)
3. Apply Koopman ergodic machinery
4. Transfer from path space to original space
-/
theorem deFinetti_viaKoopman
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_meas : ∀ i, Measurable (X i))
    (hX_exch : Exchangeable μ X) :
    ConditionallyIID μ X :=
  ((deFinetti_RyllNardzewski_equivalence_viaKoopman μ X hX_meas).mp
    (contractable_of_exchangeable hX_exch hX_meas)).2

/-- **Contractable implies conditionally i.i.d.** (via Koopman).

**Reference**: Kallenberg (2005), page 26, "First proof".

**Proof**: Follows directly from the equivalence theorem.
-/
theorem conditionallyIID_of_contractable_viaKoopman
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_meas : ∀ i, Measurable (X i))
    (hContract : Contractable μ X) :
    ConditionallyIID μ X :=
  ((deFinetti_RyllNardzewski_equivalence_viaKoopman μ X hX_meas).mp hContract).2

end Exchangeability.DeFinetti
