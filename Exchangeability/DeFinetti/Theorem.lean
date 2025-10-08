/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Exchangeability.DeFinetti.ViaL2
import Exchangeability.DeFinetti.CommonEnding

/-!
# de Finetti's Theorem - Completed Proofs

This file provides the **completed proofs** of de Finetti's theorem by combining:
- `ViaL2`: Proves convergence A_n_m → α for each bounded f (Kallenberg Lemma 1.2)
- `CommonEnding`: Builds the kernel K from the map f ↦ α and completes the proof

## Proof architecture

The L² approach (Kallenberg's "second proof", pages 26-27) follows this structure:

1. **ViaL2.weighted_sums_converge_L1**: For contractable sequences X and bounded f,
   the weighted averages `A_n_m(f∘X) = (1/m) Σᵢ f(X_{n+i+1})` converge in L¹ to
   a limit α_f : Ω → ℝ

2. **Tail measurability** (to be proved): Each α_f is tail-measurable, i.e.,
   measurable with respect to the tail σ-algebra

3. **CommonEnding.conditional_iid_from_directing_measure**: Given the family
   {α_f}, construct a directing measure ν : Ω → Measure ℝ such that
   - ν is a probability kernel
   - ν is tail-measurable
   - X is conditionally i.i.d. given ν

This yields the three-way equivalence (Kallenberg Theorem 1.1):
- (i) X is contractable
- (ii) X is exchangeable
- (iii) X is conditionally i.i.d.

## Alternative proofs (future)

- `ViaKoopman.lean` + `CommonEnding` → proof via mean ergodic theorem
- `ViaMartingale.lean` + `CommonEnding` → proof via reverse martingale convergence

## Current status

**Implementation note**: The actual completion of `deFinetti_viaL2` that calls
CommonEnding is currently in ViaL2.lean itself (lines 1547-1563) as a sorry.
The completion requires:
1. Implementing the limit operator Λ : (bounded f) ↦ α_f
2. Proving tail-measurability of α_f
3. Building ν from the conditional expectation structure
4. Calling CommonEnding.conditional_iid_from_directing_measure

This file re-exports the main theorems for easy access.

## References

* Kallenberg (2005), *Probabilistic Symmetries and Invariance Principles*,
  Theorem 1.1 (pages 26-27)
-/

noncomputable section
open scoped BigOperators MeasureTheory Topology Classical

namespace Exchangeability.DeFinetti

open MeasureTheory ProbabilityTheory
open Exchangeability.Contractability
open Exchangeability.ConditionallyIID

variable {Ω : Type*} [MeasurableSpace Ω]

/-!
## Main theorems (L² proof)

These are the user-facing theorems that complete Kallenberg Theorem 1.1.
The actual proofs are in ViaL2.lean.
-/

/-- **Kallenberg Theorem 1.1 (via L²)**: Contractable ⇔ (Exchangeable ∧ ConditionallyIID).

This is the completed three-way equivalence for real-valued sequences.

**Proof structure**:
- (i) → (iii): ViaL2 (L² contractability bounds) + CommonEnding
- (iii) → (ii): `exchangeable_of_conditionallyIID` (in ConditionallyIID.lean)
- (ii) → (i): `contractable_of_exchangeable` (in Contractability.lean)

**Reference**: Kallenberg (2005), Theorem 1.1 (pages 26-27), "Second proof".
-/
theorem deFinetti_RyllNardzewski_equivalence
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ) :
    Contractable μ X ↔ Exchangeable μ X ∧ ConditionallyIID μ X := by
  constructor
  · intro hContract
    constructor
    · -- (i) → (ii): Contractable → Exchangeable
      exact exchangeable_of_contractable hContract hX_meas
    · -- (i) → (iii): Contractable → ConditionallyIID
      -- This is the deep result proved via ViaL2 + CommonEnding
      -- Currently ViaL2.deFinetti_viaL2 has the proof structure but with sorries
      -- Once those are filled, we can call it here
      sorry  -- TODO: Call ViaL2.deFinetti_viaL2 once CommonEnding integration is complete
  · intro ⟨hExch, _hCIID⟩
    -- (ii) → (i): Exchangeable → Contractable (already proved)
    exact contractable_of_exchangeable hExch hX_meas

/-- **De Finetti's Theorem (L² proof)**: Exchangeable ⇒ ConditionallyIID.

This is the standard statement of de Finetti's theorem for real-valued sequences.

**Proof**: Exchangeable → Contractable → ConditionallyIID via the L² approach.

**Reference**: Kallenberg (2005), Theorem 1.1.
-/
theorem deFinetti
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_meas : ∀ i, Measurable (X i))
    (hX_exch : Exchangeable μ X)
    (hX_L2 : ∀ i, MemLp (X i) 2 μ) :
    ConditionallyIID μ X := by
  -- Exchangeable → Contractable (proved in Contractability.lean)
  have hContract := contractable_of_exchangeable hX_exch hX_meas
  -- Contractable → ConditionallyIID (ViaL2 + CommonEnding)
  exact (deFinetti_RyllNardzewski_equivalence μ X hX_meas hX_L2).mp hContract |>.2

/-- **Contractable implies conditionally i.i.d.** (direct statement).

This is sometimes called the "contractable de Finetti" theorem.

**Proof**: Via L² bounds (Kallenberg Lemma 1.2) + CommonEnding.

**Reference**: Kallenberg (2005), page 27, "Second proof".
-/
theorem conditionallyIID_of_contractable
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_meas : ∀ i, Measurable (X i))
    (hContract : Contractable μ X)
    (hX_L2 : ∀ i, MemLp (X i) 2 μ) :
    ConditionallyIID μ X := by
  exact (deFinetti_RyllNardzewski_equivalence μ X hX_meas hX_L2).mp hContract |>.2

end Exchangeability.DeFinetti
