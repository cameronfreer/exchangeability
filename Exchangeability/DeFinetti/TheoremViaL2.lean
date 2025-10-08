/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Exchangeability.DeFinetti.ViaL2
import Exchangeability.DeFinetti.CommonEnding

/-!
# de Finetti's Theorem - L² Proof (Completed)

This file provides the **completed L² proof** of de Finetti's theorem by combining:
- `ViaL2`: Proves convergence A_n_m → α for each bounded f (Kallenberg Lemma 1.2)
- `CommonEnding`: Builds the kernel K from the map f ↦ α and completes the proof

This is **Kallenberg's "second proof"** (pages 26-27), which uses elementary L²
contractability bounds and is the lightest-weight approach with minimal dependencies.

## Proof architecture

The L² approach follows this structure:

1. **ViaL2.weighted_sums_converge_L1**: For contractable sequences X and bounded f,
   the weighted averages `A_n_m(f∘X) = (1/m) Σᵢ f(X_{n+i+1})` converge in L¹ to
   a limit α_f : Ω → ℝ

2. **Tail measurability**: Each α_f is tail-measurable, i.e., measurable with
   respect to the tail σ-algebra (follows from contractability)

3. **CommonEnding.conditional_iid_from_directing_measure**: Given the family
   {α_f}, construct a directing measure ν : Ω → Measure ℝ such that:
   - ν is a probability kernel
   - ν is tail-measurable
   - X is conditionally i.i.d. given ν

This yields the three-way equivalence (Kallenberg Theorem 1.1):
- (i) X is contractable
- (ii) X is exchangeable
- (iii) X is conditionally i.i.d.

## Alternative proofs

For other proof approaches, see:
- `TheoremViaKoopman.lean`: Proof via mean ergodic theorem
- `TheoremViaMartingale.lean`: Proof via reverse martingale convergence

## Current status

**Implementation note**: The actual completion that calls CommonEnding is
currently in ViaL2.lean itself (lines 1547-1563) as a sorry. Once those
sorries are filled, this file will provide the complete, fully-formal proof.

## References

* Kallenberg (2005), *Probabilistic Symmetries and Invariance Principles*,
  Theorem 1.1 (pages 26-27), "Second proof"
-/

noncomputable section
open scoped BigOperators MeasureTheory Topology Classical

namespace Exchangeability.DeFinetti

open MeasureTheory ProbabilityTheory

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
    · -- (i) → (iii): Contractable → ConditionallyIID via L² + CommonEnding
      -- Build the directing measure ν from ViaL2 infrastructure
      let ν := ViaL2.directing_measure X hContract hX_meas hX_L2

      -- Verify the three requirements for CommonEnding.complete_from_directing_measure
      have hν_prob : ∀ ω, IsProbabilityMeasure (ν ω) := by
        intro ω
        exact ViaL2.directing_measure_isProbabilityMeasure X hContract hX_meas hX_L2 ω

      have hν_meas : ∀ (s : Set ℝ), MeasurableSet s →
          Measurable (fun ω => ν ω s) := by
        intro s hs
        exact ViaL2.directing_measure_measurable X hContract hX_meas hX_L2 s hs

      have h_bridge : ∀ {m : ℕ} (k : Fin m → ℕ) (B : Fin m → Set ℝ),
          (∀ i, MeasurableSet (B i)) →
            ∫⁻ ω, ∏ i : Fin m,
                ENNReal.ofReal ((B i).indicator (fun _ => (1 : ℝ)) (X (k i) ω)) ∂μ
              = ∫⁻ ω, ∏ i : Fin m, ν ω (B i) ∂μ := by
        intro m k B hB
        exact ViaL2.directing_measure_bridge X hContract hX_meas hX_L2 k B hB

      -- Apply CommonEnding to complete the proof
      sorry  -- TODO: Apply CommonEnding.complete_from_directing_measure once its sorries are filled

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
