/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Exchangeability.DeFinetti.CommonEnding
import Exchangeability.Contractability
import Exchangeability.ConditionallyIID
import Exchangeability.DeFinetti.ViaKoopman
import Exchangeability.Bridge.CesaroToCondExp

/-!
# de Finetti's Theorem - Koopman/Ergodic Proof (TODO)

This file will provide the **completed Koopman proof** of de Finetti's theorem
by combining:
- `ViaKoopman`: Proves convergence via Mean Ergodic Theorem (to be implemented)
- `CommonEnding`: Builds the kernel K from the map f ↦ α and completes the proof

This is **Kallenberg's "first proof"** (page 26), which uses the Mean Ergodic
Theorem applied to the Koopman operator on L²(μ).

## Proof architecture

The Koopman approach follows this structure:

1. **ViaKoopman** (to be implemented): Apply the Mean Ergodic Theorem to the
   Koopman operator U : L²(μ) → L²(μ) defined by (Uf)(ω) = f(shift(ω)).

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

## Current status

**TODO**: This file is a stub. The actual proof via ergodic theory has not
been implemented yet. Once `ViaKoopman.lean` is created, this file will
provide the completion.

## References

* Kallenberg (2005), *Probabilistic Symmetries and Invariance Principles*,
  Theorem 1.1 (page 26), "First proof"
* Yosida (1980), *Functional Analysis*, Mean Ergodic Theorem
-/

noncomputable section
open scoped BigOperators MeasureTheory Topology Classical

namespace Exchangeability.DeFinetti

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-!
## Main theorems (Koopman proof)

These theorems connect the general theory to the classical de Finetti result.

**Status**: The equivalence axiom remains unproved because it depends on ViaKoopman.lean's axioms
(particularly `condindep_pair_given_tail`). However, two of the three theorems can be proved
from the equivalence using infrastructure from Contractability.lean and ConditionallyIID.lean.
-/

/-- **Kallenberg Theorem 1.1 (via Koopman)**: Contractable ⇔ (Exchangeable ∧ ConditionallyIID).

This is the three-way equivalence proved using the Mean Ergodic Theorem.

**Proof structure**:
- (i) → (ii): `contractable_of_exchangeable` (in Contractability.lean) ✓
- (ii) → (iii): ViaKoopman (Mean Ergodic Theorem) + CommonEnding [AXIOM]
- (iii) → (ii): `exchangeable_of_conditionallyIID` (in ConditionallyIID.lean) ✓

**Reference**: Kallenberg (2005), Theorem 1.1 (page 26), "First proof".

**Note**: This remains a sorry because the direction (Exchangeable → ConditionallyIID) requires
the full ViaKoopman machinery, which depends on unproved lemmas like `condindep_pair_given_tail`.

**IMPLEMENTATION ANALYSIS** (2025-12-10):

Given the imports from `Contractability` and `ConditionallyIID`, you likely already have a
theorem with this exact content proved via the earlier (non-Koopman) approach. If so, the
easiest implementation is to **reuse the existing equivalence**:

```lean
lemma deFinetti_RyllNardzewski_equivalence_viaKoopman
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ) :
    Contractable μ X ↔ Exchangeable μ X ∧ ConditionallyIID μ X := by
  -- Currently ignore the L² hypothesis; it's only needed for the Koopman proof,
  -- but the statement of the equivalence doesn't care how we prove it
  simpa using
    Exchangeability.DeFinetti.deFinetti_RyllNardzewski_equivalence μ X hX_meas
```

Then `deFinetti_viaKoopman` becomes a different proof (conceptually via Koopman/bridge)
but type-theoretically reuses the existing equivalence without re-doing all machinery.

**Alternative (Koopman-only proof)**: Thread together:
- `exchangeable_implies_ciid_modulo_bridge` from `ViaKoopman.lean`
- `contractable_iff_exchangeable` from `Contractability.lean`
- `exchangeable_of_conditionallyIID` from `ConditionallyIID.lean`

Either way, this is a few lines of glue once the heavy lemmas are in place.
-/

/-- Transfer ConditionallyIID from path space to original space.

If (μ_path X) has conditionally i.i.d. coordinates, then μ has conditionally i.i.d. X.

**Key insight**: The map φ : Ω → ℕ → ℝ defined by φ ω i = X i ω induces a bijection
between the ConditionallyIID conditions:
- For path space: ν' : (ℕ → ℝ) → Measure ℝ is the directing measure
- For original space: ν = ν' ∘ φ is the directing measure
-/
private lemma conditionallyIID_of_path_ciid
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_meas : ∀ i, Measurable (X i))
    (h : ConditionallyIID (Exchangeability.Bridge.CesaroToCondExp.μ_path μ X) (fun i (ω : ℕ → ℝ) => ω i)) :
    ConditionallyIID μ X := by
  -- Extract the directing measure ν' on path space
  obtain ⟨ν', hν'_prob, hν'_meas, h_marginal⟩ := h
  -- Define the pathify map φ : Ω → (ℕ → ℝ)
  let φ : Ω → (ℕ → ℝ) := fun ω i => X i ω
  have hφ_meas : Measurable φ := measurable_pi_lambda _ hX_meas
  -- Define ν = ν' ∘ φ as the directing measure on Ω
  let ν : Ω → Measure ℝ := fun ω => ν' (φ ω)
  refine ⟨ν, ?_, ?_, ?_⟩
  · -- IsProbabilityMeasure (ν ω) for all ω
    intro ω
    exact hν'_prob (φ ω)
  · -- Measurability: ∀ B, MeasurableSet B → Measurable (fun ω => ν ω B)
    intro B hB
    exact (hν'_meas B hB).comp hφ_meas
  · -- Marginal condition
    intro m k hk
    -- Use the fact that μ_path μ X = μ.map φ
    have h_path_def : Exchangeability.Bridge.CesaroToCondExp.μ_path μ X = μ.map φ := rfl
    -- Specialize h_marginal
    specialize h_marginal m k hk
    -- LHS transformation: coordinates on path space compose with φ
    have h_lhs : Measure.map (fun ω' => fun i => ω' (k i)) (μ.map φ)
               = Measure.map (fun ω => fun i => X (k i) ω) μ := by
      rw [Measure.map_map]
      · rfl
      · exact measurable_pi_lambda _ (fun i => measurable_pi_apply (k i))
      · exact hφ_meas
    -- RHS transformation: bind distributes over map
    have h_rhs : (μ.map φ).bind (fun ω' => Measure.pi fun _ => ν' ω')
               = μ.bind (fun ω => Measure.pi fun _ => ν ω) := by
      rw [Measure.bind_map hφ_meas]
      · rfl
      · exact Measure.measurable_measure_prod_mk_left _
    -- Combine
    rw [h_path_def] at h_marginal
    rw [h_lhs, h_marginal, h_rhs]

lemma deFinetti_RyllNardzewski_equivalence_viaKoopman
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_meas : ∀ i, Measurable (X i))
    (hX_L2 : ∀ i, MemLp (X i) 2 μ) :
    Contractable μ X ↔ Exchangeable μ X ∧ ConditionallyIID μ X := by
  constructor
  · -- Forward: Contractable → Exchangeable ∧ ConditionallyIID
    intro hContract
    constructor
    · -- Contractable → ConditionallyIID → Exchangeable
      -- First prove ConditionallyIID via ViaKoopman
      have hCIID : ConditionallyIID μ X := by
        -- Step 1: Get MeasurePreserving shift on path space
        have hσ : MeasurePreserving (Exchangeability.Ergodic.shift (α := ℝ))
                   (Exchangeability.Bridge.CesaroToCondExp.μ_path μ X)
                   (Exchangeability.Bridge.CesaroToCondExp.μ_path μ X) :=
          Exchangeability.Bridge.CesaroToCondExp.measurePreserving_shift_path μ X hContract
        -- Step 2: Apply ViaKoopman's main theorem on path space
        have h_path_ciid : ConditionallyIID (Exchangeability.Bridge.CesaroToCondExp.μ_path μ X)
                            (fun i (ω : ℕ → ℝ) => ω i) :=
          Exchangeability.DeFinetti.ViaKoopman.exchangeable_implies_ciid_modulo_bridge hσ
        -- Step 3: Transfer from path space to original space
        exact conditionallyIID_of_path_ciid μ X hX_meas h_path_ciid
      exact exchangeable_of_conditionallyIID hX_meas hCIID
    · -- Contractable → ConditionallyIID (same as above)
      -- Step 1: Get MeasurePreserving shift on path space
      have hσ : MeasurePreserving (Exchangeability.Ergodic.shift (α := ℝ))
                 (Exchangeability.Bridge.CesaroToCondExp.μ_path μ X)
                 (Exchangeability.Bridge.CesaroToCondExp.μ_path μ X) :=
        Exchangeability.Bridge.CesaroToCondExp.measurePreserving_shift_path μ X hContract
      -- Step 2: Apply ViaKoopman's main theorem on path space
      have h_path_ciid : ConditionallyIID (Exchangeability.Bridge.CesaroToCondExp.μ_path μ X)
                          (fun i (ω : ℕ → ℝ) => ω i) :=
        Exchangeability.DeFinetti.ViaKoopman.exchangeable_implies_ciid_modulo_bridge hσ
      -- Step 3: Transfer from path space to original space
      exact conditionallyIID_of_path_ciid μ X hX_meas h_path_ciid
  · -- Backward: Exchangeable ∧ ConditionallyIID → Contractable
    intro ⟨hExch, _hCIID⟩
    exact contractable_of_exchangeable hExch hX_meas

/-- **De Finetti's Theorem (Koopman proof)**: Exchangeable ⇒ ConditionallyIID.

**Reference**: Kallenberg (2005), Theorem 1.1 (page 26), "First proof".

**Proof**: Apply `contractable_of_exchangeable` to get contractability, then use the equivalence
to extract ConditionallyIID.
-/
theorem deFinetti_viaKoopman
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_meas : ∀ i, Measurable (X i))
    (hX_exch : Exchangeable μ X)
    (hX_L2 : ∀ i, MemLp (X i) 2 μ) :
    ConditionallyIID μ X := by
  have hContract := contractable_of_exchangeable hX_exch hX_meas
  exact ((deFinetti_RyllNardzewski_equivalence_viaKoopman μ X hX_meas hX_L2).mp hContract).2

/-- **Contractable implies conditionally i.i.d.** (via Koopman).

**Reference**: Kallenberg (2005), page 26, "First proof".

**Proof**: Follows directly from the equivalence theorem.
-/
theorem conditionallyIID_of_contractable_viaKoopman
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX_meas : ∀ i, Measurable (X i))
    (hContract : Contractable μ X)
    (hX_L2 : ∀ i, MemLp (X i) 2 μ) :
    ConditionallyIID μ X := by
  exact ((deFinetti_RyllNardzewski_equivalence_viaKoopman μ X hX_meas hX_L2).mp hContract).2

end Exchangeability.DeFinetti
