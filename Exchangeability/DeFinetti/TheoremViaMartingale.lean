/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Exchangeability.DeFinetti.ViaMartingale
import Exchangeability.DeFinetti.CommonEnding
import Exchangeability.Contractability
import Exchangeability.ConditionallyIID

/-!
# de Finetti's Theorem - Martingale Proof

This file provides the **main theorem statements** for de Finetti's theorem
proved using the martingale approach (Kallenberg's "third proof").

## Proof architecture

The martingale approach follows this structure:

1. **ViaMartingale.lean**: Contains all the proof machinery:
   - Reverse martingale convergence for conditional expectations
   - Tail σ-algebra factorization lemmas
   - Construction of the directing measure ν via condExpKernel
   - Finite-dimensional product formula

2. **This file**: Provides clean public-facing theorem statements that
   assemble the machinery from ViaMartingale.lean

## Main results

* `conditionallyIID_of_contractable`: Contractable ⇒ ConditionallyIID
* `deFinetti_viaMartingale`: Exchangeable ⇒ ConditionallyIID (uses contractability)
* `deFinetti_equivalence`: Contractable ⇔ (Exchangeable ∧ ConditionallyIID)

## References

* Kallenberg (2005), *Probabilistic Symmetries and Invariance Principles*,
  Theorem 1.1 (page 27-28), "Third proof" and Lemma 1.3
* Aldous (1983), *Exchangeability and related topics*, École d'Été de
  Probabilités de Saint-Flour XIII
-/

noncomputable section
open scoped BigOperators MeasureTheory Topology Classical

namespace Exchangeability.DeFinetti

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-!
## Main theorems (Martingale proof)
-/

open ViaMartingale

/-- **Contractable implies conditionally i.i.d.** (via Martingale).

This is the core result proved using reverse martingale convergence.
The proof constructs the directing measure ν via conditional expectation kernels
and verifies the finite-dimensional product formula.

**Reference**: Kallenberg (2005), page 27-28, "Third proof".
-/
theorem conditionallyIID_of_contractable
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → α) (hX_meas : ∀ i, Measurable (X i))
    (hContract : Contractable μ X) :
    ConditionallyIID μ X := by
  -- Step 1: Construct the directing measure ν using condExpKernel
  obtain ⟨ν, hν_prob, hν_law, hν_meas⟩ := 
    directingMeasure_of_contractable (μ:=μ) X hX_meas
  
  -- Step 2: Verify it's a ConditionallyIID certificate
  refine ⟨ν, hν_prob, fun m k => ?_⟩
  
  -- Step 3: Prove finite-dimensional product formula
  exact finite_product_formula X hContract hX_meas ν hν_prob hν_meas
    (fun n B hB => conditional_law_eq_directingMeasure X hContract hX_meas ν hν_law n B hB) m k

/-- **De Finetti's Theorem (Martingale proof)**: Exchangeable ⇒ ConditionallyIID.

Uses the fact that exchangeable sequences are contractable.

**Reference**: Kallenberg (2005), Theorem 1.1 (page 27), "Third proof".
-/
theorem deFinetti_viaMartingale
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → α) (hX_meas : ∀ i, Measurable (X i))
    (hX_exch : Exchangeable μ X) :
    ConditionallyIID μ X := by
  -- Exchangeable implies contractable
  have hContract : Contractable μ X := contractable_of_exchangeable X hX_exch
  -- Apply the main theorem
  exact conditionallyIID_of_contractable X hX_meas hContract

/-- **Kallenberg Theorem 1.1 (via Martingale)**: Contractable ⇔ (Exchangeable ∧ ConditionallyIID).

This is the three-way equivalence proved using reverse martingale convergence.

**Proof structure**:
- (i) → (iii): `conditionallyIID_of_contractable` (this file)
- (iii) → (ii): `exchangeable_of_conditionallyIID` (in ConditionallyIID.lean)
- (ii) → (i): `contractable_of_exchangeable` (in Contractability.lean)

**Reference**: Kallenberg (2005), Theorem 1.1 (page 27), "Third proof".
-/
theorem deFinetti_equivalence
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → α) (hX_meas : ∀ i, Measurable (X i)) :
    Contractable μ X ↔ Exchangeable μ X ∧ ConditionallyIID μ X := by
  constructor
  · -- Contractable → (Exchangeable ∧ ConditionallyIID)
    intro hContract
    constructor
    · -- Contractable → Exchangeable
      exact exchangeable_of_contractable X hContract
    · -- Contractable → ConditionallyIID
      exact conditionallyIID_of_contractable X hX_meas hContract
  · -- (Exchangeable ∧ ConditionallyIID) → Contractable
    intro ⟨hExch, _⟩
    exact contractable_of_exchangeable X hExch

end Exchangeability.DeFinetti
