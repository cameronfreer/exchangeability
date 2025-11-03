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
* `deFinetti_viaMartingale`: Exchangeable ⇔ ConditionallyIID

## References

* Kallenberg (2005), *Probabilistic Symmetries and Invariance Principles*,
  Theorem 1.1 (page 27-28), "Third proof" and Lemma 1.3
* Aldous (1983), *Exchangeability and related topics*, École d'Été de
  Probabilités de Saint-Flour XIII
-/

noncomputable section
open scoped BigOperators MeasureTheory Topology Classical

namespace Exchangeability.DeFinetti

open MeasureTheory ProbabilityTheory ViaMartingale

variable {Ω : Type*} [MeasurableSpace Ω]

/-!
## Main theorems (Martingale proof)
-/

/-- **Contractable ⇒ Conditionally i.i.d.** (via martingale).

This is the core result proved using reverse martingale convergence.
The proof constructs the directing measure ν from the tail σ-algebra
and verifies the finite-dimensional product formula.

**Proof strategy:**
1. Define ν := directingMeasure X (constructed from tail σ-algebra)
2. Collect three key facts: ν is probability, measurable, satisfies conditional law
3. Apply finite_product_formula for strictly monotone selections
4. Package as ConditionallyIID

**Reference**: Kallenberg (2005), page 27-28, "Third proof".
-/
theorem conditionallyIID_of_contractable
    [StandardBorelSpace Ω]
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → α) (hX_meas : ∀ i, Measurable (X i))
    (hContract : Contractable μ X) :
    ConditionallyIID μ X := by
  -- Conditional expectation kernels live under a finite-measure assumption
  haveI : IsFiniteMeasure μ := inferInstance

  -- 1) Directing measure from the tail σ-algebra
  set ν : Ω → Measure α := directingMeasure (μ := μ) X with hν_def

  -- 2) νω is a probability measure
  have hν_prob : ∀ ω, IsProbabilityMeasure (ν ω) :=
    directingMeasure_isProb (μ := μ) X

  -- 3) measurability of evaluations ω ↦ νω(B)
  have hν_meas : ∀ B : Set α, MeasurableSet B → Measurable (fun ω => ν ω B) :=
    directingMeasure_measurable_eval (μ := μ) X hX_meas

  -- 4) conditional laws of all coordinates agree with ν
  have hν_law :
      ∀ n (B : Set α), MeasurableSet B →
        (fun ω => (ν ω B).toReal)
          =ᵐ[μ] μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ (X n) | tailSigma X] := by
    intro n B hB
    exact conditional_law_eq_directingMeasure (μ := μ) X hContract hX_meas n B hB

  -- 5) finite-dimensional product formula for strictly-monotone selections
  have hProduct :
      ∀ (m : ℕ) (k : Fin m → ℕ), StrictMono k →
        Measure.map (fun ω => fun i : Fin m => X (k i) ω) μ
          = μ.bind (fun ω => Measure.pi (fun _ : Fin m => ν ω)) := by
    intro m k hk
    exact finite_product_formula X hContract hX_meas ν hν_prob hν_meas hν_law m k hk

  -- 6) package as ConditionallyIID (only needs the StrictMono case)
  exact ⟨ν, hν_prob, hν_meas, hProduct⟩

/-- **de Finetti's theorem (martingale proof):** Exchangeable ⇒ Conditionally i.i.d.

If X is exchangeable, then X is conditionally i.i.d. given the tail σ-algebra.

**Proof path:** Exchangeable → Contractable → ConditionallyIID

**Reference**: Kallenberg (2005), Theorem 1.1 (page 27), "Third proof".
-/
theorem deFinetti
    [StandardBorelSpace Ω]
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → α) (hX_meas : ∀ i, Measurable (X i))
    (hX_exch : Exchangeable μ X) :
    ConditionallyIID μ X := by
  have hContr := contractable_of_exchangeable hX_exch hX_meas
  exact conditionallyIID_of_contractable X hX_meas hContr

/-- **Full equivalence (martingale proof):** Exchangeable ⇔ Conditionally i.i.d.

This establishes the full equivalence between exchangeability and conditional i.i.d.
for sequences on standard Borel spaces.

**Proof structure:**
- (⇒) Exchangeable → Contractable → ConditionallyIID
- (⇐) ConditionallyIID → Exchangeable (from ConditionallyIID.lean)

**Reference**: Kallenberg (2005), Theorem 1.1 (page 27).
-/
theorem deFinetti_equivalence
    [StandardBorelSpace Ω]
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → α) (hX_meas : ∀ i, Measurable (X i)) :
    Exchangeable μ X ↔ ConditionallyIID μ X := by
  constructor
  · exact deFinetti X hX_meas
  · exact exchangeable_of_conditionallyIID hX_meas

/-- **Kallenberg Theorem 1.1 (via martingale):** Three-way equivalence.

This is the full de Finetti-Ryll-Nardzewski equivalence for sequences on standard Borel spaces:
Contractable ↔ Exchangeable ↔ Conditionally i.i.d.

**Proof structure:**
- Contractable → ConditionallyIID: Via reverse martingale convergence (this file)
- ConditionallyIID → Exchangeable: From ConditionallyIID.lean
- Exchangeable → Contractable: From Contractability.lean

**Reference**: Kallenberg (2005), Theorem 1.1 (pages 26-28).
-/
theorem deFinetti_RyllNardzewski_equivalence
    [StandardBorelSpace Ω]
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → α) (hX_meas : ∀ i, Measurable (X i)) :
    Contractable μ X ↔ Exchangeable μ X ∧ ConditionallyIID μ X := by
  constructor
  · intro hContract
    -- Contractable → ConditionallyIID (our main theorem)
    have hCIID := conditionallyIID_of_contractable X hX_meas hContract
    -- ConditionallyIID → Exchangeable
    have hExch := exchangeable_of_conditionallyIID hX_meas hCIID
    exact ⟨hExch, hCIID⟩
  · intro ⟨hExch, _⟩
    -- Exchangeable → Contractable
    exact contractable_of_exchangeable hExch hX_meas

end Exchangeability.DeFinetti
