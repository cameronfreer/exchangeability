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

**Current status:** ⚠️ BLOCKED - Waiting for 3 sorries in ViaMartingale.lean to be resolved
(see ViaMartingale.lean header "Remaining Work" section for details)
-/
theorem conditionallyIID_of_contractable
    [StandardBorelSpace Ω]
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → α) (hX_meas : ∀ i, Measurable (X i))
    (hContract : Contractable μ X) :
    ConditionallyIID μ X := by
  -- IsProbabilityMeasure → IsFiniteMeasure (needed for condExpKernel)
  haveI : IsFiniteMeasure μ := inferInstance

  -- Step 1: Construct the directing measure ν using condExpKernel
  let ν : Ω → Measure α := directingMeasure_of_contractable (μ := μ) X hX_meas

  -- Step 2: Prove ν is a probability measure for each ω
  have hν_prob : ∀ ω, IsProbabilityMeasure (ν ω) := by
    intro ω
    -- ν ω is defined as Measure.map (X 0) (condExpKernel μ (tailSigma X) ω)
    -- by the definition of directingMeasure_of_contractable
    show IsProbabilityMeasure (Measure.map (X 0) (condExpKernel μ (tailSigma X) ω))
    -- condExpKernel is a Markov kernel, so it produces probability measures
    haveI : IsMarkovKernel (condExpKernel μ (tailSigma X)) :=
      ProbabilityTheory.instIsMarkovKernelCondExpKernel
    haveI : IsProbabilityMeasure (condExpKernel μ (tailSigma X) ω) :=
      IsMarkovKernel.is_probability_measure' ω
    -- Measure.map (X 0) preserves probability measures when applied to a probability measure
    constructor
    simp [Measure.map_apply (hX_meas 0) MeasurableSet.univ]

  -- Step 3: Prove measurability of ν
  have hν_meas : ∀ B : Set α, MeasurableSet B → Measurable (fun ω => ν ω B) := by
    intro B hB
    -- ν ω = Measure.map (X 0) (condExpKernel μ (tailSigma X) ω)
    -- So ν ω B = (condExpKernel μ (tailSigma X) ω) ((X 0)⁻¹' B)
    -- We use the fact that fun ω => condExpKernel μ m ω is a measurable kernel
    -- and Measure.map f is measurable in the measure argument
    sorry
    -- TODO: This requires composition of measurable measure-valued functions
    -- The key lemmas needed:
    -- 1. measurable_condExpKernel: fun ω => condExpKernel μ m ω s is measurable
    -- 2. Measure.measurable_map: fun κ => Measure.map f κ is measurable
    -- These need to be composed, but the composition is not straightforward

  -- Step 4: Prove the conditional law property
  have hν_law : ∀ n B, MeasurableSet B →
      (fun ω => (ν ω B).toReal) =ᵐ[μ] μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ (X n) | tailSigma X] := by
    intro n B hB
    -- Strategy: First prove for n=0, then use extreme_members_equal_on_tail

    -- Step 4a: Prove for n=0
    have h0 : (fun ω => (ν ω B).toReal) =ᵐ[μ] μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ (X 0) | tailSigma X] := by
      sorry
      -- This requires:
      -- 1. ν ω B = (Measure.map (X 0) (condExpKernel μ (tailSigma X) ω)) B
      --          = (condExpKernel μ (tailSigma X) ω) ((X 0)⁻¹' B)
      -- 2. The fundamental property of condExpKernel
      -- 3. Relating measure evaluation to conditional expectation of indicators

    -- Step 4b: Use extreme_members_equal_on_tail for general n
    have hn : μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ (X n) | tailSigma X]
            =ᵐ[μ] μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ (X 0) | tailSigma X] :=
      extreme_members_equal_on_tail hContract hX_meas n B hB

    -- Combine: (ν ω B).toReal =ᵐ E[1_B ∘ X₀] =ᵐ E[1_B ∘ Xₙ]
    exact ae_eq_trans h0 hn.symm

  -- Step 5: Apply finite_product_formula
  have hProduct : ∀ (m : ℕ) (k : Fin m → ℕ),
      Measure.map (fun ω => fun i : Fin m => X (k i) ω) μ
        = μ.bind (fun ω => Measure.pi fun _ : Fin m => ν ω) := by
    intro m k
    by_cases hk : StrictMono k
    · -- Strictly monotone case: directly apply finite_product_formula
      exact finite_product_formula X hContract hX_meas ν hν_prob hν_meas hν_law m k hk
    · -- Non-strictly-monotone case
      sorry
      -- Strategy: The product measure on the RHS doesn't depend on k at all -
      -- it's always the same (product of ν ω for each coordinate).
      -- For the LHS, if k has repeated indices, we can use the fact that
      -- repeated sampling from the same measure gives the product measure with repeats.
      -- This should follow from properties of product measures and pushforwards.

  -- Step 6: Package as ConditionallyIID
  exact ⟨ν, hν_prob, hProduct⟩

/-- **De Finetti's Theorem (Martingale proof)**: Exchangeable ⇒ ConditionallyIID.

Uses the fact that exchangeable sequences are contractable.

**Reference**: Kallenberg (2005), Theorem 1.1 (page 27), "Third proof".

**Current status:** ⚠️ BLOCKED - Depends on `conditionallyIID_of_contractable`
-/
theorem deFinetti_viaMartingale
    [StandardBorelSpace Ω]
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → α) (hX_meas : ∀ i, Measurable (X i))
    (hX_exch : Exchangeable μ X) :
    ConditionallyIID μ X := by
  -- Exchangeable implies contractable
  have hContract : Contractable μ X := contractable_of_exchangeable hX_exch hX_meas
  -- Apply the main theorem
  exact conditionallyIID_of_contractable X hX_meas hContract

/-- **Three-way equivalence (Kallenberg Theorem 1.1 via Martingale)**:
Exchangeable ⇔ Contractable ⇔ ConditionallyIID.

This establishes that all three properties are equivalent for sequences on Borel spaces.

**Proof structure**:
- Exchangeable ⇔ Contractable: `contractable_of_exchangeable` and converse (Contractability.lean)
- Contractable → ConditionallyIID: `conditionallyIID_of_contractable` (this file)
- ConditionallyIID → Exchangeable: `exchangeable_of_conditionallyIID` (ConditionallyIID.lean)

**Reference**: Kallenberg (2005), Theorem 1.1 (page 27).

**Current status:** ⚠️ BLOCKED - Depends on `conditionallyIID_of_contractable`
-/
theorem deFinetti_equivalence_exch_condIID
    [StandardBorelSpace Ω]
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → α) (hX_meas : ∀ i, Measurable (X i)) :
    Exchangeable μ X ↔ ConditionallyIID μ X := by
  constructor
  · -- Exchangeable → ConditionallyIID
    intro hExch
    -- Exchangeable → Contractable → ConditionallyIID
    have hContract := contractable_of_exchangeable hExch hX_meas
    exact conditionallyIID_of_contractable X hX_meas hContract
  · -- ConditionallyIID → Exchangeable
    exact exchangeable_of_conditionallyIID

end Exchangeability.DeFinetti
