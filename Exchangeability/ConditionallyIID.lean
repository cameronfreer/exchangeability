/-
Copyright (c) 2025 The Exchangeability Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.GiryMonad
import Exchangeability.Contractability

/-!
# Conditionally i.i.d. Sequences

This file defines conditionally i.i.d. and mixed i.i.d. sequences, and establishes the
relationship with exchangeability.

## Main definitions

* `ConditionallyIID`: A sequence is conditionally i.i.d. if there exists a probability kernel
  such that coordinates are independent given the kernel value.
* `MixedIID`: A sequence is mixed i.i.d. if its distribution is a mixture of i.i.d. distributions.

## Main results

* `exchangeable_of_conditionallyIID`: Conditionally i.i.d. implies exchangeable.

## References

* Kallenberg, "Probabilistic Symmetries and Invariance Principles" (2005), Theorem 1.1
-/

open MeasureTheory ProbabilityTheory

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

-- Axioms for missing mathlib infrastructure
namespace MeasureTheory.Measure

/-- Finite product measure construction. Given a family of measures indexed by a finite type,
construct the product measure on the product space.
This is `Measure.pi` in mathlib's MeasureTheory.Constructions.Pi but may not be available yet.

Note: `Measure.bind` already exists in mathlib (imported from GiryMonad), so we only need
to axiomatize the finite product measure construction. -/
axiom pi {ι : Type*} [Fintype ι] {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
    (μ : ∀ i, Measure (α i)) : Measure (∀ i, α i)

/-- The product of probability measures is a probability measure. -/
axiom pi_isProbabilityMeasure {ι : Type*} [Fintype ι] {α : ι → Type*}
    [∀ i, MeasurableSpace (α i)] (μ : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (μ i)] :
    IsProbabilityMeasure (Measure.pi μ)

end MeasureTheory.Measure

namespace Exchangeability

/-- A random sequence `X` is **conditionally i.i.d.** (with respect to `μ`) if there exists a
probability kernel assigning to each base point `ω : Ω` a distribution `ν ω : Measure α` such
that, for every finite selection of indices, the joint law of the corresponding coordinates of
`X` is obtained by averaging the product measure built from `ν ω`.

This formulation expresses that, conditionally on the value of the kernel, the coordinates of
`X` are independent and share the common conditional law `ν ω`.

The definition uses `Measure.pi` (finite product) and `Measure.bind` (kernel bind) which are
assumed as axioms until available in mathlib. -/
def ConditionallyIID (μ : Measure Ω) (X : ℕ → Ω → α) : Prop :=
  ∃ ν : Ω → Measure α,
    (∀ ω, IsProbabilityMeasure (ν ω)) ∧
      ∀ (m : ℕ) (k : Fin m → ℕ) (hk : StrictMono k),
        Measure.map (fun ω => fun i : Fin m => X (k i) ω) μ
          = μ.bind (fun ω => Measure.pi fun _ : Fin m => ν ω)

/-- A random sequence ξ is **mixed i.i.d.** if its distribution is a mixture of
i.i.d. distributions: P{ξ ∈ ·} = E[ν^∞] = ∫ m^∞ P(ν ∈ dm).

This is obtained by taking expectations in the conditionally i.i.d. definition.

TODO: Full definition requires integration over the space of measures and
product measure construction. For now, we use a simplified placeholder. -/
def MixedIID (μ : Measure Ω) (X : ℕ → Ω → α) : Prop :=
  ∃ (ν : Measure (Measure α)),
    IsProbabilityMeasure ν ∧
    -- Placeholder: full definition needs integration over measure spaces
    True

/-- Conditionally i.i.d. implies exchangeable.
If `X` is conditionally i.i.d., then permutations preserve the distribution.

Sketch: by the definition of `ConditionallyIID`, the finite-dimensional distributions of `X`
are given by mixtures of product measures.  Finite permutations act trivially on the product
measure, hence also on the mixture, so the push-forward measures agree.  Filling in the details
requires bookkeeping lemmas on `Measure.bind` and `Measure.pi`, which are still TODO. -/
theorem exchangeable_of_conditionallyIID {μ : Measure Ω} {X : ℕ → Ω → α}
    (hX : ConditionallyIID μ X) : Exchangeable μ X := by
  intro n σ
  -- The formalisation of the sketch above is left for future work.
  sorry

end Exchangeability
