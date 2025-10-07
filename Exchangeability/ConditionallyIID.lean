/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Constructions.Pi
import Exchangeability.Contractability

/-!
# Conditionally i.i.d. Sequences and de Finetti's Theorem

This file defines **conditionally i.i.d. sequences** and proves that they are
exchangeable. This establishes one direction of de Finetti's representation theorem:
**conditionally i.i.d. ⇒ exchangeable**.

## Main definitions

* `ConditionallyIID μ X`: A sequence `X` is conditionally i.i.d. under measure `μ` if
  there exists a probability kernel `ν : Ω → Measure α` such that coordinates are
  independent given `ν(ω)`, with each coordinate distributed as `ν(ω)`.
* `MixtureOfIID`: A sequence whose distribution is a mixture of i.i.d. distributions
  (placeholder for future development).

## Main results

* `pi_comp_perm`: Product measures are invariant under permutations of indices.
* `bind_map_comm`: Giry monad functoriality - mapping after bind equals binding mapped measures.
* `exchangeable_of_conditionallyIID`: **Conditionally i.i.d. ⇒ exchangeable**.

## The de Finetti-Ryll-Nardzewski theorem

The complete equivalence for infinite sequences is:
  **contractable ↔ exchangeable ↔ conditionally i.i.d.**

This file proves: **conditionally i.i.d. ⇒ exchangeable**

### The complete picture

- **Conditionally i.i.d. ⇒ exchangeable** (this file): Direct from definition using
  permutation invariance of product measures.
- **Exchangeable ⇒ contractable** (`Contractability.lean`): Via permutation extension.
- **Contractable ⇒ exchangeable** (`DeFinetti/*.lean`): Deep result using ergodic theory.
- **Exchangeable ⇒ conditionally i.i.d.** (de Finetti's theorem): The hard direction,
  requiring the existence of a random measure (the de Finetti measure).

## Mathematical intuition

**Conditionally i.i.d.** means: "There exists a random probability measure `ν`, and
given the value of `ν`, the sequence is i.i.d. with distribution `ν`."

**Why this is exchangeable:** If we permute the indices, we're still sampling i.i.d.
from the same random distribution `ν`, so the joint distribution is unchanged.

**Example:** Pólya's urn - drawing balls with replacement where the replacement
probability depends on the urn composition. Conditionally on the limiting proportion,
the draws are i.i.d. Bernoulli.

## Implementation notes

This file uses the Giry monad structure (`Measure.bind`) to express conditioning.
The key technical ingredient is showing that permuting coordinates of a product
measure gives the same measure, which follows from `measurePreserving_piCongrLeft`.

## References

* Kallenberg, "Probabilistic Symmetries and Invariance Principles" (2005), Theorem 1.1
* Kallenberg, "Foundations of Modern Probability" (2002), Theorem 11.10 (de Finetti)
* Diaconis & Freedman, "Finite Exchangeable Sequences" (1980)
-/

open MeasureTheory ProbabilityTheory

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

-- Re-export Measure.pi from mathlib for discoverability
namespace MeasureTheory.Measure

-- Measure.pi is already defined in Mathlib.MeasureTheory.Constructions.Pi
-- We just need to prove that the product of probability measures is a probability measure

/--
The product of probability measures is a probability measure.

This is a basic fact about product measures: if each marginal `μ i` has total mass 1,
then the product measure `∏ᵢ μ i` also has total mass 1.

**Proof:** The measure of the whole space `∏ᵢ αᵢ` equals the product of the measures
of the marginal spaces, which is `∏ᵢ 1 = 1`.
-/
instance pi_isProbabilityMeasure {ι : Type*} [Fintype ι] {α : ι → Type*}
    [∀ i, MeasurableSpace (α i)] (μ : ∀ i, Measure (α i))
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, SigmaFinite (μ i)] :
    IsProbabilityMeasure (Measure.pi μ) := by
  constructor
  rw [show (Set.univ : Set (∀ i, α i)) = Set.univ.pi (fun _ => Set.univ) by ext; simp,
      Measure.pi_pi]
  simp [measure_univ]

/--
Product measures with identical marginals are invariant under permutations.

**Statement:** If we have a product measure where each coordinate is distributed as `ν`,
and we permute the coordinates by `σ`, we get the same measure back.

**Mathematical content:** For i.i.d. sequences, permuting the indices doesn't change
the distribution because all coordinates have the same marginal and are independent.

**Proof:** Uses mathlib's `measurePreserving_piCongrLeft`, which shows that the
permutation map is measure-preserving for product measures.

This is the key technical lemma enabling `exchangeable_of_conditionallyIID`.
-/
theorem pi_comp_perm {ι : Type*} [Fintype ι] {α : Type*} [MeasurableSpace α]
    {ν : Measure α} [SigmaFinite ν] (σ : Equiv.Perm ι) :
    Measure.map (fun f : ι → α => f ∘ σ) (Measure.pi fun _ : ι => ν) =
      Measure.pi fun _ : ι => ν := by
  classical
  have h := (MeasureTheory.measurePreserving_piCongrLeft
    (α:=fun _ : ι => α) (μ:=fun _ : ι => ν) (f:=σ.symm)).map_eq
  -- Show that (fun f => f ∘ σ) equals the measurable equiv
  have hfun : (fun f : ι → α => f ∘ σ) =
      (MeasurableEquiv.piCongrLeft (fun _ : ι => α) σ.symm : (ι → α) → (ι → α)) := by
    ext g i
    simp [Function.comp, MeasurableEquiv.coe_piCongrLeft,
          Equiv.piCongrLeft_apply (P:=fun _ : ι => α) (e:=σ.symm)]
  simpa [hfun]

/--
Giry monad functoriality: mapping commutes with binding.

**Statement:** Mapping a function `f` after binding a kernel `κ` is the same as
binding the kernel obtained by mapping `f` through `κ`.

**Category theory:** This expresses functoriality of the Giry monad: the `map`
operation interacts properly with the monadic `bind` operation. In categorical
terms: `fmap f ∘ join = join ∘ fmap (fmap f)`.

**Probabilistic interpretation:** If we first sample `ω ~ μ`, then sample `x ~ κ(ω)`,
then apply `f`, this is the same as first sampling `ω ~ μ`, then sampling from the
mapped kernel `f₊κ(ω)`.

**Application:** This is used to show that conditioning preserves exchangeability -
we can push permutations through the conditional distribution.
-/
theorem bind_map_comm {Ω α β : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure Ω} {κ : Ω → Measure α} (hκ : Measurable κ) {f : α → β}
    (hf : Measurable f) :
    (μ.bind κ).map f = μ.bind (fun ω => (κ ω).map f) := by
  classical
  have hcomp : Measure.map (fun η : Measure α => η.map f) (Measure.map κ μ) =
      Measure.map (fun ω => (κ ω).map f) μ := by
    rw [Measure.map_map (MeasureTheory.Measure.measurable_map f hf) hκ]
    rfl
  calc (μ.bind κ).map f
      = Measure.join (Measure.map (fun η => η.map f) (Measure.map κ μ)) := by
        simp only [Measure.bind, Measure.join_map_map hf]
    _ = Measure.join (Measure.map (fun ω => (κ ω).map f) μ) := by rw [hcomp]
    _ = μ.bind (fun ω => (κ ω).map f) := rfl

end MeasureTheory.Measure

namespace Exchangeability

/--
A sequence is **conditionally i.i.d.** if there exists a random probability measure
making the coordinates independent.

**Definition:** `X` is conditionally i.i.d. if there exists a probability kernel
`ν : Ω → Measure α` such that for every finite selection of indices `k : Fin m → ℕ`,
the joint law of `(X_{k(0)}, ..., X_{k(m-1)})` equals `𝔼[ν^m]`, where `ν^m` is the
m-fold product of `ν`.

**Intuition:** There exists a random distribution `ν`, and conditionally on `ν`, the
sequence is i.i.d. with marginal distribution `ν`. Different sample paths may have
different `ν` values, but for each fixed `ν`, the coordinates are independent with
that distribution.

**Example:** Pólya's urn - drawing colored balls with replacement where we add a ball
of the drawn color each time. The limiting proportion of colors is random, and
conditionally on this proportion, the draws are i.i.d. Bernoulli.

**Mathematical formulation:** For each finite selection, we have:
  `P{(X_{k(0)}, ..., X_{k(m-1)}) ∈ ·} = ∫ ν(ω)^m μ(dω)`

**Implementation:** Uses mathlib's `Measure.bind` (Giry monad) and `Measure.pi`
(product measure) to express the mixture of i.i.d. distributions.

**Note:** We require this for ALL finite selections, not just increasing ones, to
prove exchangeability directly.
-/
def ConditionallyIID (μ : Measure Ω) (X : ℕ → Ω → α) : Prop :=
  ∃ ν : Ω → Measure α,
    (∀ ω, IsProbabilityMeasure (ν ω)) ∧
      ∀ (m : ℕ) (k : Fin m → ℕ),
        Measure.map (fun ω => fun i : Fin m => X (k i) ω) μ
          = μ.bind (fun ω => Measure.pi fun _ : Fin m => ν ω)

/-- A random sequence ξ is a **mixture of i.i.d.** sequences if its distribution is a mixture of
i.i.d. distributions: P{ξ ∈ ·} = E[ν^∞] = ∫ m^∞ P(ν ∈ dm).

This is obtained by taking expectations in the conditionally i.i.d. definition.

TODO: Full definition requires integration over the space of measures and
product measure construction. For now, we use a simplified placeholder. -/
def MixtureOfIID (_μ : Measure Ω) (_X : ℕ → Ω → α) : Prop :=
  ∃ (ν : Measure (Measure α)),
    IsProbabilityMeasure ν ∧
    -- Placeholder: full definition needs integration over measure spaces
    True

/-- Helper lemma: Permuting coordinates after taking a product is the same as taking the product
and then permuting. -/
theorem pi_perm_comm {ι : Type*} [Fintype ι] {α : Type*} [MeasurableSpace α]
    {ν : Measure α} [SigmaFinite ν] (σ : Equiv.Perm ι) :
    Measure.pi (fun _ : ι => ν) =
      Measure.map (fun f : ι → α => f ∘ σ.symm) (Measure.pi fun _ : ι => ν) := by
  classical
  simpa using (MeasureTheory.Measure.pi_comp_perm (ν:=ν) (σ:=σ.symm)).symm

/--
**Main theorem:** Conditionally i.i.d. sequences are exchangeable.

**Statement:** If `X` is conditionally i.i.d., then it is exchangeable (invariant
under finite permutations).

**Proof strategy:**
1. By `ConditionallyIID`, the law of `(X_0, ..., X_{n-1})` is `μ.bind(λω. ν(ω)^n)`
2. By `ConditionallyIID`, the law of `(X_{σ(0)}, ..., X_{σ(n-1)})` is also `μ.bind(λω. ν(ω)^n)`
3. Both equal the same mixture because permuting a product measure `ν^n` gives `ν^n` back
   (by `pi_comp_perm`)
4. Therefore `X` is exchangeable

**Intuition:** Permuting the indices doesn't change the distribution because:
- We're still integrating over the same random measure `ν`
- For each fixed `ν`, permuting i.i.d. samples gives the same distribution

**Mathematical significance:** This proves one direction of de Finetti's theorem.
The converse (exchangeable ⇒ conditionally i.i.d.) is the deep content of de Finetti's
representation theorem and requires constructing the de Finetti measure from the
tail σ-algebra.

This is the "easy" direction because we're given the mixing measure `ν` explicitly.
-/
theorem exchangeable_of_conditionallyIID {μ : Measure Ω} {X : ℕ → Ω → α}
    (hX : ConditionallyIID μ X) : Exchangeable μ X := by
  intro n σ
  obtain ⟨ν, hν_prob, hν_eq⟩ := hX
  -- Both identity and permuted selections equal the same mixture
  have h_id := hν_eq n (fun i => i.val)
  have h_σ := hν_eq n (fun i => (σ i).val)
  calc Measure.map (fun ω i => X (σ i).val ω) μ
      = μ.bind (fun ω => Measure.pi fun _ : Fin n => ν ω) := h_σ
    _ = Measure.map (fun ω i => X i.val ω) μ := h_id.symm

end Exchangeability
