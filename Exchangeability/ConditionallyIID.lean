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
import Exchangeability.Probability.MeasureKernels

/-!
# Conditionally i.i.d. Sequences and de Finetti's Theorem

This file defines **conditionally i.i.d. sequences** and proves that they are
exchangeable. This establishes one direction of de Finetti's representation theorem:
**conditionally i.i.d. ⇒ exchangeable**.

## Main definitions

* `ConditionallyIID μ X`: A sequence `X` is conditionally i.i.d. under measure `μ` if
  there exists a probability kernel `ν : Ω → Measure α` such that coordinates are
  independent given `ν(ω)`, with each coordinate distributed as `ν(ω)`.

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
- **Contractable ⇒ exchangeable** (`DeFinetti/Theorem.lean`): Deep result using ergodic theory.
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
@[nolint unusedArguments]
instance pi_isProbabilityMeasure {ι : Type*} [Fintype ι] {α : ι → Type*}
    [∀ i, MeasurableSpace (α i)] (μ : ∀ i, Measure (α i))
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, SigmaFinite (μ i)] :
    IsProbabilityMeasure (Measure.pi μ) := by
  constructor
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
  convert (MeasureTheory.measurePreserving_piCongrLeft
    (α:=fun _ : ι => α) (μ:=fun _ : ι => ν) (f:=σ.symm)).map_eq using 2
  ext g i
  simp [Function.comp, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]

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
  calc (μ.bind κ).map f
      = Measure.join (Measure.map (fun η => η.map f) (Measure.map κ μ)) := by
        simp only [Measure.bind, Measure.join_map_map hf]
    _ = Measure.join (Measure.map (fun ω => (κ ω).map f) μ) := by
        rw [Measure.map_map (Measure.measurable_map f hf) hκ]; rfl
    _ = μ.bind (fun ω => (κ ω).map f) := rfl

end MeasureTheory.Measure

namespace Exchangeability

/--
A sequence is **conditionally i.i.d.** if there exists a random probability measure
making the coordinates independent.

**Definition:** `X` is conditionally i.i.d. if there exists a probability kernel
`ν : Ω → Measure α` such that for every finite selection of **distinct** indices
`k : Fin m → ℕ` (i.e., strictly monotone), the joint law of `(X_{k(0)}, ..., X_{k(m-1)})`
equals `𝔼[ν^m]`, where `ν^m` is the m-fold product of `ν`.

**Intuition:** There exists a random distribution `ν`, and conditionally on `ν`, the
sequence is i.i.d. with marginal distribution `ν`. Different sample paths may have
different `ν` values, but for each fixed `ν`, the coordinates are independent with
that distribution.

**Example:** Pólya's urn - drawing colored balls with replacement where we add a ball
of the drawn color each time. The limiting proportion of colors is random, and
conditionally on this proportion, the draws are i.i.d. Bernoulli.

**Mathematical formulation:** For each finite selection of distinct indices, we have:
  `P{(X_{k(0)}, ..., X_{k(m-1)}) ∈ ·} = ∫ ν(ω)^m μ(dω)`

**Implementation:** Uses mathlib's `Measure.bind` (Giry monad) and `Measure.pi`
(product measure) to express the mixture of i.i.d. distributions.

**Note on repeated indices:** This definition only requires the product formula for
strictly monotone index functions (distinct coordinates). For non-strictly-monotone
functions (e.g., `k = (0,0,1)`), the correct law involves a duplication map, which
follows trivially from the distinct-indices case. This matches Kallenberg (2005),
Theorem 1.1.

**Reference:** Kallenberg (2005), "Probabilistic Symmetries and Invariance Principles",
Theorem 1.1 (page 27-28).
-/
def ConditionallyIID (μ : Measure Ω) (X : ℕ → Ω → α) : Prop :=
  ∃ ν : Ω → Measure α,
    (∀ ω, IsProbabilityMeasure (ν ω)) ∧
    (∀ B, MeasurableSet B → Measurable (fun ω => ν ω B)) ∧
      ∀ (m : ℕ) (k : Fin m → ℕ), StrictMono k →
        Measure.map (fun ω => fun i : Fin m => X (k i) ω) μ
          = μ.bind (fun ω => Measure.pi fun _ : Fin m => ν ω)

/--
**Main theorem:** Conditionally i.i.d. sequences are exchangeable.

**Statement:** If `X` is conditionally i.i.d., then it is exchangeable (invariant
under finite permutations).

**Proof strategy:**
1. By `ConditionallyIID`, the law of `(X_0, ..., X_{n-1})` is `μ.bind(λω. ν(ω)^n)`
   (using the identity function, which is strictly monotone)
2. Show that permuting coordinates after sampling from this mixture gives the same measure
3. Use `pi_comp_perm` to show that permuting a product measure `ν^n` gives `ν^n` back
4. Use `bind_map_comm` to push the permutation through the bind operation
5. Therefore the law of `(X_{σ(0)}, ..., X_{σ(n-1)})` equals the law of `(X_0, ..., X_{n-1})`

**Intuition:** Permuting the indices doesn't change the distribution because:
- We're still integrating over the same random measure `ν`
- For each fixed `ν`, permuting i.i.d. samples gives the same distribution (by `pi_comp_perm`)

**Mathematical significance:** This proves one direction of de Finetti's theorem.
The converse (exchangeable ⇒ conditionally i.i.d.) is the deep content of de Finetti's
representation theorem and requires constructing the de Finetti measure from the
tail σ-algebra.

This is the "easy" direction because we're given the mixing measure `ν` explicitly.
-/
theorem exchangeable_of_conditionallyIID {μ : Measure Ω} {X : ℕ → Ω → α}
    (hX_meas : ∀ i, Measurable (X i)) (hX : ConditionallyIID μ X) :
    Exchangeable μ X := by
  intro n σ
  obtain ⟨ν, hν_prob, hν_meas_coe, hν_eq⟩ := hX
  have h_id : Measure.map (fun ω i => X i.val ω) μ =
              μ.bind (fun ω => Measure.pi fun _ : Fin n => ν ω) :=
    hν_eq n (fun i => i.val) (fun _ _ => id)
  have hXvec_meas : Measurable (fun ω => fun i : Fin n => X i.val ω) := by
    fun_prop
  have hperm_meas : Measurable (fun f : Fin n → α => f ∘ σ) := by
    fun_prop
  calc Measure.map (fun ω i => X (σ i).val ω) μ
      = Measure.map (fun f => f ∘ σ) (Measure.map (fun ω i => X i.val ω) μ) :=
          (Measure.map_map hperm_meas hXvec_meas).symm
    _ = Measure.map (fun f => f ∘ σ) (μ.bind (fun ω => Measure.pi fun _ : Fin n => ν ω)) := by
          rw [h_id]
    _ = μ.bind (fun ω => Measure.map (fun f => f ∘ σ) (Measure.pi fun _ : Fin n => ν ω)) :=
          MeasureTheory.Measure.bind_map_comm
            (measurable_measure_pi ν hν_prob hν_meas_coe) hperm_meas
    _ = μ.bind (fun ω => Measure.pi fun _ : Fin n => ν ω) := by
          simp_rw [MeasureTheory.Measure.pi_comp_perm σ]
    _ = Measure.map (fun ω i => X i.val ω) μ := h_id.symm

end Exchangeability
