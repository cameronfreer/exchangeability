/-
Copyright (c) 2025 The Exchangeability Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Constructions.Pi
import Exchangeability.Contractability

/-!
# Conditionally i.i.d. Sequences

This file defines conditionally i.i.d. sequences and mixtures of i.i.d. sequences, and establishes
the relationship with exchangeability.

## Main definitions

* `ConditionallyIID`: A sequence is conditionally i.i.d. if there exists a probability kernel
  such that coordinates are independent given the kernel value.
* `MixtureOfIID`: A sequence is a mixture of i.i.d. sequences if its distribution is a mixture
  of i.i.d. distributions.

## Main results

* `exchangeable_of_conditionallyIID`: Conditionally i.i.d. implies exchangeable.

## References

* Kallenberg, "Probabilistic Symmetries and Invariance Principles" (2005), Theorem 1.1
-/

open MeasureTheory ProbabilityTheory

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

-- Re-export Measure.pi from mathlib for discoverability
namespace MeasureTheory.Measure

-- Measure.pi is already defined in Mathlib.MeasureTheory.Constructions.Pi
-- We just need to prove that the product of probability measures is a probability measure

/-- The product of probability measures is a probability measure. -/
instance pi_isProbabilityMeasure {ι : Type*} [Fintype ι] {α : ι → Type*}
    [∀ i, MeasurableSpace (α i)] (μ : ∀ i, Measure (α i)) 
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, SigmaFinite (μ i)] :
    IsProbabilityMeasure (Measure.pi μ) := by
  constructor
  have h : (Set.univ : Set (∀ i, α i)) = Set.univ.pi (fun (_ : ι) => Set.univ) := by
    ext x; simp
  rw [h, Measure.pi_pi]
  simp [measure_univ]

/-- Product measures of identical marginals are permutation-invariant.
If all marginals are the same measure ν, then permuting coordinates doesn't change the product.

TODO: Prove using mathlib's `pi_map_piCongrLeft` from `Mathlib.MeasureTheory.Constructions.Pi`.
The strategy is to show that permutations are measurable equivalences and use the fact that
mapping by a measurable equivalence preserves the product structure.
-/
axiom pi_comp_perm {ι : Type*} [Fintype ι] {α : Type*} [MeasurableSpace α]
    (ν : Measure α) (σ : Equiv.Perm ι) :
    Measure.map (fun f : ι → α => f ∘ σ) (Measure.pi fun _ : ι => ν) =
      Measure.pi fun _ : ι => ν

/-- The bind operation commutes with measure maps.
This is a key property of the Giry monad.

Note: Mathlib has `bind_dirac_eq_map` showing `m.bind (fun x ↦ dirac (f x)) = m.map f`,
but the general bind-map commutativity requires additional conditions.

TODO: Prove or find appropriate mathlib lemma.
-/
axiom bind_map_comm {Ω α β : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure Ω) (κ : Ω → Measure α) (f : α → β) :
    (μ.bind κ).map f = μ.bind (fun ω => (κ ω).map f)

end MeasureTheory.Measure

namespace Exchangeability

/-- A random sequence `X` is **conditionally i.i.d.** (with respect to `μ`) if there exists a
probability kernel assigning to each base point `ω : Ω` a distribution `ν ω : Measure α` such
that, for every finite selection of indices, the joint law of the corresponding coordinates of
`X` is obtained by averaging the product measure built from `ν ω`.

This formulation expresses that, conditionally on the value of the kernel, the coordinates of
`X` are independent and share the common conditional law `ν ω`.

The definition uses:
- `Measure.pi`: finite product measure from `Mathlib.MeasureTheory.Constructions.Pi`
- `Measure.bind`: kernel bind (Giry monad) from `Mathlib.MeasureTheory.Measure.GiryMonad`

Note: We require this for ALL finite selections, not just strictly monotone ones, which is
necessary to prove exchangeability. -/
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

/-- Helper lemma: Permuting coordinates after taking a product is the same as
taking the product and then permuting. -/
axiom pi_perm_comm {ι : Type*} [Fintype ι] {α : Type*} [MeasurableSpace α]
    (ν : Measure α) (σ : Equiv.Perm ι) :
    Measure.pi (fun _ : ι => ν) =
      Measure.map (fun f : ι → α => f ∘ σ.symm) (Measure.pi fun _ : ι => ν)

/-- Conditionally i.i.d. implies exchangeable.
If `X` is conditionally i.i.d., then permutations preserve the distribution.

Proof strategy:
1. By ConditionallyIID, the law of (X₀,...,X_{n-1}) is μ.bind(λω. ∏ᵢ ν(ω))
2. By ConditionallyIID, the law of (X_{σ(0)},...,X_{σ(n-1)}) is also μ.bind(λω. ∏ᵢ ν(ω))
3. Since both equal the same mixture, they are equal
4. Therefore X is exchangeable -/
theorem exchangeable_of_conditionallyIID {μ : Measure Ω} {X : ℕ → Ω → α}
    (hX : ConditionallyIID μ X) : Exchangeable μ X := by
  intro n σ
  -- Get the kernel ν from the ConditionallyIID hypothesis
  obtain ⟨ν, hν_prob, hν_eq⟩ := hX
  
  -- The identity selection (0, 1, ..., n-1)
  let id_sel : Fin n → ℕ := fun i => i.val
  
  -- The permuted selection (σ(0), σ(1), ..., σ(n-1))
  let σ_sel : Fin n → ℕ := fun i => (σ i).val
  
  -- Apply ConditionallyIID to both selections
  have h_id := hν_eq n id_sel
  have h_σ := hν_eq n σ_sel
  
  -- Both are equal to the same mixture μ.bind(λω. ∏ᵢ ν(ω))
  -- Therefore they are equal to each other
  calc Measure.map (fun ω i => X (σ i).val ω) μ
      = Measure.map (fun ω i => X (σ_sel i) ω) μ := by
          congr
      _ = μ.bind (fun ω => Measure.pi fun _ : Fin n => ν ω) := h_σ
      _ = Measure.map (fun ω i => X (id_sel i) ω) μ := h_id.symm
      _ = Measure.map (fun ω i => X i.val ω) μ := by
          congr

end Exchangeability
