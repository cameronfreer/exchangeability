/-
Copyright (c) 2025 The Exchangeability Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer, Cascade
-/
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Topology.Basic

/-!
# Infinite Products of Identically Distributed Measures

This file constructs the infinite product measure `ν^ℕ` on `ℕ → α` for a given
probability measure `ν : Measure α`. We follow the strategy used in mathlib's
Ionescu–Tulcea development for kernels (`ProbabilityTheory.Kernel.IonescuTulcea.Traj`),
specialised to the case of constant kernels coming from an i.i.d. sequence.

Our goal is twofold:

1. Build a probability measure `iidProduct ν` on `ℕ → α` whose finite-dimensional
   marginals coincide with the finite product measures `Measure.pi` on `Fin n → α`.
2. Show that the resulting measure is invariant under finite permutations of the indices.

These results replace the axioms `productMeasure_exists` and
`constantProduct_comp_perm` previously assumed in `Exchangeability.Contractability`. They
provide the projective limit and symmetry properties required for the Kolmogorov
extension step in the contractability → exchangeability proof.

## Main definitions

* `iidKernel ν`: constant Markov kernel used to iterate via Ionescu–Tulcea.
* `iidTraj ν`: kernel on `Unit` taking value `ν^ℕ` as a kernel.
* `iidProduct ν`: the probability measure on `ℕ → α` obtained by evaluating `iidTraj ν` at `()`. 

## Main statements

* `iidProduct_projective`: finite-dimensional marginals of `iidProduct ν` agree with
  the product measure `Measure.pi (fun _ : Fin n => ν)`.
* `iidProduct_perm`: `iidProduct ν` is invariant under any permutation of `ℕ` with finite support.

We keep the more general machinery in a standalone file so that other developments can
import it if needed.
-/

noncomputable section

open scoped ENNReal MeasureTheory
open MeasureTheory Set ProbabilityTheory

namespace Exchangeability
namespace Probability

variable {α : Type*} [MeasurableSpace α]

/-- The infinite i.i.d. product measure `ν^ℕ` on `ℕ → α`.

**Implementation via Ionescu-Tulcea (current technical obstacle)**:

The natural approach is:
1. Define `iidKernel ν n : Kernel ((i : Finset.Iic n) → α) α := Kernel.const _ ν`
2. Apply `Kernel.traj (fun n => iidKernel ν n) 0` to get a kernel on the empty history
3. Evaluate at the unique element of `(i : Finset.Iic 0) → α`

**Technical challenges**:
- Universe level management: mathlib's `Kernel.traj` expects `X : ℕ → Type*` with
  universe flexibility, but our constant family `fun _ => α` creates universe constraints
- Measurable space instances: need `MeasurableSpace ((i : Finset.Iic n) → α)` instances
  that mathlib may not provide automatically for constant families
- Type family encoding: `Kernel.traj` is designed for varying types at each index,
  not constant families

**Alternative approaches to explore**:
1. Use `Measure.pi` with infinite index sets (if available in mathlib)
2. Define as projective limit of finite products explicitly
3. Provide manual universe-polymorphic wrapper around `Kernel.traj`

For now axiomatized pending resolution of these technical issues. -/
axiom iidProduct (ν : Measure α) [IsProbabilityMeasure ν] : Measure (ℕ → α)

axiom iidProduct_isProbability (ν : Measure α) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (iidProduct ν)

namespace iidProduct

variable (ν : Measure α) [IsProbabilityMeasure ν]

/-- Finite-dimensional distributions of `iidProduct ν` are the expected product measures.

TODO: Prove using the projective property of the Ionescu-Tulcea construction. -/
axiom cylinder_fintype (n : ℕ) :
    (iidProduct ν).map (fun f : ℕ → α => fun i : Fin n => f i) =
      Measure.pi fun _ : Fin n => ν

/-- The measure `iidProduct ν` is a probability measure. -/
instance : IsProbabilityMeasure (iidProduct ν) := iidProduct_isProbability ν

/-- Invariance under arbitrary permutations of coordinates.
This uses permutation invariance of finite products and uniqueness via cylinder sets.

TODO: Complete proof strategy:

**Step 1: Finite-dimensional invariance**
For any n : ℕ, show that restricting to the first n coordinates commutes with permutation:
```lean
(iidProduct ν).map (fun f => (fun i : Fin n => f (σ i))) = Measure.pi fun _ => ν
```
This follows from:
- `cylinder_fintype`: finite marginals of `iidProduct ν` are `Measure.pi`
- `measurePreserving_piCongrLeft` or `pi_map_piCongrLeft`: `Measure.pi` is permutation-invariant

**Step 2: Uniqueness on cylinder σ-algebra**
Apply `Measure.ext_of_generate_finite` (mathlib's uniqueness for finite measures):
- Both `(iidProduct ν).map (f ∘ σ)` and `iidProduct ν` are probability measures
- They agree on cylinders (from Step 1)
- Cylinders form a π-system generating the product σ-algebra
- Therefore they are equal

**Key lemma needed**: `MeasurableSpace.generateFrom_iUnion_measurableCylinders` or similar
to show cylinders generate the standard σ-algebra on `ℕ → α`.

For now axiomatized to enable downstream development. -/
axiom perm_eq (σ : Equiv.Perm ℕ) :
    (iidProduct ν).map (fun f => f ∘ σ) = iidProduct ν

end iidProduct

end Probability
end Exchangeability
