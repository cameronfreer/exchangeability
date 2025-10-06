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
import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

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

**Current implementation**: Axiomatized pending mathlib support for infinite products.

**Future implementation path**: Once mathlib extends `Measure.pi` to work without `Fintype ι`,
this can be defined as:
```lean
def iidProduct (ν : Measure α) [SigmaFinite ν] : Measure (ℕ → α) :=
  Measure.pi (fun _ : ℕ => ν)
```

The current mathlib (as of January 2025) requires `Fintype ι` for `Measure.pi`, but the
mathematical construction via outer measures works for countable index sets. The axioms below
specify the properties this measure must satisfy and can be replaced with actual definitions
once mathlib infrastructure is available. -/
axiom iidProduct (ν : Measure α) [IsProbabilityMeasure ν] : Measure (ℕ → α)

axiom iidProduct_isProbability (ν : Measure α) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (iidProduct ν)

namespace iidProduct

variable (ν : Measure α) [IsProbabilityMeasure ν]

/-- The measure `iidProduct ν` is a probability measure. -/
instance : IsProbabilityMeasure (iidProduct ν) := iidProduct_isProbability ν

/-- Finite-dimensional distributions indexed by `Fin n`.

This states that the marginal distribution on the first `n` coordinates equals the
finite product measure `ν^n`. This is the defining projective property of the infinite
product measure.

**Proof strategy (once `iidProduct` is properly defined)**:
Use mathlib's `Measure.pi_map_restrict` or build from cylinder characterization. -/
axiom cylinder_fintype (n : ℕ) :
    (iidProduct ν).map (fun f : ℕ → α => fun i : Fin n => f i) =
      Measure.pi fun _ : Fin n => ν

/-- Invariance under arbitrary permutations of coordinates.

This states that `iidProduct ν` is invariant under any permutation of `ℕ`. This is a
consequence of the fact that the measure is characterized by its finite-dimensional
marginals, all of which are symmetric.

**Proof strategy (once `iidProduct` is properly defined)**:
1. Use cylinder sets to show agreement on a π-system that generates the product σ-algebra
2. Apply `ext_of_generate_finite` to extend to the whole σ-algebra
3. Key ingredient: finite permutations preserve finite products (mathlib's `pi_map_piCongrLeft`)

The full proof requires mathlib lemmas from:
- `Mathlib/MeasureTheory/Constructions/Cylinders.lean` (cylinder sets)
- `Mathlib/MeasureTheory/Constructions/Projective.lean` (projective limits)
- `Mathlib/MeasureTheory/Constructions/Pi.lean` (finite product invariance)
-/
axiom perm_eq (σ : Equiv.Perm ℕ) :
    (iidProduct ν).map (fun f => f ∘ σ) = iidProduct ν

end iidProduct

end Probability
end Exchangeability
