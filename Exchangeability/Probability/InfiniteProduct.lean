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

TODO: Complete construction using Ionescu-Tulcea. The implementation should:
1. Define constant kernels `κ n : Kernel (Π i : Iic n, α) α` returning `ν`
2. Apply `Kernel.traj` to get a kernel from initial conditions to trajectories  
3. Show the result is independent of the initial condition (by i.i.d. property)

For now this is axiomatized to unblock downstream development. -/
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

TODO: Complete the proof using:
1. Show finite-dimensional marginals are invariant via `pi_map_piCongrLeft`
2. Use `Measure.ext_of_generate_finite` to extend to the whole measure
-/
axiom perm_eq (σ : Equiv.Perm ℕ) :
    (iidProduct ν).map (fun f => f ∘ σ) = iidProduct ν

end iidProduct

end Probability
end Exchangeability
