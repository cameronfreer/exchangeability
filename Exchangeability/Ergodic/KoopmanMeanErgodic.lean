/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.MeanErgodic
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Exchangeability.PathSpace.Shift

/-!
# Koopman Operator and the Mean Ergodic Theorem

This file develops the **Koopman operator** approach to de Finetti's theorem, using
ergodic theory and the Mean Ergodic Theorem to characterize Birkhoff averages.

## Mathematical background

The **Mean Ergodic Theorem** is a fundamental result in ergodic theory that generalizes
the law of large numbers. For a measure-preserving transformation `T : Ω → Ω` on a
probability space, Birkhoff averages of L² functions converge:

  `n⁻¹ ∑ᵢ₌₀ⁿ⁻¹ f(Tⁱω) → 𝔼[f | invariant σ-algebra]`

The **Koopman operator** `U : L²(μ) → L²(μ)` is defined by `(Uf)(ω) = f(Tω)`. It's
a unitary operator when `T` is measure-preserving, and the Mean Ergodic Theorem says
Birkhoff averages converge to the projection onto the fixed-point subspace
`{f : Uf = f}`.

## Application to de Finetti

For the **left shift** `T(ω₀, ω₁, ω₂, ...) = (ω₁, ω₂, ω₃, ...)` on path space:
1. The shift is measure-preserving for i.i.d. and exchangeable sequences
2. The fixed-point subspace `{f : f ∘ shift = f}` consists of tail-measurable functions
3. The Mean Ergodic Theorem gives convergence to conditional expectation onto the
   tail σ-algebra
4. For exchangeable sequences, this yields de Finetti's representation

## Main definitions

* `shift`: The left shift on path space `ℕ → α`, defined by `(shift ω) n = ω(n+1)`
* `koopman`: The Koopman operator on `L²(μ)` induced by a measure-preserving
  transformation, acting by composition

## Main results

* `measurable_shift`: The shift map is measurable (re-exported from `PathSpace.Shift`)
* `birkhoffAverage_tendsto_metProjection`: **Birkhoff averages converge in L² to the
  projection onto the fixed-point subspace** (via Mean Ergodic Theorem)

## The ergodic approach to exchangeability

This provides one path to proving de Finetti's theorem:
1. **Exchangeability** ⇒ shift-invariance of the measure
2. **Mean Ergodic Theorem** ⇒ convergence to conditional expectation on tail σ-algebra
3. **Tail σ-algebra** ⇒ de Finetti measure (random probability)
4. **Representation** ⇒ conditionally i.i.d. structure

This is more sophisticated than the direct π-system approach but provides deeper
ergodic theory insights.

## References

* Kallenberg, "Probabilistic Symmetries and Invariance Principles" (2005), Chapter 1
* Krengel, "Ergodic Theorems" (1985), Chapter 2 (Mean Ergodic Theorem)
* Walters, "An Introduction to Ergodic Theory" (1982), Chapter 4
-/

noncomputable section

namespace Exchangeability.Ergodic

open MeasureTheory Filter Topology
open Exchangeability.PathSpace (shift shift_measurable measurable_shift)

open scoped ENNReal

variable {α : Type*} [MeasurableSpace α]

-- Ensure Lp spaces work with p = 2
attribute [local instance] fact_one_le_two_ennreal

variable {Ω : Type*} [MeasurableSpace Ω]

/--
The Koopman operator: composition with a measure-preserving transformation.

**Definition:** For a measure-preserving `T : Ω → Ω`, the Koopman operator on `L²(μ)`
is defined by `(U f)(ω) = f(T ω)`.

**Properties:**
- **Linear:** `U(af + bg) = aUf + bUg`
- **Isometric:** `‖Uf‖ = ‖f‖` (preserves L² norm)
- **Unitary:** When `T` is invertible and measure-preserving

**Intuition:** The Koopman operator "pulls back" functions along the dynamics. If `T`
represents time evolution, `Uf` is the composition of `f` with one time step.

**Role in ergodic theory:** The eigenspaces of the Koopman operator correspond to
different frequencies of the dynamics. The fixed-point subspace `{f : Uf = f}`
consists of functions constant along orbits (the invariant σ-algebra).

**Application to de Finetti:** For the shift on path space, the fixed-point subspace
is the tail σ-algebra, and the Mean Ergodic Theorem shows convergence to conditional
expectation onto this σ-algebra.
-/
@[nolint unusedArguments]
def koopman {μ : Measure Ω} [IsProbabilityMeasure μ] (T : Ω → Ω) (hT : MeasurePreserving T μ μ) :
    Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  (MeasureTheory.Lp.compMeasurePreservingₗᵢ ℝ T hT).toContinuousLinearMap

/--
The Koopman operator is an isometry.

This follows from measure-preservation: if `T` preserves the measure, then composition
with `T` preserves the L² norm.
-/
lemma koopman_isometry {μ : Measure Ω} [IsProbabilityMeasure μ] (T : Ω → Ω) (hT : MeasurePreserving T μ μ) :
    Isometry (koopman T hT) :=
  (MeasureTheory.Lp.compMeasurePreservingₗᵢ ℝ T hT).isometry
/--
The fixed-point subspace of a continuous linear map.

**Definition:** `fixedSpace U = {x : U x = x}` - the set of vectors fixed by `U`.

**Intuition:** In dynamical systems, the fixed points represent the "steady states" -
states that don't change under the dynamics. For the Koopman operator, the fixed-point
subspace consists of functions that are invariant along orbits of the transformation.

**Role in ergodic theory:** For a measure-preserving transformation `T : Ω → Ω`, the
fixed-point subspace of the Koopman operator `U(f) = f ∘ T` consists of functions
constant along orbits - equivalently, functions measurable with respect to the
invariant σ-algebra.

**Application to de Finetti:** For the shift on path space `Ω[α] = ℕ → α`, the
fixed-point subspace is the tail σ-algebra. Functions `f : Ω[α] → ℝ` that satisfy
`f(shift ω) = f(ω)` are precisely those that depend only on the "tail" of the sequence,
ignoring finitely many initial values. The Mean Ergodic Theorem then shows that
Birkhoff averages converge to the conditional expectation onto this tail σ-algebra.
-/
def fixedSpace {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : E →L[ℝ] E) : Submodule ℝ E :=
  LinearMap.eqLocus U.toLinearMap 1

/--
The Mean Ergodic Theorem projection: orthogonal projection onto the fixed-point subspace.

**Definition:** For a measure-preserving transformation `T`, this is the orthogonal
projection `P : L²(μ) → L²(μ)` onto the fixed-point subspace of the Koopman operator.

**Construction:**
1. Let `S = fixedSpace(koopman T)` be the set of functions invariant under composition with `T`
2. Show `S` is a closed subspace (follows from continuity of the Koopman operator)
3. Construct the orthogonal projection onto `S` using Hilbert space theory
4. Return the composition of the projection and subtype inclusion

**Properties:**
- **Idempotent:** `P² = P` (projecting twice = projecting once)
- **Self-adjoint:** `⟨Pf, g⟩ = ⟨f, Pg⟩` (symmetric in the inner product)
- **Range:** `P(L²) = fixedSpace(koopman T)` (hits exactly the fixed-point subspace)
- **Minimality:** `Pf` is the closest point in the fixed-point subspace to `f`

**Mathematical significance:** The Mean Ergodic Theorem states that Birkhoff averages
converge to this projection:

  `n⁻¹ ∑ᵢ₌₀ⁿ⁻¹ f(Tⁱω) → (Pf)(ω)`  in L²

For the shift on path space, this becomes:

  `n⁻¹ ∑ᵢ₌₀ⁿ⁻¹ f(ω_i, ω_{i+1}, ...) → 𝔼[f | tail σ-algebra]`

This is the key step in the ergodic proof of de Finetti's theorem.

**Uniqueness:** By the uniqueness of orthogonal projections, this is the *unique*
continuous linear map `P` satisfying the properties above. This allows us to identify
it with conditional expectation onto the tail σ-algebra.
-/
noncomputable def metProjection {μ : Measure Ω} [IsProbabilityMeasure μ]
    (T : Ω → Ω) (hT : MeasurePreserving T μ μ) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ := by
  classical
  let S := fixedSpace (koopman T hT)
  let K := koopman T hT
  have hS_closed : IsClosed (S : Set (Lp ℝ 2 μ)) := by
    have hset : (S : Set (Lp ℝ 2 μ)) = (fun x => K x - x) ⁻¹' {0} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, SetLike.mem_coe, sub_eq_zero]
      rfl
    rw [hset]
    exact isClosed_singleton.preimage (K.continuous.sub continuous_id)
  haveI : CompleteSpace S := hS_closed.completeSpace_coe
  haveI : S.HasOrthogonalProjection := Submodule.HasOrthogonalProjection.ofCompleteSpace S
  exact S.subtypeL.comp S.orthogonalProjection

/--
**The Mean Ergodic Theorem:** Birkhoff averages converge in L² to the orthogonal projection
onto the fixed-point subspace.

**Statement:** For a measure-preserving transformation `T` and any `f ∈ L²(μ)`,

  `n⁻¹ ∑ᵢ₌₀ⁿ⁻¹ (Uⁱf) → Pf`  in L²-norm

where `U = koopman T` is the Koopman operator and `P = metProjection T` is the orthogonal
projection onto `fixedSpace U = {f : Uf = f}`.

**Mathematical significance:** This is the **Mean Ergodic Theorem**, one of the fundamental
results of ergodic theory. It generalizes the law of large numbers from probability to
arbitrary measure-preserving dynamical systems.

**Intuition:** If we repeatedly apply a measure-preserving transformation and average
the results, the average converges to the "invariant part" of the function - the part
that doesn't change under the dynamics. For ergodic systems (where the fixed-point
subspace is trivial), this collapses to convergence to a constant, recovering the law
of large numbers.

**Application to de Finetti:** For the shift `T` on path space `ℕ → α`:
1. The fixed-point subspace consists of tail-measurable functions (depend only on the
   tail of the sequence)
2. Birkhoff averages `n⁻¹ ∑ᵢ f(ωᵢ, ωᵢ₊₁, ...)` converge to the conditional expectation
   onto the tail σ-algebra
3. For exchangeable sequences, the shift is measure-preserving
4. This yields de Finetti's representation: exchangeable sequences are conditionally
   i.i.d. with the conditioning on the tail σ-algebra

**Proof strategy:** This follows from mathlib's
`ContinuousLinearMap.tendsto_birkhoffAverage_orthogonalProjection`, which proves the
Mean Ergodic Theorem for any continuous linear operator with operator norm ≤ 1. The
Koopman operator satisfies this because it's an isometry (preserves L² norms).

**Historical note:** This theorem was first proved by von Neumann (1932) as part of
his pioneering work on operator algebras and quantum mechanics. It's dual to the
Birkhoff Ergodic Theorem (pointwise convergence), proved by Birkhoff (1931).
-/
theorem birkhoffAverage_tendsto_metProjection
    {μ : Measure Ω} [IsProbabilityMeasure μ] (T : Ω → Ω)
    (hT : MeasurePreserving T μ μ) (f : Lp ℝ 2 μ) :
    Tendsto (fun n => birkhoffAverage ℝ (koopman T hT) _root_.id n f)
      atTop (𝓝 (metProjection T hT f)) := by
  classical
  let K : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ := koopman T hT
  have hnorm : ‖K‖ ≤ (1 : ℝ) := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) ?_
    intro g
    have hnorm_eq : ‖K g‖ = ‖g‖ := by
      simp [K, koopman]
    simp [hnorm_eq]
  let S := LinearMap.eqLocus K.toLinearMap 1
  have hS_closed : IsClosed (S : Set (Lp ℝ 2 μ)) := by
    have hset : (S : Set (Lp ℝ 2 μ)) = (fun x => K x - x) ⁻¹' {0} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, SetLike.mem_coe, sub_eq_zero]
      rfl
    rw [hset]
    exact isClosed_singleton.preimage (K.continuous.sub continuous_id)
  haveI : CompleteSpace S := hS_closed.completeSpace_coe
  haveI : S.HasOrthogonalProjection := Submodule.HasOrthogonalProjection.ofCompleteSpace S
  have h_tendsto :=
    ContinuousLinearMap.tendsto_birkhoffAverage_orthogonalProjection K hnorm f
  have hS_eq : S = fixedSpace (koopman T hT) := rfl
  simp only [metProjection]
  convert h_tendsto using 2

end Exchangeability.Ergodic
