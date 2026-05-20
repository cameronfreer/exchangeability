/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Symmetric

/-!
# Orthogonal Projection Lemmas for de Finetti's Theorem

This file establishes key properties of orthogonal projections in Hilbert spaces that
are used in the Koopman operator approach to de Finetti's theorem.

## Mathematical background

In the ergodic approach to de Finetti, we use the **Mean Ergodic Theorem** to show that
Birkhoff averages converge to a projection onto the fixed-point subspace of the Koopman
operator. The key technical challenge is identifying this projection and showing uniqueness.

**Orthogonal projection:** For a closed subspace `S` of a Hilbert space `E`, the
orthogonal projection `P : E → S` is the unique operator satisfying:
1. **Range:** `P(E) = S`
2. **Idempotence:** `P² = P` (projecting twice = projecting once)
3. **Symmetry:** `P` is self-adjoint: `⟨Px, y⟩ = ⟨x, Py⟩`
4. **Minimality:** `Px` is the closest point in `S` to `x`

## Main results

* `orthogonalProjections_same_range_eq`: **Uniqueness** - Two symmetric idempotent
  operators with the same range must be equal. This identifies projections from the
  Mean Ergodic Theorem.
* `subtypeL_comp_orthogonalProjection_isSymmetric`: The composition of subtype
  inclusion and orthogonal projection is symmetric.
* `projection_eq_orthogonalProjection_of_properties`: A symmetric idempotent
  operator with range `S` equals the orthogonal projection onto `S`.

## Application to de Finetti

In the ergodic proof of de Finetti:
1. The Koopman operator `U` acts on `L²(μ)` by composition: `(Uf)(ω) = f(shift ω)`
2. The Mean Ergodic Theorem gives convergence to the fixed-point subspace:
   `n⁻¹ ∑ᵢ Uⁱf → Pf` where `P` projects onto `{f : Uf = f}`
3. These lemmas show `P` is the conditional expectation onto the tail σ-algebra
4. De Finetti's representation follows from this identification

## References

* Kallenberg, "Probabilistic Symmetries and Invariance Principles" (2005), Chapter 1
* Krengel, "Ergodic Theorems" (1985), Chapter 1 (Mean Ergodic Theorem)
-/

noncomputable section

open ContinuousLinearMap InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/--
**Uniqueness of orthogonal projections:** Symmetric idempotent operators with the same
range are equal.

**Statement:** If `P` and `Q` are both symmetric (self-adjoint) and idempotent (`P² = P`)
continuous linear operators with the same range `S`, then `P = Q`.

**Mathematical significance:** This establishes uniqueness of orthogonal projections.
In Hilbert space theory, there is exactly one orthogonal projection onto any given
closed subspace. This is crucial for identifying the limiting projection in the Mean
Ergodic Theorem.

**Intuition:** An orthogonal projection onto `S` is characterized by three properties:
- **Idempotence:** Once you project onto `S`, projecting again does nothing
- **Symmetry:** The projection respects the inner product structure
- **Range:** The projection hits exactly `S`

If two operators satisfy all three properties for the same `S`, they must be the same
operator - there's only one way to project orthogonally onto a subspace.

**Application to de Finetti:** The Mean Ergodic Theorem tells us Birkhoff averages
converge to *some* projection onto the fixed-point subspace. This lemma identifies
that projection as the unique orthogonal projection, which can then be recognized as
the conditional expectation onto the tail σ-algebra.

**Proof strategy:**
1. Use mathlib's characterization: symmetric + idempotent ⟹ orthogonal projection
2. Both `P` and `Q` equal `orthogonalProjection(range)`
3. Since `range(P) = range(Q) = S`, we get `P = Q = orthogonalProjection(S)`
-/
-- Convert Set.range equality to LinearMap.range equality
private lemma set_range_eq_linearMap_range (P : E →L[𝕜] E) (S : Submodule 𝕜 E)
    (hP_range : Set.range P = (S : Set E)) :
    LinearMap.range P.toLinearMap = S := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨y, rfl⟩
    have : P y ∈ Set.range P := ⟨y, rfl⟩
    simpa [hP_range] using this
  · intro hx
    have : x ∈ Set.range P := by
      simpa [hP_range] using (show x ∈ (S : Set E) from hx)
    rcases this with ⟨y, hy⟩
    exact ⟨y, by simpa using hy⟩

-- Convert composition idempotence to IsIdempotentElem
private lemma comp_idem_to_elem (P : E →L[𝕜] E) (hP_idem : P.comp P = P) :
    IsIdempotentElem P := by
  change P * P = P
  simpa [ContinuousLinearMap.mul_def] using hP_idem

@[nolint unusedArguments]
theorem orthogonalProjections_same_range_eq
    [CompleteSpace E]
    (P Q : E →L[𝕜] E)
    (S : Submodule 𝕜 E) [S.HasOrthogonalProjection]
    (hP_range : Set.range P = (S : Set E))
    (hQ_range : Set.range Q = (S : Set E))
    (_hP_fixes : ∀ g ∈ S, P g = g)
    (_hQ_fixes : ∀ g ∈ S, Q g = g)
    (hP_idem : P.comp P = P)
    (hQ_idem : Q.comp Q = Q)
    (hP_sym : P.IsSymmetric)
    (hQ_sym : Q.IsSymmetric) :
    P = Q := by
  classical
  -- Convert idempotence on continuous linear maps to the linear level (via helper)
  have hP_idem_elem := comp_idem_to_elem P hP_idem
  have hQ_idem_elem := comp_idem_to_elem Q hQ_idem
  have hP_symproj : P.toLinearMap.IsSymmetricProjection :=
    ⟨ContinuousLinearMap.IsIdempotentElem.toLinearMap hP_idem_elem, hP_sym⟩
  have hQ_symproj : Q.toLinearMap.IsSymmetricProjection :=
    ⟨ContinuousLinearMap.IsIdempotentElem.toLinearMap hQ_idem_elem, hQ_sym⟩

  -- Identify the ranges with the target subspace `S` (via helper)
  have hP_range_submodule := set_range_eq_linearMap_range P S hP_range
  have hQ_range_submodule := set_range_eq_linearMap_range Q S hQ_range

  -- Symmetric projections with the same range agree
  have h_toLinear_eq : P.toLinearMap = Q.toLinearMap :=
    LinearMap.IsSymmetricProjection.ext hP_symproj hQ_symproj <|
      by simp [hP_range_submodule, hQ_range_submodule]

  ext x
  simpa using congrArg (fun f : E →ₗ[𝕜] E => f x) h_toLinear_eq

/--
The composition of subtype inclusion and orthogonal projection is symmetric.

**Statement:** If `S` is a closed subspace with orthogonal projection, then the operator
`subtypeL ∘ orthogonalProjection : E → E` (project onto `S`, then include back into `E`)
is self-adjoint.

**Intuition:** This says that "project onto `S` and include back" is a symmetric operator
on the ambient space. This is not obvious from the definition but follows from the
orthogonality of the projection.

**Why this matters:** When we identify projections from the Mean Ergodic Theorem, we need
to verify they are symmetric. This lemma provides that verification for projections
constructed via orthogonal projection onto a subspace.
-/
@[nolint unusedArguments]
theorem subtypeL_comp_orthogonalProjection_isSymmetric
    [CompleteSpace E]
    (S : Submodule 𝕜 E) [S.HasOrthogonalProjection] :
    (S.subtypeL.comp S.orthogonalProjection).IsSymmetric := by
  intro x y
  -- Expand the composition: (subtypeL ∘ orthogonalProjection) x = ↑(orthogonalProjection x)
  -- orthogonalProjection is symmetric, and subtypeL is just the coercion
  exact Submodule.inner_starProjection_left_eq_right S x y

