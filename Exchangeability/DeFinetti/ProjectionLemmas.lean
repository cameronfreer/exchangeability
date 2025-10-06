/-
Copyright (c) 2025 exchangeability contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: exchangeability contributors
-/
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Symmetric

/-!
# Helper lemmas for orthogonal projections

This file contains helper lemmas about orthogonal projections that are used in the
Koopman approach to de Finetti. These wrap and apply mathlib's projection theory.

## Main results

* `orthogonalProjections_same_range_eq` : Uniqueness of orthogonal projections
-/

noncomputable section

open ContinuousLinearMap InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-- Two continuous linear maps that both act as orthogonal projections onto the same
closed subspace must be equal.

**Mathematical Content:**
The uniqueness of orthogonal projections in an inner product space. If `P` and `Q` are both
symmetric (`IsSymmetric`) and idempotent (`P ∘ P = P`), they are the orthogonal projections
onto their respective ranges. If their ranges are the same subspace `S`, then `P` and `Q` must
be equal to the unique orthogonal projection onto `S`.

**Proof Strategy:**
1. Use `ContinuousLinearMap.IsSymmetric.isIdempotent_iff_eq_orthogonalProjection` which states
   that a symmetric operator `P` is idempotent if and only if it equals the orthogonal projection
   onto its range (`orthogonalProjection (P.range)`).
2. Apply this to both `P` and `Q`, using the hypotheses `hP_sym` and `hP_idem` (and similarly
   for `Q`). This gives `P = orthogonalProjection P.range` and `Q = orthogonalProjection Q.range`.
3. Use the hypotheses `hP_range` and `hQ_range` to show `P.range = S` and `Q.range = S`.
4. Substitute these equalities to get `P = orthogonalProjection S` and `Q = orthogonalProjection S`.
5. Conclude `P = Q`.

Note: The hypotheses `hP_fixes` and `hQ_fixes` are not needed for the proof, as they are
consequences of the other properties of an orthogonal projection.
-/
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
  -- Convert idempotence on continuous linear maps to the linear level
  have hP_idem_elem : IsIdempotentElem P := by
    change P * P = P
    simpa [ContinuousLinearMap.mul_def] using hP_idem
  have hQ_idem_elem : IsIdempotentElem Q := by
    change Q * Q = Q
    simpa [ContinuousLinearMap.mul_def] using hQ_idem
  have hP_symproj : P.toLinearMap.IsSymmetricProjection :=
    ⟨ContinuousLinearMap.IsIdempotentElem.toLinearMap hP_idem_elem, hP_sym⟩
  have hQ_symproj : Q.toLinearMap.IsSymmetricProjection :=
    ⟨ContinuousLinearMap.IsIdempotentElem.toLinearMap hQ_idem_elem, hQ_sym⟩

  -- Identify the ranges with the target subspace `S`
  have hP_range_submodule : LinearMap.range P.toLinearMap = S := by
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

  have hQ_range_submodule : LinearMap.range Q.toLinearMap = S := by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨y, rfl⟩
      have : Q y ∈ Set.range Q := ⟨y, rfl⟩
      simpa [hQ_range] using this
    · intro hx
      have : x ∈ Set.range Q := by
        simpa [hQ_range] using (show x ∈ (S : Set E) from hx)
      rcases this with ⟨y, hy⟩
      exact ⟨y, by simpa using hy⟩

  -- Symmetric projections with the same range agree
  have h_toLinear_eq : P.toLinearMap = Q.toLinearMap :=
    LinearMap.IsSymmetricProjection.ext hP_symproj hQ_symproj <|
      by simp [hP_range_submodule, hQ_range_submodule]

  ext x
  simpa using congrArg (fun f : E →ₗ[𝕜] E => f x) h_toLinear_eq

end
