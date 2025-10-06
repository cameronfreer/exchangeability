/-
Copyright (c) 2025 exchangeability contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: exchangeability contributors
-/
import Mathlib.Analysis.InnerProductSpace.Projection

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
  -- Convert idempotence to LinearMap level
  have hP_idem_lm : IsIdempotentElem P.toLinearMap := by
    rw [IsIdempotentElem]
    ext x
    show (P.toLinearMap * P.toLinearMap) x = P.toLinearMap x
    simp only [LinearMap.mul_apply]
    exact congrFun (congrArg DFunLike.coe hP_idem) x
  
  have hQ_idem_lm : IsIdempotentElem Q.toLinearMap := by
    rw [IsIdempotentElem]
    ext x  
    show (Q.toLinearMap * Q.toLinearMap) x = Q.toLinearMap x
    simp only [LinearMap.mul_apply]
    exact congrFun (congrArg DFunLike.coe hQ_idem) x
  
  -- Build symmetric projection structures
  have hP_symproj : P.toLinearMap.IsSymmetricProjection := ⟨hP_idem_lm, hP_sym⟩
  have hQ_symproj : Q.toLinearMap.IsSymmetricProjection := ⟨hQ_idem_lm, hQ_sym⟩
  
  -- Prove that the LinearMap range of P equals S
  have hP_range_submodule : LinearMap.range P.toLinearMap = S := by
    ext x
    constructor
    · intro ⟨y, hy⟩
      rw [← hy, ← hP_range]
      exact ⟨y, rfl⟩
    · intro hx
      have : x ∈ Set.range P := by
        rw [hP_range]
        exact hx
      obtain ⟨y, hy⟩ := this
      exact ⟨y, hy⟩
  
  have hQ_range_submodule : LinearMap.range Q.toLinearMap = S := by
    ext x
    constructor
    · intro ⟨y, hy⟩
      rw [← hy, ← hQ_range]
      exact ⟨y, rfl⟩
    · intro hx
      have : x ∈ Set.range Q := by
        rw [hQ_range]
        exact hx
      obtain ⟨y, hy⟩ := this
      exact ⟨y, hy⟩
  
  -- Use mathlib's theorem that symmetric projections equal starProjection of their range
  obtain ⟨_, hP_eq⟩ := (LinearMap.isSymmetricProjection_iff_eq_coe_starProjection_range).mp hP_symproj
  obtain ⟨_, hQ_eq⟩ := (LinearMap.isSymmetricProjection_iff_eq_coe_starProjection_range).mp hQ_symproj
  
  -- Convert back to ContinuousLinearMap
  ext x
  calc P x = P.toLinearMap x := rfl
    _ = (LinearMap.range P.toLinearMap).starProjection x := by rw [hP_eq]
    _ = S.starProjection x := by rw [hP_range_submodule]
    _ = (LinearMap.range Q.toLinearMap).starProjection x := by rw [← hQ_range_submodule]
    _ = Q.toLinearMap x := by rw [← hQ_eq]
    _ = Q x := rfl

end
