/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Exchangeability.DeFinetti.ViaKoopman.Infrastructure
import Exchangeability.DeFinetti.ViaKoopman.CesaroHelpers
import Exchangeability.DeFinetti.ViaKoopman.CylinderFunctions

/-! # Koopman Operator and Mean Ergodic Theorem

This file contains the core results connecting the Koopman operator to conditional expectation:
- `condexpL2_fixes_fixedSubspace` - CE fixes the fixed subspace
- `birkhoffAverage_tendsto_condexp` - Birkhoff averages converge to CE in L²
- `condexpL2_koopman_comm` - CE commutes with Koopman operator

These results are fundamental for the de Finetti proof via ergodic theory.
-/

open Filter MeasureTheory

noncomputable section

namespace Exchangeability.DeFinetti.ViaKoopman

open MeasureTheory Filter Topology ProbabilityTheory
open Exchangeability.Ergodic
open Exchangeability.PathSpace
open scoped BigOperators RealInnerProductSpace

variable {α : Type*} [MeasurableSpace α]

section MainConvergence

variable {μ : Measure (Ω[α])} [IsProbabilityMeasure μ]
variable (hσ : MeasurePreserving shift μ μ)

-- Note: We use explicit @inner ℝ (Lp ℝ 2 μ) _ syntax instead of ⟪⟫_ℝ notation
-- due to type class resolution issues with the standard notation.

/-- Conditional expectation onto shift-invariant σ-algebra fixes elements of fixedSubspace.

This is the tower property of conditional expectation: E[f|σ] = f when f is σ-measurable.
-/
lemma condexpL2_fixes_fixedSubspace {g : Lp ℝ 2 μ}
    (hg : g ∈ fixedSubspace hσ) :
    condexpL2 (μ := μ) g = g := by
  classical
  have h_range : Set.range (condexpL2 (μ := μ)) =
      (fixedSubspace hσ : Set (Lp ℝ 2 μ)) :=
    range_condexp_eq_fixedSubspace (μ := μ) hσ
  have hg_range : g ∈ Set.range (condexpL2 (μ := μ)) := by
    simpa [h_range] using (show g ∈ (fixedSubspace hσ : Set (Lp ℝ 2 μ)) from hg)
  obtain ⟨f, hf⟩ := hg_range
  change condexpL2 (μ := μ) f = g at hf
  subst hf
  simpa [ContinuousLinearMap.comp_apply] using congrArg (fun T => T f) (condexpL2_idem (μ := μ))

/-- Main theorem: Birkhoff averages converge in L² to conditional expectation.

This combines:
1. The Mean Ergodic Theorem (MET) giving convergence to orthogonal projection
2. The identification proj = condexp via range_condexp_eq_fixedSubspace
-/
theorem birkhoffAverage_tendsto_condexp (f : Lp ℝ 2 μ) :
    Tendsto (fun n => birkhoffAverage ℝ (koopman shift hσ) (fun f => f) n f)
      atTop (𝓝 (condexpL2 (μ := μ) f)) := by
  -- Step 1: Get convergence to projection P onto fixedSpace from MET
  classical
  -- Use the canonical mean ergodic projection from `InvariantSigma`
  let P := metProjectionShift (μ := μ) hσ
  have hP_tendsto := metProjectionShift_tendsto (μ := μ) hσ f
  have hP_fixed : ∀ g ∈ fixedSubspace hσ, P g = g :=
    fun g hg => metProjectionShift_fixes_fixedSubspace (μ := μ) hσ hg

  -- Step 2: Show P = condexpL2 using the factored lemmas
  have hP_eq : P = condexpL2 (μ := μ) := by
    -- Both P and condexpL2 are orthogonal projections onto the fixed subspace
    -- Use uniqueness of symmetric idempotent projections with the same range
    exact proj_eq_condexp hσ

  -- Step 3: Conclude using equality
  rw [← hP_eq]
  exact hP_tendsto

/-! ### Part B (Shift Equivariance): Conditional expectation commutes with Koopman operator

The conditional expectation onto the shift-invariant σ-algebra commutes with composition
by shift. This is the key fact for showing CE[f(ω₀)·g(ωₖ) | 𝓘] is constant in k.

**Proof Strategy**: Both `condexpL2` and `koopman shift` are continuous linear operators,
with `condexpL2` being the orthogonal projection onto `fixedSubspace hσ`. For any `f ∈ Lp`,
we show `P(Uf) = Pf` where `P = condexpL2` and `U = koopman shift`:
1. Decompose `f = Pf + (f - Pf)` with `Pf ∈ S` and `(f - Pf) ⊥ S` where `S = fixedSubspace`
2. `U(Pf) = Pf` since `Pf ∈ fixedSubspace` (definition of fixed subspace)
3. `U(f - Pf) ⊥ S` since `U` is an isometry preserving orthogonality
4. Therefore `P(Uf) = P(Pf) = Pf` since projection onto invariant subspace commutes. -/

/-- The residual `f - condexpL2 f` is orthogonal to the fixed subspace.

Uses symmetry of condexpL2: ⟨Pf, g⟩ = ⟨f, Pg⟩, and when g ∈ S we have Pg = g. -/
private lemma orthogonal_complement_of_condexpL2
    (f g : Lp ℝ 2 μ) (hg : g ∈ fixedSubspace hσ) :
    @inner ℝ (Lp ℝ 2 μ) _ (f - condexpL2 (μ := μ) f) g = 0 := by
  -- Since g ∈ fixedSubspace, we have Pg = g
  have hPg : condexpL2 (μ := μ) g = g := condexpL2_fixes_fixedSubspace hσ hg
  -- Symmetry: ⟨Pf, g⟩ = ⟨f, Pg⟩ = ⟨f, g⟩
  have h_sym : @inner ℝ (Lp ℝ 2 μ) _ (condexpL2 (μ := μ) f) g
             = @inner ℝ (Lp ℝ 2 μ) _ f (condexpL2 (μ := μ) g) := by
    unfold condexpL2
    exact MeasureTheory.inner_condExpL2_left_eq_right shiftInvariantSigma_le
  -- ⟨f - Pf, g⟩ = ⟨f, g⟩ - ⟨Pf, g⟩ = ⟨f, g⟩ - ⟨f, g⟩ = 0
  calc @inner ℝ (Lp ℝ 2 μ) _ (f - condexpL2 (μ := μ) f) g
      = @inner ℝ (Lp ℝ 2 μ) _ f g - @inner ℝ (Lp ℝ 2 μ) _ (condexpL2 (μ := μ) f) g := inner_sub_left f _ g
    _ = @inner ℝ (Lp ℝ 2 μ) _ f g - @inner ℝ (Lp ℝ 2 μ) _ f (condexpL2 (μ := μ) g) := by rw [h_sym]
    _ = @inner ℝ (Lp ℝ 2 μ) _ f g - @inner ℝ (Lp ℝ 2 μ) _ f g := by rw [hPg]
    _ = 0 := sub_self _

/-- Koopman operator preserves orthogonality to the fixed subspace. -/
private lemma koopman_preserves_orthogonality_to_fixed_subspace
    (r g : Lp ℝ 2 μ)
    (h_r_orth : ∀ h ∈ fixedSubspace hσ, @inner ℝ (Lp ℝ 2 μ) _ r h = 0)
    (h_fix : ∀ h ∈ fixedSubspace hσ, koopman shift hσ h = h)
    (hg : g ∈ fixedSubspace hσ) :
    @inner ℝ (Lp ℝ 2 μ) _ (koopman shift hσ r) g = 0 := by
  set U := koopman shift hσ
  haveI : Fact (1 ≤ (2 : ℕ∞)) := ⟨by norm_num⟩
  let Uₗᵢ : (Lp ℝ 2 μ) →ₗᵢ[ℝ] (Lp ℝ 2 μ) :=
    MeasureTheory.Lp.compMeasurePreservingₗᵢ ℝ (shift (α := α)) hσ
  have hU_coe : ∀ x, U x = Uₗᵢ x := fun _ => rfl
  have hUg : U g = g := h_fix g hg
  -- Isometry preserves inner products: ⟨Ur, Ug⟩ = ⟨r, g⟩
  have h_inner_pres := Uₗᵢ.inner_map_map r g
  -- Since Ug = g (fixed point), we have ⟨Ur, g⟩ = ⟨r, g⟩ = 0
  calc @inner ℝ (Lp ℝ 2 μ) _ (U r) g
      = @inner ℝ (Lp ℝ 2 μ) _ (U r) (U g) := by rw [hUg]
    _ = @inner ℝ (Lp ℝ 2 μ) _ (Uₗᵢ r) (Uₗᵢ g) := by simp only [hU_coe]
    _ = @inner ℝ (Lp ℝ 2 μ) _ r g := h_inner_pres
    _ = 0 := h_r_orth g hg

/-- An element in a subspace that is orthogonal to all elements of that subspace must be zero. -/
private lemma zero_from_subspace_and_orthogonal
    (x : Lp ℝ 2 μ)
    (hx_mem : x ∈ fixedSubspace hσ)
    (hx_orth : ∀ g ∈ fixedSubspace hσ, @inner ℝ (Lp ℝ 2 μ) _ x g = 0) :
    x = 0 := by
  have hinner := hx_orth x hx_mem
  exact inner_self_eq_zero.mp hinner

/-- **Part B (Shift Equivariance)**: Conditional expectation commutes with Koopman operator. -/
lemma condexpL2_koopman_comm (f : Lp ℝ 2 μ) :
    condexpL2 (μ := μ) (koopman shift hσ f) = condexpL2 (μ := μ) f := by
  classical
  set P := condexpL2 (μ := μ)
  set U := koopman shift hσ
  let S := fixedSubspace hσ
  have h_range : Set.range P = (S : Set (Lp ℝ 2 μ)) := range_condexp_eq_fixedSubspace hσ
  have hPf_mem : P f ∈ S := by
    have : P f ∈ Set.range P := ⟨f, rfl⟩
    simpa [P, h_range] using this
  have h_fix : ∀ g ∈ S, U g = g := fun g hg => (mem_fixedSubspace_iff (μ := μ) (α := α) hσ g).1 hg
  set r := f - P f
  -- Step 1: r = f - Pf is orthogonal to S
  have h_r_orth : ∀ g ∈ S, @inner ℝ (Lp ℝ 2 μ) _ r g = 0 := fun g hg =>
    orthogonal_complement_of_condexpL2 hσ f g hg
  -- Step 2: Ur is also orthogonal to S (isometry preserves orthogonality)
  have h_r_orth_after : ∀ g ∈ S, @inner ℝ (Lp ℝ 2 μ) _ (U r) g = 0 := fun g hg =>
    koopman_preserves_orthogonality_to_fixed_subspace hσ r g h_r_orth h_fix hg
  -- Step 3: P(Ur) ∈ S and P(Ur) ⊥ S, hence P(Ur) = 0
  have hPUr_mem : P (U r) ∈ S := by
    have : P (U r) ∈ Set.range P := ⟨U r, rfl⟩
    simpa [P, h_range] using this
  have hPUr_orth : ∀ g ∈ S, @inner ℝ (Lp ℝ 2 μ) _ (P (U r)) g = 0 := by
    intro g hg
    -- ⟨P(Ur), g⟩ = ⟨Ur, Pg⟩ = ⟨Ur, g⟩ = 0 (since g ∈ S means Pg = g)
    have hPg : P g = g := condexpL2_fixes_fixedSubspace hσ hg
    have h_sym : @inner ℝ (Lp ℝ 2 μ) _ (P (U r)) g
               = @inner ℝ (Lp ℝ 2 μ) _ (U r) (P g) := by
      unfold P condexpL2
      exact MeasureTheory.inner_condExpL2_left_eq_right shiftInvariantSigma_le
    rw [h_sym, hPg]
    exact h_r_orth_after g hg
  have hPUr_zero : P (U r) = 0 := zero_from_subspace_and_orthogonal hσ (P (U r)) hPUr_mem hPUr_orth
  -- Step 4: P(Uf) = P(U(Pf) + Ur) = P(U(Pf)) + P(Ur) = P(Pf) + 0 = Pf
  -- f = Pf + r by construction (r = f - Pf)
  have hf_decomp : f = P f + r := by
    rw [add_comm]
    exact (sub_add_cancel f (P f)).symm
  -- U is linear: U(f) = U(Pf + r) = U(Pf) + U(r)
  have hUf_decomp : U f = U (P f) + U r := by
    conv_lhs => rw [hf_decomp]
    exact U.map_add (P f) r
  -- U(Pf) = Pf since Pf ∈ S (fixed)
  have hPUf_eq : P (U (P f)) = P (P f) := by rw [h_fix (P f) hPf_mem]
  -- P(P f) = P f by idempotence
  have hPP_eq : P (P f) = P f := by
    have h_idem := condexpL2_idem (μ := μ)
    exact congrFun (congrArg DFunLike.coe h_idem) f
  calc
    P (U f) = P (U (P f) + U r) := by rw [hUf_decomp]
    _ = P (U (P f)) + P (U r) := P.map_add (U (P f)) (U r)
    _ = P (P f) + 0 := by rw [hPUf_eq, hPUr_zero]
    _ = P f := by rw [add_zero, hPP_eq]

/-
COMMENTED OUT - Original helper lemmas (now uncommented above):

/-! ### Helper lemmas for condexpL2_koopman_comm -/

private lemma orthogonal_complement_of_condexpL2
    (f : Lp ℝ 2 μ) :
    let P := condexpL2 (μ := μ)
    let S := fixedSubspace hσ
    let r := f - P f
    ∀ g ∈ S, ⟪r, g⟫_ℝ = 0 := by
  intro g hg
  set P := condexpL2 (μ := μ)
  set S := fixedSubspace hσ
  set r := f - P f

  have h_sym :=
    MeasureTheory.inner_condExpL2_left_eq_right
      (μ := μ)
      (m := shiftInvariantSigma (α := α))
      (hm := shiftInvariantSigma_le (α := α))
      (f := f)
      (g := g)
  have hPg : P g = g := condexpL2_fixes_fixedSubspace (hσ := hσ) hg
  have hPg' : condexpL2 (μ := μ) g = g := hPg
  have h_eq :
      ⟪P f, g⟫_ℝ = ⟪f, g⟫_ℝ := by
    simpa [P, hPg'] using h_sym
  have hinner :
      ⟪r, g⟫_ℝ = ⟪f, g⟫_ℝ - ⟪P f, g⟫_ℝ := by
    simpa [r] using
      (inner_sub_left (x := f) (y := P f) (z := g))
  simpa [h_eq] using hinner

private lemma koopman_preserves_orthogonality_to_fixed_subspace
    (r : Lp ℝ 2 μ)
    (h_r_orth : ∀ g ∈ fixedSubspace hσ, ⟪r, g⟫_ℝ = 0)
    (h_fix : ∀ g ∈ fixedSubspace hσ, koopman shift hσ g = g) :
    ∀ g ∈ fixedSubspace hσ, ⟪koopman shift hσ r, g⟫_ℝ = 0 := by
  set U := koopman shift hσ
  set S := fixedSubspace hσ
  let Uₗᵢ := MeasureTheory.Lp.compMeasurePreservingₗᵢ ℝ (shift (α := α)) hσ
  have hU_coe : ∀ g, U g = Uₗᵢ g := by intro g; rfl

  intro g hg
  have hUg : U g = g := h_fix g hg
  have h_inner_pres := Uₗᵢ.inner_map_map r g
  have h_base : ⟪U r, U g⟫_ℝ = ⟪r, g⟫_ℝ := by
    simpa [U, hU_coe r, hU_coe g] using h_inner_pres
  simpa [U, hUg, hU_coe r, hU_coe g, h_r_orth g hg] using h_base

private lemma zero_from_subspace_and_orthogonal
    (x : Lp ℝ 2 μ)
    (hx_mem : x ∈ fixedSubspace hσ)
    (hx_orth : ∀ g ∈ fixedSubspace hσ, ⟪x, g⟫_ℝ = 0) :
    x = 0 := by
  have hinner := hx_orth x hx_mem
  exact (inner_self_eq_zero : ⟪x, x⟫_ℝ = 0 ↔ x = 0).mp hinner

lemma condexpL2_koopman_comm (f : Lp ℝ 2 μ) :
    condexpL2 (μ := μ) (koopman shift hσ f) = condexpL2 (μ := μ) f := by
  classical
  -- Abbreviations for the projection and Koopman operator
  set P := condexpL2 (μ := μ)
  set U := koopman shift hσ
  let S := fixedSubspace hσ

  -- Image of `P` equals the fixed subspace
  have h_range : Set.range P = (S : Set (Lp ℝ 2 μ)) :=
    range_condexp_eq_fixedSubspace hσ

  -- `P f` and `P (U f)` lie in the fixed subspace
  have hPf_mem : P f ∈ S := by
    have : P f ∈ Set.range P := ⟨f, rfl⟩
    simpa [P, h_range] using this
  have hPUf_mem : P (U f) ∈ S := by
    have : P (U f) ∈ Set.range P := ⟨U f, rfl⟩
    simpa [P, h_range] using this

  -- Elements of the fixed subspace are fixed points of the Koopman operator
  have h_fix : ∀ g ∈ S, U g = g := by
    intro g hg
    exact (mem_fixedSubspace_iff (μ := μ) (α := α) hσ g).1 hg

  -- Decompose `f` into its projection plus orthogonal complement
  set r := f - P f
  have h_decomp : f = P f + r := by
    simp [r, add_comm, add_left_comm, add_assoc]

  -- `r` is orthogonal to the fixed subspace
  have h_r_orth : ∀ g ∈ S, ⟪r, g⟫_ℝ = 0 := orthogonal_complement_of_condexpL2 f

  -- The Koopman operator preserves orthogonality
  have h_r_orth_after : ∀ g ∈ S, ⟪U r, g⟫_ℝ = 0 :=
    koopman_preserves_orthogonality_to_fixed_subspace r h_r_orth h_fix

  -- `P (U r)` lies in the subspace
  have hPUr_mem : P (U r) ∈ S := by
    have : P (U r) ∈ Set.range P := ⟨U r, rfl⟩
    simpa [P, h_range] using this

  -- `P (U r)` is orthogonal to the fixed subspace
  have hPUr_orth : ∀ g ∈ S, ⟪P (U r), g⟫_ℝ = 0 := by
    intro g hg
    have hPg : P g = g := condexpL2_fixes_fixedSubspace (hσ := hσ) hg
    have h_sym :=
      MeasureTheory.inner_condExpL2_left_eq_right
        (μ := μ)
        (m := shiftInvariantSigma (α := α))
        (hm := shiftInvariantSigma_le (α := α))
        (f := U r)
        (g := g)
    have h_eq : ⟪P (U r), g⟫_ℝ = ⟪U r, g⟫_ℝ := by
      simpa [P, hPg] using h_sym
    simpa [h_eq, h_r_orth_after g hg]

  -- Element in S ∩ S⊥ is zero
  have hPUr_zero : P (U r) = 0 := zero_from_subspace_and_orthogonal (P (U r)) hPUr_mem hPUr_orth

  -- Combine the pieces: `P (U f)` equals `P f`
  have hUf_decomp :
      U f = U (P f) + U r := by
    have h := congrArg U h_decomp
    have hUadd := U.map_add (P f) r
    simpa [hUadd] using h
  calc
    P (U f)
        = P (U (P f) + U r) := by simpa [hUf_decomp]
    _ = P (U (P f)) + P (U r) := by
          simpa [P] using (condexpL2 (μ := μ)).map_add (U (P f)) (U r)
    _ = P (P f) + 0 := by
          simp [P, h_fix (P f) hPf_mem, hPUr_zero]
    _ = P f := by simp [P]

/-
Full proof sketch using orthogonal projection characterization:
  classical
  -- Abbreviations
  let U := koopman shift hσ
  let P := condexpL2 (μ := μ)
  let S := fixedSubspace hσ

  -- `P` projects onto `S`
  have hRange : Set.range P = (S : Set (Lp ℝ 2 μ)) :=
    range_condexp_eq_fixedSubspace (μ := μ) hσ
  have hPf_mem : P f ∈ S := by
    have : P f ∈ Set.range P := ⟨f, rfl⟩
    simpa [hRange] using this
  have hPUf_mem : P (U f) ∈ S := by
    have : P (U f) ∈ Set.range P := ⟨U f, rfl⟩
    simpa [hRange] using this

  -- (1) `U s = s` for every `s ∈ S` (definition of fixedSubspace)
  have h_fix : ∀ s ∈ S, U s = s := by
    intro s hs
    exact (mem_fixedSubspace_iff (hσ := hσ) (f := s)).1 hs

  -- (2) `f - P f ⟂ S` (characterization of orthogonal projection)
  have h_perp_f : ∀ s ∈ S, ⟪f - P f, s⟫_ℝ = 0 := by
    intro s hs
    -- Symmetry of CE: ⟪P f, s⟫ = ⟪f, s⟫ for `s` measurable w.r.t. invariant σ-algebra
    have hsym : ⟪P f, s⟫_ℝ = ⟪f, s⟫_ℝ :=
      MeasureTheory.inner_condExpL2_left_eq_right (μ := μ)
        (m := shiftInvariantSigma (α := α))
        (hm := shiftInvariantSigma_le (α := α)) (f := f) (g := s)
    simp [inner_sub_left, hsym]

  -- (3) `U f - P f ⟂ S` because `U` is an isometry and fixes `S` pointwise
  have h_perp_Uf_minus_Pf : ∀ s ∈ S, ⟪U f - P f, s⟫_ℝ = 0 := by
    intro s hs
    have hperp := h_perp_f s hs
    -- ⟪U(f - Pf), s⟫ = ⟪U(f - Pf), U s⟫ = ⟪f - Pf, s⟫ = 0
    have h1 : ⟪U f - P f, s⟫_ℝ = ⟪U (f - P f), s⟫_ℝ := by
      simp [U, LinearIsometry.map_sub]
    have h2 : ⟪U (f - P f), s⟫_ℝ = ⟪U (f - P f), U s⟫_ℝ := by
      rw [h_fix s hs]
    have h3 : ⟪U (f - P f), U s⟫_ℝ = ⟪f - P f, s⟫_ℝ := by
      have := LinearIsometry.inner_map_map (koopman shift hσ) (f - P f) s
      simpa [U] using this
    simp [h1, h2, h3, hperp]

  -- (4) `U f - P (U f) ⟂ S` by the same projection characterization (with input `U f`)
  have h_perp_Uf_minus_PUf : ∀ s ∈ S, ⟪U f - P (U f), s⟫_ℝ = 0 := by
    intro s hs
    have hsym : ⟪P (U f), s⟫_ℝ = ⟪U f, s⟫_ℝ :=
      MeasureTheory.inner_condExpL2_left_eq_right (μ := μ)
        (m := shiftInvariantSigma (α := α)) (hm := shiftInvariantSigma_le (α := α))
        (f := U f) (g := s)
    simp [inner_sub_left, hsym]

  -- (5) `(P(U f) - P f) ∈ S ∩ S⊥`, hence it is zero
  have h_in_S : P (U f) - P f ∈ S := S.sub_mem hPUf_mem hPf_mem
  have h_in_S_perp : P (U f) - P f ∈ Sᗮ := by
    -- Difference of two S-orthogonal remainders
    -- (Uf - PUf) - (Uf - Pf) = Pf - PUf ∈ S⊥ (submodule is closed under subtraction)
    have hx : U f - P (U f) ∈ Sᗮ :=
      (Submodule.mem_orthogonal).2 (h_perp_Uf_minus_PUf)
    have hy : U f - P f ∈ Sᗮ :=
      (Submodule.mem_orthogonal).2 (h_perp_Uf_minus_Pf)
    have hsub : (P (U f) - P f) = (U f - P f) - (U f - P (U f)) := by abel
    -- S⊥ closed under subtraction
    simpa [hsub] using Submodule.sub_mem _ hy hx

  -- A vector in `S ∩ S⊥` is 0: take its inner product with itself
  have : P (U f) - P f = 0 := by
    have h0 := (Submodule.mem_orthogonal).1 h_in_S_perp
    have : ⟪P (U f) - P f, P (U f) - P f⟫_ℝ = 0 := h0 _ h_in_S
    have : ‖P (U f) - P f‖ ^ 2 = 0 := by simpa [inner_self_eq_norm_sq_real] using this
    have : ‖P (U f) - P f‖ = 0 := by simpa [sq_eq_zero_iff] using this
    exact norm_eq_zero.mp this
  -- Conclude
  exact sub_eq_zero.mp this
  -/
-/

/-- Specialization to cylinder functions: the core case for de Finetti. -/
theorem birkhoffCylinder_tendsto_condexp
    {m : ℕ} (fs : Fin m → α → ℝ)
    (hmeas : ∀ k, Measurable (fs k))
    (hbd : ∀ k, ∃ C, ∀ x, |fs k x| ≤ C) :
    let F := productCylinder fs
    ∃ (fL2 : Lp ℝ 2 μ),
      (∀ᵐ ω ∂μ, fL2 ω = F ω) ∧
      Tendsto (fun n => birkhoffAverage ℝ (koopman shift hσ) (fun f => f) n fL2)
        atTop
        (𝓝 (condexpL2 (μ := μ) fL2)) := by
  classical
  -- Use productCylinderLp as the L² representative
  use productCylinderLp (μ := μ) (fs := fs) hmeas hbd
  constructor
  -- First conjunct: a.e. equality between fL2 and F
  · exact productCylinderLp_ae_eq (μ := μ) (fs := fs) hmeas hbd
  -- Second conjunct: convergence to condexpL2
  · -- Apply Mean Ergodic Theorem from KoopmanMeanErgodic.lean
    exact birkhoffAverage_tendsto_condexp hσ (productCylinderLp fs hmeas hbd)

end MainConvergence

end Exchangeability.DeFinetti.ViaKoopman
