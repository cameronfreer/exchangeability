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
2. The identification proj = condexp via `proj_eq_condexp`
-/
theorem birkhoffAverage_tendsto_condexp (f : Lp ℝ 2 μ) :
    Tendsto (fun n => birkhoffAverage ℝ (koopman shift hσ) (fun f => f) n f)
      atTop (𝓝 (condexpL2 (μ := μ) f)) := by
  -- MET gives convergence to the mean-ergodic projection; `proj_eq_condexp`
  -- identifies that projection with `condexpL2`.
  have hP_tendsto := metProjectionShift_tendsto (μ := μ) hσ f
  rw [← Exchangeability.DeFinetti.proj_eq_condexp (μ := μ) hσ]
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
  · -- MET gives convergence to `metProjection`, which is defeq to
    -- `metProjectionShift`; `proj_eq_condexp` identifies it with `condexpL2`.
    have h_met := Exchangeability.Ergodic.birkhoffAverage_tendsto_metProjection
      shift hσ (productCylinderLp (μ := μ) (fs := fs) hmeas hbd)
    simpa [Exchangeability.DeFinetti.proj_eq_condexp (μ := μ) hσ] using h_met

end MainConvergence

end Exchangeability.DeFinetti.ViaKoopman
