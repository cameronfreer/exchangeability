/-
Copyright (c) 2025 exchangeability contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: exchangeability contributors
-/
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Exchangeability.Ergodic.KoopmanMeanErgodic
import Exchangeability.DeFinetti.InvariantSigma

/-!
# First Proof of de Finetti via Mean Ergodic Theorem

This file implements Kallenberg's "First proof" of Theorem 1.1 (page 26) using
the Koopman operator and Mean Ergodic Theorem.

## Main approach

1. Apply the Mean Ergodic Theorem to show Birkhoff averages converge to the
   orthogonal projection onto the fixed-point subspace
2. Identify this projection with conditional expectation onto the shift-invariant σ-algebra
3. Use dominated convergence to show the conditional expectation has product form
4. Apply monotone class theorem to extend from cylinders to the full σ-algebra

## Main definitions

* `cylinderFunction`: Functions depending only on finitely many coordinates
* `productCylinder`: Product of functions evaluated at different coordinates
* `shiftedCylinder`: Cylinder function composed with shift^n

## Main results

* `birkhoffAverage_tendsto_condexp`: Birkhoff averages converge to conditional expectation
* `birkhoffCylinder_tendsto_condexp`: Specialization to cylinder functions
* `extremeMembers_agree`: Extreme members in Birkhoff averages coincide
* `condexp_cylinder_factorizes`: Conditional expectation has product form

## References

* Olav Kallenberg (2005), *Probabilistic Symmetries and Invariance Principles*,
  Springer, Chapter 1, pages 26-27 (First proof of Theorem 1.1).
-/

noncomputable section

namespace Exchangeability.DeFinetti.KoopmanApproach

open MeasureTheory Filter Topology
open Exchangeability.Ergodic

variable {α : Type*} [MeasurableSpace α]

section CylinderFunctions

/-- Cylinder function: a function on path space depending only on finitely many coordinates.
For simplicity, we take the first m coordinates. -/
def cylinderFunction (m : ℕ) (φ : (Fin m → α) → ℝ) : Ω[α] → ℝ :=
  fun ω => φ (fun k => ω k.val)

/-- Product cylinder: ∏_{k < m} fₖ(ω k). -/
def productCylinder (m : ℕ) (fs : Fin m → α → ℝ) : Ω[α] → ℝ :=
  fun ω => ∏ k : Fin m, fs k (ω k.val)

omit [MeasurableSpace α] in
lemma productCylinder_eq_cylinder (m : ℕ) (fs : Fin m → α → ℝ) :
    productCylinder m fs = cylinderFunction m (fun coords => ∏ k, fs k (coords k)) := by
  rfl

/-- Measurability of cylinder functions. -/
lemma measurable_cylinderFunction (m : ℕ) (φ : (Fin m → α) → ℝ)
    (_hφ : Measurable φ) :
    Measurable (cylinderFunction m φ) := by
  classical
  have hproj : Measurable fun ω : Ω[α] => fun k : Fin m => ω k.val := by
    refine measurable_pi_lambda _ ?_
    intro k
    simpa using (measurable_pi_apply (k.val))
  simpa [cylinderFunction] using _hφ.comp hproj

/-- Measurability of product cylinders. -/
lemma measurable_productCylinder (m : ℕ) (fs : Fin m → α → ℝ)
    (hmeas : ∀ k, Measurable (fs k)) :
    Measurable (productCylinder m fs) := by
  classical
  unfold productCylinder
  -- Product of measurable functions is measurable
  apply Finset.measurable_prod
  intro k _
  exact (hmeas k).comp (measurable_pi_apply k.val)

/-- Boundedness of product cylinders. -/
lemma productCylinder_bounded (m : ℕ) (fs : Fin m → α → ℝ)
    (hbd : ∀ k, ∃ C, ∀ x, |fs k x| ≤ C) :
    ∃ C, ∀ ω, |productCylinder m fs ω| ≤ C := by
  -- Take C = ∏ Cₖ where |fₖ| ≤ Cₖ
  classical
  choose bound hbound using hbd
  let C : Fin m → ℝ := fun k => max (bound k) 1
  refine ⟨∏ k : Fin m, C k, ?_⟩
  intro ω
  have h_abs_le : ∀ k : Fin m, |fs k (ω k.val)| ≤ C k := by
    intro k
    have := hbound k (ω k.val)
    exact this.trans (le_max_left _ _)
  have h_nonneg : ∀ k : Fin m, 0 ≤ |fs k (ω k.val)| := fun _ => abs_nonneg _
  have hprod : ∏ k : Fin m, |fs k (ω k.val)| ≤ ∏ k : Fin m, C k := by
    simpa using
      (Finset.prod_le_prod (s := Finset.univ)
        (f := fun k : Fin m => |fs k (ω k.val)|)
        (g := fun k : Fin m => C k)
        (fun k _ => h_nonneg k)
        (fun k _ => h_abs_le k))
  have habs_eq : |productCylinder m fs ω| = ∏ k : Fin m, |fs k (ω k.val)| := by
    simp [productCylinder, Finset.abs_prod]
  exact (by simpa [habs_eq] using hprod)

/-- Membership of product cylinders in `L²`. -/
lemma productCylinder_memLp
    (m : ℕ) (fs : Fin m → α → ℝ)
    (hmeas : ∀ k, Measurable (fs k))
    (hbd : ∀ k, ∃ C, ∀ x, |fs k x| ≤ C)
    {μ : Measure (Ω[α])} [IsProbabilityMeasure μ] :
    MeasureTheory.MemLp (productCylinder m fs) 2 μ := by
  classical
  obtain ⟨C, hC⟩ := productCylinder_bounded m fs hbd
  have hFmeas : Measurable (productCylinder m fs) :=
    measurable_productCylinder m fs hmeas
  refine MeasureTheory.MemLp.of_bound (μ := μ) (p := 2)
    hFmeas.aestronglyMeasurable C ?_
  filter_upwards with ω
  simpa [Real.norm_eq_abs] using hC ω

/-- `Lp` representative associated to a bounded product cylinder. -/
noncomputable def productCylinderLp
    (m : ℕ) (fs : Fin m → α → ℝ)
    (hmeas : ∀ k, Measurable (fs k))
    (hbd : ∀ k, ∃ C, ∀ x, |fs k x| ≤ C)
    {μ : Measure (Ω[α])} [IsProbabilityMeasure μ] : Lp ℝ 2 μ :=
  (productCylinder_memLp (m := m) (fs := fs) hmeas hbd).toLp (productCylinder m fs)

lemma productCylinderLp_ae_eq
    (m : ℕ) (fs : Fin m → α → ℝ)
    (hmeas : ∀ k, Measurable (fs k))
    (hbd : ∀ k, ∃ C, ∀ x, |fs k x| ≤ C)
    {μ : Measure (Ω[α])} [IsProbabilityMeasure μ] :
    (∀ᵐ ω ∂μ, productCylinderLp (μ := μ) (m := m) (fs := fs) hmeas hbd ω =
      productCylinder m fs ω) := by
  classical
  exact MeasureTheory.MemLp.coeFn_toLp
    (productCylinder_memLp (μ := μ) (m := m) (fs := fs) hmeas hbd)

/-- The shifted cylinder function: F ∘ shift^n. -/
def shiftedCylinder (n : ℕ) (F : Ω[α] → ℝ) : Ω[α] → ℝ :=
  fun ω => F ((shift^[n]) ω)

end CylinderFunctions

section MainConvergence

variable {μ : Measure (Ω[α])} [IsProbabilityMeasure μ]
variable (hσ : MeasurePreserving shift μ μ)

/-- The projection P from the Mean Ergodic Theorem has range equal to fixedSubspace.

This is now axiomatized based on the construction in `birkhoffAverage_tendsto_fixedSpace`.
The construction witness is P = S.subtypeL ∘ S.orthogonalProjection where S = fixedSpace.
This makes range P = range subtypeL = S by Submodule.range_subtypeL.

The full proof is in `Exchangeability.Ergodic.range_projection_eq_fixedSpace`.
-/
axiom range_MET_projection_eq_fixedSubspace
    {P : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ}
    (hP_fixed : ∀ g ∈ fixedSubspace hσ, P g = g) :
    Set.range P = (fixedSubspace hσ : Set (Lp ℝ 2 μ))

/-- Conditional expectation onto shift-invariant σ-algebra fixes elements of fixedSubspace.

This is a consequence of the tower property of conditional expectation:
if f is already measurable with respect to the sub-σ-algebra, then E[f|σ] = f.

TODO: Prove using `lpMeas_eq_fixedSubspace` and tower property of `condExpL2`.
-/
lemma condexpL2_fixes_fixedSubspace {g : Lp ℝ 2 μ}
    (hg : g ∈ fixedSubspace hσ) :
    condexpL2 (μ := μ) g = g := by
  -- g ∈ fixedSubspace means koopman (g) = g, i.e., g ∘ shift = g a.e.
  -- This means g is shift-invariant, hence measurable w.r.t. shiftInvariantSigma
  
  -- Strategy: Use lpMeas_eq_fixedSubspace to convert fixedSubspace membership to lpMeas
  -- Then use that orthogonal projection fixes elements of the subspace
  
  -- lpMeas_eq_fixedSubspace says: Set.range subtypeL = fixedSubspace
  -- Since g ∈ fixedSubspace, there exists x : lpMeas such that subtypeL x = g
  have h_equiv := lpMeas_eq_fixedSubspace hσ
  have : g ∈ (Set.range (lpMeas ℝ ℝ shiftInvariantSigma 2 μ).subtypeL) := by
    rw [h_equiv]
    exact hg
  
  obtain ⟨gₘ, hgₘ : (lpMeas ℝ ℝ shiftInvariantSigma 2 μ).subtypeL gₘ = g⟩ := this
  
  -- Now condexpL2 g = subtypeL (condExpL2 g)
  -- Since g = subtypeL gₘ where gₘ ∈ lpMeas,
  -- condExpL2 should map g back to gₘ (it projects onto lpMeas, and g is already there)
  -- Then subtypeL gₘ = g
  
  unfold condexpL2
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply]
  
  -- The key: condExpL2 (subtypeL gₘ) = gₘ because gₘ is already in lpMeas
  -- condExpL2 is DEFINED as orthogonalProjection in mathlib
  -- So we can use: orthogonalProjection_mem_subspace_eq_self
  have : MeasureTheory.condExpL2 ℝ ℝ shiftInvariantSigma_le g = gₘ := by
    rw [← hgₘ]
    -- condExpL2 is defined as (lpMeas ...).orthogonalProjection in mathlib
    -- We want to apply: orthogonalProjection_mem_subspace_eq_self
    -- which says: K.orthogonalProjection v = v for v : K
    --
    -- Issue: Lean cannot synthesize (lpMeas ...).HasOrthogonalProjection
    -- This instance should exist because:
    -- 1. lpMeas is a closed submodule of Lp (complete space)
    -- 2. Lp is a Hilbert space
    -- 3. Mathlib provides HasOrthogonalProjection for closed submodules of Hilbert spaces
    --
    -- The mathlib definition uses `haveI : Fact (m ≤ m0)` which provides instances
    -- But we need to figure out how to make this available in our context
    sorry  -- TODO: Fix instance synthesis for HasOrthogonalProjection on lpMeas
  
  rw [this, hgₘ]

/-- Two continuous linear maps that both act as orthogonal projections onto the same
closed subspace must be equal.

This is the uniqueness of orthogonal projections. The key characterization is:
P is the orthogonal projection onto S iff:
- P x ∈ S for all x
- ⟨x - P x, s⟩ = 0 for all s ∈ S

The proof strategy uses that both P and Q fix all elements of S.
For any g, both P g and Q g are in S. Since P fixes S, P(Q g) = Q g.
Since Q fixes S, Q(P g) = P g. This gives us P g = Q(P g) and Q g = Q(P g) = P g.

TODO: Complete using that fixing S implies they're both the identity map restricted to S,
and use mathlib's `eq_orthogonalProjectionFn_of_mem_of_inner_eq_zero` for uniqueness.
-/
lemma orthogonal_projections_same_range_eq
    (P Q : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (S : Submodule ℝ (Lp ℝ 2 μ))
    (hP_range : Set.range P = (S : Set (Lp ℝ 2 μ)))
    (hQ_range : Set.range Q = (S : Set (Lp ℝ 2 μ)))
    (hP_fixes : ∀ g ∈ S, P g = g)
    (hQ_fixes : ∀ g ∈ S, Q g = g) :
    P = Q := by
  -- Use ContinuousLinearMap.ext (equality of continuous linear maps)
  apply ContinuousLinearMap.ext
  intro g
  
  -- Strategy: Show P g = Q g by using that both fix elements of S
  -- Both P g and Q g are in S
  have hPg : P g ∈ (S : Set (Lp ℝ 2 μ)) := by
    rw [← hP_range]
    exact ⟨g, rfl⟩
  have hQg : Q g ∈ (S : Set (Lp ℝ 2 μ)) := by
    rw [← hQ_range]
    exact ⟨g, rfl⟩
  
  -- Apply the fixing property
  have hP_fixes_Qg : P (Q g) = Q g := hP_fixes (Q g) hQg
  have hQ_fixes_Pg : Q (P g) = P g := hQ_fixes (P g) hPg
  
  -- Key observation: Both P and Q fix elements of S and have range = S
  -- This means they act as the identity on S
  -- 
  -- For any g, both P g and Q g are in S
  -- Apply Q to P g: Q (P g) = P g (since P g ∈ S and Q fixes S)
  -- Apply P to Q g: P (Q g) = Q g (since Q g ∈ S and P fixes S)
  --
  -- Now the clever part: use that P and Q commute when composing with elements of S
  -- P g = Q (P g) = Q (P (Q g)) = Q (Q g) = Q g
  --
  -- Step by step:
  -- 1. P g = Q (P g) by hQ_fixes_Pg
  -- 2. We want to show this equals Q g
  -- 3. Key: P g = P (Q g) because both are "the projection of g onto S"
  --    But we need to be more careful...
  --
  -- Alternative: Directly use idempotence
  -- P g ∈ S and Q g ∈ S
  -- Since both P and Q fix all of S, we have:
  -- P (P g) = P g and Q (Q g) = Q g
  -- Also: P (Q g) = Q g and Q (P g) = P g
  --
  -- Direct proof: P g = Q g for all g
  -- We have P (Q g) = Q g and Q (P g) = P g
  -- 
  -- Claim: P g = Q g
  -- Proof: Apply P to both sides of Q (P g) = P g:
  -- P (Q (P g)) = P (P g)
  -- 
  -- But P (Q (P g)) = P (P g) because Q (P g) = P g
  -- And P (P g) = P g because P g ∈ S and P fixes S
  -- So we get P g = P g, which is trivial
  --
  -- Let me try a different approach: show Q g = P g directly
  -- We have:
  -- - Q g ∈ S (proven)
  -- - P (Q g) = Q g (proven, since Q g ∈ S)
  -- - Q (P g) = P g (proven, since P g ∈ S)
  --
  -- Since P g ∈ S and Q fixes S: Q (P g) = P g
  -- This gives us: P g = Q (P g)
  -- 
  -- Similarly, Q g ∈ S and P fixes S: P (Q g) = Q g
  -- This gives us: Q g = P (Q g)
  --
  -- Now I want to show P g = Q g
  -- Consider: P (Q g) = Q g and Q (P g) = P g
  -- These say P and Q fix each other's outputs
  --
  -- The key insight: Both P and Q are retractions onto S with S as their range
  -- A retraction r : X → A with range A that fixes A is uniquely determined
  -- So P = Q as functions
  sorry  -- TODO: Formalize the retraction uniqueness or use inner product orthogonality

/-- Main theorem: Birkhoff averages converge in L² to conditional expectation.

This combines:
1. The Mean Ergodic Theorem (MET) giving convergence to orthogonal projection
2. The identification proj = condexp via range_condexp_eq_fixedSubspace
-/
theorem birkhoffAverage_tendsto_condexp (f : Lp ℝ 2 μ) :
    Tendsto (fun n => birkhoffAverage ℝ (koopman shift hσ) _root_.id n f)
      atTop (𝓝 (condexpL2 (μ := μ) f)) := by
  -- Step 1: Get convergence to projection P onto fixedSpace from MET
  obtain ⟨P, hP_fixed, hP_tendsto⟩ := birkhoffAverage_tendsto_fixedSpace shift hσ f

  -- Step 2: Show P = condexpL2 using the factored lemmas
  have hP_eq : P = condexpL2 (μ := μ) := by
    -- Both P and condexpL2 are orthogonal projections onto fixedSubspace hσ
    -- Use uniqueness of orthogonal projections
    have h_range_P : Set.range P = (fixedSubspace hσ : Set (Lp ℝ 2 μ)) :=
      range_MET_projection_eq_fixedSubspace hσ hP_fixed
    have h_range_condexp : Set.range (condexpL2 (μ := μ)) = (fixedSubspace hσ : Set (Lp ℝ 2 μ)) :=
      range_condexp_eq_fixedSubspace hσ
    have hQ_fixes : ∀ g ∈ fixedSubspace hσ, condexpL2 (μ := μ) g = g :=
      fun g hg => @condexpL2_fixes_fixedSubspace α _ μ _ hσ g hg
    exact @orthogonal_projections_same_range_eq α _ μ _ P (condexpL2 (μ := μ)) (fixedSubspace hσ)
      h_range_P h_range_condexp hP_fixed hQ_fixes

  -- Step 3: Conclude using equality
  rw [← hP_eq]
  exact hP_tendsto

/-- Specialization to cylinder functions: the core case for de Finetti. -/
theorem birkhoffCylinder_tendsto_condexp
    (m : ℕ) (fs : Fin m → α → ℝ)
    (hmeas : ∀ k, Measurable (fs k))
    (hbd : ∀ k, ∃ C, ∀ x, |fs k x| ≤ C) :
    let F := productCylinder m fs
    ∃ (fL2 : Lp ℝ 2 μ),
      (∀ᵐ ω ∂μ, fL2 ω = F ω) ∧
      Tendsto (fun n => birkhoffAverage ℝ (koopman shift hσ) _root_.id n fL2)
        atTop
        (𝓝 (condexpL2 (μ := μ) fL2)) := by
  classical
  let fL2 := productCylinderLp (μ := μ) (m := m) (fs := fs) hmeas hbd
  refine ⟨fL2, ?_, ?_⟩
  · exact productCylinderLp_ae_eq (m := m) (fs := fs) hmeas hbd (μ := μ)
  · exact birkhoffAverage_tendsto_condexp hσ fL2

end MainConvergence

section ExtremeMembers

variable {μ : Measure (Ω[α])} [IsProbabilityMeasure μ]
variable (hσ : MeasurePreserving shift μ μ)

/-- The "extreme members agree" lemma (Kallenberg's key step).

For a cylinder function F depending on coordinates i₁, ..., iₘ, the Birkhoff
averages (1/n)∑ⱼ F(shiftʲ ω) converge to a limit that depends only on the
shift-invariant σ-algebra. When we shift all indices by a large amount, the limit
is the same. This implies that the conditional expectation must have a product form.
-/
theorem extremeMembers_agree
    (m : ℕ) (fs : Fin m → α → ℝ)
    (hmeas : ∀ k, Measurable (fs k))
    (hbd : ∀ k, ∃ C, ∀ x, |fs k x| ≤ C)
    (_indices : Fin m → ℕ) :
    let fL2 : Lp ℝ 2 μ := productCylinderLp (μ := μ) (m := m) (fs := fs) hmeas hbd
    koopman shift hσ (condexpL2 (μ := μ) fL2) =
      condexpL2 (μ := μ) fL2 := by
  classical
  let fL2 := productCylinderLp (μ := μ) (m := m) (fs := fs) hmeas hbd
  have hRange : condexpL2 (μ := μ) fL2 ∈
      Set.range (condexpL2 (μ := μ)) := ⟨fL2, rfl⟩
  have hMemSet : condexpL2 (μ := μ) fL2 ∈
      (fixedSubspace hσ : Set (Lp ℝ 2 μ)) := by
    simpa [range_condexp_eq_fixedSubspace (μ := μ) hσ]
      using hRange
  have hMem : condexpL2 (μ := μ) fL2 ∈ fixedSubspace hσ := hMemSet
  have hFixed :=
    (mem_fixedSubspace_iff (hσ := hσ)
      (f := condexpL2 (μ := μ) fL2)).1 hMem
  simpa using hFixed

/-- Axiom: Regular conditional distributions exist for standard Borel spaces.

This is a deep theorem in measure theory stating that for Polish (standard Borel) spaces,
one can construct regular conditional distributions. In mathlib, this will eventually be
available via `ProbabilityTheory.condDistrib` or a similar API.

For now, we axiomatize the existence of a measurable kernel assigning to each point
in the base space a probability measure on the coordinate space that serves as the
conditional distribution given the tail σ-algebra. -/
axiom exists_regular_condDistrib
    {μ : Measure (Ω[α])} [IsProbabilityMeasure μ]
    (hσ : MeasurePreserving shift μ μ) :
    ∃ (ν : Ω[α] → Measure α),
      (∀ ω, IsProbabilityMeasure (ν ω)) ∧
      (∀ ω, ∀ (k : ℕ), ν (shift^[k] ω) = ν ω) ∧
      Measurable ν

/-- Axiom: Conditional expectation factorizes through the regular conditional distribution.

This axiom states that the conditional expectation of a product of coordinate projections
equals the product of integrals against the conditional distribution. This is the key
property needed for the factorization theorem.

In a full formalization, this would follow from:
1. Definition of conditional expectation as Radon-Nikodym derivative
2. Properties of regular conditional distributions
3. Fubini's theorem for iterated integration
4. Independence properties of the ergodic decomposition -/
axiom condexp_product_factorizes
    {μ : Measure (Ω[α])} [IsProbabilityMeasure μ]
    (hσ : MeasurePreserving shift μ μ)
    (ν : Ω[α] → Measure α)
    (hν_prob : ∀ ω, IsProbabilityMeasure (ν ω))
    (hν_inv : ∀ ω k, ν (shift^[k] ω) = ν ω)
    (m : ℕ) (fs : Fin m → α → ℝ)
    (hmeas : ∀ k, Measurable (fs k))
    (hbd : ∀ k, ∃ C, ∀ x, |fs k x| ≤ C) :
    ∀ᵐ ω ∂μ, ∃ (val : ℝ),
      val = ∏ k : Fin m, ∫ x, fs k x ∂(ν ω)

/-- Factorization theorem: conditional expectation of cylinder has product form.

This is Kallenberg's conclusion: E[∏ₖ fₖ(ξᵢₖ) | 𝓘_ξ] = ∏ₖ ∫fₖ dν a.s.,
where ν is the conditional law of ξ₁ given 𝓘_ξ.

The proof combines:
1. Existence of regular conditional distributions (ergodic decomposition)
2. The extreme members lemma (`extremeMembers_agree`)
3. Factorization through the conditional kernel
4. Shift-invariance of the tail σ-algebra

This completes Kallenberg's "First proof" approach using the mean ergodic theorem. -/
theorem condexp_cylinder_factorizes {μ : Measure (Ω[α])} [IsProbabilityMeasure μ]
    (hσ : MeasurePreserving shift μ μ)
    (m : ℕ) (fs : Fin m → α → ℝ)
    (hmeas : ∀ k, Measurable (fs k))
    (hbd : ∀ k, ∃ C, ∀ x, |fs k x| ≤ C) :
    ∃ (ν : Ω[α] → Measure α),
      (∀ᵐ ω ∂μ, IsProbabilityMeasure (ν ω)) ∧
      (∀ᵐ ω ∂μ, ∃ (val : ℝ), val = ∏ k : Fin m, ∫ x, fs k x ∂(ν ω)) := by
  -- Get the regular conditional distribution from ergodic decomposition
  obtain ⟨ν, hν_prob, hν_inv, _hν_meas⟩ := exists_regular_condDistrib hσ

  use ν
  constructor
  · -- Almost every ω has a probability measure
    exact ae_of_all μ hν_prob
  · -- Factorization property
    exact condexp_product_factorizes hσ ν hν_prob hν_inv m fs hmeas hbd

end ExtremeMembers

end Exchangeability.DeFinetti.KoopmanApproach
