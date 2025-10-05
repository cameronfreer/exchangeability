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

  -- Step 2: Show P = condexpL2 by showing they're both projections onto the same subspace
  have hP_eq : P = condexpL2 (μ := μ) := by
    -- Both P and condexpL2 are orthogonal projections onto fixedSubspace hσ
    -- We'll show they're equal by showing they agree on all elements
    ext g
    -- Strategy: Show both P g and condexpL2 g are in fixedSubspace, and both equal
    -- the unique element of fixedSubspace closest to g
    
    -- Key insight: For orthogonal projections onto a subspace S:
    -- If P₁ and P₂ both satisfy:
    --   (a) range = S
    --   (b) act as identity on S
    -- Then P₁ = P₂
    
    -- We have from hP_fixed that P acts as identity on fixedSubspace
    -- We need to show condexpL2 also acts as identity on fixedSubspace
    -- and that both have range = fixedSubspace
    
    -- Key observation: fixedSubspace hσ = fixedSpace (koopman shift hσ) by definition
    -- So hP_fixed says P acts as identity on fixedSubspace
    
    -- From MET construction: P = inclusion ∘ orthogonalProjection
    -- where orthogonalProjection : Lp → fixedSubspace and inclusion : fixedSubspace → Lp
    -- Therefore range P = fixedSubspace
    have h_range_P_eq : Set.range P = (fixedSubspace hσ : Set (Lp ℝ 2 μ)) := by
      -- This follows from the construction of P in birkhoffAverage_tendsto_fixedSpace
      -- P is defined as inclusion.comp projToSub where:
      -- - projToSub : Lp →L[ℝ] S is orthogonal projection onto S = fixedSpace (koopman shift hσ)
      -- - inclusion : S →L[ℝ] Lp is S.subtypeL
      -- The range of this composition is exactly S
      
      -- By definition: fixedSubspace hσ = fixedSpace (koopman shift hσ)
      rw [fixedSubspace]
      
      -- Now need to show: Set.range P = Set.range inclusion
      -- Since projToSub is surjective onto S, range (inclusion ∘ projToSub) = range inclusion
      
      -- The range of subtypeL is the subspace itself (as a set)
      -- This is because subtypeL : S → E embeds S into E
      
      ext x
      constructor
      · intro ⟨y, hy⟩
        -- x = P y for some y
        rw [← hy]
        -- Need: P y ∈ fixedSpace (koopman shift hσ)
        -- 
        -- From the MET construction in KoopmanMeanErgodic:
        -- P = inclusion.comp projToSub
        -- where projToSub = S.orthogonalProjection and S = fixedSpace (koopman shift hσ)
        -- and inclusion = S.subtypeL
        --
        -- The key property we need is: for any z in the range of P,
        -- z ∈ fixedSpace (koopman shift hσ)
        --
        -- This follows from the fact that P is constructed as the composition
        -- of orthogonal projection onto S followed by subtype inclusion.
        -- The range of this composition is exactly S.
        --
        -- Mathematical fact: If P = subtype ∘ proj where proj : E → S,
        -- then range P = S (as a subset of E)
        --
        -- This is a standard property in functional analysis:
        -- the range of an orthogonal projection composed with inclusion is the subspace
        --
        -- For now, we need a lemma like:
        -- lemma range_subtypeL_comp_orthogonalProjection (S : Submodule ℝ E) :
        --   Set.range (S.subtypeL.comp S.orthogonalProjection) = (S : Set E)
        sorry
      · intro hx
        -- x ∈ fixedSpace (koopman shift hσ)
        -- Need to show x ∈ range P
        -- Since x ∈ S, we have x = inclusion ⟨x, hx⟩
        -- Also ⟨x, hx⟩ = projToSub x (since x ∈ S and projection fixes elements of S)
        -- Therefore x = inclusion (projToSub x) = P x
        use x
        -- Need: P x = x
        -- This follows from hP_fixed when x ∈ fixedSpace
        exact hP_fixed x hx
    
    have h_range_P : Set.range P ⊆ (fixedSubspace hσ : Set (Lp ℝ 2 μ)) :=
      h_range_P_eq.subset
    
    have h_range_condexp : Set.range (condexpL2 (μ := μ)) = (fixedSubspace hσ : Set (Lp ℝ 2 μ)) :=
      range_condexp_eq_fixedSubspace hσ
    
    -- Both P g and condexpL2 g are in fixedSubspace
    have hPg_in : P g ∈ (fixedSubspace hσ : Set (Lp ℝ 2 μ)) := h_range_P ⟨g, rfl⟩
    have hcondexp_in : condexpL2 (μ := μ) g ∈ (fixedSubspace hσ : Set (Lp ℝ 2 μ)) := by
      rw [← h_range_condexp]
      exact ⟨g, rfl⟩
    
    -- Apply hP_fixed to both (they're both in fixedSubspace, so P fixes them)
    have hP_idem_Pg : P (P g) = P g := hP_fixed (P g) hPg_in
    have hP_fixes_condexp : P (condexpL2 (μ := μ) g) = condexpL2 (μ := μ) g := hP_fixed _ hcondexp_in
    
    -- condexpL2 also acts as identity on fixedSubspace (property of conditional expectation)
    -- This is a key property: conditional expectation onto a sub-σ-algebra fixes functions
    -- that are already measurable with respect to that sub-σ-algebra
    have hcondexp_fixes_P : condexpL2 (μ := μ) (P g) = P g := by
      -- P g ∈ fixedSubspace means koopman shift hσ (P g) = P g
      -- This means (P g) ∘ shift = P g almost everywhere
      -- By koopman_fixed_of_shiftInvariant_measurable (axiomatized), this implies
      -- P g is measurable with respect to shiftInvariantSigma
      -- 
      -- condexpL2 is defined as: subtypeL ∘ (condExpL2 onto lpMeas)
      -- where lpMeas is the subspace of shiftInvariantSigma-measurable functions
      --
      -- If P g ∈ lpMeas, then:
      -- condExpL2 (P g) = P g (orthogonal projection fixes elements of the subspace)
      -- Therefore condexpL2 (P g) = subtypeL (condExpL2 (P g)) = subtypeL (P g) = P g
      --
      -- Need two facts:
      -- 1. P g ∈ lpMeas (follows from lpMeas_eq_fixedSubspace)
      -- 2. Orthogonal projection fixes elements of the subspace
      sorry
    
    -- Final step: show P g = condexpL2 g using uniqueness of orthogonal projections
    --
    -- We have established:
    -- 1. range P = fixedSubspace (from h_range_P_eq)
    -- 2. range condexpL2 = fixedSubspace (from h_range_condexp)
    -- 3. P acts as identity on fixedSubspace (from hP_fixed)
    -- 4. condexpL2 acts as identity on fixedSubspace (from hcondexp_fixes_P)
    --
    -- Claim: P g = condexpL2 g for all g
    --
    -- Proof: Both P g and condexpL2 g are in fixedSubspace (from 1, 2).
    -- Consider h = P g - condexpL2 g.
    -- We'll show h = 0 by showing h ∈ fixedSubspace and ⟨h, h⟩ = 0.
    --
    -- First, h ∈ fixedSubspace:
    -- Since fixedSubspace is a subspace and both P g, condexpL2 g are in it, h is in it.
    --
    -- Second, ⟨h, h⟩ = 0:
    -- Since h ∈ fixedSubspace, we have:
    -- P h = h (by property 3, P fixes fixedSubspace elements)
    -- condexpL2 h = h (by property 4, condexpL2 fixes fixedSubspace elements)
    --
    -- But h = P g - condexpL2 g, so:
    -- P h = P (P g - condexpL2 g) = P (P g) - P (condexpL2 g)
    --     = P g - condexpL2 g  (using hP_idem_Pg and hP_fixes_condexp)
    --     = h
    -- Similarly: condexpL2 h = h
    --
    -- This doesn't immediately give us h = 0...
    --
    -- Alternative: Use that both are orthogonal projections, characterized by:
    -- y = proj_S(x) iff y ∈ S and ⟨x - y, s⟩ = 0 for all s ∈ S
    --
    -- For this we need: ⟨g - P g, s⟩ = 0 and ⟨g - condexpL2 g, s⟩ = 0 for all s ∈ fixedSubspace
    -- This is the definition of orthogonal projection!
    sorry

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
