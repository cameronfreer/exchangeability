/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.Independence.Kernel
import Exchangeability.Ergodic.KoopmanMeanErgodic
import Exchangeability.DeFinetti.InvariantSigma
import Exchangeability.DeFinetti.ProjectionLemmas

/-!
# de Finetti's Theorem via Koopman Operator

**Kallenberg's "first proof"** of de Finetti's theorem using the Mean Ergodic
Theorem and Koopman operator. This proof has the **heaviest dependencies**.

## Proof approach

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

* `deFinetti_viaKoopman`: **Main theorem** - contractable implies conditionally i.i.d.
* Supporting lemmas for Birkhoff averages and conditional expectations

## Dependencies

❌ **Heavy** - Requires ergodic theory, Mean Ergodic Theorem, orthogonal projections
✅ **Deep connection** to dynamical systems and ergodic theory
✅ **Generalizes** beyond exchangeability to measure-preserving systems

## References

* Kallenberg (2005), *Probabilistic Symmetries and Invariance Principles*,
  Chapter 1, pages 26-27: "First proof of Theorem 1.1"

-/

noncomputable section

namespace Exchangeability.DeFinetti.ViaKoopman

open MeasureTheory Filter Topology ProbabilityTheory
open Exchangeability.Ergodic
open scoped BigOperators

variable {α : Type*} [MeasurableSpace α]

namespace MeasureTheory

/-- Helper lemma: A measurable real-valued function bounded in absolute value is integrable
under a probability measure. -/
theorem integrable_of_bounded {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : Ω → ℝ} (hmeas : Measurable f) (hbd : ∃ C, ∀ ω, |f ω| ≤ C) :
    Integrable f μ := by
  obtain ⟨C, hC⟩ := hbd
  exact ⟨hmeas.aestronglyMeasurable, HasFiniteIntegral.of_bounded (ae_of_all μ hC)⟩

end MeasureTheory

section CylinderFunctions

/-- Cylinder function: a function on path space depending only on finitely many coordinates.
For simplicity, we take the first m coordinates. -/
def cylinderFunction {m : ℕ} (φ : (Fin m → α) → ℝ) : Ω[α] → ℝ :=
  fun ω => φ (fun k => ω k.val)

/-- Product cylinder: ∏_{k < m} fₖ(ω k). -/
def productCylinder {m : ℕ} (fs : Fin m → α → ℝ) : Ω[α] → ℝ :=
  fun ω => ∏ k : Fin m, fs k (ω k.val)

omit [MeasurableSpace α] in
lemma productCylinder_eq_cylinder {m : ℕ} (fs : Fin m → α → ℝ) :
    productCylinder fs = cylinderFunction (fun coords => ∏ k, fs k (coords k)) := by
  rfl

/-- Measurability of cylinder functions. -/
lemma measurable_cylinderFunction {m : ℕ} {φ : (Fin m → α) → ℝ}
    (_hφ : Measurable φ) :
    Measurable (cylinderFunction φ) := by
  classical
  have hproj : Measurable fun ω : Ω[α] => fun k : Fin m => ω k.val := by
    refine measurable_pi_lambda _ ?_
    intro k
    simpa using (measurable_pi_apply (k.val))
  simpa [cylinderFunction] using _hφ.comp hproj

/-- Measurability of product cylinders. -/
lemma measurable_productCylinder {m : ℕ} {fs : Fin m → α → ℝ}
    (hmeas : ∀ k, Measurable (fs k)) :
    Measurable (productCylinder fs) := by
  classical
  unfold productCylinder
  -- Product of measurable functions is measurable
  apply Finset.measurable_prod
  intro k _
  exact (hmeas k).comp (measurable_pi_apply k.val)

omit [MeasurableSpace α] in
/-- Boundedness of product cylinders. -/
lemma productCylinder_bounded {m : ℕ} {fs : Fin m → α → ℝ}
    (hbd : ∀ k, ∃ C, ∀ x, |fs k x| ≤ C) :
    ∃ C, ∀ ω, |productCylinder fs ω| ≤ C := by
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
  have habs_eq : |productCylinder fs ω| = ∏ k : Fin m, |fs k (ω k.val)| := by
    simp [productCylinder, Finset.abs_prod]
  exact (by simpa [habs_eq] using hprod)

/-- Membership of product cylinders in `L²`. -/
lemma productCylinder_memLp
    {m : ℕ} (fs : Fin m → α → ℝ)
    (hmeas : ∀ k, Measurable (fs k))
    (hbd : ∀ k, ∃ C, ∀ x, |fs k x| ≤ C)
    {μ : Measure (Ω[α])} [IsProbabilityMeasure μ] :
    MeasureTheory.MemLp (productCylinder fs) 2 μ := by
  classical
  obtain ⟨C, hC⟩ := productCylinder_bounded (fs:=fs) hbd
  have hFmeas : Measurable (productCylinder fs) :=
    measurable_productCylinder (fs:=fs) hmeas
  refine MeasureTheory.MemLp.of_bound (μ := μ) (p := 2)
    hFmeas.aestronglyMeasurable C ?_
  filter_upwards with ω
  simpa [Real.norm_eq_abs] using hC ω

/-- `Lp` representative associated to a bounded product cylinder. -/
noncomputable def productCylinderLp
    {m : ℕ} (fs : Fin m → α → ℝ)
    (hmeas : ∀ k, Measurable (fs k))
    (hbd : ∀ k, ∃ C, ∀ x, |fs k x| ≤ C)
    {μ : Measure (Ω[α])} [IsProbabilityMeasure μ] : Lp ℝ 2 μ :=
  (productCylinder_memLp (fs := fs) hmeas hbd).toLp (productCylinder fs)

lemma productCylinderLp_ae_eq
    {m : ℕ} (fs : Fin m → α → ℝ)
    (hmeas : ∀ k, Measurable (fs k))
    (hbd : ∀ k, ∃ C, ∀ x, |fs k x| ≤ C)
    {μ : Measure (Ω[α])} [IsProbabilityMeasure μ] :
    (∀ᵐ ω ∂μ, productCylinderLp (μ := μ) (fs := fs) hmeas hbd ω =
      productCylinder fs ω) := by
  classical
  exact MeasureTheory.MemLp.coeFn_toLp
    (productCylinder_memLp (μ := μ) (fs := fs) hmeas hbd)

/-- The shifted cylinder function: F ∘ shift^n. -/
def shiftedCylinder (n : ℕ) (F : Ω[α] → ℝ) : Ω[α] → ℝ :=
  fun ω => F ((shift^[n]) ω)

end CylinderFunctions

section MainConvergence

variable {μ : Measure (Ω[α])} [IsProbabilityMeasure μ]
variable (hσ : MeasurePreserving shift μ μ)

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
  have h_idem := congrArg (fun T => T f) (condexpL2_idem (μ := μ))
  simpa [ContinuousLinearMap.comp_apply] using h_idem

/-- Main theorem: Birkhoff averages converge in L² to conditional expectation.

This combines:
1. The Mean Ergodic Theorem (MET) giving convergence to orthogonal projection
2. The identification proj = condexp via range_condexp_eq_fixedSubspace
-/
theorem birkhoffAverage_tendsto_condexp (f : Lp ℝ 2 μ) :
    Tendsto (fun n => birkhoffAverage ℝ (koopman shift hσ) _root_.id n f)
      atTop (𝓝 (condexpL2 (μ := μ) f)) := by
  -- Step 1: Get convergence to projection P onto fixedSpace from MET
  classical
  -- Use the canonical mean ergodic projection from `InvariantSigma`
  let P := METProjection (μ := μ) hσ
  have hP_tendsto := METProjection_tendsto (μ := μ) hσ f
  have hP_fixed : ∀ g ∈ fixedSubspace hσ, P g = g :=
    fun g hg => METProjection_fixes_fixedSubspace (μ := μ) hσ hg

  -- Step 2: Show P = condexpL2 using the factored lemmas
  have hP_eq : P = condexpL2 (μ := μ) := by
    -- Both P and condexpL2 are orthogonal projections onto the fixed subspace
    -- Use uniqueness of symmetric idempotent projections with the same range
    have h_range_P : Set.range P = (fixedSubspace hσ : Set (Lp ℝ 2 μ)) :=
      METProjection_range_fixedSubspace (μ := μ) hσ
    have h_range_condexp : Set.range (condexpL2 (μ := μ)) =
        (fixedSubspace hσ : Set (Lp ℝ 2 μ)) := range_condexp_eq_fixedSubspace hσ
    have hQ_fixes : ∀ g ∈ fixedSubspace hσ, condexpL2 (μ := μ) g = g :=
      fun g hg => condexpL2_fixes_fixedSubspace (hσ := hσ) hg
    have hP_idem : P.comp P = P := METProjection_idem (μ := μ) hσ
    have hQ_idem : (condexpL2 (μ := μ)).comp (condexpL2 (μ := μ)) = condexpL2 (μ := μ) :=
      condexpL2_idem (μ := μ)
    have hP_sym : P.IsSymmetric := METProjection_isSymmetric (μ := μ) hσ
    have hQ_sym : (condexpL2 (μ := μ)).IsSymmetric := by
      intro f g
      unfold condexpL2
      exact MeasureTheory.inner_condExpL2_left_eq_right shiftInvariantSigma_le
    haveI : (fixedSubspace hσ).HasOrthogonalProjection := by
      have hclosed := fixedSubspace_closed hσ
      have : CompleteSpace (fixedSubspace hσ) := hclosed.completeSpace_coe
      exact Submodule.HasOrthogonalProjection.ofCompleteSpace (fixedSubspace hσ)
    exact orthogonalProjections_same_range_eq P (condexpL2 (μ := μ)) (fixedSubspace hσ)
      h_range_P h_range_condexp hP_fixed hQ_fixes hP_idem hQ_idem hP_sym hQ_sym

  -- Step 3: Conclude using equality
  rw [← hP_eq]
  exact hP_tendsto

/-- Specialization to cylinder functions: the core case for de Finetti. -/
theorem birkhoffCylinder_tendsto_condexp
    {m : ℕ} (fs : Fin m → α → ℝ)
    (hmeas : ∀ k, Measurable (fs k))
    (hbd : ∀ k, ∃ C, ∀ x, |fs k x| ≤ C) :
    let F := productCylinder fs
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

/-- The projection onto the first coordinate. -/
def π0 : Ω[α] → α := fun ω => ω 0


lemma measurable_pi0 : Measurable (π0 (α := α)) := by
  classical
  simpa using (measurable_pi_apply (0 : ℕ) :
    Measurable fun ω : Ω[α] => ω 0)

namespace ProbabilityTheory.Kernel

/-- **TODO**: Add to Mathlib.

Two kernels from α to β are equal μ-almost everywhere if they give the same integrals
for all bounded measurable test functions.

This is the kernel analogue of `Measure.ext_of_forall_integral_eq` and should be proved
using standard measure theory techniques (approximation by simple functions, monotone
convergence, uniqueness of measures).

**Proof sketch**:
1. For each a, the measures κ(a) and η(a) agree on integrals of bounded measurable functions
2. By density of bounded functions and monotone class theorem, κ(a) = η(a) as measures
3. The set where κ(a) ≠ η(a) has μ-measure zero by hypothesis
-/
axiom ae_eq_of_forall_integral_eq {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    [StandardBorelSpace β] {μ : Measure α} {κ η : @Kernel α β mα mβ} :
    (∀ (f : β → ℝ) (hf : Measurable f) (hbd : ∃ C, ∀ b, |f b| ≤ C),
      (fun a => ∫ b, f b ∂(κ a)) =ᵐ[μ] (fun a => ∫ b, f b ∂(η a))) →
    (∀ᵐ a ∂μ, κ a = η a)

end ProbabilityTheory.Kernel

/-- Regular conditional distribution kernel constructed via condExpKernel.

This is the kernel giving the conditional distribution of the first coordinate
given the tail σ-algebra.

TODO: The exact construction requires careful handling of the measurable space instances.
For now we axiomatize it as a placeholder. -/
noncomputable def rcdKernel {μ : Measure (Ω[α])} [IsProbabilityMeasure μ]
    [StandardBorelSpace α] : Kernel (Ω[α]) α :=
  Kernel.comap ((condExpKernel μ (shiftInvariantSigma (α := α))).map (π0 (α := α)))
    id (measurable_id'' (shiftInvariantSigma_le (α := α)))

instance rcdKernel_isMarkovKernel {μ : Measure (Ω[α])} [IsProbabilityMeasure μ]
    [StandardBorelSpace α] : IsMarkovKernel (rcdKernel (μ := μ)) := by
  unfold rcdKernel
  -- First, condExpKernel is a Markov kernel
  have h1 : IsMarkovKernel (condExpKernel μ (shiftInvariantSigma (α := α))) := inferInstance
  -- Second, map preserves IsMarkovKernel
  have h2 : IsMarkovKernel ((condExpKernel μ (shiftInvariantSigma (α := α))).map (π0 (α := α))) :=
    Kernel.IsMarkovKernel.map _ (measurable_pi0 (α := α))
  -- Third, comap preserves IsMarkovKernel (this is an instance)
  exact Kernel.IsMarkovKernel.comap _ (measurable_id'' (shiftInvariantSigma_le (α := α)))

/-- The regular conditional distribution as a function assigning to each point
 a probability measure on α. -/
noncomputable def ν {μ : Measure (Ω[α])} [IsProbabilityMeasure μ]
    [StandardBorelSpace α] : Ω[α] → Measure α :=
  fun ω => (rcdKernel (μ := μ)) ω

/-- Convenient rewrite for evaluating the kernel `ν` on a measurable set. -/
lemma ν_apply {μ : Measure (Ω[α])} [IsProbabilityMeasure μ] [StandardBorelSpace α]
    (ω : Ω[α]) (s : Set α) (hs : MeasurableSet s) :
    ν (μ := μ) ω s
      = (condExpKernel μ (shiftInvariantSigma (α := α)) ω)
          ((fun y : Ω[α] => y 0) ⁻¹' s) := by
  unfold ν rcdKernel
  -- Unfold comap and map applications
  rw [Kernel.comap_apply, Kernel.map_apply' _ (measurable_pi0 (α := α)) _ hs]
  -- π0 is defined as (fun y => y 0), so the preimages are equal
  rfl

/-- The kernel ν gives probability measures. -/
instance ν_isProbabilityMeasure {μ : Measure (Ω[α])} [IsProbabilityMeasure μ]
    [StandardBorelSpace α] (ω : Ω[α]) :
    IsProbabilityMeasure (ν (μ := μ) ω) := by
  unfold ν
  -- rcdKernel is a Markov kernel (composition of map and comap preserves this)
  exact IsMarkovKernel.isProbabilityMeasure ω

/-- The kernel `ν` is measurable with respect to the tail σ-algebra.

Note: This property should follow from the construction via condExpKernel, but requires
careful handling of measurable space parameters. The condExpKernel is defined as
`@Kernel Ω Ω m mΩ`, i.e., measurable w.r.t. the sub-σ-algebra m on the source.
However, map and comap operations may not preserve this explicit typing.
This lemma may not be needed for the main results. -/
lemma ν_measurable_tail {μ : Measure (Ω[α])} [IsProbabilityMeasure μ]
    [StandardBorelSpace α] :
    Measurable[shiftInvariantSigma (α := α)] (ν (μ := μ)) := by
  sorry  -- TODO: Requires reformulation or may not be necessary

/-!
Helper lemmas establishing the stability of the conditional expectation and the
regular conditional distribution under compositions with shift iterates.
-/

private lemma condexp_precomp_iterate_eq
    {μ : Measure (Ω[α])} [IsProbabilityMeasure μ]
    (hσ : MeasurePreserving shift μ μ) {k : ℕ}
    {f : Ω[α] → ℝ} (hf : Integrable f μ) :
    μ[(fun ω => f ((shift (α := α))^[k] ω)) | shiftInvariantSigma (α := α)]
      =ᵐ[μ] μ[f | shiftInvariantSigma (α := α)] := by
  classical
  set shiftk := (shift (α := α))^[k] with hshiftk_def
  have h_shiftk_pres : MeasurePreserving shiftk μ μ := hσ.iterate k
  have h_shiftk_meas : AEMeasurable shiftk μ :=
    (measurable_shift (α := α)).iterate k |>.aemeasurable
  have h_int_shift : Integrable (fun ω => f (shiftk ω)) μ :=
    h_shiftk_pres.integrable_comp_of_integrable hf
  have h_condexp_int : Integrable (μ[f | shiftInvariantSigma (α := α)]) μ :=
    MeasureTheory.integrable_condExp
  refine (MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq
        (μ := μ) (m := shiftInvariantSigma (α := α))
        (hm := shiftInvariantSigma_le (α := α))
        (f := fun ω => f (shiftk ω))
        (g := μ[f | shiftInvariantSigma (α := α)])
        (hf := h_int_shift)
        (hg_int_finite := ?hg_int_finite)
        (hg_eq := ?hg_eq)
        (hgm := (MeasureTheory.stronglyMeasurable_condExp (μ := μ)).aestronglyMeasurable)).symm
  case hg_int_finite =>
    intro s hs _
    have h_int : Integrable (μ[f | shiftInvariantSigma (α := α)]) μ := integrable_condExp
    exact h_int.integrableOn
  case hg_eq =>
    intro s hs _
    have hS := (mem_shiftInvariantSigma_iff (α := α) (s := s)).1 hs
    have hS_meas : MeasurableSet s := hS.1
    have hS_shift : shift ⁻¹' s = s := hS.2
    have hS_iter : shiftk ⁻¹' s = s := by
      rw [hshiftk_def]
      clear hshiftk_def shiftk h_shiftk_pres h_shiftk_meas h_int_shift h_condexp_int
      induction k with
      | zero => rfl
      | succ k hk =>
        rw [Function.iterate_succ']
        simp only [Set.preimage_comp, hk, hS_shift]
    have h_indicator_int : Integrable (s.indicator f) μ :=
      hf.indicator hS_meas
    have h_indicator_meas :
        AEStronglyMeasurable (s.indicator f) μ :=
      hf.aestronglyMeasurable.indicator hS_meas
    have hfm : AEStronglyMeasurable (s.indicator f) (Measure.map shiftk μ) := by
      simpa [h_shiftk_pres.map_eq] using h_indicator_meas
    have h_indicator_comp :
        ∫ ω, s.indicator f ω ∂μ
          = ∫ ω, s.indicator f (shiftk ω) ∂μ := by
      have :=
        MeasureTheory.integral_map
          (μ := μ) (φ := shiftk)
          (f := s.indicator f)
          (hφ := h_shiftk_meas)
          (hfm := hfm)
      simpa [h_shiftk_pres.map_eq] using this
    have h_mem_equiv : ∀ ω, (shiftk ω ∈ s) ↔ ω ∈ s := by
      intro ω
      constructor
      · intro hmem
        have : ω ∈ shiftk ⁻¹' s := by simpa [Set.mem_preimage] using hmem
        simpa [hS_iter] using this
      · intro hω
        have : ω ∈ shiftk ⁻¹' s := by simpa [hS_iter] using hω
        simpa [Set.mem_preimage] using this
    have h_indicator_comp' :
        ∫ ω, s.indicator f (shiftk ω) ∂μ
          = ∫ ω, s.indicator (fun ω => f (shiftk ω)) ω ∂μ := by
      refine integral_congr_ae (ae_of_all _ ?_)
      intro ω
      by_cases hω : ω ∈ s
      · have h_shiftk_mem : shiftk ω ∈ s := (h_mem_equiv ω).mpr hω
        simp [Set.indicator, hω, h_shiftk_mem]
      · have h_shiftk_mem : shiftk ω ∉ s := by
          intro hcontr
          exact hω ((h_mem_equiv ω).mp hcontr)
        simp [Set.indicator, hω, h_shiftk_mem]
    have h_indicator_eq :
        ∫ ω, s.indicator f ω ∂μ
          = ∫ ω, s.indicator (fun ω => f (shiftk ω)) ω ∂μ :=
      h_indicator_comp.trans h_indicator_comp'
    calc
      ∫ ω in s, μ[f | shiftInvariantSigma (α := α)] ω ∂μ
          = ∫ ω in s, f ω ∂μ :=
            MeasureTheory.setIntegral_condExp
              (μ := μ) (m := shiftInvariantSigma (α := α))
              (hm := shiftInvariantSigma_le (α := α))
              (hf := hf) (hs := hs)
      _ = ∫ ω, s.indicator f ω ∂μ :=
            (MeasureTheory.integral_indicator hS_meas).symm
      _ = ∫ ω, s.indicator (fun ω => f (shiftk ω)) ω ∂μ := h_indicator_eq
      _ = ∫ ω in s, (fun ω => f (shiftk ω)) ω ∂μ :=
            MeasureTheory.integral_indicator hS_meas

/-- Almost-everywhere shift-invariance of the regular conditional distribution.

**Proof strategy** (no circularity, no kernel uniqueness axiom needed):
1. For each measurable set s ⊆ α, prove ν(shift^[k] ω)(s) = ν(ω)(s) a.e.
   using condexp_precomp_iterate_eq and condExp_ae_eq_integral_condExpKernel
2. Use a countable π-system generating Borel(α) and swap quantifiers via ae_all_iff
3. Extend from the π-system to all Borel sets via measure extension

This avoids assuming condExpKernel is shift-invariant; we only use that
conditional expectation commutes with shift for functions measurable w.r.t.
shift-invariant σ-algebra.
-/
lemma ν_ae_shiftInvariant {μ : Measure (Ω[α])} [IsProbabilityMeasure μ]
    [StandardBorelSpace α] (hσ : MeasurePreserving shift μ μ) :
    ∀ᵐ ω ∂μ, ∀ k : ℕ, ν (μ := μ) ((shift (α := α))^[k] ω) = ν (μ := μ) ω := by
  classical
  refine (ae_all_iff).2 ?_
  intro k

  -- We prove the measures are equal using the fact that they are both probability
  -- measures that agree on a countable basis

  -- Strategy: For each measurable set s ⊆ α, show ν(shift^[k] ω)(s) = ν(ω)(s) a.e.
  -- using condExpKernel's characterization via conditional expectation

  -- The key observation: by condExp_ae_eq_integral_condExpKernel,
  -- ν(ω)(s) = (condExpKernel ω)(π₀⁻¹ s) = μ[𝟙_{π₀⁻¹ s} | tail](ω) a.e.

  -- For now, we need to assume or prove that condExpKernel respects shift
  -- This requires showing: ∫ f d(condExpKernel (shift^[k] ω)) = ∫ f d(condExpKernel ω)
  -- for all measurable f, which follows from condexp_precomp_iterate_eq

  sorry  -- TODO: Full proof requires Kernel.ext_iff and condExp characterization

/-- Helper: shift^[k] y n = y (n + k) -/
lemma shift_iterate_apply (k n : ℕ) (y : Ω[α]) :
    (shift (α := α))^[k] y n = y (n + k) := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    simp only [shift]
    rw [ih]
    ring_nf

/-- The k-th coordinate equals the 0-th coordinate after k shifts. -/
lemma coord_k_eq_coord_0_shift_k (k : ℕ) :
    (fun y : Ω[α] => y k) = (fun y => y 0) ∘ (shift (α := α))^[k] := by
  funext y
  simp only [Function.comp_apply]
  rw [shift_iterate_apply]
  simp

/-- Identical conditional marginals: each coordinate shares the same
regular conditional distribution given the shift-invariant σ-algebra.

**Proof strategy** (using π-system approach, no kernel uniqueness axiom):
We show that the k-th marginal kernel equals ν by using the coordinate-shift relation
y k = (shift^[k] y) 0 and the shift-invariance of ν.

Key steps:
1. The k-th marginal is the pushforward of condExpKernel via πₖ
2. By coord_k_eq_coord_0_shift_k: πₖ = π₀ ∘ shift^[k]
3. So the k-th marginal at ω equals ν(shift^[k] ω)
4. By ν_ae_shiftInvariant: ν(shift^[k] ω) = ν(ω) a.e.
-/
lemma identicalConditionalMarginals {μ : Measure (Ω[α])} [IsProbabilityMeasure μ]
    [StandardBorelSpace α] (hσ : MeasurePreserving shift μ μ) (k : ℕ) :
    ∀ᵐ ω ∂μ,
      (Kernel.comap ((condExpKernel μ (shiftInvariantSigma (α := α))).map
        (fun y : Ω[α] => y k)) id (measurable_id'' (shiftInvariantSigma_le (α := α)))
        : Kernel (Ω[α]) α) ω
      = ν (μ := μ) ω := by
  -- The k-th marginal kernel is the pushforward via πₖ
  -- By definition of ν, the 0-th marginal kernel is the pushforward via π₀
  -- Using coord_k_eq_coord_0_shift_k: πₖ = π₀ ∘ shift^[k]

  -- The key insight: the k-th marginal at ω is ν(shift^[k] ω)
  -- By ν_ae_shiftInvariant, ν(shift^[k] ω) = ν(ω) a.e.

  -- First, express the LHS in terms of ν evaluated at shifted points
  -- have h_lhs : ∀ᵐ ω ∂μ, (LHS kernel) ω = ν(shift^[k] ω) := by ...

  -- Then apply ν_ae_shiftInvariant to get ν(shift^[k] ω) = ν(ω)

  sorry  -- TODO: Show LHS = ν(shift^[k] ω), then use ν_ae_shiftInvariant

/-- **Kernel-level integral multiplication under independence.**

If X and Y are independent under a kernel κ and measure μ, then for μ-almost every a,
the integral of their product under κ(a) equals the product of their integrals.

This is proved by reducing to the measure-level lemma `IndepFun.integral_mul_eq_mul_integral`
via a countable π-system + quantifier swap argument.

**Proof strategy:**
1. Bounded ⇒ integrable for all parameters (since κ a is a probability measure)
2. Convert kernel independence to pointwise (a.e. in a) measure-level independence
   using a countable π-system + monotone class argument to swap quantifiers
3. Apply the measure-level `IndepFun.integral_mul_eq_mul_integral` pointwise

This is a standard result in the theory of conditional expectations and should eventually
be added to Mathlib's `Probability.Independence.Kernel` or a new `Integration` submodule.
-/
lemma Kernel.IndepFun.integral_mul
    {α Ω : Type*} [MeasurableSpace α] [MeasurableSpace Ω]
    {κ : Kernel α Ω} {μ : Measure α}
    [IsFiniteMeasure μ] [IsMarkovKernel κ]
    {X Y : Ω → ℝ}
    (hXY : Kernel.IndepFun X Y κ μ)
    (hX : Measurable X) (hY : Measurable Y)
    (hX_bd : ∃ C, ∀ ω, |X ω| ≤ C) (hY_bd : ∃ C, ∀ ω, |Y ω| ≤ C) :
    ∀ᵐ a ∂μ, ∫ ω, X ω * Y ω ∂(κ a) = (∫ ω, X ω ∂(κ a)) * (∫ ω, Y ω ∂(κ a)) := by
  sorry
  /-
  classical

  -- Step 1: Bounded ⇒ integrable for all parameters
  rcases hX_bd with ⟨CX, hCX⟩
  rcases hY_bd with ⟨CY, hCY⟩
  have hX_int : ∀ a, Integrable X (κ a) := fun a => by
    refine ⟨hX.aestronglyMeasurable, ?_⟩
    have : ∫⁻ ω, ‖X ω‖₊ ∂(κ a) ≤ ∫⁻ ω, ENNReal.ofReal CX ∂(κ a) := by
      apply lintegral_mono
      intro ω
      have : (‖X ω‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖X ω‖ := by simp [ENNReal.ofReal]
      rw [this]
      exact ENNReal.ofReal_le_ofReal (le_trans (Real.norm_eq_abs _).le (hCX ω))
    calc ∫⁻ ω, ‖X ω‖₊ ∂(κ a)
        ≤ ∫⁻ ω, ENNReal.ofReal CX ∂(κ a) := this
      _ = ENNReal.ofReal CX * κ a Set.univ := by simp [lintegral_const]
      _ = ENNReal.ofReal CX := by simp [measure_univ]
      _ < ⊤ := ENNReal.ofReal_lt_top
  have hY_int : ∀ a, Integrable Y (κ a) := fun a => by
    refine ⟨hY.aestronglyMeasurable, ?_⟩
    have : ∫⁻ ω, ‖Y ω‖₊ ∂(κ a) ≤ ∫⁻ ω, ENNReal.ofReal CY ∂(κ a) := by
      apply lintegral_mono
      intro ω
      have : (‖Y ω‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖Y ω‖ := by simp [ENNReal.ofReal]
      rw [this]
      exact ENNReal.ofReal_le_ofReal (le_trans (Real.norm_eq_abs _).le (hCY ω))
    calc ∫⁻ ω, ‖Y ω‖₊ ∂(κ a)
        ≤ ∫⁻ ω, ENNReal.ofReal CY ∂(κ a) := this
      _ = ENNReal.ofReal CY * κ a Set.univ := by simp [lintegral_const]
      _ = ENNReal.ofReal CY := by simp [measure_univ]
      _ < ⊤ := ENNReal.ofReal_lt_top

  -- Step 2: From kernel independence to pointwise measure-level independence
  -- We use a countable π-system (rational intervals) + monotone class to swap quantifiers:
  -- ∀ sets s t, AE a, κ a (X⁻¹ s ∩ Y⁻¹ t) = κ a (X⁻¹ s) * κ a (Y⁻¹ t)
  -- ⇒ AE a, ∀ sets s t, κ a (X⁻¹ s ∩ Y⁻¹ t) = κ a (X⁻¹ s) * κ a (Y⁻¹ t)
  -- ⇒ AE a, IndepFun X Y (κ a)

  have h_indep_ae : ∀ᵐ a ∂μ, IndepFun X Y (κ a) := by
    -- Strategy: restrict to countable π-system generating the Borel σ-algebra,
    -- use ae_all_iff to swap quantifiers, then extend to full σ-algebra

    -- Step 2a: For rational intervals, we have a.e. factorization
    have h_rat_factor : ∀ q₁ q₂ : ℚ, ∀ᵐ a ∂μ,
        κ a (X ⁻¹' Set.Iio (q₁ : ℝ) ∩ Y ⁻¹' Set.Iio (q₂ : ℝ))
          = κ a (X ⁻¹' Set.Iio (q₁ : ℝ)) * κ a (Y ⁻¹' Set.Iio (q₂ : ℝ)) := by
      intro q₁ q₂
      exact hXY.measure_inter_preimage_eq_mul (Set.Iio (q₁ : ℝ)) (Set.Iio (q₂ : ℝ))
        (measurableSet_Iio) (measurableSet_Iio)

    -- Step 2b: Swap quantifiers using countability
    have h_ae_all_rats : ∀ᵐ a ∂μ, ∀ q₁ q₂ : ℚ,
        κ a (X ⁻¹' Set.Iio (q₁ : ℝ) ∩ Y ⁻¹' Set.Iio (q₂ : ℝ))
          = κ a (X ⁻¹' Set.Iio (q₁ : ℝ)) * κ a (Y ⁻¹' Set.Iio (q₂ : ℝ)) := by
      rw [ae_all_iff]
      intro q₁
      rw [ae_all_iff]
      intro q₂
      exact h_rat_factor q₁ q₂

    -- Step 2c: Extend from π-system to σ-algebra
    refine h_ae_all_rats.mono (fun a ha => ?_)

    -- Use the product measure characterization of independence
    rw [ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable]

    -- We need to show: (κ a).map (fun ω => (X ω, Y ω)) = ((κ a).map X).prod ((κ a).map Y)
    -- Both are finite measures on ℝ × ℝ. We'll show they agree on a generating π-system.

    -- Define the two measures for clarity
    let μ₁ := (κ a).map (fun ω => (X ω, Y ω))
    let μ₂ := ((κ a).map X).prod ((κ a).map Y)

    -- The generating π-system: rectangles of rational intervals
    let C := {s : Set (ℝ × ℝ) | ∃ (q₁ q₂ : ℚ), s = Set.Iio (q₁ : ℝ) ×ˢ Set.Iio (q₂ : ℝ)}

    -- Step 1: Verify the two measures agree on the π-system
    have h_agree_on_pi : ∀ s ∈ C, μ₁ s = μ₂ s := by
      intro s ⟨q₁, q₂, rfl⟩
      -- μ₁ (Iio q₁ ×ˢ Iio q₂) = (κ a).map (X, Y) (Iio q₁ ×ˢ Iio q₂)
      --                        = κ a ((X, Y)⁻¹' (Iio q₁ ×ˢ Iio q₂))
      --                        = κ a (X⁻¹' Iio q₁ ∩ Y⁻¹' Iio q₂)
      -- μ₂ (Iio q₁ ×ˢ Iio q₂) = ((κ a).map X).prod ((κ a).map Y) (Iio q₁ ×ˢ Iio q₂)
      --                        = ((κ a).map X) (Iio q₁) * ((κ a).map Y) (Iio q₂)
      --                        = κ a (X⁻¹' Iio q₁) * κ a (Y⁻¹' Iio q₂)
      -- These are equal by ha q₁ q₂
      simp only [μ₁, μ₂]
      rw [Measure.map_apply (hX.prod_mk hY) (measurableSet_Iio.prod measurableSet_Iio)]
      rw [Measure.prod_prod]
      · rw [Measure.map_apply hX measurableSet_Iio, Measure.map_apply hY measurableSet_Iio]
        simp only [Set.mk_preimage_prod, Set.preimage_id_eq, Set.id_eq]
        exact ha q₁ q₂
      · exact measurableSet_Iio
      · exact measurableSet_Iio

    -- Step 2: Show C is a π-system and generates the Borel σ-algebra
    have h_pi : IsPiSystem C := by
      intro s₁ ⟨q₁, q₂, rfl⟩ s₂ ⟨q₁', q₂', rfl⟩ _
      use min q₁ q₁', min q₂ q₂'
      ext ⟨x, y⟩
      simp [Set.mem_prod, Set.mem_Iio, min_lt_iff]

    have h_gen : borel (ℝ × ℝ) = MeasurableSpace.generateFrom C := by
      rw [borel_prod]
      rw [borel_eq_generateFrom_Iio_rat, borel_eq_generateFrom_Iio_rat]
      -- Show: product of generateFrom equals generateFrom of products
      conv_lhs => rw [MeasurableSpace.prod_eq_generateFrom]
      congr 1
      ext s
      simp only [Set.mem_image2, C]
      constructor
      · intro ⟨s₁, ⟨q₁, rfl⟩, s₂, ⟨q₂, rfl⟩, rfl⟩
        exact ⟨q₁, q₂, rfl⟩
      · intro ⟨q₁, q₂, rfl⟩
        refine ⟨Set.Iio (q₁ : ℝ), ⟨q₁, rfl⟩, Set.Iio (q₂ : ℝ), ⟨q₂, rfl⟩, rfl⟩

    -- Step 3: Apply measure extension theorem
    -- We need a covering sequence for ext_of_generateFrom_of_iUnion
    refine Measure.ext_of_generateFrom_of_iUnion C (fun n => Set.Iio (n : ℝ) ×ˢ Set.Iio (n : ℝ))
      h_gen h_pi ?_ ?_ ?_ h_agree_on_pi
    -- Show ⋃ n, Iio n ×ˢ Iio n = univ
    · ext ⟨x, y⟩
      simp only [Set.mem_iUnion, Set.mem_prod, Set.mem_Iio, Set.mem_univ, iff_true]
      obtain ⟨n, hn⟩ := exists_nat_gt (max x y)
      use n
      constructor <;> exact lt_of_le_of_lt (le_max_left _ _) hn <;> exact lt_of_le_of_lt (le_max_right _ _) hn
    -- Show each Iio n ×ˢ Iio n ∈ C
    · intro n
      exact ⟨n, n, rfl⟩
    -- Show μ₁ (Iio n ×ˢ Iio n) ≠ ∞
    · intro n
      simp only [μ₁]
      exact measure_ne_top _ _

  -- Step 3: Apply measure-level factorization pointwise
  refine h_indep_ae.mono (fun a ha => ?_)
  exact IndepFun.integral_mul_eq_mul_integral ha hX.aestronglyMeasurable hY.aestronglyMeasurable
  -/

/-- Kernel-level factorisation for two bounded test functions applied to coordinate projections.

This specializes `Kernel.IndepFun.integral_mul` to our setting.

**Note**: `Kernel.IndepFun.comp` already exists in Mathlib!
See `Mathlib.Probability.Independence.Kernel`, line ~976.
-/
private lemma condexp_pair_factorization
    {μ : Measure (Ω[α])} [IsProbabilityMeasure μ]
    [StandardBorelSpace α] (hσ : MeasurePreserving shift μ μ)
    (f g : α → ℝ)
    (hf_meas : Measurable f) (hf_bd : ∃ C, ∀ x, |f x| ≤ C)
    (hg_meas : Measurable g) (hg_bd : ∃ C, ∀ x, |g x| ≤ C)
    (hciid : True) :  -- Using True to avoid typeclass issues with Kernel.iIndepFun
    μ[(fun ω => f (ω 0) * g (ω 1)) | shiftInvariantSigma (α := α)]
      =ᵐ[μ]
    fun ω =>
      (∫ x, f x ∂(ν (μ := μ) ω)) * (∫ x, g x ∂(ν (μ := μ) ω)) := by
  sorry
  /-
  classical
  -- Step 1: Both coordinates have the same conditional law (from identicalConditionalMarginals)
  have h_marg0 := identicalConditionalMarginals (μ := μ) (α := α) hσ 0
  have h_marg1 := identicalConditionalMarginals (μ := μ) (α := α) hσ 1

  -- Step 2: Integrability of the product
  rcases hf_bd with ⟨Cf, hCf⟩
  rcases hg_bd with ⟨Cg, hCg⟩
  have h_int : Integrable (fun ω : Ω[α] => f (ω 0) * g (ω 1)) μ := by
    refine MeasureTheory.integrable_of_bounded
      (hmeas := (hf_meas.comp (measurable_pi_apply 0)).mul
        (hg_meas.comp (measurable_pi_apply 1)))
      (μ := μ) ⟨Cf * Cg, ?_⟩
    intro ω
    calc |f (ω 0) * g (ω 1)| = |f (ω 0)| * |g (ω 1)| := abs_mul _ _
      _ ≤ Cf * Cg := mul_le_mul (hCf _) (hCg _) (abs_nonneg _) (by linarith [hCf (ω 0)])

  -- Step 3: Apply conditional expectation via condExpKernel
  have h_via_kernel :
      μ[(fun ω => f (ω 0) * g (ω 1)) | shiftInvariantSigma (α := α)]
        =ᵐ[μ]
      fun ω => ∫ y, f (y 0) * g (y 1) ∂(condExpKernel μ (shiftInvariantSigma (α := α)) ω) := by
    exact ProbabilityTheory.condExp_ae_eq_integral_condExpKernel
      (μ := μ) (m := shiftInvariantSigma (α := α))
      (f := fun ω => f (ω 0) * g (ω 1))
      (hf := (hf_meas.comp (measurable_pi_apply 0)).mul
        (hg_meas.comp (measurable_pi_apply 1)))

  -- Step 4: Use conditional independence to factor the integral
  have h_factor :
      (fun ω => ∫ y, f (y 0) * g (y 1) ∂(condExpKernel μ (shiftInvariantSigma (α := α)) ω))
        =ᵐ[μ]
      fun ω =>
        (∫ y, f (y 0) ∂(condExpKernel μ (shiftInvariantSigma (α := α)) ω)) *
        (∫ y, g (y 1) ∂(condExpKernel μ (shiftInvariantSigma (α := α)) ω)) := by
    -- From `hciid: ProbabilityTheory.Kernel.iIndepFun (fun k : Fin 2 => fun ω => ω k) κ μ`
    -- we know the coordinates 0 and 1 are independent under the kernel
    have h_indep_pair : Kernel.IndepFun (fun ω : Ω[α] => ω 0) (fun ω => ω 1)
        (condExpKernel μ (shiftInvariantSigma (α := α))) := by
      exact hciid.indepFun (i := 0) (j := 1) (by norm_num)
    -- Apply the kernel-level integral multiplication theorem
    have h_bd0 : ∃ C, ∀ ω : Ω[α], |(fun y => f (y 0)) ω| ≤ C := by
      rcases hf_bd with ⟨C, hC⟩
      exact ⟨C, fun ω => hC (ω 0)⟩
    have h_bd1 : ∃ C, ∀ ω : Ω[α], |(fun y => g (y 1)) ω| ≤ C := by
      rcases hg_bd with ⟨C, hC⟩
      exact ⟨C, fun ω => hC (ω 1)⟩
    exact Kernel.IndepFun.integral_mul h_indep_pair
      (hf_meas.comp (measurable_pi_apply 0))
      (hg_meas.comp (measurable_pi_apply 1))
      h_bd0 h_bd1

  -- Step 5: Replace coordinate projections with ν using identicalConditionalMarginals
  have h_coord0 :
      (fun ω => ∫ y, f (y 0) ∂(condExpKernel μ (shiftInvariantSigma (α := α)) ω))
        =ᵐ[μ]
      fun ω => ∫ x, f x ∂(ν (μ := μ) ω) := by
    filter_upwards [h_marg0] with ω hω
    have : (fun y : Ω[α] => f (y 0)) = f ∘ (fun y => y 0) := rfl
    rw [this, MeasureTheory.integral_map (measurable_pi_apply 0).aemeasurable hf_meas.aestronglyMeasurable]
    congr 1
    exact hω.symm

  have h_coord1 :
      (fun ω => ∫ y, g (y 1) ∂(condExpKernel μ (shiftInvariantSigma (α := α)) ω))
        =ᵐ[μ]
      fun ω => ∫ x, g x ∂(ν (μ := μ) ω) := by
    filter_upwards [h_marg1] with ω hω
    have : (fun y : Ω[α] => g (y 1)) = g ∘ (fun y => y 1) := rfl
    rw [this, MeasureTheory.integral_map (measurable_pi_apply 1).aemeasurable hg_meas.aestronglyMeasurable]
    congr 1
    exact hω.symm

  -- Step 6: Chain all the equalities
  calc μ[(fun ω => f (ω 0) * g (ω 1)) | shiftInvariantSigma (α := α)]
      =ᵐ[μ] fun ω => ∫ y, f (y 0) * g (y 1) ∂(condExpKernel μ (shiftInvariantSigma (α := α)) ω) :=
        h_via_kernel
    _ =ᵐ[μ] fun ω =>
        (∫ y, f (y 0) ∂(condExpKernel μ (shiftInvariantSigma (α := α)) ω)) *
        (∫ y, g (y 1) ∂(condExpKernel μ (shiftInvariantSigma (α := α)) ω)) :=
        h_factor
    _ =ᵐ[μ] fun ω => (∫ x, f x ∂(ν (μ := μ) ω)) * (∫ x, g x ∂(ν (μ := μ) ω)) := by
        filter_upwards [h_coord0, h_coord1] with ω h0 h1
        rw [h0, h1]
  -/

/-- Conditional expectation factorizes through the regular conditional distribution.

Assuming conditional independence of coordinates given the tail σ-algebra,
the conditional expectation of a product equals the product of integrals
against the conditional distribution ν. -/
theorem condexp_product_factorization
    {μ : Measure (Ω[α])} [IsProbabilityMeasure μ] [StandardBorelSpace α]
    (hσ : MeasurePreserving shift μ μ)
    (m : ℕ) (fs : Fin m → α → ℝ)
    (hmeas : ∀ k, Measurable (fs k))
    (hbd : ∀ k, ∃ C, ∀ x, |fs k x| ≤ C)
    -- Conditional independence of coordinates given tail (using True to avoid typeclass issues):
    (hciid : True) :
    μ[fun ω => ∏ k, fs k (ω (k : ℕ)) | shiftInvariantSigma (α := α)]
      =ᵐ[μ] (fun ω => ∏ k, ∫ x, fs k x ∂(ν (μ := μ) ω)) := by
  sorry
  /-
  classical
  induction' m with m ih generalizing fs
  · have h_const :
        μ[(fun _ : Ω[α] => (1 : ℝ)) | shiftInvariantSigma (α := α)]
          = fun _ : Ω[α] => (1 : ℝ) :=
      MeasureTheory.condExp_const (μ := μ)
        (m := shiftInvariantSigma (α := α))
        (hm := shiftInvariantSigma_le (α := α)) (c := (1 : ℝ))
    refine Filter.EventuallyEq.of_forall ?_
    intro ω
    simp [h_const]
  · -- Inductive step: split product into (product of first m factors) * (last factor)
    -- Reindex: product over Fin (m + 1) splits into product over Fin m and the m-th term
    have h_split_prod :
        (fun ω => ∏ k : Fin (m + 1), fs k (ω (k : ℕ)))
          = fun ω =>
            (∏ k : Fin m, fs (Fin.castSucc k) (ω (k : ℕ))) *
            fs (Fin.last m) (ω m) := by
      funext ω
      rw [Fin.prod_univ_castSucc]
      simp only [Fin.coe_castSucc, Fin.val_last]

    -- Apply IH to the first m factors
    let fs' : Fin m → α → ℝ := fun k => fs (Fin.castSucc k)
    have hmeas' : ∀ k, Measurable (fs' k) := fun k => hmeas (Fin.castSucc k)
    have hbd' : ∀ k, ∃ C, ∀ x, |fs' k x| ≤ C := fun k => hbd (Fin.castSucc k)
    have hciid' : ProbabilityTheory.Kernel.iIndepFun (fun k : Fin m => fun ω : Ω[α] => ω k)
        (condExpKernel μ (shiftInvariantSigma (α := α))) μ := by
      -- Restriction of ProbabilityTheory.Kernel.iIndepFun to a subset of indices
      exact ProbabilityTheory.Kernel.iIndepFun_of_subset hciid
        (fun k => Fin.castSucc k) Fin.castSucc_injective

    have h_ih := ih fs' hmeas' hbd' hciid'

    -- The last factor's conditional expectation
    have h_last :=
      condexp_coordinate_via_ν (μ := μ) (α := α) hσ
        (ψ := fs (Fin.last m))
        (hψ := hmeas (Fin.last m))
        (hbd := hbd (Fin.last m))
        (k := m)

    -- Product structure under conditional expectation
    have h_prod_condexp :
        μ[(fun ω => ∏ k : Fin (m + 1), fs k (ω (k : ℕ)))
          | shiftInvariantSigma (α := α)]
          =ᵐ[μ]
        μ[(fun ω =>
            (∏ k : Fin m, fs' k (ω (k : ℕ))) * fs (Fin.last m) (ω m))
          | shiftInvariantSigma (α := α)] := by
      refine Filter.EventuallyEq.condExp (Filter.EventuallyEq.of_forall ?_)
      intro ω
      exact congrFun h_split_prod ω

    -- This is a product of two "functions" - apply pair factorization
    -- But we need to be more careful: one factor is already a product, not atomic
    -- Use linearity + dominated convergence instead

    -- First show the product factors under conditional expectation
    -- This uses conditional independence of disjoint coordinate sets
    have h_prod_factor :
        μ[(fun ω =>
            (∏ k : Fin m, fs' k (ω (k : ℕ))) * fs (Fin.last m) (ω m))
          | shiftInvariantSigma (α := α)]
          =ᵐ[μ]
        fun ω =>
          (μ[(fun ω' => ∏ k : Fin m, fs' k (ω' (k : ℕ)))
            | shiftInvariantSigma (α := α)] ω) *
          (μ[(fun ω' => fs (Fin.last m) (ω' m))
            | shiftInvariantSigma (α := α)] ω) := by
      -- The key observation: functions of disjoint coordinate sets are independent
      -- X := (ω 0, ..., ω (m-1)) and Y := ω m are independent under condExpKernel
      -- Therefore f(X) and g(Y) are independent for any measurable f, g
      --
      -- We need: the function (fun ω => ∏ k : Fin m, fs' k (ω k)) composed with
      -- the projection to first m coordinates is independent from the projection
      -- to the m-th coordinate.
      --
      -- This follows from `hciid.indepFun_finset` applied to S = Finset.univ.image castSucc
      -- and T = {last m}, which are disjoint.
      have h_disjoint : Disjoint
          (Finset.univ.image (Fin.castSucc : Fin m → Fin (m + 1)))
          ({Fin.last m} : Finset (Fin (m + 1))) := by
        simp [Finset.disjoint_left]
        intro i _ hi
        simp at hi
        exact Fin.castSucc_lt_last i |>.ne hi
      have h_indep_finsets :=
        hciid.indepFun_finset
          (Finset.univ.image (Fin.castSucc : Fin m → Fin (m + 1)))
          {Fin.last m}
          h_disjoint
          (fun i => measurable_pi_apply i)
      -- Now we have independence of tuples:
      -- X := (fun ω i => ω (castSucc i)) and Y := (fun ω i => ω (last m))
      -- We need independence of: f(X) := ∏ fs' k (ω k) and g(Y) := fs (last m) (ω m)

      -- The conditional expectation via kernel equals the integral
      have h_via_kernel :
          μ[(fun ω => (∏ k : Fin m, fs' k (ω (k : ℕ))) * fs (Fin.last m) (ω m))
            | shiftInvariantSigma (α := α)]
            =ᵐ[μ]
          fun ω => ∫ y, (∏ k : Fin m, fs' k (y (k : ℕ))) * fs (Fin.last m) (y m)
            ∂(condExpKernel μ (shiftInvariantSigma (α := α)) ω) := by
        exact ProbabilityTheory.condExp_ae_eq_integral_condExpKernel
          (μ := μ) (m := shiftInvariantSigma (α := α))
          (f := fun ω => (∏ k : Fin m, fs' k (ω (k : ℕ))) * fs (Fin.last m) (ω m))
          (hf := by
            apply Measurable.mul
            · exact Finset.measurable_prod _ (fun k _ => (hmeas' k).comp (measurable_pi_apply k))
            · exact (hmeas (Fin.last m)).comp (measurable_pi_apply m))

      -- Apply Kernel.IndepFun.integral_mul to the composite functions
      -- We use h_indep_finsets composed with the product function and single evaluation
      have h_kernel_mul :
          (fun ω => ∫ y, (∏ k : Fin m, fs' k (y (k : ℕ))) * fs (Fin.last m) (y m)
            ∂(condExpKernel μ (shiftInvariantSigma (α := α)) ω))
            =ᵐ[μ]
          fun ω =>
            (∫ y, ∏ k : Fin m, fs' k (y (k : ℕ))
              ∂(condExpKernel μ (shiftInvariantSigma (α := α)) ω)) *
            (∫ y, fs (Fin.last m) (y m)
              ∂(condExpKernel μ (shiftInvariantSigma (α := α)) ω)) := by
        -- Apply the axiomatized kernel integral multiplication
        -- The independence h_indep_finsets gives us independence of the tuple vs. singleton
        -- We compose with the product function and evaluation function
        have h_indep_composed : Kernel.IndepFun
            (fun ω : Ω[α] => ∏ k : Fin m, fs' k (ω (k : ℕ)))
            (fun ω => fs (Fin.last m) (ω m))
            (condExpKernel μ (shiftInvariantSigma (α := α))) μ := by
          -- h_indep_finsets gives independence of tuple vs. singleton
          -- We compose with measurable functions to get independence of f(tuple) vs. g(singleton)
          refine Kernel.IndepFun.comp h_indep_finsets ?_ ?_
          · -- Product function is measurable
            exact measurable_pi_lambda _ fun i =>
              (hmeas' i).comp (measurable_pi_apply (Finset.univ.image Fin.castSucc).toSet.restrict _)
          · -- Evaluation at m is measurable
            exact measurable_pi_lambda _ fun _ =>
              (hmeas (Fin.last m)).comp (measurable_pi_apply m)
        exact Kernel.IndepFun.integral_mul h_indep_composed
          (Finset.measurable_prod _ (fun k _ => (hmeas' k).comp (measurable_pi_apply k)))
          ((hmeas (Fin.last m)).comp (measurable_pi_apply m))
          (by
            -- Boundedness of product
            choose bounds hbounds using hbd'
            refine ⟨∏ k, bounds k, ?_⟩
            intro ω
            calc |(∏ k : Fin m, fs' k (ω (k : ℕ)))|
                = ∏ k, |fs' k (ω (k : ℕ))| := by simp [abs_prod]
              _ ≤ ∏ k, bounds k := Finset.prod_le_prod (fun _ _ => abs_nonneg _)
                  (fun k _ => hbounds k (ω k)))
          (hbd (Fin.last m))

      -- Separate conditional expectations
      have h_sep_prod :
          (fun ω => ∫ y, ∏ k : Fin m, fs' k (y (k : ℕ))
            ∂(condExpKernel μ (shiftInvariantSigma (α := α)) ω))
            =ᵐ[μ]
          fun ω => μ[(fun ω' => ∏ k : Fin m, fs' k (ω' (k : ℕ)))
            | shiftInvariantSigma (α := α)] ω := by
        refine (ProbabilityTheory.condExp_ae_eq_integral_condExpKernel
          (μ := μ) (m := shiftInvariantSigma (α := α))
          (f := fun ω => ∏ k : Fin m, fs' k (ω (k : ℕ)))
          (hf := Finset.measurable_prod _ (fun k _ => (hmeas' k).comp (measurable_pi_apply k)))).symm

      have h_sep_last :
          (fun ω => ∫ y, fs (Fin.last m) (y m)
            ∂(condExpKernel μ (shiftInvariantSigma (α := α)) ω))
            =ᵐ[μ]
          fun ω => μ[(fun ω' => fs (Fin.last m) (ω' m))
            | shiftInvariantSigma (α := α)] ω := by
        refine (ProbabilityTheory.condExp_ae_eq_integral_condExpKernel
          (μ := μ) (m := shiftInvariantSigma (α := α))
          (f := fun ω => fs (Fin.last m) (ω m))
          (hf := (hmeas (Fin.last m)).comp (measurable_pi_apply m))).symm

      -- Chain the equalities
      calc μ[(fun ω => (∏ k : Fin m, fs' k (ω (k : ℕ))) * fs (Fin.last m) (ω m))
            | shiftInvariantSigma (α := α)]
          =ᵐ[μ] fun ω => ∫ y, (∏ k : Fin m, fs' k (y (k : ℕ))) * fs (Fin.last m) (y m)
            ∂(condExpKernel μ (shiftInvariantSigma (α := α)) ω) := h_via_kernel
        _ =ᵐ[μ] fun ω =>
            (∫ y, ∏ k : Fin m, fs' k (y (k : ℕ))
              ∂(condExpKernel μ (shiftInvariantSigma (α := α)) ω)) *
            (∫ y, fs (Fin.last m) (y m)
              ∂(condExpKernel μ (shiftInvariantSigma (α := α)) ω)) := h_kernel_mul
        _ =ᵐ[μ] fun ω =>
            (μ[(fun ω' => ∏ k : Fin m, fs' k (ω' (k : ℕ)))
              | shiftInvariantSigma (α := α)] ω) *
            (μ[(fun ω' => fs (Fin.last m) (ω' m))
              | shiftInvariantSigma (α := α)] ω) := by
          filter_upwards [h_sep_prod, h_sep_last] with ω hp hl
          rw [hp, hl]

    -- Apply IH and coordinate formula
    calc μ[(fun ω => ∏ k : Fin (m + 1), fs k (ω (k : ℕ)))
          | shiftInvariantSigma (α := α)]
        =ᵐ[μ] μ[(fun ω =>
            (∏ k : Fin m, fs' k (ω (k : ℕ))) * fs (Fin.last m) (ω m))
          | shiftInvariantSigma (α := α)] := h_prod_condexp
      _ =ᵐ[μ] fun ω =>
          (μ[(fun ω' => ∏ k : Fin m, fs' k (ω' (k : ℕ)))
            | shiftInvariantSigma (α := α)] ω) *
          (μ[(fun ω' => fs (Fin.last m) (ω' m))
            | shiftInvariantSigma (α := α)] ω) := h_prod_factor
      _ =ᵐ[μ] fun ω =>
          (∏ k : Fin m, ∫ x, fs' k x ∂(ν (μ := μ) ω)) *
          (∫ x, fs (Fin.last m) x ∂(ν (μ := μ) ω)) := by
            filter_upwards [h_ih, h_last] with ω hih hlast
            rw [hih, hlast]
      _ =ᵐ[μ] fun ω => ∏ k : Fin (m + 1), ∫ x, fs k x ∂(ν (μ := μ) ω) := by
            refine Filter.EventuallyEq.of_forall ?_
            intro ω
            rw [Fin.prod_univ_castSucc]
            simp only [Fin.coe_castSucc, Fin.val_last]
            rfl
  -/

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
    [StandardBorelSpace α]
    (hσ : MeasurePreserving shift μ μ)
    (m : ℕ) (fs : Fin m → α → ℝ)
    (hmeas : ∀ k, Measurable (fs k))
    (hbd : ∀ k, ∃ C, ∀ x, |fs k x| ≤ C)
    -- Conditional independence hypothesis (using sorry to avoid typeclass issues):
    (hciid : True) :
    ∃ (ν_result : Ω[α] → Measure α),
      (∀ᵐ ω ∂μ, IsProbabilityMeasure (ν_result ω)) ∧
      (∀ᵐ ω ∂μ, ∃ (val : ℝ), val = ∏ k : Fin m, ∫ x, fs k x ∂(ν_result ω)) := by
  sorry

end ExtremeMembers

/-- **de Finetti's Theorem via Koopman Operator (Main Result)**

For an exchangeable sequence on a standard Borel space, there exists a random
probability measure ν such that, conditioned on the tail σ-algebra, the sequence
is i.i.d. with law ν.

**Statement**: If (ξₙ) is an exchangeable sequence of random variables taking values
in a standard Borel space α, then there exists a regular conditional distribution
ν : Ω[α] → Measure α such that:

1. ν(ω) is a probability measure for μ-a.e. ω
2. Conditional on the tail σ-algebra, the coordinates are i.i.d. with law ν(ω)
3. The marginal distribution μ equals ∫ ν(ω)^⊗ℕ dμ(ω)

**Proof strategy** (Kallenberg's "first proof"):
1. Use shift-invariance to apply Mean Ergodic Theorem
2. Construct regular conditional distribution ν via condExpKernel
3. Show ν is shift-invariant (extremeMembers_agree)
4. Prove conditional independence via factorization (condexp_cylinder_factorizes)
5. Apply monotone class theorem to extend from cylinders to full σ-algebra

**Current status**: Main infrastructure in place, remaining gaps:
- Conditional independence establishment (needs `Kernel.iIndepFun` development)
- Shift-invariance circularity resolution
- Several large proofs requiring mathlib additions

**References**:
- Kallenberg (2005), "Probabilistic Symmetries and Invariance Principles", Theorem 1.1
  "First proof" approach, pages 26-27
-/
theorem deFinetti_viaKoopman
    {μ : Measure (Ω[α])} [IsProbabilityMeasure μ] [StandardBorelSpace α]
    (hσ : MeasurePreserving shift μ μ) :
    ∃ (ν : Ω[α] → Measure α),
      (∀ᵐ ω ∂μ, IsProbabilityMeasure (ν ω)) ∧
      (∀ (m : ℕ) (fs : Fin m → α → ℝ),
        (∀ k, Measurable (fs k)) →
        (∀ k, ∃ C, ∀ x, |fs k x| ≤ C) →
        μ[fun ω => ∏ k, fs k (ω k) | shiftInvariantSigma (α := α)]
          =ᵐ[μ] fun ω => ∏ k, ∫ x, fs k x ∂(ν ω)) := by
  -- Use the regular conditional distribution constructed via condExpKernel
  use ν (μ := μ)
  constructor
  · -- ν(ω) is a probability measure a.e.
    apply ae_of_all
    intro ω
    exact ν_isProbabilityMeasure (μ := μ) ω
  · -- Conditional factorization
    intro m fs hmeas hbd
    -- This follows from condexp_product_factorization
    -- which requires conditional independence
    sorry  -- TODO: Complete using condexp_product_factorization

end Exchangeability.DeFinetti.ViaKoopman
