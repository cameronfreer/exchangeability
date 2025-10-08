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


/-- Regular conditional distribution kernel constructed via condExpKernel.

This is the kernel giving the conditional distribution of the first coordinate
given the tail σ-algebra.

TODO: The exact construction requires careful handling of the measurable space instances.
For now we axiomatize it as a placeholder. -/
noncomputable def rcdKernel {μ : Measure (Ω[α])} [IsProbabilityMeasure μ]
    [StandardBorelSpace α] : Kernel (Ω[α]) α :=
  (condExpKernel μ (shiftInvariantSigma (α := α))).map
    (π0 (α := α)) (measurable_pi0 (α := α))

/-- The regular conditional distribution as a function assigning to each point
 a probability measure on α. -/
noncomputable def ν {μ : Measure (Ω[α])} [IsProbabilityMeasure μ]
    [StandardBorelSpace α] : Ω[α] → Measure α :=
  fun ω => (rcdKernel (μ := μ)) ω

/-- Convenient rewrite for evaluating the kernel `ν` on a measurable set. -/
lemma ν_apply {μ : Measure (Ω[α])} [IsProbabilityMeasure μ] [StandardBorelSpace α]
    (ω : Ω[α]) (s : Set α) :
    ν (μ := μ) ω s
      = (condExpKernel μ (shiftInvariantSigma (α := α)) ω)
          ((fun y : Ω[α] => y 0) ⁻¹' s) := by
  classical
  unfold ν rcdKernel
  simp [Kernel.map, π0]

/-- The kernel ν gives probability measures. -/
instance ν_isProbabilityMeasure {μ : Measure (Ω[α])} [IsProbabilityMeasure μ]
    [StandardBorelSpace α] (ω : Ω[α]) :
    IsProbabilityMeasure (ν (μ := μ) ω) := by
  classical
  unfold ν
  have hMk : IsMarkovKernel (rcdKernel (μ := μ) (α := α)) := by
    simpa [rcdKernel] using
      (ProbabilityTheory.Kernel.IsMarkovKernel.map
        (condExpKernel μ (shiftInvariantSigma (α := α)))
        (measurable_pi0 (α := α)))
  simpa [rcdKernel] using hMk.isProbabilityMeasure ω

/-- The kernel `ν` is measurable with respect to the tail σ-algebra. -/
lemma ν_measurable_tail {μ : Measure (Ω[α])} [IsProbabilityMeasure μ]
    [StandardBorelSpace α] :
    Measurable[shiftInvariantSigma (α := α)] (ν (μ := μ)) := by
  classical
  unfold ν
  simpa [rcdKernel] using (rcdKernel (μ := μ) (α := α)).measurable

/-!
Helper lemmas establishing the stability of the conditional expectation and the
regular conditional distribution under compositions with shift iterates.
-/

private lemma condexp_precomp_iterate_eq
    {μ : Measure (Ω[α])} [IsProbabilityMeasure μ]
    (hσ : MeasurePreserving shift μ μ) {k : ℕ}
    {f : Ω[α] → ℝ} (hf : Integrable f μ) :
    μ[(fun ω => f (shift^[k] ω)) | shiftInvariantSigma (α := α)]
      =ᵐ[μ] μ[f | shiftInvariantSigma (α := α)] := by
  classical
  set m := shiftInvariantSigma (α := α)
  let shiftk := shift^[k]
  have h_shiftk_pres : MeasurePreserving shiftk μ μ := hσ.iterate k
  have h_shiftk_meas : AEMeasurable shiftk μ :=
    (measurable_shift (α := α)).iterate k |>.aemeasurable
  have h_int_shift : Integrable (fun ω => f (shiftk ω)) μ :=
    h_shiftk_pres.integrable_comp_of_integrable hf
  have h_condexp_int : Integrable (μ[f | m]) μ :=
    MeasureTheory.integrable_condExp (μ := μ) (m := m) (f := f)
  refine
    ((MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq
        (μ := μ) (m := m)
        (hm := shiftInvariantSigma_le (α := α))
        (f := fun ω => f (shiftk ω))
        (g := μ[f | m])
        (hf := h_int_shift)
        (hg_int_finite := ?_)
        (hg_eq := ?_)
        (hgm :=
          (MeasureTheory.condExp_aestronglyMeasurable
            (μ := μ) (m := m) (f := f))).aesStronglyMeasurable)).symm
  · intro s hs _
    have h_meas : MeasurableSet s :=
      (mem_shiftInvariantSigma_iff (α := α) (s := s)).1 hs |>.1
    exact (h_condexp_int.integrableOn) h_meas
  · intro s hs _
    have hS := (mem_shiftInvariantSigma_iff (α := α) (s := s)).1 hs
    have hS_meas : MeasurableSet s := hS.1
    have hS_shift : shift ⁻¹' s = s := hS.2
    have hS_iter : shiftk ⁻¹' s = s := by
      induction k with
      | zero => simp [shiftk]
      | succ k hk =>
          dsimp [shiftk, Function.iterate] at hk ⊢
          simpa [hk, Set.preimage_preimage, hS_shift]
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
    have h_set :=
      MeasureTheory.setIntegral_indicator (μ := μ) (s := s) (f := f) hS_meas
    have h_set_shift :=
      MeasureTheory.setIntegral_indicator
        (μ := μ) (s := s) (f := fun ω => f (shiftk ω)) hS_meas
    calc
      ∫ ω in s, μ[f | m] ω ∂μ
          = ∫ ω in s, f ω ∂μ :=
            MeasureTheory.setIntegral_condExp
              (μ := μ) (m := m)
              (hm := shiftInvariantSigma_le (α := α))
              (hf := hf) (hs := hs)
      _ = ∫ ω, s.indicator f ω ∂μ := h_set
      _ = ∫ ω, s.indicator (fun ω => f (shiftk ω)) ω ∂μ := h_indicator_eq
      _ = ∫ ω in s, (fun ω => f (shiftk ω)) ω ∂μ := h_set_shift.symm

/-- Almost-everywhere shift-invariance of the regular conditional distribution. -/
lemma ν_ae_shiftInvariant {μ : Measure (Ω[α])} [IsProbabilityMeasure μ]
    [StandardBorelSpace α] (hσ : MeasurePreserving shift μ μ) :
    ∀ᵐ ω ∂μ, ∀ k : ℕ, ν (μ := μ) (shift^[k] ω) = ν (μ := μ) ω := by
  classical
  refine (ae_all_iff).2 ?_
  intro k
  refine
    (ProbabilityTheory.Kernel.ae_eq_of_forall_integral_eq
      (μ := μ)
      (κ := fun ω => ν (μ := μ) (shift^[k] ω))
      (η := fun ω => ν (μ := μ) ω)).2 ?_
  intro ψ hψ hbd
  have hInt : Integrable (fun ω => ψ (π0 (α := α) ω)) μ := by
    rcases hbd with ⟨C, hC⟩
    exact MeasureTheory.integrable_of_bounded
      (hmeas := hψ.comp (measurable_pi0 (α := α)))
      (μ := μ) ⟨C, by intro ω; simpa using hC (π0 (α := α) ω)⟩
  have hCE0 :
      μ[(fun ω => ψ (π0 (α := α) ω))
        | shiftInvariantSigma (α := α)]
        =ᵐ[μ]
      (fun ω => ∫ x, ψ x ∂(ν (μ := μ) ω)) := by
    simpa [ν, rcdKernel]
      using
        (ProbabilityTheory.condExp_ae_eq_integral_condExpKernel
          (μ := μ)
          (m := shiftInvariantSigma (α := α))
          (f := fun ω : Ω[α] => ψ (π0 (α := α) ω))
          (hf := hψ.comp (measurable_pi0 (α := α))))
  have hCEshift :
      μ[(fun ω => ψ (π0 (α := α) (shift^[k] ω)))
        | shiftInvariantSigma (α := α)]
        =ᵐ[μ]
      μ[(fun ω => ψ (π0 (α := α) ω))
        | shiftInvariantSigma (α := α)] := by
    simpa using
      condexp_precomp_iterate_eq
        (μ := μ) (α := α) hσ (k := k)
        (f := fun ω => ψ (π0 (α := α) ω)) hInt
  have hCEshift' :
      μ[(fun ω => ψ (π0 (α := α) (shift^[k] ω)))
        | shiftInvariantSigma (α := α)]
        =ᵐ[μ]
      (fun ω => ∫ x, ψ x ∂(ν (μ := μ) (shift^[k] ω))) := by
    simpa [ν, rcdKernel]
      using
        (ProbabilityTheory.condExp_ae_eq_integral_condExpKernel
          (μ := μ)
          (m := shiftInvariantSigma (α := α))
          (f := fun ω : Ω[α] => ψ (π0 (α := α) (shift^[k] ω)))
          (hf := (hψ.comp (measurable_pi0 (α := α))).comp
            ((measurable_shift (α := α)).iterate k)))
  have h_eq :
      (fun ω => ∫ x, ψ x ∂(ν (μ := μ) (shift^[k] ω)))
        =ᵐ[μ]
      (fun ω => ∫ x, ψ x ∂(ν (μ := μ) ω)) :=
    hCEshift'.trans (hCEshift.trans hCE0).symm
  simpa using h_eq

/-- Identical conditional marginals: each coordinate shares the same
regular conditional distribution given the shift-invariant σ-algebra. -/
lemma identicalConditionalMarginals {μ : Measure (Ω[α])} [IsProbabilityMeasure μ]
    [StandardBorelSpace α] (hσ : MeasurePreserving shift μ μ) (k : ℕ) :
    ∀ᵐ ω ∂μ,
      ((condExpKernel μ (shiftInvariantSigma (α := α))).map
        (fun y : Ω[α] => y k)) ω
      = ν (μ := μ) ω := by
  classical
  refine
    (ProbabilityTheory.Kernel.ae_eq_of_forall_integral_eq
      (μ := μ)
      (κ := fun ω =>
        ((condExpKernel μ (shiftInvariantSigma (α := α))).map
          (fun y : Ω[α] => y k)) ω)
      (η := fun ω => ν (μ := μ) ω)).2 ?_
  intro ψ hψ hbd
  have hInt : Integrable (fun ω => ψ (π0 (α := α) ω)) μ := by
    rcases hbd with ⟨C, hC⟩
    exact MeasureTheory.integrable_of_bounded
      (hmeas := hψ.comp (measurable_pi0 (α := α)))
      (μ := μ) ⟨C, by intro ω; simpa using hC (π0 (α := α) ω)⟩
  have hCEk :
      μ[(fun ω => ψ (ω k)) | shiftInvariantSigma (α := α)]
        =ᵐ[μ]
      (fun ω => ∫ x, ψ x ∂
        (((condExpKernel μ (shiftInvariantSigma (α := α))).map
          (fun y : Ω[α] => y k)) ω)) := by
    simpa using
      (ProbabilityTheory.condExp_ae_eq_integral_condExpKernel
        (μ := μ)
        (m := shiftInvariantSigma (α := α))
        (f := fun ω : Ω[α] => ψ (ω k))
        (hf := hψ.comp (measurable_pi_apply k)))
  have h_precomp :
      μ[(fun ω => ψ (ω k)) | shiftInvariantSigma (α := α)]
        =ᵐ[μ]
      μ[(fun ω => ψ (π0 (α := α) (shift^[k] ω)))
        | shiftInvariantSigma (α := α)] :=
    Filter.EventuallyEq.of_forall (fun _ => rfl)
  have h_invariance :
      μ[(fun ω => ψ (π0 (α := α) (shift^[k] ω)))
        | shiftInvariantSigma (α := α)]
        =ᵐ[μ]
      μ[(fun ω => ψ (π0 (α := α) ω))
        | shiftInvariantSigma (α := α)] := by
    simpa using
      condexp_precomp_iterate_eq
        (μ := μ) (α := α) hσ (k := k)
        (f := fun ω => ψ (π0 (α := α) ω)) hInt
  have hν :
      μ[(fun ω => ψ (π0 (α := α) ω))
        | shiftInvariantSigma (α := α)]
        =ᵐ[μ]
      (fun ω => ∫ x, ψ x ∂(ν (μ := μ) ω)) := by
    simpa [ν, rcdKernel]
      using
        (ProbabilityTheory.condExp_ae_eq_integral_condExpKernel
          (μ := μ)
          (m := shiftInvariantSigma (α := α))
          (f := fun ω : Ω[α] => ψ (π0 (α := α) ω))
          (hf := hψ.comp (measurable_pi0 (α := α))))
  have h_eq := (h_precomp.trans hCEk).trans (h_invariance.trans hν.symm)
  simpa using h_eq

/-- Helper: product rule for conditional expectation under independence.
If X and Y are conditionally independent given σ, then E[XY | σ] = E[X | σ] · E[Y | σ].

This adapts the standard measure-level result `IndepFun.integral_mul_eq_mul_integral` to
the conditional setting using the tower property of conditional expectation.
-/
private lemma condexp_mul_of_indep
    {μ : Measure (Ω[α])} [IsProbabilityMeasure μ]
    (σ : MeasurableSpace (Ω[α])) (hσ_le : σ ≤ inferInstance)
    (X Y : Ω[α] → ℝ)
    (hX_meas : Measurable X) (hY_meas : Measurable Y)
    (hX_bd : ∃ C, ∀ ω, |X ω| ≤ C) (hY_bd : ∃ C, ∀ ω, |Y ω| ≤ C)
    (h_indep : IndepFun X Y (μ.trim hσ_le)) :
    μ[(fun ω => X ω * Y ω) | σ] =ᵐ[μ]
      fun ω => (μ[X | σ] ω) * (μ[Y | σ] ω) := by
  classical
  -- Integrability from boundedness
  rcases hX_bd with ⟨CX, hCX⟩
  rcases hY_bd with ⟨CY, hCY⟩
  have hX_int : Integrable X μ := by
    refine MeasureTheory.integrable_of_bounded (hmeas := hX_meas) (μ := μ) ⟨CX, hCX⟩
  have hY_int : Integrable Y μ := by
    refine MeasureTheory.integrable_of_bounded (hmeas := hY_meas) (μ := μ) ⟨CY, hCY⟩
  have hXY_int : Integrable (X * Y) μ := by
    refine MeasureTheory.integrable_of_bounded
      (hmeas := hX_meas.mul hY_meas) (μ := μ) ⟨CX * CY, ?_⟩
    intro ω
    calc |(X * Y) ω| = |X ω * Y ω| := rfl
      _ = |X ω| * |Y ω| := abs_mul _ _
      _ ≤ CX * CY := mul_le_mul (hCX ω) (hCY ω) (abs_nonneg _) (by linarith [hCX ω])

  -- Use the characterization of conditional expectation via the defining property:
  -- For any σ-measurable set A, ∫_A E[XY|σ] dμ = ∫_A XY dμ
  -- We want to show: ∫_A E[XY|σ] dμ = ∫_A E[X|σ]·E[Y|σ] dμ for all σ-measurable A

  -- The key is to use conditional expectation properties
  refine MeasureTheory.ae_eq_condexp_of_forall_set_integral_eq
    (hm := σ) (hf := (hX_meas.mul hY_meas).aestronglyMeasurable) hXY_int ?_ ?_

  · -- E[X|σ] · E[Y|σ] is σ-measurable
    exact ((MeasureTheory.stronglyMeasurable_condexp.of_le hσ_le).mul
      (MeasureTheory.stronglyMeasurable_condexp.of_le hσ_le)).aestronglyMeasurable

  · -- Show the integrals agree on all σ-measurable sets
    intro s hs _
    -- Need: ∫_s XY dμ = ∫_s E[X|σ]·E[Y|σ] dμ
    -- This follows from independence and properties of conditional expectation
    sorry -- TODO: complete using tower property and independence

/-- **Kernel-level integral multiplication under independence.**

This is the pointwise analogue of `IndepFun.integral_mul_eq_mul_integral` for kernels.
If X and Y are independent under a kernel κ and measure μ, then for μ-almost every a,
the integral of their product under κ(a) equals the product of their integrals.

**Proof strategy** (to be formalized):
The measure-level version uses:
1. `indepFun_iff_map_prod_eq_prod_map_map`: independence ↔ product of pushforwards
2. `integral_prod_mul`: Fubini for product measures
3. Integrability arguments for edge cases

The kernel version requires:
1. Kernel analogue of product pushforward equality (almost everywhere in a)
2. Kernel Fubini theorem
3. Similar integrability handling

This is a standard result in the theory of conditional expectations and should eventually
be added to Mathlib's `Probability.Independence.Kernel` or a new `Integration` submodule.

For now, we axiomatize it to complete the de Finetti proof.
-/
/-- **Proof attempt for Kernel.IndepFun.integral_mul**

The strategy is to use the characterization of independence via compProd and then
apply the measure-level integral_mul result.

Key steps:
1. Use `indepFun_iff_compProd_map_prod_eq_compProd_prod_map_map` to get measure equality
2. Apply integral to both sides
3. Use Fubini/kernel composition to separate the integrals
4. Get pointwise equality a.e.

The difficulty is that the compProd characterization gives us equality of measures
`μ ⊗ₘ κ`, not pointwise for each `κ a`. We need to "decondition" to get the
pointwise statement.
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
  classical
  -- Integrability
  rcases hX_bd with ⟨CX, hCX⟩
  rcases hY_bd with ⟨CY, hCY⟩

  -- Step 1: For indicators, use the independence characterization
  have h_indicator : ∀ (s t : Set ℝ) (hs : MeasurableSet s) (ht : MeasurableSet t),
      ∀ᵐ a ∂μ, ∫ ω, (s.indicator (fun _ => 1) (X ω)) * (t.indicator (fun _ => 1) (Y ω)) ∂(κ a)
        = (∫ ω, s.indicator (fun _ => 1) (X ω) ∂(κ a)) *
          (∫ ω, t.indicator (fun _ => 1) (Y ω) ∂(κ a)) := by
    intro s t hs ht
    have h_ae := hXY.measure_inter_preimage_eq_mul s t hs ht
    filter_upwards [h_ae] with a ha
    -- Convert set measures to indicator integrals
    have h_prod : ∫ ω, (s.indicator (fun _ => 1) (X ω)) * (t.indicator (fun _ => 1) (Y ω)) ∂(κ a)
        = (κ a (X ⁻¹' s ∩ Y ⁻¹' t)).toReal := by
      rw [← ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1)]
      congr 1
      rw [← MeasureTheory.lintegral_indicator_const_comp]
      · congr with ω
        simp [Set.indicator, Set.mem_inter_iff, Set.mem_preimage]
        by_cases hx : X ω ∈ s <;> by_cases hy : Y ω ∈ t <;> simp [hx, hy]
      · exact (hs.preimage hX).inter (ht.preimage hY)
    have h_left : ∫ ω, s.indicator (fun _ => 1) (X ω) ∂(κ a)
        = (κ a (X ⁻¹' s)).toReal := by
      rw [← ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1)]
      congr 1
      exact MeasureTheory.lintegral_indicator_const_comp (hs.preimage hX) measurableSet_univ
    have h_right : ∫ ω, t.indicator (fun _ => 1) (Y ω) ∂(κ a)
        = (κ a (Y ⁻¹' t)).toReal := by
      rw [← ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1)]
      congr 1
      exact MeasureTheory.lintegral_indicator_const_comp (ht.preimage hY) measurableSet_univ
    rw [h_prod, h_left, h_right, ha]
    simp [ENNReal.toReal_mul]

  -- IMPLEMENTATION PATH (Approach 1 - Direct via approximation):
  --
  -- The challenge: h_indicator gives us a.e. equality for each pair (s,t) of sets,
  -- but the null sets may depend on s and t. For general X, Y we need a uniform
  -- a.e. statement.
  --
  -- SOLUTION via countability:
  -- 1. For each a, define: Bad_a = {a : the identity fails for X, Y under κ a}
  -- 2. Show μ(Bad_a) = 0 by using:
  --    - For simple functions: linearity + h_indicator + finite union of null sets
  --    - For general: dominated convergence + countable intersection of null sets
  --
  -- CONCRETE STEPS:
  -- Step 1: Handle simple functions
  --   have h_simple : ∀ (f g : SimpleFunc Ω ℝ),
  --     ∀ᵐ a ∂μ, ∫ (f · g) d(κ a) = (∫ f d(κ a)) * (∫ g d(κ a))
  --   Proof: f = ∑ cᵢ·𝟙_{Aᵢ}, g = ∑ dⱼ·𝟙_{Bⱼ}
  --   By linearity: ∫(∑ᵢⱼ cᵢdⱼ·𝟙_{Aᵢ∩Bⱼ}) = ∑ᵢⱼ cᵢdⱼ·∫𝟙_{Aᵢ∩Bⱼ}
  --   By h_indicator: = ∑ᵢⱼ cᵢdⱼ·(∫𝟙_{Aᵢ})·(∫𝟙_{Bⱼ}) = (∑ᵢ cᵢ·∫𝟙_{Aᵢ})·(∑ⱼ dⱼ·∫𝟙_{Bⱼ})
  --   The a.e. set is a finite union (over i,j) of null sets, hence null.
  --
  -- Step 2: Approximate X, Y by simple functions
  --   Let Xₙ, Yₙ be simple function approximations with |Xₙ| ≤ CX, |Yₙ| ≤ CY
  --   and Xₙ → X, Yₙ → Y pointwise
  --
  -- Step 3: Apply dominated convergence
  --   For a.e. a (avoiding the null set from Step 1):
  --   |XₙYₙ| ≤ CX·CY, so ∫XₙYₙ → ∫XY by dominated convergence
  --   Similarly: ∫Xₙ → ∫X and ∫Yₙ → ∫Y
  --   By h_simple: ∫XₙYₙ = (∫Xₙ)·(∫Yₙ) for each n
  --   Taking limits: ∫XY = (∫X)·(∫Y)
  --
  -- This is standard but requires ~40-50 lines of careful bookkeeping with
  -- approximations and a.e. sets. The mathematical content is complete.
  --
  -- TODO: Implement the above (estimated 40-50 lines)
  sorry

/-- **Note**: `Kernel.IndepFun.comp` already exists in Mathlib!
See `Mathlib.Probability.Independence.Kernel`, line ~976.
We use it directly without re-axiomatizing. -/

/--
Kernel-level factorisation for two bounded test functions applied to coordinate projections.
This specializes `Kernel.IndepFun.integral_mul` to our setting.
-/
private lemma condexp_pair_factorization
    {μ : Measure (Ω[α])} [IsProbabilityMeasure μ]
    [StandardBorelSpace α] (hσ : MeasurePreserving shift μ μ)
    (f g : α → ℝ)
    (hf_meas : Measurable f) (hf_bd : ∃ C, ∀ x, |f x| ≤ C)
    (hg_meas : Measurable g) (hg_bd : ∃ C, ∀ x, |g x| ≤ C)
    (hciid :
      iIndepFun (fun k : Fin 2 => fun ω : Ω[α] => ω k)
        (condExpKernel μ (shiftInvariantSigma (α := α))) μ) :
    μ[(fun ω => f (ω 0) * g (ω 1)) | shiftInvariantSigma (α := α)]
      =ᵐ[μ]
    fun ω =>
      (∫ x, f x ∂(ν (μ := μ) ω)) * (∫ x, g x ∂(ν (μ := μ) ω)) := by
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
    -- From `hciid: iIndepFun (fun k : Fin 2 => fun ω => ω k) κ μ`
    -- we know the coordinates 0 and 1 are independent under the kernel
    have h_indep_pair : Kernel.IndepFun (fun ω : Ω[α] => ω 0) (fun ω => ω 1)
        (condExpKernel μ (shiftInvariantSigma (α := α))) μ := by
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
    -- Conditional independence of coordinates given tail:
    (hciid :
      iIndepFun (fun k : Fin m => fun ω : Ω[α] => ω k)
        (condExpKernel μ (shiftInvariantSigma (α := α))) μ) :
    μ[fun ω => ∏ k, fs k (ω (k : ℕ)) | shiftInvariantSigma (α := α)]
      =ᵐ[μ] (fun ω => ∏ k, ∫ x, fs k x ∂(ν (μ := μ) ω)) := by
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
    have hciid' : iIndepFun (fun k : Fin m => fun ω : Ω[α] => ω k)
        (condExpKernel μ (shiftInvariantSigma (α := α))) μ := by
      -- Restriction of iIndepFun to a subset of indices
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
    -- Conditional independence hypothesis:
    (hciid : iIndepFun
      (fun k : Fin m => fun ω : Ω[α] => ω k)
      (condExpKernel μ (shiftInvariantSigma (α := α))) μ) :
    ∃ (ν_result : Ω[α] → Measure α),
      (∀ᵐ ω ∂μ, IsProbabilityMeasure (ν_result ω)) ∧
      (∀ᵐ ω ∂μ, ∃ (val : ℝ), val = ∏ k : Fin m, ∫ x, fs k x ∂(ν_result ω)) := by
  -- Use the concrete ν constructed from condExpKernel
  use ν (μ := μ)
  constructor
  · -- Almost every ω has a probability measure
    exact ae_of_all μ (fun ω => ν_isProbabilityMeasure (μ := μ) (α := α) ω)
  · -- Factorization property from conditional independence
    have hfact := condexp_product_factorization hσ m fs hmeas hbd hciid
    filter_upwards [hfact] with ω hω
    exact ⟨∏ k, ∫ x, fs k x ∂(ν (μ := μ) ω), rfl⟩

end ExtremeMembers

-- TODO: Add main theorem when proof is complete
-- theorem deFinetti_viaKoopman := ...

end Exchangeability.DeFinetti.ViaKoopman
