/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Data.EReal.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Exchangeability.Ergodic.KoopmanMeanErgodic
import Exchangeability.Ergodic.ProjectionLemmas
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondexpL2
import Exchangeability.Ergodic.ShiftInvariantSigma
import Exchangeability.Ergodic.ShiftInvariantRepresentatives

-- NOTE: shift was moved from KoopmanMeanErgodic to PathSpace.Shift in Oct 2025
-- to avoid duplication with CommonEnding. See commit 57890e9.

/-!
# Shift-invariant σ-algebra and conditional expectation

This file establishes the fundamental connection between:
- The fixed-point subspace of the Koopman operator
- The L² space with respect to the shift-invariant σ-algebra
- The conditional expectation onto the shift-invariant σ-algebra

The core definitions (`shiftInvariantSigma`, `isShiftInvariant`, `tailSigma`) and
the construction of shift-invariant representatives (`gRep`, `mkShiftInvariantRep`)
are in separate modules:
- `ShiftInvariantSigma.lean`: Core σ-algebra definitions
- `ShiftInvariantRepresentatives.lean`: Limsup construction for representatives

## Main definitions

* `fixedSubspace`: The subspace of L² functions fixed by the Koopman operator.
* `metProjectionShift`: Orthogonal projection onto the fixed-point subspace.
* `condexpL2`: Conditional expectation on L² with respect to the shift-invariant σ-algebra.

## Main results

* `fixedSpace_eq_invMeasurable`: Functions fixed by Koopman are exactly those
  measurable with respect to the shift-invariant σ-algebra.
* `proj_eq_condexp`: The orthogonal projection onto the fixed-point subspace equals
  the conditional expectation onto the shift-invariant σ-algebra.

## References

* Olav Kallenberg (2005), *Probabilistic Symmetries and Invariance Principles*,
  Springer, Chapter 1 (pages 26-27). The shift-invariant σ-algebra is denoted
  𝓘_ξ in Kallenberg.
* FMP 10.4: Invariant sets and functions (Chapter 10, pages 180-181).
  Key results used in the first proof.

## FMP 10.4: Invariant Sets and Functions

For a measure-preserving transformation T on (S, 𝒮, μ):

**Definitions**:
- A set I ∈ 𝒮 is **invariant** if I = T⁻¹I
- A set I is **almost invariant** if μ(I Δ T⁻¹I) = 0
- 𝓘 = invariant σ-field (invariant sets in 𝒮)
- 𝓘' = almost invariant σ-field (almost invariant sets in 𝒮^μ)
- A function f is **invariant** if f = f ∘ T
- A function f is **almost invariant** if f = f ∘ T a.s. μ

**Lemma 1 (invariant sets and functions)**:
A measurable function f: S → S' (Borel space) is invariant/almost invariant
iff it is 𝓘-measurable/𝓘^μ-measurable, respectively.

**Lemma 2 (almost invariance)**:
For any distribution μ and μ-preserving transformation T,
the invariant and almost invariant σ-fields satisfy: 𝓘' = 𝓘^μ
(almost invariant = completion of invariant).

**Lemma 3 (ergodicity)**:
Let ξ be a random element in S with distribution μ, and T a μ-preserving map on S.
Then ξ is T-ergodic iff the sequence (T^n ξ) is θ-ergodic, in which case
even η = (f ∘ T^n ξ) is θ-ergodic for every measurable f: S → S'.

-/

noncomputable section

open scoped Classical Topology

namespace Exchangeability.DeFinetti

open MeasureTheory Filter Topology
open Exchangeability.Ergodic
open Exchangeability.PathSpace

variable {α : Type*} [MeasurableSpace α]

/-- Functions that are `AEStronglyMeasurable` with respect to the invariant σ-algebra are
almost everywhere fixed by the shift. -/
lemma shiftInvariantSigma_aestronglyMeasurable_ae_shift_eq
    {μ : Measure (Ω[α])} [IsProbabilityMeasure μ]
    (hσ : MeasurePreserving shift μ μ) {f : Ω[α] → ℝ}
    (hf : AEStronglyMeasurable[shiftInvariantSigma (α := α)] f μ) :
    (fun ω => f (shift ω)) =ᵐ[μ] f := by
  classical
  rcases hf with ⟨g, hg_meas, hfg⟩
  have hcomp :=
    (hσ.quasiMeasurePreserving).ae_eq_comp (μ := μ) (ν := μ)
      (f := shift (α := α)) (g := fun ω => f ω) (g' := fun ω => g ω) hfg
  have hshift : (fun ω => g (shift ω)) =ᵐ[μ] g :=
    EventuallyEq.of_eq (shiftInvariantSigma_measurable_shift_eq g hg_meas.measurable)
  exact hcomp.trans <| hshift.trans hfg.symm

/-- If an `Lp` function is measurable with respect to the invariant σ-algebra, the Koopman
operator fixes it. -/
lemma koopman_eq_self_of_shiftInvariant
    {μ : Measure (Ω[α])} [IsProbabilityMeasure μ]
    (hσ : MeasurePreserving shift μ μ)
    {f : Lp ℝ 2 μ}
    (hf : AEStronglyMeasurable[shiftInvariantSigma (α := α)] f μ) :
    koopman shift hσ f = f := by
  classical
  have hcomp :
      (koopman shift hσ f) =ᵐ[μ]
        (fun ω => f (shift ω)) := by
    change MeasureTheory.Lp.compMeasurePreserving (shift (α := α)) hσ f =ᵐ[μ]
        fun ω => f (shift ω)
    simpa [koopman]
      using
        (MeasureTheory.Lp.coeFn_compMeasurePreserving f hσ)
  have hshift := shiftInvariantSigma_aestronglyMeasurable_ae_shift_eq (μ := μ) hσ hf
  have hfinal : (koopman shift hσ f) =ᵐ[μ] f := hcomp.trans hshift
  exact Lp.ext hfinal

/-- A Koopman-fixed function is automatically measurable with respect to the
invariant σ-algebra.

Starting from the a.e. identity `f ∘ shift = f`, the previous lemma replaces a
representative of `f` by an actual shift-invariant function, and the resulting
measurability is transported back to `f`. -/
lemma aestronglyMeasurable_shiftInvariant_of_koopman
    {μ : Measure (Ω[α])} [IsProbabilityMeasure μ]
    (hσ : MeasurePreserving shift μ μ)
    {f : Lp ℝ 2 μ}
    (hfix : koopman shift hσ f = f) :
    AEStronglyMeasurable[shiftInvariantSigma (α := α)] f μ := by
  classical
  /-
  Proof strategy sketch:
  1. Unfold the equality `koopman shift hσ f = f` to obtain the almost-everywhere
     identity `(fun ω => f (shift ω)) =ᵐ[μ] f`.
  2. Choose a strongly measurable representative `g` of `f`.
  3. Apply `exists_shiftInvariantRepresentative` to obtain a version `g'` of `g`
     that is literally shift-invariant and measurable with respect to the
     invariant σ-algebra.
  4. Transport measurability of `g'` back to `f` using the almost everywhere
     equality.

  Implementing steps (3)–(5) will likely require a bespoke lemma about
  modifying functions on null sets to enforce invariance; this will be filled in
  later.
  -/
  -- STEP 1. Extract the a.e. invariance statement from `koopman` equality.
  have hcomp : (koopman shift hσ f) =ᵐ[μ] fun ω => f (shift ω) := by
    change MeasureTheory.Lp.compMeasurePreserving (shift (α := α)) hσ f =ᵐ[μ]
        fun ω => f (shift ω)
    simpa [koopman]
      using
        (MeasureTheory.Lp.coeFn_compMeasurePreserving f hσ)
  have hfixAE : (koopman shift hσ f) =ᵐ[μ] f := by
    simp [hfix]
  have hshift : (fun ω => f (shift ω)) =ᵐ[μ] f := by
    exact hcomp.symm.trans hfixAE
  have hf_base : AEStronglyMeasurable f μ := Lp.aestronglyMeasurable f
  obtain ⟨g', hg'_meas, hAE, _⟩ :=
    mkShiftInvariantRep (μ := μ) hσ (fun ω => f ω) hf_base hshift
  have hf_meas : AEStronglyMeasurable[shiftInvariantSigma (α := α)] f μ :=
    (AEStronglyMeasurable.congr hg'_meas hAE)
  exact hf_meas

/-! ### The Mean Ergodic Theorem and conditional expectation

This section establishes the key connection between:
1. The **Koopman operator** `U : L²(μ) → L²(μ)` given by `(Uf)(ω) = f(shift ω)`
2. The **fixed-point subspace** `{f : Uf = f}` (shift-invariant functions)
3. The **conditional expectation** `E[·|ℐ]` onto the shift-invariant σ-algebra

**Main theorem** (`proj_eq_condexp`): The orthogonal projection onto the fixed-point
subspace equals the conditional expectation onto the shift-invariant σ-algebra.

**Mathematical background**:
- The Mean Ergodic Theorem states that Cesàro averages `n⁻¹ ∑ᵢ₌₀ⁿ⁻¹ Uⁱf` converge
  in L² to the orthogonal projection onto the fixed-point subspace
- Conditional expectation `E[f|ℐ]` is also characterized as an orthogonal projection
  (onto functions measurable w.r.t. ℐ)
- Both projections are idempotent and symmetric, with the same range
- By uniqueness of orthogonal projections (`orthogonalProjections_same_range_eq`),
  they must be equal

**Application to de Finetti**: This identification allows us to use ergodic theory
(Koopman operator, Mean Ergodic Theorem) to prove facts about conditional expectations,
which are central to the probabilistic formulation of de Finetti's theorem.
-/

/-- **The fixed-point subspace of the Koopman operator.**

This is the closed subspace of L²(μ) consisting of equivalence classes of functions
f such that f ∘ shift = f almost everywhere.

In the ergodic approach to de Finetti, this is the target space of the limiting
projection from the Mean Ergodic Theorem.
-/
abbrev fixedSubspace {μ : Measure (Ω[α])} [IsProbabilityMeasure μ]
    (hσ : MeasurePreserving shift μ μ) : Submodule ℝ (Lp ℝ 2 μ) :=
  fixedSpace (koopman shift hσ)

/-- Functions in the fixed-point subspace are exactly those that are a.e. invariant under shift. -/
lemma mem_fixedSubspace_iff {μ : Measure (Ω[α])} [IsProbabilityMeasure μ]
    (hσ : MeasurePreserving shift μ μ) (f : Lp ℝ 2 μ) :
    f ∈ fixedSubspace hσ ↔ koopman shift hσ f = f := by
  rfl

/-- The orthogonal projection onto the fixed-point subspace exists (as a closed subspace). -/
lemma fixedSubspace_closed {μ : Measure (Ω[α])} [IsProbabilityMeasure μ]
    (hσ : MeasurePreserving shift μ μ) :
    IsClosed (fixedSubspace hσ : Set (Lp ℝ 2 μ)) := by
  classical
  let T := koopman shift hσ
  have hset : (fixedSubspace hσ : Set (Lp ℝ 2 μ)) =
      (fun f : Lp ℝ 2 μ => T f - f) ⁻¹' ({0} : Set (Lp ℝ 2 μ)) := by
    ext f
    unfold fixedSubspace fixedSpace
    simp [T, LinearMap.mem_eqLocus, sub_eq_zero]
  have hcont : Continuous fun f : Lp ℝ 2 μ => T f - f :=
    (T.continuous.sub continuous_id)
  have hclosed : IsClosed ((fun f : Lp ℝ 2 μ => T f - f) ⁻¹'
      ({0} : Set (Lp ℝ 2 μ))) :=
    IsClosed.preimage hcont isClosed_singleton
  simpa [hset]

/-- **Orthogonal projection onto the fixed-point subspace (MET projection).**

This is the orthogonal projection `P : L²(μ) → fixedSubspace` arising from the
Mean Ergodic Theorem (MET). It is defined as the composition of:
1. Orthogonal projection onto the fixed-point subspace (as an abstract subspace)
2. The subtype inclusion back into L²(μ)

**Properties** (established in subsequent lemmas):
- `metProjectionShift_idem`: Idempotent (`P² = P`)
- `metProjectionShift_isSymmetric`: Symmetric/self-adjoint
- `metProjectionShift_range`: Range equals the fixed-point subspace
- `metProjectionShift_tendsto`: Limit of Cesàro averages (Mean Ergodic Theorem)

**Key theorem**: `proj_eq_condexp` shows this projection equals conditional expectation
onto the shift-invariant σ-algebra.

Defined as an alias for `metProjection shift`, the generic projection for any
measure-preserving transformation.
-/
noncomputable abbrev metProjectionShift
    {μ : Measure (Ω[α])} [IsProbabilityMeasure μ]
    (hσ : MeasurePreserving shift μ μ) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  metProjection shift hσ

lemma metProjectionShift_apply
    {μ : Measure (Ω[α])} [IsProbabilityMeasure μ]
    (hσ : MeasurePreserving shift μ μ) (f : Lp ℝ 2 μ) :
    let hclosed := fixedSubspace_closed (μ := μ) hσ
    haveI : CompleteSpace (fixedSubspace hσ) := hclosed.completeSpace_coe
    haveI : (fixedSubspace hσ).HasOrthogonalProjection :=
      Submodule.HasOrthogonalProjection.ofCompleteSpace (fixedSubspace hσ)
    metProjectionShift (μ := μ) hσ f =
      (fixedSubspace hσ).subtypeL ((fixedSubspace hσ).orthogonalProjection f) := by
  -- Now definitionally equal since fixedSubspace = fixedSpace (koopman shift hσ)
  rfl

lemma metProjectionShift_mem
    {μ : Measure (Ω[α])} [IsProbabilityMeasure μ]
    (hσ : MeasurePreserving shift μ μ) (f : Lp ℝ 2 μ) :
    metProjectionShift (μ := μ) hσ f ∈ fixedSubspace hσ := by
  classical
  have hclosed := fixedSubspace_closed (μ := μ) hσ
  haveI : CompleteSpace (fixedSubspace hσ) := hclosed.completeSpace_coe
  haveI : (fixedSubspace hσ).HasOrthogonalProjection :=
    Submodule.HasOrthogonalProjection.ofCompleteSpace (fixedSubspace hσ)
  rw [metProjectionShift_apply]
  simp

lemma metProjectionShift_fixed
    {μ : Measure (Ω[α])} [IsProbabilityMeasure μ]
    (hσ : MeasurePreserving shift μ μ) {g : Lp ℝ 2 μ}
    (hg : g ∈ fixedSubspace hσ) :
    metProjectionShift (μ := μ) hσ g = g := by
  classical
  have hclosed := fixedSubspace_closed (μ := μ) hσ
  haveI : CompleteSpace (fixedSubspace hσ) := hclosed.completeSpace_coe
  haveI : (fixedSubspace hσ).HasOrthogonalProjection :=
    Submodule.HasOrthogonalProjection.ofCompleteSpace (fixedSubspace hσ)
  have hproj :=
      Submodule.orthogonalProjection_mem_subspace_eq_self
        (⟨g, hg⟩ : fixedSubspace hσ)
  have hproj_val :
      (((fixedSubspace hσ).orthogonalProjection g) : Lp ℝ 2 μ) = g := by
    simpa using congrArg Subtype.val hproj
  rw [metProjectionShift_apply]
  simp [hproj_val]

lemma metProjectionShift_idem
    {μ : Measure (Ω[α])} [IsProbabilityMeasure μ]
    (hσ : MeasurePreserving shift μ μ) :
    (metProjectionShift (μ := μ) hσ).comp (metProjectionShift (μ := μ) hσ) =
      metProjectionShift (μ := μ) hσ := by
  classical
  apply ContinuousLinearMap.ext
  intro f
  have hf_mem := metProjectionShift_mem (μ := μ) hσ f
  simp [ContinuousLinearMap.coe_comp', Function.comp_apply,
    metProjectionShift_fixed (μ := μ) hσ hf_mem]

lemma metProjectionShift_range
    {μ : Measure (Ω[α])} [IsProbabilityMeasure μ]
    (hσ : MeasurePreserving shift μ μ) :
    Set.range (metProjectionShift (μ := μ) hσ) =
      (fixedSubspace hσ : Set (Lp ℝ 2 μ)) := by
  classical
  have hclosed := fixedSubspace_closed (μ := μ) hσ
  have : CompleteSpace (fixedSubspace hσ) := hclosed.completeSpace_coe
  ext x
  constructor
  · intro hx
    rcases hx with ⟨f, rfl⟩
    exact metProjectionShift_mem (μ := μ) hσ f
  · intro hx
    refine ⟨x, ?_⟩
    simpa using metProjectionShift_fixed (μ := μ) hσ hx

lemma metProjectionShift_isSymmetric
    {μ : Measure (Ω[α])} [IsProbabilityMeasure μ]
    (hσ : MeasurePreserving shift μ μ) :
    (metProjectionShift (μ := μ) hσ).IsSymmetric := by
  classical
  have hclosed := fixedSubspace_closed (μ := μ) hσ
  have : CompleteSpace (fixedSubspace hσ) := hclosed.completeSpace_coe
  simpa [metProjectionShift] using
    (subtypeL_comp_orthogonalProjection_isSymmetric
      (fixedSubspace hσ : Submodule ℝ (Lp ℝ 2 μ)))

lemma metProjectionShift_tendsto
    {μ : Measure (Ω[α])} [IsProbabilityMeasure μ]
    (hσ : MeasurePreserving shift μ μ) (f : Lp ℝ 2 μ) :
    Tendsto (fun n => birkhoffAverage ℝ (koopman shift hσ) _root_.id n f)
      atTop (𝓝 (metProjectionShift (μ := μ) hσ f)) := by
  classical
  let K : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ := koopman shift hσ
  have hnorm : ‖K‖ ≤ (1 : ℝ) := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) ?_
    intro g
    have hiso : Isometry (koopman shift hσ) := koopman_isometry shift hσ
    have hg : ‖K g‖ = ‖g‖ := by
      simpa [K] using Isometry.norm_map_of_map_zero hiso (map_zero _) g
    simp [hg]
  have hclosed := fixedSubspace_closed (μ := μ) hσ
  haveI : CompleteSpace (fixedSubspace hσ) := hclosed.completeSpace_coe
  haveI : (fixedSubspace hσ).HasOrthogonalProjection :=
    Submodule.HasOrthogonalProjection.ofCompleteSpace (fixedSubspace hσ)
  have hS : (LinearMap.eqLocus K.toLinearMap 1) = fixedSubspace hσ := rfl
  -- Set up the instance context for the eqLocus subspace
  have : CompleteSpace (LinearMap.eqLocus K.toLinearMap 1) := by
    rw [hS]; exact hclosed.completeSpace_coe
  have : (LinearMap.eqLocus K.toLinearMap 1).HasOrthogonalProjection := by
    rw [hS]; exact Submodule.HasOrthogonalProjection.ofCompleteSpace (fixedSubspace hσ)
  have hlimit := ContinuousLinearMap.tendsto_birkhoffAverage_orthogonalProjection K hnorm f
  convert hlimit using 1

/-- The range of `metProjectionShift` equals the fixed subspace. -/
lemma metProjectionShift_range_fixedSubspace
    {μ : Measure (Ω[α])} [IsProbabilityMeasure μ]
    (hσ : MeasurePreserving shift μ μ) :
    Set.range (metProjectionShift (μ := μ) hσ) =
      (fixedSubspace hσ : Set (Lp ℝ 2 μ)) :=
  metProjectionShift_range (μ := μ) hσ

/-- `metProjectionShift` fixes elements of the fixed subspace. -/
lemma metProjectionShift_fixes_fixedSubspace
    {μ : Measure (Ω[α])} [IsProbabilityMeasure μ]
    (hσ : MeasurePreserving shift μ μ) {g : Lp ℝ 2 μ}
    (hg : g ∈ fixedSubspace hσ) :
    metProjectionShift (μ := μ) hσ g = g :=
  metProjectionShift_fixed (μ := μ) hσ hg

/-- Conditional expectation on L² with respect to the shift-invariant σ-algebra.

This is the orthogonal projection onto the subspace of shift-invariant L² functions,
implemented using mathlib's `condExpL2`. -/
noncomputable def condexpL2 {μ : Measure (Ω[α])} [IsProbabilityMeasure μ] :
    Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  -- Apply mathlib's conditional expectation to get projection onto lpMeas
  let ce : Lp ℝ 2 μ →L[ℝ] lpMeas ℝ ℝ shiftInvariantSigma 2 μ :=
    MeasureTheory.condExpL2 ℝ ℝ (m := shiftInvariantSigma) shiftInvariantSigma_le
  -- Compose with subtype inclusion to get back to full Lp space
  (lpMeas ℝ ℝ shiftInvariantSigma 2 μ).subtypeL.comp ce


/-- lpMeas functions are exactly the Koopman-fixed functions. -/

lemma condexpL2_idem {μ : Measure (Ω[α])} [IsProbabilityMeasure μ] :
    (condexpL2 (μ := μ)).comp (condexpL2 (μ := μ)) = condexpL2 (μ := μ) := by
  classical
  apply ContinuousLinearMap.ext
  intro f
  simp only [condexpL2, ContinuousLinearMap.coe_comp', Function.comp_apply]
  haveI :
      Fact
        (shiftInvariantSigma (α := α) ≤
          (inferInstance : MeasurableSpace (Ω[α]))) :=
    ⟨shiftInvariantSigma_le (α := α)⟩
  have hfix :=
    Submodule.orthogonalProjection_mem_subspace_eq_self
      (K := lpMeas ℝ ℝ shiftInvariantSigma 2 μ)
      (MeasureTheory.condExpL2 ℝ ℝ (m := shiftInvariantSigma)
        shiftInvariantSigma_le f)
  simpa [MeasureTheory.condExpL2]
    using congrArg Subtype.val hfix

lemma lpMeas_eq_fixedSubspace
    {μ : Measure (Ω[α])} [IsProbabilityMeasure μ]
    (hσ : MeasurePreserving shift μ μ) :
    (Set.range (lpMeas ℝ ℝ shiftInvariantSigma 2 μ).subtypeL : Set (Lp ℝ 2 μ)) =
    (fixedSubspace hσ : Set (Lp ℝ 2 μ)) := by
  classical
  apply Set.Subset.antisymm
  · -- → direction: range subtypeL ⊆ fixedSubspace
    intro f hf
    rcases hf with ⟨g, rfl⟩
    have hg : AEStronglyMeasurable[shiftInvariantSigma (α := α)]
        ((lpMeas ℝ ℝ shiftInvariantSigma 2 μ).subtypeL g : Ω[α] → ℝ) μ :=
      lpMeas.aestronglyMeasurable g
    -- Koopman fixes `g`:
    have := koopman_eq_self_of_shiftInvariant (μ := μ) hσ
      (f := (lpMeas ℝ ℝ shiftInvariantSigma 2 μ).subtypeL g) hg
    simpa [fixedSubspace, fixedSpace] using this
  · -- ← direction: fixedSubspace ⊆ range subtypeL
    intro f hf
    -- obtain a shift-invariant measurable representative
    have hmeas := aestronglyMeasurable_shiftInvariant_of_koopman (μ := μ) hσ
      (f := f) (by simpa [fixedSubspace, fixedSpace] using hf)
    -- put it in range of subtypeL
    exact ⟨⟨f, hmeas⟩, rfl⟩

/-- The conditional expectation equals the orthogonal projection onto the fixed-point subspace.

This fundamental connection links:
- Probability theory: conditional expectation with respect to shift-invariant σ-algebra
- Functional analysis: orthogonal projection in Hilbert space
- Ergodic theory: fixed-point subspace of the Koopman operator
-/
lemma range_condexp_eq_fixedSubspace {μ : Measure (Ω[α])}
    [IsProbabilityMeasure μ]
    (hσ : MeasurePreserving shift μ μ) :
    Set.range (condexpL2 (μ := μ)) =
    (fixedSubspace hσ : Set (Lp ℝ 2 μ)) := by
  classical
  -- Range of the composition is the image of lpMeas
  have h_proj :
      Set.range (condexpL2 (μ := μ))
        = Set.range (lpMeas ℝ ℝ shiftInvariantSigma 2 μ).subtypeL := by
    apply Set.Subset.antisymm
    · intro f hf
      rcases hf with ⟨x, rfl⟩
      exact ⟨(MeasureTheory.condExpL2 ℝ ℝ (m := shiftInvariantSigma)
        shiftInvariantSigma_le) x, rfl⟩
    · intro f hf
      rcases hf with ⟨y, rfl⟩
      refine ⟨(↑y : Lp ℝ 2 μ), ?_⟩
      have hfix : (MeasureTheory.condExpL2 ℝ ℝ (m := shiftInvariantSigma)
        shiftInvariantSigma_le)
          (↑y) = y := by
        classical
        haveI :
            Fact
              (shiftInvariantSigma (α := α) ≤
                (inferInstance : MeasurableSpace (Ω[α]))) :=
          ⟨shiftInvariantSigma_le (α := α)⟩
        simp [MeasureTheory.condExpL2]
      simp [condexpL2, ContinuousLinearMap.comp_apply, hfix]
  -- now swap range via lpMeas_eq_fixedSubspace
  rw [h_proj, lpMeas_eq_fixedSubspace (μ := μ) hσ]

/-- **Main theorem: Orthogonal projection equals conditional expectation.**

The orthogonal projection onto the fixed-point subspace of the Koopman operator
equals the conditional expectation onto the shift-invariant σ-algebra.

**Statement**: `metProjectionShift = condexpL2`

**Significance**: This theorem bridges three major areas:
1. **Ergodic theory**: The Mean Ergodic Theorem provides convergence of Cesàro averages
   to `metProjectionShift`
2. **Functional analysis**: `metProjectionShift` is the orthogonal projection in the Hilbert
   space L²(μ)
3. **Probability theory**: `condexpL2` is the L² conditional expectation operator

**Proof strategy**:
- Both operators are symmetric, idempotent, continuous linear maps
- Both have the same range (the fixed-point subspace = shift-invariant L² functions)
- By uniqueness of orthogonal projections (`orthogonalProjections_same_range_eq`),
  they must be equal

**Applications**:
- Allows using the Mean Ergodic Theorem to prove convergence properties of conditional
  expectations
- Key step in the ergodic/Koopman operator proof of de Finetti's theorem
- Connects shift-invariance (algebraic) to conditional independence (probabilistic)
-/
-- condexpL2 properties matching metProjectionShift structure
private lemma condexpL2_projection_properties {μ : Measure (Ω[α])} [IsProbabilityMeasure μ]
    (hσ : MeasurePreserving shift μ μ) :
    (condexpL2 (μ := μ) * condexpL2 (μ := μ) = condexpL2 (μ := μ)) ∧
    (condexpL2 (μ := μ)).IsSymmetric ∧
    (Set.range (condexpL2 (μ := μ)) = (fixedSubspace hσ : Set (Lp ℝ 2 μ))) ∧
    (∀ g ∈ fixedSubspace hσ, condexpL2 (μ := μ) g = g) := by
  constructor
  · exact condexpL2_idem (μ := μ)
  constructor
  · intro f g
    unfold condexpL2
    exact MeasureTheory.inner_condExpL2_left_eq_right shiftInvariantSigma_le
  constructor
  · exact range_condexp_eq_fixedSubspace hσ
  · intro g hg
    have h_range : Set.range (condexpL2 (μ := μ)) = (fixedSubspace hσ : Set (Lp ℝ 2 μ)) :=
      range_condexp_eq_fixedSubspace hσ
    have : g ∈ Set.range (condexpL2 (μ := μ)) := by rw [h_range]; exact hg
    rcases this with ⟨f, rfl⟩
    have h_idem : condexpL2 (μ := μ) * condexpL2 (μ := μ) = condexpL2 (μ := μ) :=
      condexpL2_idem (μ := μ)
    change (condexpL2 (μ := μ) * condexpL2 (μ := μ)) f = condexpL2 (μ := μ) f
    rw [h_idem]

-- Convert operator multiplication to composition form
private lemma mul_to_comp {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (T : E →L[ℝ] E) (h_mul : T * T = T) : T.comp T = T := by
  simp only [ContinuousLinearMap.mul_def] at h_mul
  exact h_mul

-- Fixed subspace has orthogonal projection structure
private lemma fixedSubspace_hasOrthogonalProjection {μ : Measure (Ω[α])} [IsProbabilityMeasure μ]
    (hσ : MeasurePreserving shift μ μ) : (fixedSubspace hσ).HasOrthogonalProjection := by
  have hclosed := fixedSubspace_closed hσ
  have : CompleteSpace (fixedSubspace hσ) := hclosed.completeSpace_coe
  exact Submodule.HasOrthogonalProjection.ofCompleteSpace (fixedSubspace hσ)

theorem proj_eq_condexp {μ : Measure (Ω[α])} [IsProbabilityMeasure μ]
    (hσ : MeasurePreserving shift μ μ) :
    metProjectionShift hσ = condexpL2 (μ := μ) := by
  classical
  -- Establish metProjectionShift properties
  have h_idem_MET : metProjectionShift hσ * metProjectionShift hσ = metProjectionShift hσ :=
    metProjectionShift_idem hσ
  have h_symm_MET : (metProjectionShift hσ).IsSymmetric :=
    metProjectionShift_isSymmetric hσ
  have h_range_MET : Set.range (metProjectionShift hσ) = (fixedSubspace hσ : Set (Lp ℝ 2 μ)) :=
    metProjectionShift_range_fixedSubspace hσ
  have h_fixes_MET : ∀ g ∈ fixedSubspace hσ, metProjectionShift hσ g = g :=
    fun g hg => metProjectionShift_fixes_fixedSubspace hσ hg

  -- Establish condexpL2 properties (via helper)
  obtain ⟨h_idem_cond, h_symm_cond, h_range_cond, h_fixes_cond⟩ :=
    condexpL2_projection_properties hσ

  -- Convert to composition form
  have h_idem_MET_comp := mul_to_comp (metProjectionShift hσ) h_idem_MET
  have h_idem_cond_comp := mul_to_comp (condexpL2 (μ := μ)) h_idem_cond

  -- Ensure orthogonal projection structure
  haveI := fixedSubspace_hasOrthogonalProjection hσ

  -- Apply uniqueness: two projections with same range are equal
  exact orthogonalProjections_same_range_eq
    (metProjectionShift hσ) (condexpL2 (μ := μ)) (fixedSubspace hσ)
    h_range_MET h_range_cond
    h_fixes_MET h_fixes_cond
    h_idem_MET_comp h_idem_cond_comp
    h_symm_MET h_symm_cond

end Exchangeability.DeFinetti
