/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Probability.Kernel.Condexp
import Exchangeability.Ergodic.ShiftInvariantSigma

/-!
# Directing Kernel for de Finetti's Theorem

This file defines the directing kernel `ν` for de Finetti's theorem. The kernel gives
the conditional distribution of the first coordinate given the shift-invariant σ-algebra.

## Main definitions

* `π0`: Projection onto the first coordinate
* `rcdKernel`: Regular conditional distribution kernel
* `ν`: The directing measure as a function `Ω[α] → Measure α`

## Main results

* `integral_ν_eq_integral_condExpKernel`: Key bridge lemma relating integrals against ν
  to integrals against the conditional expectation kernel

## References

* Kallenberg (2005), *Probabilistic Symmetries and Invariance Principles*, Chapter 1
-/

open MeasureTheory Filter Topology ProbabilityTheory

noncomputable section

namespace Exchangeability.DeFinetti.ViaKoopman

open Exchangeability.DeFinetti (shiftInvariantSigma shiftInvariantSigma_le)
open Exchangeability.PathSpace

variable {α : Type*} [MeasurableSpace α]

-- Short notation for shift-invariant σ-algebra
local notation "mSI" => shiftInvariantSigma (α := α)

/-! ## Coordinate projection -/

/-- Projection onto the first coordinate. -/
def π0 : Ω[α] → α := fun ω => ω 0

lemma measurable_pi0 : Measurable (π0 (α := α)) := measurable_pi_apply 0

/-! ## Regular conditional distribution kernel -/

/-- Regular conditional distribution kernel constructed via condExpKernel.

This is the kernel giving the conditional distribution of the first coordinate
given the tail σ-algebra.
-/
noncomputable def rcdKernel {μ : Measure (Ω[α])} [IsProbabilityMeasure μ]
    [StandardBorelSpace α] : Kernel (Ω[α]) α :=
  Kernel.comap ((condExpKernel μ (shiftInvariantSigma (α := α))).map (π0 (α := α)))
    id (measurable_id'' (shiftInvariantSigma_le (α := α)))

instance rcdKernel_isMarkovKernel {μ : Measure (Ω[α])} [IsProbabilityMeasure μ]
    [StandardBorelSpace α] : IsMarkovKernel (rcdKernel (μ := μ)) := by
  unfold rcdKernel
  haveI : IsMarkovKernel ((condExpKernel μ (shiftInvariantSigma (α := α))).map (π0 (α := α))) :=
    Kernel.IsMarkovKernel.map _ (measurable_pi0 (α := α))
  exact Kernel.IsMarkovKernel.comap _ (measurable_id'' (shiftInvariantSigma_le (α := α)))

/-- The regular conditional distribution as a function assigning to each point
a probability measure on α. -/
noncomputable def ν {μ : Measure (Ω[α])} [IsProbabilityMeasure μ]
    [StandardBorelSpace α] : Ω[α] → Measure α :=
  fun ω => (rcdKernel (μ := μ)) ω

/-- ν evaluation on measurable sets is measurable in the parameter. -/
lemma ν_eval_measurable
    {μ : Measure (Ω[α])} [IsProbabilityMeasure μ] [StandardBorelSpace α]
    {s : Set α} (hs : MeasurableSet s) :
    Measurable (fun ω => ν (μ := μ) ω s) := by
  simp only [ν]
  exact (rcdKernel (μ := μ)).measurable_coe hs

/-- ν ω is a probability measure for each ω. -/
instance ν_isProbabilityMeasure
    {μ : Measure (Ω[α])} [IsProbabilityMeasure μ] [StandardBorelSpace α]
    (ω : Ω[α]) : IsProbabilityMeasure (ν (μ := μ) ω) := by
  simp only [ν]
  -- rcdKernel is a Markov kernel (composition of map and comap preserves this)
  exact IsMarkovKernel.isProbabilityMeasure ω

/-! ## Bridge lemmas -/

/-- Helper: Integral against ν relates to integral against condExpKernel via coordinate projection.

This lemma makes explicit how integrating a function `f : α → ℝ` against the conditional
distribution `ν ω` relates to integrating `f ∘ π₀` against `condExpKernel μ m ω`.
-/
lemma integral_ν_eq_integral_condExpKernel
    {μ : Measure (Ω[α])} [IsProbabilityMeasure μ] [StandardBorelSpace α]
    (ω : Ω[α]) {f : α → ℝ} (hf : Measurable f) :
    ∫ x, f x ∂(ν (μ := μ) ω) = ∫ y, f (y 0) ∂(condExpKernel μ (shiftInvariantSigma (α := α)) ω) := by
  -- By definition: ν ω = Kernel.comap (Kernel.map (condExpKernel μ ...) π₀) id ... ω
  -- Kernel.comap with id is just evaluation, so: ν ω = (Kernel.map (condExpKernel μ ...) π₀) ω
  -- Kernel.map_apply gives: (Kernel.map κ f) a = (κ a).map f
  -- So: ν ω = ((condExpKernel μ ...) ω).map π₀
  -- Then integral_map gives: ∫ f d(μ.map g) = ∫ (f ∘ g) dμ
  unfold ν rcdKernel
  rw [Kernel.comap_apply]
  rw [Kernel.map_apply _ (measurable_pi0 (α := α))]
  -- Now: ∫ x, f x ∂((condExpKernel ... ω).map π₀) = ∫ y, f (y 0) ∂(condExpKernel ... ω)
  unfold π0
  rw [MeasureTheory.integral_map (measurable_pi_apply 0).aemeasurable hf.aestronglyMeasurable]
  rfl

end Exchangeability.DeFinetti.ViaKoopman
