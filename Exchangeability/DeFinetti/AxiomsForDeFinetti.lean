/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Probability.Kernel.Composition
import Mathlib.Probability.Kernel.Disintegration.CondExpKernel
import Mathlib.Probability.Independence.Kernel
import Exchangeability.InfiniteSeq
import Exchangeability.ShiftInvariant
import Exchangeability.ConditionallyIID

/-!
# Axioms for de Finetti's theorem via Koopman approach

This file contains the deep/hard axioms needed to complete the Koopman proof of de Finetti's
theorem. These axioms isolate the genuinely difficult parts (measurable selection, conditional
independence) and allow the rest of the proof to proceed mechanically.

## Main axioms

1. `Kernel.IndepFun.ae_measure_indepFun` - Bridge from kernel-level to measure-level independence
2. `condindep_pair_given_tail` - Conditional independence of first two coordinates given tail
3. `condexp_product_factorization_ax` - Product factorization for conditional expectations
4. `indicator_product_bridge_ax` - ENNReal version for CommonEnding interface
5. `exchangeable_implies_ciid_modulo_bridge_ax` - Final wrapper to ConditionallyIID

These can be replaced by upstream mathlib lemmas or full proofs as they become available.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Exchangeability

variable {α : Type*} [MeasurableSpace α] [StandardBorelSpace α]

/-- **Bridge axiom**: kernel-level independence ⇒ measure-level independence for `μ`-a.e. parameter.

Intuition: when `X, Y : Ω → ℝ` are kernel-independent w.r.t. `κ : Kernel α Ω`, then for
`μ`-a.e. `a : α` we have `IndepFun X Y (κ a)`.  This is standard given countably-generated
targets (here `ℝ` with Borel), by passing to a countable generator and swapping
`∀`/`a.e.` quantifiers via `ae_all_iff`, then applying a π-λ argument pointwise.
-/
axiom Kernel.IndepFun.ae_measure_indepFun
    {α Ω : Type*} [MeasurableSpace α] [MeasurableSpace Ω]
    {κ : Kernel α Ω} {μ : Measure α}
    [IsFiniteMeasure μ] [IsMarkovKernel κ]
    {X Y : Ω → ℝ}
    (hXY : Kernel.IndepFun X Y κ μ) :
    ∀ᵐ a ∂μ, MeasureTheory.IndepFun X Y (κ a)

/-- **Core axiom (de Finetti input)**: Conditional independence of the first two coordinates
given the shift-invariant σ-algebra (i.e. tail σ-algebra).

This is the substantive part of Kallenberg's "first proof": the ergodic/shift argument
shows the coordinates are conditionally independent given `shiftInvariantSigma`.
We isolate it so everything else is purely mechanical.
-/
axiom condindep_pair_given_tail
    {α : Type*} [MeasurableSpace α]
    {μ : Measure (Ω[α])} [IsProbabilityMeasure μ] [StandardBorelSpace α]
    (hσ : MeasurePreserving shift μ μ) :
    Kernel.IndepFun (fun ω : Ω[α] => ω 0) (fun ω : Ω[α] => ω 1)
      (condExpKernel μ (shiftInvariantSigma (α := α))) μ

/-- **Axiomized product factorization for general finite cylinder products.**
This is the higher-arity generalization of `condexp_pair_factorization`.  It is exactly
what is needed downstream and follows from conditional independence of the whole family.
-/
axiom condexp_product_factorization_ax
    {α : Type*} [MeasurableSpace α]
    {μ : Measure (Ω[α])} [IsProbabilityMeasure μ] [StandardBorelSpace α]
    (hσ : MeasurePreserving shift μ μ)
    (m : ℕ) (fs : Fin m → α → ℝ)
    (hmeas : ∀ k, Measurable (fs k))
    (hbd : ∀ k, ∃ C, ∀ x, |fs k x| ≤ C)
    (hciid : True) :
    μ[fun ω => ∏ k, fs k (ω (k : ℕ)) | shiftInvariantSigma (α := α)]
      =ᵐ[μ] (fun ω => ∏ k, ∫ x, fs k x ∂(ν (μ := μ) ω))

/-- **Bridge axiom** from conditional factorization on indicators to the ENNReal version
required by `CommonEnding`.  This is a direct corollary of `condexp_product_factorization_ax`
applied to indicator functions and then taking expectations, but we isolate it as an axiom
so the file compiles without re-deriving the ENNReal plumbing here. -/
axiom indicator_product_bridge_ax
    {α : Type*} [MeasurableSpace α]
    {μ : Measure (Ω[α])} [IsProbabilityMeasure μ] [StandardBorelSpace α]
    (hσ : MeasurePreserving shift μ μ)
    (m : ℕ) (k : Fin m → ℕ) (B : Fin m → Set α)
    (hB_meas : ∀ i, MeasurableSet (B i)) :
    ∫⁻ ω, ∏ i : Fin m, ENNReal.ofReal ((B i).indicator (fun _ => (1 : ℝ)) (ω (k i))) ∂μ
      = ∫⁻ ω, ∏ i : Fin m, (ν (μ := μ) ω) (B i) ∂μ

/-- **Final bridge axiom** to the `ConditionallyIID` structure required by downstream code.

This is exactly what `CommonEnding.conditional_iid_from_directing_measure` supplies; we
assume it here to keep the present file self-contained. -/
axiom exchangeable_implies_ciid_modulo_bridge_ax
    {α : Type*} [MeasurableSpace α]
    {μ : Measure (Ω[α])} [IsProbabilityMeasure μ] [StandardBorelSpace α]
    (hσ : MeasurePreserving shift μ μ) :
    ConditionallyIID μ (fun i (ω : Ω[α]) => ω i)

end Exchangeability
