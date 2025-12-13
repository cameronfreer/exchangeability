/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer, Claude (Anthropic)
-/
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-!
# Triple Law Drop-Info Property

This file contains the proof obligation for the "drop-info" property that follows from
the triple law. This is a key lemma needed to break the circular dependency in the
de Finetti theorem proof.

## Main Results

* `condExp_eq_of_triple_law_direct`: Given the triple law (Z, Y, W) =^d (Z, Y, W'),
  conditioning φ = 1_A∘Y on σ(Z,W) equals conditioning on σ(W) alone.

## Mathematical Background

The triple law (Z, Y, W) =^d (Z, Y, W') says that W' is "interchangeable" with W
in terms of its joint distribution with (Z, Y). This implies that Z doesn't provide
additional information about Y beyond what W provides - the "drop-info" property.

**Proof Strategy (Kallenberg 2005, Lemma 1.3):**
1. The triple law implies the pair law (Y,W) =^d (Y,W').
2. Use `ae_eq_condExp_of_forall_setIntegral_eq` to characterize μ[φ|σ(Z,W)].
3. Show U = μ[φ|σ(W)] satisfies the integral characterization:
   - U is σ(W)-measurable, hence σ(Z,W)-measurable
   - For all S ∈ σ(Z,W): ∫_S φ = ∫_S U
4. For product rectangles S = Z⁻¹'B ∩ W⁻¹'C, use the triple law.
5. Extend via monotone class theorem.

## Implementation Status

This file contains the proof obligation as a `sorry`. The proof requires:
- Connecting the triple law to integral characterizations
- Working with product σ-algebras and their π-system structure
- Careful application of the monotone class theorem

## References

* Kallenberg (2005), *Probabilistic Symmetries and Invariance Principles*, Lemma 1.3
* Fristedt-Gray (1997), *A Modern Approach to Probability Theory*, Section II.4
-/

open MeasureTheory MeasurableSpace
open scoped ENNReal

variable {Ω α β γ : Type*}
variable [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

/-- **Direct drop-info property from triple law (Kallenberg 1.3).**

Given the triple law (Z, Y, W) =^d (Z, Y, W'), conditioning φ = 1_A∘Y on σ(Z,W) is the
same as conditioning on σ(W) alone. The additional information from Z doesn't help
predict Y because the triple law implies Y ⊥⊥ Z | W.

**Proof obligation:** This requires showing that U = μ[φ|σ(W)] satisfies the
integral characterization for μ[φ|σ(Z,W)]:
- For all σ(Z,W)-measurable S: ∫_S φ dμ = ∫_S U dμ
- By monotone class, suffice to check on rectangles Z⁻¹'B ∩ W⁻¹'C
- The triple law provides the key equality for these rectangles

See the module docstring for the full proof strategy.
-/
lemma condExp_eq_of_triple_law_direct
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (Y : Ω → α) (Z : Ω → β) (W W' : Ω → γ)
    (hY : Measurable Y) (hZ : Measurable Z) (hW : Measurable W) (hW' : Measurable W')
    (h_triple : Measure.map (fun ω => (Z ω, Y ω, W ω)) μ =
                Measure.map (fun ω => (Z ω, Y ω, W' ω)) μ)
    {A : Set α} (hA : MeasurableSet A) :
    μ[Set.indicator (Y ⁻¹' A) (fun _ => (1 : ℝ))
       | MeasurableSpace.comap (fun ω => (Z ω, W ω)) inferInstance]
      =ᵐ[μ]
    μ[Set.indicator (Y ⁻¹' A) (fun _ => (1 : ℝ))
       | MeasurableSpace.comap W inferInstance] := by
  /-
  PROOF SKETCH:

  Let φ := (Y ⁻¹' A).indicator 1 and U := μ[φ | σ(W)].

  Goal: μ[φ | σ(Z,W)] =ᵐ[μ] U

  Step 1: U is σ(Z,W)-measurable (since σ(W) ⊆ σ(Z,W)).

  Step 2: Need to verify the integral characterization:
    ∀ S ∈ σ(Z,W), ∫_S U dμ = ∫_S φ dμ

  Step 3: By monotone class theorem, suffice to check on π-system of rectangles
    {Z⁻¹'B ∩ W⁻¹'C : B ∈ σ(β), C ∈ σ(γ)}

  Step 4: For S = Z⁻¹'B ∩ W⁻¹'C:
    RHS = ∫_S φ dμ = μ(Z ∈ B, Y ∈ A, W ∈ C)

    LHS = ∫_S U dμ
        = ∫_{Z⁻¹'B ∩ W⁻¹'C} μ[φ|σ(W)] dμ
        = ∫_{Z⁻¹'B} 1_{W⁻¹'C} · μ[φ|σ(W)] dμ
        = ∫_{Z⁻¹'B} μ[1_{W∈C} · φ|σ(W)] dμ   (pull-out property)

  Step 5: Use the triple law to relate these quantities:
    The triple law (Z,Y,W) =^d (Z,Y,W') implies that integrals of functions
    of (Z,Y,W) equal those of (Z,Y,W'). Combined with the fact that U is
    a function of W alone, this gives LHS = RHS.

  The technical details require careful handling of:
  - The pull-out property for conditional expectation
  - The triple law for test functions
  - The monotone class extension
  -/
  sorry
