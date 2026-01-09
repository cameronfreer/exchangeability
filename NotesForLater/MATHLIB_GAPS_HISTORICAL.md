# Historical Document: Mathlib Gaps (Oct 2025)

> **Note**: This document is historical. It describes infrastructure that was *expected* to be
> needed for the Koopman proof but was ultimately **bypassed** via the contractability-based
> reformulation. The ViaKoopman proof is now complete without requiring Choquet's theorem
> or full ergodic decomposition. See `paper/NOTES.md` Storyline 2 for how this was achieved.

---

<!--
Original file: Exchangeability/DeFinetti/MathlibGaps.lean
Moved: Jan 2026 (after proof completion)
-->

#
# Mathlib Gaps for de Finetti Theorem (Ergodic Approach)

This document catalogs the ergodic theory and measure theory results that are **missing from mathlib**
but required to complete the formalization of de Finetti's theorem via Kallenberg's "first proof"
(the Koopman operator / Mean Ergodic Theorem approach).

## Executive Summary

**Main Blocker**: Ergodic decomposition theory (Choquet's theorem for probability measures)

**Difficulty**: Graduate-level ergodic theory, equivalent to ~1-2 chapters of a textbook

**Impact**: Unblocks not just de Finetti, but many other results in ergodic theory, dynamical
systems, and statistical mechanics

**References**:
- Walters, "An Introduction to Ergodic Theory" (1982), Chapter 6
- Phelps, "Lectures on Choquet's Theorem" (1966)
- Parthasarathy, "Probability Measures on Metric Spaces" (1967), Chapter 5

## Critical Missing Pieces

### 1. Choquet's Theorem (Integral Representation)

**Statement**: Every point in a compact convex metrizable set K can be represented as
a barycenter of a probability measure concentrated on the extremal points of K.

**Application to de Finetti**: The set of shift-invariant probability measures is a
compact convex set (in weak* topology). Extremal points = ergodic measures.
Any shift-invariant measure can be decomposed as ∫ μ_e dλ(e) over ergodic measures.

**What needs to be formalized**:
```lean
-- Extremal points of a convex set
def IsExtremal (K : Set E) (x : E) : Prop :=
  ∀ y z : E, y ∈ K → z ∈ K → ∀ t : ℝ, 0 < t → t < 1 →
    x = t • y + (1 - t) • z → x = y ∧ x = z

-- Choquet's theorem: representation by extremal measures
theorem choquet_representation
    {E : Type*} [LocallyConvexSpace ℝ E] [SecondCountableTopology E]
    (K : Set E) (hK_compact : IsCompact K) (hK_convex : Convex ℝ K) (hK_metrizable : ...) :
    ∀ x ∈ K, ∃ μ : Measure (ExtremalPoints K),
      IsProbabilityMeasure μ ∧
      x = ∫ e, e.val ∂μ  -- x is the barycenter of μ
```

**Difficulty**: Medium-High. Requires:
- Theory of extremal points and faces of convex sets
- Weak* topology on measures
- Barycenters and integral representations
- Metrization of measure spaces

**Estimated LOC**: 500-1000 lines

### 2. Ergodic Decomposition Theorem

**Statement**: Every invariant measure can be uniquely decomposed as an integral
over ergodic measures.

**Application to de Finetti**: For shift-invariant μ, decompose as μ = ∫ μ_e dλ(e)
where each μ_e is ergodic. Ergodic measures have the property that
E_μ_e[f(ω_0)·g(ω_1)] = E_μ_e[f(ω_0)]·E_μ_e[g(ω_1)], giving conditional independence.

**What needs to be formalized**:
```lean
-- Ergodic measures (extremal invariant measures)
def IsErgodic (μ : Measure Ω) (T : Ω → Ω) (hT : MeasurePreserving T μ μ) : Prop :=
  ∀ A : Set Ω, MeasurableSet A → T ⁻¹' A = A → μ A = 0 ∨ μ A = 1

-- Ergodic = extremal in the space of invariant measures
theorem ergodic_iff_extremal
    (μ : Measure Ω) (T : Ω → Ω) (hT : MeasurePreserving T μ μ) :
    IsErgodic μ T hT ↔
    IsExtremal {ν : Measure Ω | MeasurePreserving T ν ν ∧ IsProbabilityMeasure ν} μ

-- Ergodic decomposition
theorem ergodic_decomposition
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Ω → Ω) (hT : MeasurePreserving T μ μ) :
    ∃ κ : Kernel Ω Ω, ∃ λ : Measure Ω,
      (∀ᵐ ω ∂λ, IsErgodic (κ ω) T ...) ∧
      μ = ∫⁻ ω, κ ω ∂λ
```

**Difficulty**: High. Requires Choquet's theorem plus ergodic theory infrastructure.

**Estimated LOC**: 300-500 lines (assuming Choquet is done)

### 3. Conditional Independence from Ergodicity

**Statement**: For ergodic shift-invariant measures, distant coordinates are
asymptotically independent.

**Application to de Finetti**: This is the key to proving `condindep_pair_given_tail`.
For each ergodic component, the conditional expectation factorizes.

**What needs to be formalized**:
```lean
-- For ergodic measures, product expectations factorize for shifted coordinates
theorem ergodic_factorization
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Ω → Ω) (hT : MeasurePreserving T μ μ) (herg : IsErgodic μ T hT)
    (f g : Ω → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hf_bd : ∃ C, ∀ ω, |f ω| ≤ C) (hg_bd : ∃ C, ∀ ω, |g ω| ≤ C) :
    ∫ ω, f ω * g (T ω) ∂μ = (∫ ω, f ω ∂μ) * (∫ ω, g ω ∂μ)

-- Conditional version (the key result)
theorem conditional_independence_from_ergodic_decomposition
    (μ : Measure (Ω[α])) [IsProbabilityMeasure μ] [StandardBorelSpace α]
    (hσ : MeasurePreserving shift μ μ)
    (f g : α → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hf_bd : ∃ C, ∀ x, |f x| ≤ C) (hg_bd : ∃ C, ∀ x, |g x| ≤ C) :
    (fun ω => ∫ y, f (y 0) * g (y 1) ∂(condExpKernel μ (shiftInvariantSigma (α := α)) ω))
      =ᵐ[μ]
    (fun ω => (∫ y, f (y 0) ∂(condExpKernel μ (shiftInvariantSigma (α := α)) ω)) *
              (∫ y, g (y 1) ∂(condExpKernel μ (shiftInvariantSigma (α := α)) ω)))
```

**Difficulty**: High. Requires ergodic decomposition plus careful measure theory.

**Estimated LOC**: 200-400 lines (assuming ergodic decomposition is done)

## Secondary Missing Pieces

### 4. Kernel Independence API Improvements

**Issue**: Cannot state `Kernel.IndepFun (proj 0) (proj 1) (condExpKernel μ ℐ) μ`
due to autoparam issues with `condExpKernel`.

**What's needed**:
- Better autoparam handling or explicit type annotations
- OR: Bypass by proving factorization directly (current approach)

**Difficulty**: Low-Medium. May require compiler/elaborator improvements.

**Estimated LOC**: 50-100 lines (if fixable in Lean 4)

### 5. π-λ Theorem for Kernels

**Statement**: Extension of independence from generators to full σ-algebras at the
kernel level.

**Status**: Partially in mathlib for measure-level independence, needs kernel version.

**Difficulty**: Medium. Mostly adapting existing proofs.

**Estimated LOC**: 200-300 lines

## Total Effort Estimate

**Core critical path** (Choquet + Ergodic Decomposition + Conditional Independence):
- **Lines of code**: ~1000-1500 lines
- **Time estimate**: 1-2 person-months for an expert in both Lean and ergodic theory
- **Difficulty**: Graduate-level probability + measure theory + ergodic theory

**Full completion** (including secondary pieces):
- **Lines of code**: ~1500-2500 lines
- **Time estimate**: 2-3 person-months
- **Difficulty**: Requires deep understanding of mathlib's measure theory infrastructure

## Recommended Approach

1. **Start with Choquet's theorem** (most general and reusable)
   - Formalize extremal points and faces
   - Prove Choquet representation for compact convex sets
   - PR to mathlib (benefits many areas beyond de Finetti)

2. **Add ergodic decomposition**
   - Specialize Choquet to invariant measures
   - Prove ergodic = extremal
   - PR to mathlib (benefits all of ergodic theory)

3. **Complete de Finetti**
   - Use ergodic decomposition to prove conditional independence
   - Fill in the axioms in ViaKoopman.lean
   - Complete formalization!

## Alternative: Bypass Strategy

If full ergodic decomposition is too ambitious, consider:
1. **Axiomatize at a higher level**: Accept ergodic decomposition as an axiom
2. **Use different proof**: Try Kallenberg's "second proof" (martingale approach)
   which may have fewer mathlib gaps
3. **Specialize**: Prove only for specific cases (e.g., i.i.d. sequences first)

## References and Resources

### Textbooks
- Walters, "An Introduction to Ergodic Theory" (1982), Chapters 4-6
- Phelps, "Lectures on Choquet's Theorem" (1966)
- Kallenberg, "Probabilistic Symmetries and Invariance Principles" (2005), Chapter 1

### Papers
- de Finetti (1937), "La prévision: ses lois logiques, ses sources subjectives"
- Hewitt & Savage (1955), "Symmetric measures on Cartesian products"
- Aldous (1985), "Exchangeability and related topics" (Saint-Flour lectures)

### Mathlib precedents
- `Mathlib.Analysis.InnerProductSpace.MeanErgodic` - Mean Ergodic Theorem
- `Mathlib.Dynamics.Ergodic.MeasurePreserving` - Basic ergodic theory
- `Mathlib.MeasureTheory.Decomposition.Lebesgue` - Measure decomposition
- `Mathlib.Analysis.Convex.Extremal` - (TODO: doesn't exist yet!)

## Conclusion

The de Finetti theorem via Koopman approach is **blocked by missing ergodic decomposition theory**.
This is a **high-value mathlib contribution** that would enable not just de Finetti, but many
other results in:
- Ergodic theory
- Dynamical systems
- Statistical mechanics
- Extreme value theory
- Optimal transport

**Note (Jan 2026)**: This assessment is historical. All three proofs are now complete.
The Koopman proof succeeded by using contractability-based factorization instead of
full ergodic decomposition, bypassing most of the infrastructure described above.
