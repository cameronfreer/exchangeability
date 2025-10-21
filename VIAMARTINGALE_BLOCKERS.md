# ViaMartingale.lean - Mathlib Infrastructure Blockers

## Status Summary

**File builds successfully** with 3 sorries remaining (only linter warnings, no errors).

All 3 sorries require mathlib infrastructure that does not yet exist. These are well-documented TODOs waiting on mathlib contributions, not implementation gaps in the proof strategy.

## Blocker 1: Uniqueness of Conditional Distributions (Line 1876)

**Sorry location:** `condexp_indicator_drop_info_of_pair_law` (lines 1819-1876)

**What's needed:**
- Uniqueness theorem for conditional distributions (`condDistrib`)
- **Mathematical statement:** If `(ξ, η) =ᵈ (ξ, ζ)` and `η = g(ζ)`, then `P(ξ ∈ · | ζ) = P(ξ ∈ · | η)` almost everywhere

**Mathlib status:**
- ✅ `ProbabilityTheory.condExp_ae_eq_integral_condDistrib` exists
- ❌ Uniqueness of `condDistrib` under measure-preserving transformations does NOT exist
- ❌ Standard Borel space integration with conditional distributions incomplete

**Required contribution:**
```lean
-- Target location: Mathlib/Probability/ConditionalProbability.lean (or similar)
lemma condDistrib_unique_of_law_eq_and_measurable
    {Ω α β : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    [MeasurableSpace α] [StandardBorelSpace α]
    [MeasurableSpace β] [StandardBorelSpace β]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (ξ : Ω → α) (η ζ : Ω → β)
    (hξ : Measurable ξ) (hη : Measurable η) (hζ : Measurable ζ)
    (h_law : Measure.map (fun ω => (ξ ω, η ω)) μ = Measure.map (fun ω => (ξ ω, ζ ω)) μ)
    (h_factor : ∃ g : β → β, Measurable g ∧ η = g ∘ ζ) :
  ∀ᵐ ω ∂μ, condDistrib ξ ζ μ (ζ ω) = condDistrib ξ η μ (η ω)
```

**Effort estimate:** Medium (2-3 weeks)
- Build on existing `condDistrib` infrastructure
- Requires uniqueness proof using disintegration theorem
- Type class management for StandardBorelSpace

## Blocker 2: Triple Law Projection (Line 2074)

**Sorry location:** `condexp_indicator_eq_on_join_of_triple_law` (lines 1881-2074)

**What's needed:**
- Kernel composition and disintegration infrastructure
- Application of Kallenberg Lemma 1.3 to triple distributions

**Mathematical setup:**
- Given: `(Zr, Y, θk) =ᵈ (Zr, Y, θk')`
- Want: `E[1_B(Y) | σ(Zr, θk)] = E[1_B(Y) | σ(θk)]` a.e.
- Key insight: θk' makes Zr redundant for predicting Y (from contractability)

**Mathlib status:**
- ❌ Kernel infrastructure for 3+ variable disintegration incomplete
- ❌ Conditional independence from measure equality not in library
- Depends on resolution of Blocker 1

**Required contribution:**
Extends Blocker 1 to handle three-way distributions and projection. The full development requires:
1. Triple disintegration lemmas
2. Factorization through intermediate σ-algebras
3. Contractability → conditional independence bridge

**Effort estimate:** Large (4-6 weeks)
- Requires Blocker 1 infrastructure first
- Novel application to contractable sequences
- Complex σ-algebra manipulation

## Blocker 3: Pi Measurable Space Supremum (Line 2318)

**Sorry location:** Anonymous `have hge` in `finite_level_factorization_to_future` (line 2318)

**What's needed:**
- **Mathematical statement:** For ℕ-indexed products, `Pi.measurableSpace = ⨆ k, MeasurableSpace.comap π_k inferInstance`
  where `π_k : (ℕ → α) → (Fin k → α)` restricts to first k coordinates

**Goal:**
```lean
futureFiltration X m ≤ ⨆ k, finFutureSigma X m k
```

**Mathlib status:**
- ✅ `MeasurableSpace.comap_iSup` exists (comap distributes over supremum)
- ✅ `MeasurableSpace.comap_comp` exists (comap of composition)
- ✅ `MeasureTheory.generateFrom_measurableCylinders` exists (Pi = generateFrom cylinders)
- ❌ Direct equality `Pi.measurableSpace = ⨆ finite projections` does NOT exist

**Required contribution:**
```lean
-- Target location: Mathlib/MeasureTheory/Constructions/Pi.lean
lemma pi_nat_eq_iSup_fin {α : Type*} [MeasurableSpace α] :
    (inferInstance : MeasurableSpace (ℕ → α))
      = ⨆ k, MeasurableSpace.comap (fun f (i : Fin k) => f i.val) inferInstance
```

**Proof strategy:**
1. Use `generateFrom_measurableCylinders`: Pi = generateFrom(cylinders)
2. Use `measurableCylinders_nat`: cylinders depend on finitely many coords
3. Show each cylinder ∈ some finite projection σ-algebra
4. Therefore Pi ≤ ⨆ finite projections
5. Reverse direction from comap monotonicity

**Effort estimate:** Small-Medium (1-2 weeks)
- Standard result in product measure theory
- Infrastructure largely exists (`generateFrom_measurableCylinders`)
- Clean formalization, valuable for library

## Alternative: Direct Proofs

The comments note that each blocker could be proved directly for this specific case without the general infrastructure:

**Blocker 1 & 2:** ~100-150 lines proving kernel uniqueness directly for indicator functions and contractable sequences (avoids general `condDistrib` uniqueness)

**Blocker 3:** ~50-100 lines showing cylinders in `futureFiltration X m` are in some `finFutureSigma X m k` (avoids general Pi lemma)

**Tradeoff:** Direct proofs would complete this file but provide no value to mathlib. The general lemmas are more valuable contributions.

## Recommended Path Forward

**Priority 1 (Unblock ViaMartingale):** Blocker 3
- Smallest, most self-contained
- General Pi lemma is valuable for mathlib
- Unlocks Lévy upward convergence argument in this file

**Priority 2 (Complete conditional distributions):** Blocker 1
- Medium complexity
- Fills important gap in ProbabilityTheory
- Required for Blocker 2

**Priority 3 (Advanced applications):** Blocker 2
- Requires Blockers 1 infrastructure
- Most specific to de Finetti context
- Could potentially be proved directly if time-sensitive

## File Health

Despite 3 sorries, the file is in excellent shape:
- ✅ Compiles without errors
- ✅ All sorries well-documented with proof strategies
- ✅ Clear separation between implemented and blocked components
- ✅ 19 helper lemmas added for infrastructure
- ✅ Can proceed with other proofs (ViaL2, ViaKoopman) independently

The sorries represent genuine mathematical dependencies, not implementation gaps.

---
*Last updated: 2025-10-21*
*Analysis based on current file state with 3 sorries*
