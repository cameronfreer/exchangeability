# Proof Decomposition Opportunities

**Date:** 2025-10-19
**Status:** Documentation for future refactoring

## Overview

This document identifies opportunities to split large proofs into smaller, more manageable lemmas in files that already compile successfully.

## Motivation

Large proofs (>100 lines) are difficult to:
- Understand and maintain
- Debug when they break
- Reuse across different contexts
- Review for correctness

Decomposing them into intermediate lemmas with clear names improves:
- Code readability and documentation
- Modularity and reusability
- Debugging (isolate which step fails)
- Mathematical clarity (explicit intermediate results)

## Candidates for Decomposition

### High Priority: Already Compiling Files

#### 1. **Core.lean** - `measure_eq_of_fin_marginals_eq` (~80 lines)

**Current structure:** Single monolithic proof

**Decomposition opportunity:**
```lean
-- Current: One big proof
theorem measure_eq_of_fin_marginals_eq ...
  -- 80 lines of proof

-- Proposed: Break into steps
lemma prefixCylinders_generate_product : 
  MeasurableSpace.generateFrom prefixCylinders = Pi.measurableSpace := ...
  
lemma prefixCylinders_isPiSystem : 
  IsPiSystem prefixCylinders := ...
  
lemma measures_eq_on_prefixCylinders :
  (∀ n, marginal μ n = marginal ν n) → 
  ∀ C ∈ prefixCylinders, μ C = ν C := ...

theorem measure_eq_of_fin_marginals_eq :
  (∀ n, marginal μ n = marginal ν n) → μ = ν := by
  intro h
  apply ext_of_generate_finite _ prefixCylinders_isPiSystem _ _
  · exact prefixCylinders_generate_product
  · exact measures_eq_on_prefixCylinders h
```

**Impact:** 
- 4 small lemmas instead of 1 large proof
- Each lemma <20 lines, self-documenting
- Intermediate results become reusable

#### 2. **Contractability.lean** - `exists_perm_extending_strictMono` (~60 lines)

**Current structure:** Extension construction all in one proof

**Decomposition opportunity:**
```lean
-- Proposed intermediate lemmas:
lemma strictMono_implies_injective : 
  StrictMono k → Function.Injective k := ...

lemma strictMono_range_card :
  StrictMono (k : Fin m → ℕ) → Fintype.card (range k) = m := ...

lemma extend_to_perm_aux :
  -- Helper for extending to full permutation
  ...

theorem exists_perm_extending_strictMono := by
  -- Combine the pieces
  ...
```

#### 3. **TailSigma.lean** - `tailProcess_eq_iInf_revFiltration` (~40 lines)

**Current structure:** Direct proof of bridge lemma

**Decomposition opportunity:**
```lean
-- Proposed intermediate steps:
lemma tailFamily_eq_revFiltration_of :
  tailFamily X m = revFiltration X m ↔ 
  (revFiltration satisfies definition) := ...

lemma iInf_congr_family :
  (∀ m, F m = G m) → ⨅ m, F m = ⨅ m, G m := ...

theorem tailProcess_eq_iInf_revFiltration :=
  iInf_congr_family tailFamily_eq_revFiltration_of
```

**Impact:**
- Reusable `iInf_congr_family` lemma
- Clearer proof structure
- Each piece independently testable

### Medium Priority: Files with Pre-existing Errors

#### 4. **ViaL2.lean** - Large CDF proofs (lines 2555-3423)

**Current:** 700+ lines of CDF/Stieltjes infrastructure in one section

**Decomposition opportunity:**
- Extract `alphaIic` properties to separate lemmas
- Split `cdf_from_alpha` construction into stages:
  1. Rational envelope definition
  2. Monotonicity proof
  3. Right-continuity proof
  4. Limit behavior
- Each stage <50 lines

**Status:** Defer until ViaL2 compilation is clean

#### 5. **ViaMartingale.lean** - Conditional independence proofs

**Current:** Several proofs >50 lines

**Decomposition opportunity:**
- Extract measurability lemmas
- Separate indicator algebra calculations
- Break martingale convergence into steps

**Status:** Defer until ViaMartingale compilation is clean

## Implementation Guidelines

### When to Decompose

✅ **Do decompose when:**
- Proof is >50 lines
- Multiple distinct mathematical steps
- Intermediate result has independent interest
- Proof repeats similar patterns
- Multiple `have` statements that could be lemmas

❌ **Don't decompose when:**
- Proof is <30 lines
- Steps are tightly coupled
- No clear intermediate lemmas
- Would create more complexity than clarity

### How to Decompose

1. **Identify natural break points:**
   - Look for `have` statements with complex proofs
   - Find distinct mathematical claims
   - Identify reusable sub-computations

2. **Name intermediate lemmas clearly:**
   - Use descriptive names that capture mathematical content
   - Follow mathlib naming conventions
   - Add docstrings explaining significance

3. **Test independently:**
   - Each new lemma should compile on its own
   - Verify the main theorem still works
   - Check for performance regressions

4. **Document the structure:**
   - Add comments showing proof flow
   - Link lemmas in documentation
   - Explain why decomposition was chosen

## Next Steps

1. **Core.lean decomposition** (1-2 hours)
   - High impact, already compiles
   - Clear decomposition path
   - Improves key theorem clarity

2. **Contractability.lean decomposition** (1 hour)
   - Medium impact
   - Relatively straightforward
   - Makes permutation construction clearer

3. **TailSigma.lean polish** (30 minutes)
   - Low-hanging fruit
   - Recently created file
   - Good opportunity to establish patterns

4. **Defer ViaL2/ViaMartingale** until compilation is clean

## Success Metrics

- Number of proofs >50 lines reduced by 50%
- Number of standalone reusable lemmas increased
- No performance regression (<5% compile time increase)
- Improved git blame granularity

---

**Note:** This is documentation for future work. Current priority is completing Tier 1 refactoring (IntegrationHelpers + StrictMono).

---

## Additional Refactoring Tiers (For Later)

### Tier 2: Medium-Value Consolidation (deferred)

#### Extract CE Utilities from ViaKoopman (~half day, -120 lines)

**Current status:** ViaKoopman has extensive conditional expectation utilities tightly coupled with proof

**Files to extract to:**
- `Probability/CondExp.lean` (already exists)
- `Probability/CondExpExtras.lean` (already exists)

**Key utilities to extract:**
- `condexp_pullback_factor` (line 463) - CE pullback along factor maps
- `condexp_precomp_iterate_eq_of_invariant` (line 542) - CE invariance under measure-preserving iterates
- Various axioms that could be proven lemmas

**Why deferred:**
- ViaKoopman still has compilation issues
- CE utilities are tightly coupled with Koopman operator proof
- Better to wait until proof stabilizes
- Estimated effort: ~4 hours

**Expected impact:**
- Reduce ViaKoopman by ~120 lines
- Make CE utilities available to other proofs
- Cleaner separation of concerns

---

### Tier 3: Long-Term Organization (1-2 weeks, mathlib contribution)

#### Extract Ergodic Theory Infrastructure

**VERY HIGH VALUE for mathlib community contribution**

**Components ready for extraction:**

1. **KoopmanMeanErgodic.lean** (347 lines) → `Mathlib.Dynamics.Ergodic.MeanErgodic`
   - Koopman operator definition
   - Fixed-point subspace characterization
   - Mean Ergodic Theorem: `birkhoffAverage_tendsto_metProjection`
   - **Pure ergodic theory** - not de Finetti-specific

2. **ProjectionLemmas.lean** (227 lines) → `Mathlib.Analysis.InnerProductSpace.Projection`
   - Orthogonal projection uniqueness
   - Hilbert space machinery
   - **Pure functional analysis**

3. **InvariantSigma.lean** (~200 lines extractable) → `Mathlib.Dynamics.Ergodic.Invariant`
   - Shift-invariant σ-algebra (general theory)
   - Connection to conditional expectation
   - **General ergodic theory**

4. **Natural Extension Infrastructure** (ViaKoopman lines 122-425)
   - `Ωℤ[α]` - Bi-infinite path space
   - `shiftℤ`, `shiftℤInv` - Two-sided shift operators
   - `NaturalExtensionData` structure
   - Extract to `Exchangeability/Ergodic/NaturalExtension.lean`

**Recommended process:**
1. Extract to `Ergodic/` directory as staging area (3 days)
2. Polish to mathlib standards (2 days)
3. Write comprehensive documentation (1 day)
4. Submit mathlib PRs when de Finetti proof is published (1 week review cycle)

**Why this is valuable:**
- ~774 lines of pure mathematics that belong in mathlib
- Not used by ViaL2 or ViaMartingale - purely Koopman-specific
- Fills gaps in mathlib's ergodic theory library
- Community contribution opportunity

**Why deferred:**
- Long-term project (1-2 weeks total)
- Should wait until de Finetti proofs are complete and published
- Mathlib submission has overhead (review process, documentation standards)
- Not blocking current proof development

**Impact:**
- ~774 lines moved to mathlib (external to project)
- Cleaner project structure
- Community contribution
- Better separation of general theory vs. application

---

### Tier 4: Advanced Optimizations (future consideration)

#### Stieltjes/CDF Infrastructure Extraction

**Current status:** 700+ lines of CDF/Stieltjes infrastructure in ViaL2.lean (lines 2555-3423)

**Potential extraction:** `Probability/StieltjesMeasureHelpers.lean`

**Components:**
- `indIic` - Indicator for `(-∞, t]` intervals
- `alphaIic` - Raw CDF from Cesàro averages
- `alphaIicCE` - Canonical conditional expectation version
- `cdf_from_alpha` - Right-continuous CDF via rational envelope
- `directing_measure` - Stieltjes measure construction

**Reusability:** Medium-High
- Rational envelope technique for right-continuity is general
- Endpoint limit infrastructure uses only dominated convergence
- Stieltjes measure construction is generic

**Why deferred:**
- Currently ViaL2-specific (depends on contractability and L² bounds)
- Integrated into the L² proof flow
- Only extract if ViaMartingale or ViaKoopman need CDF construction
- Estimated extractable: ~300 lines of generic infrastructure

**Decision criteria:**
- **Extract if:** Other proofs need similar CDF constructions
- **Keep in ViaL2 if:** Only used by L² proof

---

**Updated:** 2025-10-19
**Note:** Tiers 2-4 should be considered after all three de Finetti proofs compile successfully.
