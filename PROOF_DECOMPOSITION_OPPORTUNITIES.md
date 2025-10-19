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
