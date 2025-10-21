# Mathlib PR Candidates - Staging Plan

This document outlines components from the de Finetti formalization that could be contributed upstream to mathlib, organized by dependency order and readiness.

## Table of Contents
1. [Ready for PR (Minimal Dependencies)](#ready-for-pr-minimal-dependencies)
2. [Near-Ready (Minor Cleanup Needed)](#near-ready-minor-cleanup-needed)
3. [Future Work (Requires Theory Development)](#future-work-requires-theory-development)
4. [Staging Sequence](#staging-sequence)

---

## Ready for PR (Minimal Dependencies)

### PR 1: Integration Helper Lemmas
**File:** `Exchangeability/Probability/IntegrationHelpers.lean`
**Status:** ✅ Complete, no sorries, builds cleanly
**Dependencies:** Pure mathlib imports only

**Key contributions:**
1. **`abs_integral_mul_le_L2`** - Cauchy-Schwarz for L² functions (specialized from Hölder)
   ```lean
   lemma abs_integral_mul_le_L2 [IsFiniteMeasure μ] {f g : Ω → ℝ}
       (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
       |∫ ω, f ω * g ω ∂μ| ≤ (∫ ω, (f ω)^2 ∂μ)^(1/2) * (∫ ω, (g ω)^2 ∂μ)^(1/2)
   ```

2. **`eLpNorm_one_eq_integral_abs`** - Bridge between Real integrals and eLpNorm
   ```lean
   lemma eLpNorm_one_eq_integral_abs {μ : Measure Ω} [IsFiniteMeasure μ]
       {f : Ω → ℝ} (hf : Integrable f μ) :
       eLpNorm f 1 μ = ENNReal.ofReal (∫ ω, |f ω| ∂μ)
   ```

3. **`L2_tendsto_implies_L1_tendsto_of_bounded`** - L² → L¹ convergence for bounded functions
   ```lean
   lemma L2_tendsto_implies_L1_tendsto_of_bounded
       {μ : Measure Ω} [IsProbabilityMeasure μ]
       (f : ℕ → Ω → ℝ) (g : Ω → ℝ)
       (hf_meas : ∀ n, Measurable (f n))
       (hf_bdd : ∃ M, ∀ n ω, |f n ω| ≤ M)
       (hg_memLp : MemLp g 2 μ)
       (hL2 : Tendsto (fun n => ∫ ω, (f n ω - g ω)^2 ∂μ) atTop (𝓝 0)) :
       Tendsto (fun n => ∫ ω, |f n ω - g ω| ∂μ) atTop (𝓝 0)
   ```

4. **Pushforward integral lemmas** - `integral_pushforward_id`, `integral_pushforward_sq_diff`, `integral_pushforward_continuous`

**Mathlib location:** `Mathlib.MeasureTheory.Function.L2Space` or new `Mathlib.MeasureTheory.Integral.LpConvergence`

**Rationale for upstreaming:**
- General-purpose lemmas, not specific to de Finetti
- Fill gaps in L² → L¹ convergence theory
- Clean implementations with no project dependencies
- Already used in ViaL2 proof approach

**Estimated effort:** Low - file is already clean and documented

**Key achievement from formalization:**
The L² → L¹ convergence lemma fills a surprising gap in mathlib. While Cauchy-Schwarz is available in general form (Hölder's inequality), the specialized form for probability spaces wasn't readily accessible. This infrastructure was essential for the ViaL2 proof approach and demonstrates how formalization reveals "obvious" gaps in standard libraries.

**Reference commit:** `8bea05e` - Complete L² → L¹ convergence with no sorries

---

### PR 2: Conditional Expectation Extensions
**File:** `Exchangeability/Probability/CondExp.lean`
**Status:** ✅ All 4 sorries complete, builds successfully
**Dependencies:** Pure mathlib imports only

**Key contributions:**
1. **`integrable_of_bounded_mul`** - Product of integrable and bounded is integrable
   ```lean
   lemma integrable_of_bounded_mul [IsFiniteMeasure μ]
       {f g : Ω → ℝ} (hf : Integrable f μ) (hg : Measurable g)
       (hbd : ∃ C, ∀ ω, |g ω| ≤ C) :
       Integrable (f * g) μ
   ```

2. **`condExp_abs_le_of_abs_le`** - Absolute value inequality preservation
   ```lean
   lemma condExp_abs_le_of_abs_le [IsFiniteMeasure μ]
       {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : Measure Ω}
       {m : MeasurableSpace Ω} (hm : m ≤ m₀)
       {f g : Ω → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
       (h : ∀ ω, |f ω| ≤ |g ω|) :
       ∀ᵐ ω ∂μ, |μ[f|m] ω| ≤ μ[(fun ω' => |g ω'|)|m] ω
   ```

3. **`condExp_L1_lipschitz`** - L¹ Lipschitz continuity
   ```lean
   lemma condExp_L1_lipschitz [IsFiniteMeasure μ]
       {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : Measure Ω}
       {m : MeasurableSpace Ω} (hm : m ≤ m₀)
       {f g : Ω → ℝ} (hf : Integrable f μ) (hg : Integrable g μ) :
       ∫ ω, |μ[f|m] ω - μ[g|m] ω| ∂μ ≤ ∫ ω, |f ω - g ω| ∂μ
   ```

4. **`condExp_mul_pullout`** - Pull out measurable bounded functions
   ```lean
   lemma condExp_mul_pullout {Ω : Type*} {m₀ : MeasurableSpace Ω}
       {μ : Measure Ω} [IsFiniteMeasure μ]
       {m : MeasurableSpace Ω} (hm : m ≤ m₀)
       {f g : Ω → ℝ} (hf : Integrable f μ)
       (hg_meas : @Measurable Ω ℝ m _ g)
       (hg_bd : ∃ C, ∀ ω, |g ω| ≤ C) :
       μ[f * g|m] =ᵐ[μ] fun ω => μ[f|m] ω * g ω
   ```

**Mathlib location:** `Mathlib.MeasureTheory.Function.ConditionalExpectation.Real`

**Rationale for upstreaming:**
- Fundamental operator-theoretic properties of conditional expectation
- Fill gaps in mathlib's conditional expectation API
- The `condExpWith` pattern is the canonical solution for sub-σ-algebra work
- Could benefit many probability theory formalizations

**Important note:** Should include documentation of the `condExpWith` pattern in PR description and docstrings.

**Estimated effort:** Medium - needs careful review of signatures, may need style adjustments

---

## Near-Ready (Minor Cleanup Needed)

### PR 3: π-System Uniqueness for Infinite Products
**File:** `Exchangeability/Core.lean`
**Status:** ✅ Complete, builds successfully
**Cleanup needed:** Remove project-specific definitions, isolate general machinery

**Key contributions:**
1. **`prefixCylinders` π-system** - Cylinder sets form a π-system
   ```lean
   lemma prefixCylinders_isPiSystem : IsPiSystem (prefixCylinders α)
   ```

2. **`measure_eq_of_fin_marginals_eq`** - Measures determined by finite marginals
   ```lean
   lemma measure_eq_of_fin_marginals_eq [BorelSpace α] (μ ν : Measure (ℕ → α))
       [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
       (h : ∀ n, Measure.map (prefixProj n) μ = Measure.map (prefixProj n) ν) :
       μ = ν
   ```

**Mathlib location:** `Mathlib.MeasureTheory.Constructions.Pi` or `Mathlib.MeasureTheory.Measure.ProbabilityMeasure`

**Rationale for upstreaming:**
- Fundamental result in infinite-dimensional probability
- Key lemma for product measures on infinite spaces
- Generalizes beyond de Finetti (useful for stochastic processes)

**Cleanup needed:**
- Separate general π-system machinery from project-specific definitions
- Possibly split into "product measure uniqueness" and "cylinder set π-systems"
- Add more general versions (not just ℕ → α)

**Estimated effort:** Medium - requires thoughtful refactoring to isolate general components

---

### PR 4: Permutation Extension Lemmas
**File:** `Exchangeability/Contractability.lean`
**Status:** ✅ Complete, builds successfully
**Cleanup needed:** Extract general combinatorics from probability-specific code

**Key contribution:**
- **`exists_perm_extending_strictMono`** - Extend strictly increasing functions to permutations
  ```lean
  lemma exists_perm_extending_strictMono {m : ℕ} (k : Fin m → ℕ)
      (hk_strict : StrictMono k) :
      ∃ (σ : Equiv.Perm ℕ), ∀ i : Fin m, σ (k i) = i
  ```

**Mathlib location:** `Mathlib.Combinatorics.Permutation` or `Mathlib.Data.Fintype.Perm`

**Rationale for upstreaming:**
- Pure combinatorics result, independent of probability
- Uses only `Equiv.extendSubtype` and `Fintype` machinery
- Could be useful in other combinatorial contexts

**Cleanup needed:**
- Extract from probability context
- Add more general versions (permutations of arbitrary types)
- Strengthen to give explicit construction

**Estimated effort:** Low - lemma is already clean, just needs extraction

---

## Future Work (Requires Theory Development)

### Long-term PR: Kernel Theory Extensions
**Current status:** Blocked by mathlib gaps
**Files:** `Exchangeability/Probability/InfiniteProduct.lean` (Ionescu-Tulcea construction)

**Required mathlib additions:**
1. **Kernel uniqueness theorem** (currently axiom in ViaMartingale)
2. **Disintegration theorem** (currently axiom in ViaMartingale)
3. **Regular conditional probabilities** for standard Borel spaces

**Rationale:** These are fundamental probability theory results that belong in mathlib, but require substantial development:
- Kernel theory infrastructure
- Regular conditional probabilities
- Borel space theory

**Timeline:** Post-project, potentially collaborative mathlib contributions

**Estimated effort:** High - requires significant theory development

---

### Long-term PR: Mean Ergodic Theorem Application
**Current status:** ViaKoopman has 4 TODO markers
**Files:** `Exchangeability/Ergodic/KoopmanMeanErgodic.lean`, `Exchangeability/DeFinetti/ViaKoopman.lean`

**Potential contributions:**
1. **Koopman operator on L²** for measure-preserving systems
2. **Cesàro average convergence** for ergodic operators
3. **Application to shift operators** on sequence spaces

**Rationale:** Bridges ergodic theory and probability, could be useful for:
- Stochastic processes
- Dynamical systems formalization
- Ergodic theorems library

**Blockers:** Need to complete ViaKoopman proof first

**Timeline:** After ViaKoopman completion

**Estimated effort:** High - requires ergodic theory expertise

---

## Staging Sequence

### Phase 1: Low-Hanging Fruit (Immediate)
**Goal:** Get clean, general-purpose lemmas into mathlib quickly

1. **PR 1: IntegrationHelpers** (2-3 weeks)
   - File is already clean
   - No project dependencies
   - Clear utility for probability theory

2. **PR 4: Permutation Extension** (1-2 weeks)
   - Small, focused contribution
   - Pure combinatorics
   - Easy to extract

### Phase 2: Core Infrastructure (3-6 months after project completion)
**Goal:** Contribute fundamental conditional expectation and measure theory

3. **PR 2: CondExp Extensions** (1-2 months)
   - Important API additions
   - Requires careful review
   - Document `condExpWith` pattern
   - May need mathlib style adjustments

4. **PR 3: π-System Uniqueness** (1-2 months)
   - Fundamental infinite-dimensional probability
   - Requires thoughtful refactoring
   - May need generalization

### Phase 3: Advanced Theory (6-12 months after project completion)
**Goal:** Contribute deep probability theory results

5. **Kernel Theory Extensions** (3-6 months)
   - Requires substantial development
   - Collaborate with mathlib probability theory experts
   - May require multiple PRs

6. **Ergodic Theory Applications** (3-6 months)
   - After ViaKoopman completion
   - Requires ergodic theory review
   - Coordinate with dynamical systems formalizations

---

## General PR Considerations

### Code Quality Requirements
- [ ] No `sorry` placeholders
- [ ] No project-specific imports
- [ ] Follow mathlib naming conventions
- [ ] Comprehensive docstrings
- [ ] Examples in docstrings where helpful
- [ ] Linter-clean (no warnings)

### Documentation Requirements
- [ ] Module-level docstrings explaining purpose
- [ ] Main results clearly documented
- [ ] References to mathematical literature where appropriate
- [ ] Implementation notes for non-obvious choices

### Review Considerations
- **IntegrationHelpers:** Should be straightforward, mostly standard results
- **CondExp:** May face scrutiny on signatures (the `condExpWith` pattern)
- **π-System:** May need generalization beyond probability context
- **Kernel theory:** Will require extensive review and possibly collaboration

---

## Notes for PR Preparation

### Common Refactoring Needs
1. **Remove project-specific definitions** - Keep only general lemmas
2. **Generalize types** - Replace `ℕ → α` with more general product types where possible
3. **Split large files** - Break into focused modules
4. **Add `@[simp]` attributes** - Where appropriate for simplification
5. **Namespace organization** - May need to adjust namespaces for mathlib conventions

### Potential Review Feedback
- **Signature choices:** Mathlib may prefer different parametrization
- **Naming:** May need to align with mathlib conventions
- **Proof style:** May need to simplify or restructure proofs
- **Generality:** May be asked to generalize beyond current scope

### Strategic Considerations
- **Start with IntegrationHelpers and Permutation** - Build credibility with easy PRs
- **Document patterns well** - The `condExpWith` pattern discovery is valuable
- **Coordinate with mathlib experts** - Especially for kernel theory
- **Be prepared to iterate** - Mathlib review can be thorough

---

*Document created: 2025-10-21*
*Based on: Current project status after CondExp.lean completion*
*Next review: After ViaL2 or ViaKoopman completion*
