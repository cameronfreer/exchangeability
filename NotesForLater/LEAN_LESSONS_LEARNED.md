# Lean 4 Lessons Learned & Proposed Improvements

This document captures lessons learned during the de Finetti formalization project, documenting patterns, anti-patterns, and potential improvements to Lean 4 itself.

## Table of Contents
1. [Type Class Resolution Issues](#type-class-resolution-issues)
2. [Tactic Modernization](#tactic-modernization)
3. [Proposed Lean Improvements](#proposed-lean-improvements)
4. [Best Practices Discovered](#best-practices-discovered)

---

## Type Class Resolution Issues

### Issue 1: Anonymous Instance Notation with Sub-σ-Algebras

**Problem:** The anonymous instance notation `‹_›` fails catastrophically when working with sub-σ-algebras in measure theory.

**Manifestation:**
```lean
lemma condExp_mul_pullout
    {m : MeasurableSpace Ω} (hm : m ≤ ‹_›)  -- ❌ BROKEN
    {f g : Ω → ℝ} ... :
    μ[f * g|m] =ᵐ[μ] fun ω => μ[f|m] ω * g ω := by
  exact condExp_stronglyMeasurable_mul_of_bound hm ...
  -- Error: typeclass instance problem is stuck
  --   IsFiniteMeasure ?m.104
```

**Root cause:** The `‹_›` notation is resolved to `m` itself, giving `hm : m ≤ m`, which is mathematically vacuous. Lean cannot distinguish between the sub-σ-algebra and the ambient measurable space.

**Workaround (The `condExpWith` Pattern):**
```lean
lemma condExp_mul_pullout
    {Ω : Type*} {m₀ : MeasurableSpace Ω}  -- ✅ Explicit ambient space
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ m₀)  -- ✅ Explicit inequality
    {f g : Ω → ℝ} ... := by
  -- Provide instances explicitly
  haveI : IsFiniteMeasure μ := inferInstance
  haveI : IsFiniteMeasure (μ.trim hm) := isFiniteMeasure_trim μ hm
  haveI : SigmaFinite (μ.trim hm) := sigmaFinite_trim μ hm

  exact condExp_stronglyMeasurable_mul_of_bound hm ...  -- ✅ Works!
```

**Reference Implementation:** `condExpWith` in `Exchangeability/Probability/CondExp.lean:338`

**Impact:**
- Affects ALL conditional expectation lemmas involving sub-σ-algebras
- Blocked 4 critical proofs in CondExp.lean
- Required explicit instance management throughout the codebase

---

### Issue 2: Trimmed Measure Instance Propagation

**Problem:** When working with `μ.trim hm` (measure restricted to sub-σ-algebra), type class instances don't propagate automatically from the base measure `μ`.

**Manifestation:**
Even with the correct signature, mathlib lemmas fail with:
```
error: failed to synthesize instance
  IsFiniteMeasure (μ.trim hm)
```

**Solution:** Explicit instance provisioning with `haveI`:
```lean
haveI : IsFiniteMeasure (μ.trim hm) := isFiniteMeasure_trim μ hm
haveI : SigmaFinite (μ.trim hm) := sigmaFinite_trim μ hm
```

**Why this is needed:** Mathlib's conditional expectation lemmas internally use `μ.trim hm`, and Lean's type class resolution doesn't automatically derive instances for trimmed measures.

---

## Tactic Modernization

### Issue 3: `fun_prop` Tactic Adoption

**Background:** Lean 4 introduced the `fun_prop` tactic for automated reasoning about function properties (measurability, continuity, etc.), but older code still uses manual composition proofs.

**Manual approach (old style):**
```lean
-- Prove measurability of f ∘ g manually
have : Measurable (f ∘ g) := measurable_f.comp measurable_g
```

**Modern approach with `fun_prop`:**
```lean
-- Let the tactic handle composition automatically
have : Measurable (f ∘ g) := by fun_prop
```

**Benefits discovered:**
- **Reduced boilerplate:** Manual composition chains replaced with single tactic call
- **Better maintainability:** Proofs robust to API changes
- **Clearer intent:** `fun_prop` makes the goal explicit
- **Handles complex compositions:** Automatically chains through multiple levels

**Application in project:**
Applied across multiple files with significant simplification:
- **CondExp.lean (line 123):** Indicator composition
  ```lean
  -- Before: (measurable_const.indicator hB).comp hX
  -- After: by fun_prop
  ```
- **ViaKoopman.lean:** Product measurability (lines 4976, 5240-5243)
- **CesaroToCondExp.lean:** Composition automation with `@[fun_prop]` attribute

**Special technique: Custom dischargers**
```lean
-- Use fun_prop with domain-specific discharger
by fun_prop (disch := measurability)
```

This allows `fun_prop` to use domain-specific tactics for side conditions.

**Etymology:** "disch" = "discharge" - prove and remove subgoals automatically.

**Mechanics:** `fun_prop` decomposes complex function properties into simpler components, then uses the discharger to solve each subgoal.

**Impact:** Saved ~40 lines across codebase by automating compositional measurability proofs.

**Reference commits:**
- `443b96c` - Systematic fun_prop application across codebase
- `037074d` - Comprehensive documentation of disch parameter

---

## Proposed Lean Improvements

### Improvement 1: Better Diagnostics for Anonymous Instance Failures

**Current behavior:** When `‹_›` is resolved incorrectly, Lean gives cryptic errors:
```
error: typeclass instance problem is stuck, it is often due to metavariables
  IsFiniteMeasure ?m.104
```

**Proposed improvement:** Detect when `‹_›` appears in inequality contexts like `m ≤ ‹_›` and warn:
```
warning: Anonymous instance notation `‹_›` used in inequality `m ≤ ‹_›`.
This may resolve to `m ≤ m`, making the hypothesis vacuous.
Consider using an explicit parameter instead: `{m₀ : MeasurableSpace Ω} (hm : m ≤ m₀)`
```

**Rationale:** This would have saved hours of debugging. The error message gave no hint about the root cause.

---

### Improvement 2: Auto-derive Trimmed Measure Instances

**Current behavior:** `IsFiniteMeasure (μ.trim hm)` must be explicitly provided even though it's derivable from `IsFiniteMeasure μ` and `hm : m ≤ m₀`.

**Proposed improvement:** Add instance declarations:
```lean
instance [IsFiniteMeasure μ] {m : MeasurableSpace Ω} (hm : m ≤ m₀) :
    IsFiniteMeasure (μ.trim hm) :=
  isFiniteMeasure_trim μ hm

instance [SigmaFinite μ] {m : MeasurableSpace Ω} (hm : m ≤ m₀) :
    SigmaFinite (μ.trim hm) :=
  sigmaFinite_trim μ hm
```

**Challenge:** These instances require the inequality proof `hm` as a parameter, which doesn't fit Lean's instance resolution model well.

**Alternative:** Enhance type class search to automatically try `*_trim` lemmas when looking for instances on trimmed measures.

---

### Improvement 3: Better Support for Multiple Measurable Space Structures

**Current situation:** When working with multiple measurable spaces on the same type, type class resolution is fragile. The ambient/sub-σ-algebra pattern is common in measure theory but poorly supported.

**Proposed improvement:**
- Dedicated syntax/pattern for sub-structures: `m ⊑ m₀` with special resolution rules
- Automatic instance transfer for trimmed/restricted structures
- Better documentation of this pattern in the Lean reference manual

**Example use case:** Conditional expectation, filtrations, stopping times, adapted processes—all fundamental probability theory concepts requiring this pattern.

---

## Best Practices Discovered

### Practice 1: The `condExpWith` Pattern

**When to use:** Any time you're working with conditional expectation on a sub-σ-algebra.

**Template:**
```lean
def/lemma your_condexp_result
    {Ω : Type*} {m₀ : MeasurableSpace Ω}  -- 1. Explicit ambient space
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ m₀)  -- 2. Explicit sub-algebra
    ... := by
  -- 3. Provide instances explicitly
  haveI : IsFiniteMeasure μ := inferInstance
  haveI : IsFiniteMeasure (μ.trim hm) := isFiniteMeasure_trim μ hm
  haveI : SigmaFinite (μ.trim hm) := sigmaFinite_trim μ hm

  -- 4. Now proceed with your proof
  ...
```

**Reference:** `Exchangeability/Probability/CondExp.lean:338` (`condExpWith` definition)

---

### Practice 2: Avoid Anonymous Instance Notation in Inequalities

**Anti-pattern:**
```lean
{m : MeasurableSpace Ω} (hm : m ≤ ‹_›)  -- ❌ DON'T
```

**Pattern:**
```lean
{m₀ : MeasurableSpace Ω} {m : MeasurableSpace Ω} (hm : m ≤ m₀)  -- ✅ DO
```

**Why:** Anonymous instances can resolve incorrectly in inequality contexts, leading to vacuous hypotheses.

---

### Practice 3: Use Modern Tactics (fun_prop, measurability)

**Prefer automated tactics for standard reasoning:**
```lean
-- Instead of manual composition
have : Measurable (f ∘ g ∘ h) := measurable_f.comp (measurable_g.comp measurable_h)

-- Use fun_prop
have : Measurable (f ∘ g ∘ h) := by fun_prop
```

**When to use custom dischargers:**
```lean
-- For domain-specific side conditions
by fun_prop (disch := measurability)
```

**Why:** Modern tactics are more robust, maintainable, and concise. They adapt to API changes automatically.

---

### Practice 4: Explicit Instance Management with `haveI`

**When working with derived structures** (trimmed measures, restricted σ-algebras, etc.), explicitly provide instances before calling mathlib lemmas:

```lean
haveI : IsFiniteMeasure (μ.trim hm) := isFiniteMeasure_trim μ hm
haveI : SigmaFinite (μ.trim hm) := sigmaFinite_trim μ hm
```

**Why:** Type class resolution doesn't automatically propagate instances to derived structures, even when the derivation is straightforward.

---

## Impact on Project

### Code Affected
- **CondExp.lean:** 4 critical sorries blocked by these issues
  - `integrable_of_bounded_mul`
  - `condExp_abs_le_of_abs_le`
  - `condExp_L1_lipschitz`
  - `condExp_mul_pullout`

### Resolution Time
- **Discovery:** ~2 hours of debugging cryptic type class errors
- **Understanding root cause:** ~30 minutes after finding `condExpWith` pattern
- **Implementation:** ~1 hour to fix all 4 lemmas

### Lessons Applied
- All conditional expectation work now uses the `condExpWith` pattern
- Documented in PROGRESS_SUMMARY.md as critical discovery
- Reference implementation available for future work

---

## Recommendations for Lean 4 Development

1. **Documentation:** Add a section on "Working with Sub-Structures" to the Lean 4 reference manual
   - Cover the `condExpWith` pattern
   - Warn about `‹_›` in inequalities
   - Explain instance management for derived structures

2. **Diagnostics:** Improve error messages for type class resolution failures
   - Detect common anti-patterns (`‹_›` in inequalities)
   - Suggest explicit parametrization when resolution fails

3. **Standard Library:** Consider adding trimmed measure instances to mathlib
   - Either as instances (if possible)
   - Or as a documented pattern with helper tactics

4. **Tooling:** Add linter warning for `‹_›` in inequality contexts
   - Flag potentially problematic uses
   - Suggest explicit alternatives

---

*Document created: 2025-10-21*
*Based on: Session 2 work completing CondExp.lean*
*Primary contributor: Technical insights from debugging type class failures*
