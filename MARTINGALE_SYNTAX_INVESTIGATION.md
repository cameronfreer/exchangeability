# Martingale.lean Syntax Investigation

##Date: 2025-10-12

## Problem

Attempting to create `axiom` or `theorem` declarations with existential quantifiers (`∃`) in the return type consistently fails with:
```
error: Exchangeability/Probability/Martingale.lean:90:8: expected token
```

## Attempted Fixes (All Failed)

1. **Multi-line existential with indentation** (lines 90-92)
   - Error at 90:8 (start of `∃`)

2. **Single-line existential** (all on one line)
   - Error at 90:8 (start of `∃`)

3. **Using `Exists` instead of `∃`** (desugared form)
   - Error at column 20 (lambda syntax)

4. **Different indentation levels** (0, 4, 6 spaces)
   - Error persists at `∃` position

5. **Parentheses around entire existential**
   - Error at opening parenthesis

6. **Existential on same line as `:`**
   - Error at end of line (comma after `ℝ,`)

7. **Changed from `axiom` to `theorem` with `sorry`**
   - Same error - not an axiom-specific issue

## Root Cause Hypothesis

Lean 4's parser may not support existential quantifier syntax in axiom/theorem return type position when:
- The existential body spans multiple lines
- The existential contains complex bracket notation like `StronglyMeasurable[⨅ i, 𝔽 i]`
- Some other syntax requirement I haven't discovered

## Working Patterns Found

From ViaMartingale.lean:488-496, working axiom pattern:
```lean
axiom name
    (params) :
    A =ᵐ[μ] B  -- Simple return type, no existentials
```

From CondExpDeprecated.lean:1137-1139, working lemma pattern:
```lean
lemma name
    (params) :
    (∀ᵐ ω ∂μ, ...) ∧ ...  -- Conjunction without existential wrapper
```

**No working examples found** of:
- Axioms with `∃` in return type
- Theorems with `∃` starting the return type in this codebase

## Alternative Approaches

### Option 1: Opaque Constants (Recommended)
Instead of axiomatizing the full proposition, axiomatize the witness:
```lean
axiom reverse_martingale_limit
    {ι : Type*} [Preorder ι] [IsProbabilityMeasure μ]
    {𝔽 : ι → MeasurableSpace Ω}
    (h_filtration : Antitone 𝔽)
    (h_le : ∀ i, 𝔽 i ≤ (inferInstance : MeasurableSpace Ω))
    {M : ι → Ω → ℝ}
    (h_adapted : ∀ i, StronglyMeasurable[𝔽 i] (M i))
    (h_integrable : ∀ i, Integrable (M i) μ)
    (h_martingale : ∀ i j, i ≤ j → μ[M j | 𝔽 i] =ᵐ[μ] M i)
    (f₀ : Ω → ℝ) (h_f₀_meas : Measurable f₀) (h_f₀_int : Integrable f₀ μ) :
    Ω → ℝ

axiom reverse_martingale_limit_measurable ... :
    StronglyMeasurable[⨅ i, 𝔽 i] (reverse_martingale_limit ...)

axiom reverse_martingale_limit_eq ... :
    μ[f₀ | ⨅ i, 𝔽 i] =ᵐ[μ] (reverse_martingale_limit ...)

axiom reverse_martingale_convergence ... :
    ∀ᵐ ω ∂μ, Tendsto (fun i => M i ω) atTop (𝓝 ((reverse_martingale_limit ...) ω))
```

**Pros:**
- Avoids existential syntax issue
- More flexible for use sites (have direct access to witness)
- Standard pattern in Lean for axiomatizing existence

**Cons:**
- More verbose (4 axioms instead of 1)
- Doesn't match mathematical statement as closely

### Option 2: Ask Lean Community
Post on Lean Zulip with minimal reproduction:
```lean
import Mathlib.Probability.Martingale.Basic
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

axiom test [IsProbabilityMeasure μ] (f : Ω → ℝ) :
    ∃ g : Ω → ℝ, g = f
```

Ask: "Why does `expected token` error occur at the `∃`?"

### Option 3: Wait for Infrastructure
Based on VIAMARTINGALE_BLOCKERS.md, the martingale convergence theory is:
- Not in mathlib v4.24.0
- Would require 500-1000 lines of development
- Active area of mathlib development

Consider:
- Waiting for mathlib to add these theorems natively
- Contributing the theorems to mathlib once syntax issue is resolved
- Using ViaL2 or ViaKoopman proofs instead (both compile)

## Recommendation

**Immediate:** Use Option 1 (opaque constants) to unblock development.

**Follow-up:** Post Option 2 (Zulip) to get expert help on the syntax issue.

**Long-term:** When mathlib adds martingale convergence, replace axioms with proven theorems.

## Files Status

- `Exchangeability/Probability/Martingale.lean`: Created but does not compile
- `Exchangeability/DeFinetti/ViaMartingale.lean`: Compiles, imports blocked until Martingale.lean fixed
- `Exchangeability/Probability/CondExp.lean`: Compiles successfully

## Next Steps

1. Decide on approach (opaque constants vs. community help vs. different proof)
2. If opaque constants: Rewrite Martingale.lean with 4-axiom pattern
3. If community help: Post minimal repro on Lean Zulip
4. Continue work on other axioms in ViaMartingale.lean and CondExp.lean

---
*Investigation completed after systematic debugging (6+ hypotheses tested)*
*See Systematic Debugging skill for process followed*
