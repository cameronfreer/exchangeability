# Sorry Resolution Progress in ViaMartingale.lean

## Summary

**Total Sorries:** 2
**Resolved:** 1
**Remaining:** 1 (deep kernel theory)

---

## ✅ Sorry 1: Norm Bound for Conditional Expectation (RESOLVED)

**Location:** `Exchangeability/DeFinetti/ViaMartingale.lean:1671`

**Goal:** Prove `‖μ[φ|𝔾] ω‖ ≤ 1` where φ is an indicator function.

**Solution:** Used `MeasureTheory.ae_bdd_condExp_of_ae_bdd`
- Lemma: If `|f x| ≤ R` a.e., then `|(μ[f|m]) x| ≤ R` a.e.
- Apply with R = 1 and f = φ (indicator taking values in {0, 1})

**Commit:** `6c7b9fe`

---

## ⚠️ Sorry 2: Kernel Equality from compProd (REMAINING)

**Location:** `Exchangeability/DeFinetti/ViaMartingale.lean:4149`

### Mathematical Statement

**Goal:** Prove `μ[f|σ(ζ)] =ᵐ μ[f|σ(η)]` where f is an indicator function.

**Given:**
1. Joint law equality: `Law(ζ, ξ) = Law(η, ξ)`
2. σ-algebra nesting: `σ(η) ⊆ σ(ζ)`
3. Factorization: `η = φ ∘ ζ` for some measurable φ

**Context in proof:**
- Random variables ζ, η : Ω → Γ
- Random variable ξ : Ω → E
- Function f = (ξ ⁻¹' B).indicator (fun _ => 1) for measurable set B
- Already have: `h_compProd_eq : (μ.map ζ) ⊗ₘ (condDistrib ξ ζ μ) = (μ.map ζ) ⊗ₘ (condDistrib ξ η μ)`

### Why This Is Deep

This requires connecting **conditional expectations** (measure-theoretic) with **conditional distributions** (kernel-theoretic). The infrastructure needed:

1. **Representation lemma**: Express `μ[f|σ(ζ)]` as `∫ f dCondDistrib`
2. **Kernel uniqueness**: `compProd` equality → kernel a.e. equality → integral equality
3. **Pullback/composition**: Handle η = φ ∘ ζ with σ(η) ⊆ σ(ζ)

### Current Infrastructure Work

**File:** `Exchangeability/Probability/ConditionalKernel.lean` (work-in-progress)

**Planned lemmas:**
```lean
-- Step 1: Representation
lemma condExp_indicator_eq_integral_condDistrib
    (ζ : Ω → Γ) (ξ : Ω → E) (B : Set E) :
    μ[(ξ ⁻¹' B).indicator 1 | σ(ζ)]
      =ᵐ (fun ω => ∫ e, B.indicator 1 e ∂(condDistrib ξ ζ μ (ζ ω)))

-- Step 2: Kernel uniqueness from compProd
lemma condDistrib_ae_eq_of_compProd_eq
    (h_law : μ.map (ζ, ξ₁) = μ.map (ζ, ξ₂)) :
    condDistrib ξ₁ ζ μ =ᵐ[μ.map ζ] condDistrib ξ₂ ζ μ

-- Step 3: Integral equality from kernel equality
lemma integral_condDistrib_eq_of_ae_eq
    (h_kernel_eq : κ₁ =ᵐ κ₂) :
    (fun ω => ∫ f ∂κ₁(ζ ω)) =ᵐ (fun ω => ∫ f ∂κ₂(ζ ω))

-- Step 4: Main theorem
theorem condExp_eq_of_joint_law_eq
    (h_law : Law(ζ, ξ) = Law(η, ξ))
    (h_le : σ(η) ⊆ σ(ζ))
    (hηfac : η = φ ∘ ζ) :
    μ[f|σ(ζ)] =ᵐ μ[f|σ(η)]
```

**Status:** Skeleton created, lemmas have sorries

### Key Mathlib Lemmas to Use

- `ProbabilityTheory.compProd_map_condDistrib` - connects condDistrib to compProd
- `ProbabilityTheory.Kernel.compProd_eq_iff` - kernel uniqueness from compProd equality
- `ProbabilityTheory.condExp_ae_eq_integral_condExpKernel` - condExp as kernel integral
- `ProbabilityTheory.condDistrib_apply_ae_eq_condExpKernel_map` - connects condDistrib to condExpKernel

### Path Forward

**Option A (Current):** Build full kernel infrastructure
- Pros: Mathematically complete, reusable
- Cons: Significant work (hundreds of lines estimated)
- Status: Started in ConditionalKernel.lean

**Option B (Alternative):** Direct proof using existing machinery
- Try to use tower property + uniqueness more directly
- Avoid building all the intermediate infrastructure
- May be possible if we can work more directly with the compProd equality

**Recommended Next Steps:**
1. Complete the representation lemma using `condDistrib_apply_ae_eq_condExpKernel_map`
2. Prove kernel uniqueness using `compProd_eq_iff`
3. Connect the pieces with factorization η = φ ∘ ζ
4. Apply in ViaMartingale.lean to kill the sorry

---

## Build Status

**Current:** Full project builds with 2 sorries total (both in ViaMartingale.lean)
- Sorry 1: RESOLVED ✅
- Sorry 2: Infrastructure in progress ⚠️

**Dependencies:** No new external dependencies needed, using existing mathlib lemmas
