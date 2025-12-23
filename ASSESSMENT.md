# Project Assessment - December 23, 2025

## Build Status

| Component | Status | Notes |
|-----------|--------|-------|
| Main project | ✅ BUILDS | 3220+ jobs |
| TripleLawDropInfo.lean | ⚠️ BUILDS | Has 1 sorry (h_sq_eq step) |
| ViaMartingale.lean | ⚠️ BUILDS | Has 1 sorry (depends on TripleLawDropInfo) |
| ViaKoopman approach | ⚠️ BUILDS | Has 2 custom axioms |

## Main Theorem Status

**Theorem:** `conditionallyIID_of_contractable` (ViaMartingale approach)

**Axioms:**
```
[propext, sorryAx, Classical.choice, Quot.sound]
```

**Status:** INCOMPLETE (depends on `sorryAx`)

## Critical Path Sorries

### 1. TripleLawDropInfo.lean:291 - h_sq_eq
- **Declaration:** `condExp_indicator_eq_of_law_eq_of_comap_le`
- **Purpose:** Core Kallenberg 1.3 lemma (L² argument)
- **Blocking step:** `h_sq_eq : ∫ μ₁² dμ = ∫ μ₂² dμ`
- **COMPLETED steps:**
  - ✅ Tower property (h_tower)
  - ✅ Boundedness [0,1] (hμ₁_bdd, hμ₂_bdd)
  - ✅ Integrability facts (hμ₁_int, hμ₂_int, etc.)
  - ✅ Cross term E[μ₂μ₁] = E[μ₁²] (h_cross)
  - ✅ L² = 0 computation (h_L2_zero)
  - ✅ L² = 0 implies a.e. equality (h_diff_zero)
- **TODO:** h_sq_eq via Doob-Dynkin + set-integral uniqueness
  - Mathematical proof is documented in the file
  - API issues with MeasurableSpace instance shadowing

### 2. ViaMartingale.lean:1723 - h_CI_UXrW
- **Declaration:** `condExp_Xr_indicator_eq_of_contractable`
- **Purpose:** Establishes conditional independence `CondIndep μ U (X r) W`
- **Depends on:** Item 1 above

## Proof Structure (TripleLawDropInfo)

The Kallenberg 1.3 proof is **95% complete**:

```
condExp_indicator_eq_of_law_eq_of_comap_le:
├─ Step 1: Tower property ........................... ✅ DONE
├─ Step 2: Boundedness [0,1] ........................ ✅ DONE
├─ Step 3: Integrability ............................ ✅ DONE
├─ Step 4a: Cross term E[μ₂μ₁] = E[μ₁²] ............. ✅ DONE
├─ Step 4b: Square equality E[μ₁²] = E[μ₂²] ......... ❌ TODO (h_sq_eq)
│   └─ Doob-Dynkin factorization approach documented
├─ Step 5: L² = 0 computation ....................... ✅ DONE
└─ Step 6: L² = 0 ⟹ μ₂ = μ₁ a.e. .................. ✅ DONE
```

## h_sq_eq Proof Strategy (Documented in File)

**Goal:** `∫ ω, μ₁ ω * μ₁ ω ∂μ = ∫ ω, μ₂ ω * μ₂ ω ∂μ`

**Approach:**
1. **Doob-Dynkin factorization** (StronglyMeasurable.exists_eq_measurable_comp):
   - μ₁ = g₁ ∘ W for some measurable g₁ : γ → ℝ
   - μ₂ = g₂ ∘ W' for some measurable g₂ : γ → ℝ

2. **Show g₁ = g₂ ρ-a.e.** (Integrable.ae_eq_of_forall_setIntegral_eq):
   - ∫_B g₁ dρ = ∫_{W⁻¹B} φ dμ (change of variables + condExp)
   - ∫_B g₂ dρ = ∫_{W'⁻¹B} φ dμ (similarly)
   - ∫_{W⁻¹B} φ dμ = ∫_{W'⁻¹B} φ dμ (from pair law h_law)

3. **Push squares through integral_map:**
   `∫ μ₁² dμ = ∫ g₁² dρ = ∫ g₂² dρ = ∫ μ₂² dμ`

**Technical blockers:**
- MeasurableSpace instance shadowing from `let mW' := ...`
- StronglyMeasurable.pow_const dot notation not working
- Requires explicit @ notation throughout

## Other Sorries (Not Blocking Main Theorem)

| File | Line | Declaration |
|------|------|-------------|
| CondIndep.lean | 582, 607, 707, 761 | Various helpers |
| TimeReversalCrossing.lean | 79 | `timeReversal_crossing_bound` |

## Custom Axioms (ViaKoopman Only)

| File | Line | Axiom |
|------|------|-------|
| ViaKoopman/Infrastructure.lean | 805 | `condexp_precomp_iterate_eq_of_invariant` |
| ViaKoopman/Infrastructure.lean | 920 | `naturalExtension_exists` |

## Next Steps

1. **Complete h_sq_eq** in TripleLawDropInfo.lean:291
   - Work around API issues with explicit @ notation
   - Or restructure to avoid MeasurableSpace let definitions

2. **Fill h_CI_UXrW** in ViaMartingale.lean:1723
   - Should follow automatically once item 1 is complete

## Recently Completed Work (This Session)

1. ✅ Added imports for FactorsThrough and AEEqOfIntegral
2. ✅ Defined ρ alias before MeasurableSpace let definitions
3. ✅ Implemented full L² argument structure (Steps 1-6 except h_sq_eq)
4. ✅ Documented h_sq_eq proof approach with detailed TODO
5. ✅ Project builds successfully (3220+ jobs)
