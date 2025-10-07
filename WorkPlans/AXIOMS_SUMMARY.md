# Axioms Summary - Quick Reference

**Last Updated:** 2025-10-06

## Statistics
- **Total Axioms:** 12 `axiom` declarations
- **Total Sorry:** 44 `sorry` statements  
- **Total Code:** ~5,000 lines across 14 files
- **Completion:** ~70% complete/provable

---

## Axioms by Category

### Category 1: Infrastructure (Replaceable)
**Status:** Have clear mathlib replacements, blocked by technical issues

| File | Line | Name | Difficulty | ETA |
|------|------|------|------------|-----|
| `InfiniteProduct.lean` | 82 | `iidProduct` | Medium | 2-3 weeks |
| `InfiniteProduct.lean` | 84 | `iidProduct_isProbability` | Low | 1 week |
| `InfiniteProduct.lean` | 94 | `cylinder_fintype` | Low | 1 week |
| `InfiniteProduct.lean` | 135 | `perm_eq` | Low | 1 week |

**Blocker:** Universe polymorphism in mathlib's `Kernel.traj`

---

### Category 2: Standard Probability Theory (Provable)
**Status:** Should exist in mathlib or be straightforward to prove

| File | Line | Name | Difficulty | ETA |
|------|------|------|------------|-----|
| `CommonEnding.lean` | 254 | `condExp_indicator_eq_measure` | Low | 1 week |
| `CommonEnding.lean` | 281 | `integral_prod_eq_prod_integral` | Medium | 2 weeks |
| `MartingaleApproach.lean` | 166 | `condexp_convergence` | High | 4-6 weeks |

**Approach:** Use mathlib's conditional expectation + Fubini

---

### Category 3: Measure-Theoretic (Technical)
**Status:** Require careful formalization of measure transport

| File | Line | Name | Difficulty | ETA |
|------|------|------|------------|-----|
| `CommonEnding.lean` | 150 | `isTailMeasurable_iff_shift_invariant` | Medium | 2-3 weeks |
| `CommonEnding.lean` | 178 | `exchangeable_implies_shift_invariant` | Medium | 2-3 weeks |

**Approach:** Define path-space pushforward, prove invariance

---

### Category 4: Core Theorems (Goals)
**Status:** Main results to be proved

| File | Line | Name | Difficulty | ETA |
|------|------|------|------------|-----|
| `CommonEnding.lean` | 308 | `fidi_eq_avg_product` | High | 3-4 weeks |
| `DeFinetti.lean` | 171 | `conditionallyIID_of_contractable` | High | 4-6 weeks |

**Approach:** Assemble from all infrastructure pieces

---

## Sorry Statements by File

| File | Count | Difficulty | Priority |
|------|-------|------------|----------|
| `L2Proof.lean` | 16 | Medium | Low (alternative approach) |
| `KoopmanApproach.lean` | 7 | Medium-High | **High** |
| `CondExp.lean` | 6 | Low-Medium | **High** |
| `CommonEnding.lean` | 5 | Medium-High | **High** |
| `InvariantSigma.lean` | 4 | Low-Medium | **High** |
| `MartingaleApproach.lean` | 4 | Medium | Medium |
| `DeFinetti.lean` | 2 | Low | Low (API only) |

---

## Critical Path to Completion

### Week 1-2: Easy Wins ✓
- [ ] Fill 8 "low difficulty" `sorry` statements
- [ ] Complete orthogonal projection properties
- [ ] Prove L² martingale identification

### Week 3-5: Kernel Construction 🔨
- [ ] Build `rcdKernel` using `condExpKernel`
- [ ] Prove kernel measurability and probability properties
- [ ] Establish shift-invariance of conditional distributions

### Week 6-9: Measure Theory 📐
- [ ] Replace infinite product axioms
- [ ] Prove tail measurability lemmas
- [ ] Complete product integral formulas
- [ ] Prove `fidi_eq_avg_product`

### Week 10-15: Assembly 🎯
- [ ] Complete common ending proof
- [ ] Prove `conditionallyIID_of_contractable` (main theorem)
- [ ] Verify all axioms resolved

---

## Next 3 Actions

1. **Fill `InvariantSigma.lean` lines 616, 765-766**
   - Apply `Submodule.orthogonalProjection_mem_subspace_eq_self`
   - Should take 1-2 hours
   
2. **Investigate `condExpKernel` API**
   - Read mathlib documentation
   - Test with `StandardBorelSpace` instances
   - Should take 2-4 hours
   
3. **Prove `integral_prod_eq_prod_integral`**
   - Use mathlib's Fubini theorem
   - Should take 1-2 days

---

## Dependencies Graph

```
Main Theorem (conditionallyIID_of_contractable)
    ↓
fidi_eq_avg_product (Common Ending)
    ↓
├─→ rcdKernel construction (Koopman Approach)
│       ↓
│   ├─→ condExpKernel (mathlib) ✓
│   └─→ StandardBorelSpace instances ✓
│
├─→ integral_prod_eq_prod_integral
│       ↓
│   └─→ Fubini theorem (mathlib) ✓
│
├─→ condExp_indicator_eq_measure
│       ↓
│   └─→ setIntegral_condExp (mathlib) ✓
│
└─→ isTailMeasurable_iff_shift_invariant
        ↓
    └─→ Measure transport theory
```

---

## Risk Assessment

### Low Risk (Straightforward)
- ✅ Orthogonal projection lemmas
- ✅ L² identification
- ✅ Product integral formulas
- ✅ Conditional expectation properties

### Medium Risk (Requires Work)
- ⚠️ Kernel construction (API learning curve)
- ⚠️ Tail measurability (formalization complexity)
- ⚠️ Product measure axioms (universe issues)

### High Risk (May Need Help)
- 🔴 Reverse martingale convergence (may not be in mathlib)
- 🔴 StandardBorel instances (may need to add)

---

## When to Ask for Help

**Ask on Zulip if:**
1. Cannot find `condExpKernel` documentation after 4 hours
2. Universe issues with `iidProduct` unsolved after 1 week
3. `StandardBorelSpace` instances don't exist for `ℕ → α`
4. Reverse martingale convergence not found in mathlib

**Ask mathlib maintainers if:**
1. Need to upstream lemmas (after proving them)
2. Need new instances or API improvements
3. Want to contribute de Finetti theorem to mathlib

---

## Success Metrics

**Month 1 Target:** 
- All Phase 1 `sorry` statements filled (8 items)
- `rcdKernel` construction complete
- 90% of code proven or trivially provable

**Month 2 Target:**
- Product measure axioms replaced
- Common ending 75% complete
- Main theorem proof sketch verified

**Month 3 Target:**
- All axioms resolved
- Main de Finetti theorem proved
- Ready for mathlib contribution

---

## Conclusion

**The project is in excellent shape.** Most axioms are placeholders for standard results, and the proof architecture is sound. Estimated 10-15 weeks to full completion with focused effort.

**Key Insight:** The hard mathematical work is done. What remains is primarily:
1. Learning mathlib APIs (especially kernels)
2. Connecting existing pieces together
3. Filling routine technical details

**Recommendation:** Focus on Koopman approach first (most complete), then backfill alternatives if desired.
