# Remaining Sorries in ViaL2.lean (32 total)

## Category 1: L¹ Uniqueness & Endpoint Limits (9 sorries)

### In atBot L¹ uniqueness proof:
- **Line 3229**: Infimum of values all ≤ 1 is also ≤ 1 (boundedness)
- **Line 3234**: iInf of AEStronglyMeasurable functions is AEStronglyMeasurable

### In atTop L¹ uniqueness proof:
- **Line 3377**: Integrability + algebra (integral equation)
- **Line 3392**: Supremum of values all ≤ 1 is also ≤ 1 (boundedness)
- **Line 3395**: iSup of AEStronglyMeasurable functions is AEStronglyMeasurable

### Endpoint limit helper lemmas:
- **Line 3585**: `tendsto_integral_indicator_Iic` - DCT for indicator functions
- **Line 3628**: `alphaIic_tendsto_zero_at_bot` - pointwise limit at -∞
- **Line 3656**: `alphaIic_tendsto_one_at_top` - pointwise limit at +∞

### CDF limits:
- **Line 3685**: `cdf_from_alpha` tends to 0 at -∞
- **Line 3696**: `cdf_from_alpha` tends to 1 at +∞

**Difficulty**: Medium - mostly standard measure theory

---

## Category 2: Identification Lemma (4 sorries) ⭐ KEY RESULT

- **Line 2685**: `alphaIicCE_measurable` - conditional expectation is measurable (BorelSpace issue)
- **Line 2829**: Clipping to [0,1] preserves L¹ convergence
- **Line 2839**: **DEEP RESULT**: Cesàro averages → conditional expectation (reverse martingale / ergodic theorem)
- **Line 2851**: Uniqueness of L¹ limits
- **Line 2858**: Reference to alphaIicCE_measurable (duplicate)

**Difficulty**: Hard for line 2839 (deep ergodic theory), Easy-Medium for others

---

## Category 3: Directing Measure Construction (10 sorries)

These form a dependency chain - later ones depend on earlier ones:

### Core construction:
- **Line 2535**: `deFinetti_viaL2` - main theorem packaging
- **Line 3763**: `directing_measure_isProbabilityMeasure` - total mass = 1
- **Line 3806**: `directing_measure_integral` - integral formula

### Measurability (deep):
- **Line 3966**: `directing_measure_measurable` - **VERY DEEP**: ω ↦ ν(ω) is measurable
  (parameter-dependent measures)

### Consequences (depend on above):
- **Line 3868**: IsFiniteMeasure instance
- **Line 3878**: univ measure = 1
- **Line 4006**: `directing_measure_marginal` - integral identification
- **Line 4017**: `deFinetti_equivalence` - full equivalence theorem

**Difficulty**: Very Hard - requires deep measure theory

---

## Category 4: Reverse Martingale Infrastructure (2 sorries)

- **Line 2371**: `reverse_martingale_subsequence_convergence` - integrability hypothesis
  (Gap in hypothesis: need explicit `Integrable` assumption)
- **Line 4065**: Related to convergence

**Difficulty**: Medium - formalization issue, not mathematical difficulty

---

## Non-Issue (1 item):
- **Line 1736**: Just a comment, not an actual sorry!

---

## RECOMMENDED PRIORITY ORDER:

### **TIER 1: Do These First** (Easiest, High Impact)
1. **Line 2851**: L¹ uniqueness - standard analysis
2. **Lines 3229, 3392**: Boundedness (inf ≤ 1, sup ≤ 1) - pure real analysis
3. **Lines 3234, 3395**: Measurability of inf/sup - search mathlib
4. **Line 2829**: Clipping preserves L¹ limits - continuity argument

### **TIER 2: Medium Difficulty**
5. **Line 2685**: alphaIicCE_measurable - need to solve BorelSpace issue
6. **Line 3377**: Integrability + algebra
7. **Lines 3585, 3628, 3656**: Endpoint limits - dominated convergence
8. **Lines 3685, 3696**: CDF limits - follow from above
9. **Line 2371**: Fix integrability hypothesis

### **TIER 3: Hard (Deep Math)**
10. **Line 2839**: ⭐ **CRITICAL** - Cesàro → conditional expectation
    - This is the reverse martingale / ergodic convergence theorem
    - Might need to prove or axiomatize
11. **Lines 3763, 3806**: Directing measure properties
12. **Line 3966**: Measurability of parameter-dependent measures (VERY DEEP)

### **TIER 4: Depends on Tier 3**
13. Everything else in Category 3 (depends on earlier results)

---

## QUICK WINS (Start Here! 🎯):

If you want to reduce the sorry count quickly:
1. **L¹ uniqueness** (line 2851) - triangle inequality argument
2. **Boundedness** (lines 3229, 3392) - direct from definition
3. **Clipping** (line 2829) - Lipschitz continuity of max/min

These 4 sorries are genuinely straightforward and don't require deep theory!

---

## Notes on Key Blockers:

**The Critical Sorry (Line 2839)**: This is proving that Cesàro averages of f(X_i) converge in L¹ to E[f(X_0)|tailSigma]. This is:
- The reverse martingale convergence theorem, OR
- A consequence of the mean ergodic theorem for exchangeable sequences

This is a **deep result** that may need to be:
- Proved from scratch (substantial work)
- Found in mathlib (if it exists)
- Taken as an axiom for exchangeable sequences
- Proved using the ergodic theory machinery

**The Very Deep Sorry (Line 3966)**: Measurability of parameter-dependent measures ω ↦ ν(ω) is a research-level topic in measure theory. This may need to be axiomatized.
