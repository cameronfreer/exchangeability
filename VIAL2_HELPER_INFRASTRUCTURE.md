# ViaL2 Helper Infrastructure Plan

**Date:** 2025-10-19
**Status:** ViaL2.lean builds with 19 sorries, needs helper implementations

## Overview

ViaL2.lean currently has **11 axioms** serving as helper placeholders. These need to be implemented or proven to complete the L² proof of de Finetti's theorem.

## Helper Categories

### Category 1: L¹ Convergence (Lines 1544-1586)

#### 1.1 `subseq_ae_of_L1` (Line 1549)
**Statement:** L¹ convergence implies a.e. convergence along a subsequence
```lean
axiom subseq_ae_of_L1
  {Ω : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  (alpha alpha_inf : Ω → ℝ)
  (h_alpha_meas : Measurable alpha)
  (h_alpha_inf_meas : Measurable alpha_inf)
  (h_L1_conv : ∀ ε > 0, ∫ ω, |alpha ω - alpha_inf ω| ∂μ < ε) :
  alpha =ᵐ[μ] alpha_inf
```

**Approach:**
- This is a standard result: if ∫|f - g| = 0 then f = g a.e.
- Use `MeasureTheory.ae_eq_of_forall_setIntegral_eq` or similar
- Key lemma: `integral_eq_zero_iff_of_nonneg`

**mathlib search:** Look for `ae_eq_of_integral_eq_zero`

**Difficulty:** Easy - Should exist in mathlib or be 1-line proof

---

#### 1.2 `cesaro_to_condexp_L1` (Line 1563) **KEY HELPER**
**Statement:** Cesàro averages converge to conditional expectation in L¹
```lean
axiom cesaro_to_condexp_L1
  {Ω : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {X : ℕ → Ω → ℝ} (hX_contract : Contractable μ X)
  (hX_meas : ∀ i, Measurable (X i))
  (f : ℝ → ℝ) (hf_meas : Measurable f) (hf_bdd : ∀ x, |f x| ≤ 1) :
  ∀ ε > 0, ∃ (M : ℕ), ∀ (m : ℕ), m ≥ M →
    ∫ ω, |(1 / (m : ℝ)) * ∑ i : Fin m, f (X i ω) -
           (μ[(f ∘ X 0) | tailSigma X] ω)| ∂μ < ε
```

**Mathematical Content:**
- For contractable (exchangeable) sequences, Cesàro averages converge to tail-σ-algebra conditional expectation
- This is the **Mean Ergodic Theorem** for stationary processes
- Equivalent to **Reverse Martingale Convergence Theorem**

**Dependencies:**
- Contractable → Exchangeable (done)
- Exchangeable → Stationary under time shift
- Apply mean ergodic theorem or reverse martingale convergence

**Proof Strategy:**
1. Use contractability to show X is "essentially" stationary
2. Form the reverse martingale `Mₙ = E[f(X₀) | σ(X_n, X_{n+1}, ...)]`
3. Apply reverse martingale convergence: `Mₙ → E[f(X₀) | tail-σ]` a.e. and in L¹
4. Show Cesàro averages equal these reverse martingale values (up to L¹ error)

**mathlib resources:**
- Check `Mathlib.Probability.Martingale.Convergence` (if it exists)
- Ergodic theory modules
- Birkhoff ergodic theorem lemmas

**Difficulty:** Hard - This is a deep theorem. Options:
- **Option A:** Find existing mathlib result
- **Option B:** Build from martingale convergence (if available)
- **Option C:** Keep as axiom, cite Kallenberg/Durrett as reference

---

#### 1.3 `tendsto_integral_indicator_Iic` (Line 1576)
**Statement:** Integral continuity for indicators under pointwise convergence
```lean
axiom tendsto_integral_indicator_Iic
  {Ω : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ) (t : ℝ)
  (hXn_meas : ∀ n, Measurable (Xn n)) (hX_meas : Measurable (X))
  (hae : ∀ᵐ ω ∂μ, Tendsto (fun n => Xn n ω) atTop (𝓝 (X ω))) :
  Tendsto (fun n => ∫ ω, (Set.Iic t).indicator (fun _ => (1 : ℝ)) (Xn n ω) ∂μ)
          atTop
          (𝓝 (∫ ω, (Set.Iic t).indicator (fun _ => (1 : ℝ)) (X ω) ∂μ))
```

**Approach:**
- This is **Dominated Convergence Theorem** (DCT)
- Indicators are bounded by 1, so dominance condition is satisfied
- Pointwise a.e. convergence `Xn → X` implies `1_{≤t}(Xn) → 1_{≤t}(X)` a.e. (except at discontinuity point t)

**Proof:**
1. Indicator functions converge a.e.: `1_{≤t}(Xn ω) → 1_{≤t}(X ω)` for ω where `X ω ≠ t`
2. Bounded by integrable function: `|1_{≤t}(·)| ≤ 1`
3. Apply DCT: `∫ 1_{≤t} ∘ Xn → ∫ 1_{≤t} ∘ X`

**mathlib:** `MeasureTheory.tendsto_integral_of_dominated_convergence`

**Difficulty:** Medium - Need to handle discontinuity at t (measure zero set)

---

### Category 2: CDF and Stieltjes Functions (Lines 3642-3697)

#### 2.1 `cdf_from_alpha_limits` (Line 3647)
**Statement:** The constructed CDF has correct limits
```lean
axiom cdf_from_alpha_limits
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
  (hX_meas : ∀ i, Measurable (X i))
  (hX_L2 : ∀ i, MemLp (X i) 2 μ)
  (ω : Ω) :
  Tendsto (cdf_from_alpha X hX_contract hX_meas hX_L2 ω) atBot (𝓝 0) ∧
  Tendsto (cdf_from_alpha X hX_contract hX_meas hX_L2 ω) atTop (𝓝 1)
```

**Approach:**
- `cdf_from_alpha` is built from `alphaIic` values
- Need to show:
  - As t → -∞: P(X ≤ t) → 0
  - As t → +∞: P(X ≤ t) → 1
- Use monotone convergence and continuity of probability

**Dependencies:**
- Lines 3608-3640: `alphaIic_tendsto_zero` and `alphaIic_tendsto_one`

**Difficulty:** Medium - Requires monotone convergence arguments

---

### Category 3: Directing Measure (Lines 3750-3849)

#### 3.1 `directing_measure_isProbabilityMeasure` (Line 3754)
**Statement:** The directing measure is a probability measure
```lean
axiom directing_measure_isProbabilityMeasure
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  (X : ℕ → Ω → ℝ) (hX_contract : Contractable μ X)
  (hX_meas : ∀ i, Measurable (X i))
  (hX_L2 : ∀ i, MemLp (X i) 2 μ)
  (ω : Ω) :
  IsProbabilityMeasure (directing_measure X hX_contract hX_meas hX_L2 ω)
```

**Approach:**
- directing_measure is built from `cdf_from_alpha` via `StieltjesFunction.measure`
- Need to show: `ν(ℝ) = 1`
- Uses: `cdf_from_alpha ω +∞ = 1` (from 2.1 above)

**Difficulty:** Easy once 2.1 is done

---

#### 3.2 Other Directing Measure Axioms
- `clip01_1Lipschitz` (Line 3806) - Trivial Lipschitz property
- `l1_convergence_under_clip01` (Line 3814) - Lipschitz functions preserve convergence
- `directing_measure_eval_measurable` (Line 3829) - Technical measurability
- `directing_measure_identification` (Line 3838) - Integration formula
- `alpha_is_conditional_expectation_packaged` (Line 3849) - Main identification

**These all build on the previous helpers and the monotone class theorem application**

---

## Implementation Priority

### Tier 1: Foundation (Relatively Easy)
1. ✅ `subseq_ae_of_L1` - Should exist in mathlib or be 1-liner
2. ⏳ `clip01_1Lipschitz` - Trivial proof
3. ⏳ `directing_measure_isProbabilityMeasure` - Easy once CDFs work

### Tier 2: Convergence (Medium)
4. ⏳ `tendsto_integral_indicator_Iic` - Dominated convergence application
5. ⏳ `cdf_from_alpha_limits` - Monotone convergence
6. ⏳ `alphaIic_tendsto_zero` / `alphaIic_tendsto_one` - Monotone limits

### Tier 3: Deep Theory (Hard - Consider keeping as axioms)
7. ❌ `cesaro_to_condexp_L1` - **Mean Ergodic Theorem** - Very hard
8. ❌ Directing measure construction - Requires Carathéodory extension theory
9. ❌ Monotone class applications - Requires functional monotone class theorem

---

## Recommended Approach

### Short Term (Now)
1. Implement Tier 1 helpers (easy wins)
2. Document proof sketches for Tier 2 helpers
3. Search mathlib thoroughly for Tier 3 results

### Medium Term
1. Attempt Tier 2 helpers using DCT and monotone convergence
2. For `cesaro_to_condexp_L1`: Search literature for Lean formalizations of:
   - Reverse martingale convergence
   - Mean ergodic theorem
   - Birkhoff ergodic theorem

### Long Term
1. Either:
   - **Option A:** Keep deep results as well-documented axioms with literature citations
   - **Option B:** Collaborate with Lean community to build ergodic theory infrastructure
   - **Option C:** Wait for mathlib ergodic theory development

---

## Alternative: ViaKoopman Approach

**Note:** ViaKoopman.lean uses the Koopman/ergodic approach which *also* needs these results. However, it has **6 type class compilation fixes** (3-6 hour estimate) that are more tractable than these deep measure theory results.

Consider working on ViaKoopman's type class fixes as a parallel track while the ergodic theory infrastructure is being built.

---

## Files to Create

1. `Exchangeability/Probability/ConvergenceHelpers.lean` - L¹ convergence utilities
2. `Exchangeability/Probability/CDFHelpers.lean` - CDF and Stieltjes function properties
3. `Exchangeability/Ergodic/MeanErgodicTheorem.lean` - Ergodic theory results (if possible)

---

## Summary

**Total helpers needed:** 11
**Easy (Tier 1):** 3
**Medium (Tier 2):** 3
**Hard (Tier 3):** 5

**Estimated time:**
- Tier 1: 2-4 hours
- Tier 2: 8-12 hours
- Tier 3: 20-40 hours (or keep as axioms)

**Recommendation:** Start with Tier 1, document Tier 2 strategies, defer Tier 3 pending mathlib developments.
