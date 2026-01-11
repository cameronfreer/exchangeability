# Infrastructure Overlap Analysis: exchangeability vs brownian-motion

> **Status:** Exploratory recommendations/ideas for potential collaboration
>
> **Date:** January 2026 (updated with 4.27.0-rc1)
>
> **Repository:** https://github.com/RemyDegenne/brownian-motion

## Summary

Both projects formalize probability theory in Lean 4 with significant infrastructure overlap. The **brownian-motion** project (RemyDegenne) focuses on constructing Brownian motion and stochastic integration, while **exchangeability** focuses on de Finetti's theorem and conditional i.i.d. sequences. Despite different goals, they share ~40-50% infrastructure overlap in foundational areas.

---

## High-Overlap Areas (Strong Candidates for Sharing)

### 1. Projective Limit / Kolmogorov Extension Machinery

| brownian-motion | exchangeability |
|-----------------|-----------------|
| `ProjectiveLimit.lean`: `gaussianProjectiveFamily`, `gaussianLimit` | `InfiniteProduct.lean`: `iidProjectiveFamily`, `iidProduct` |
| Constructs BM as projective limit of finite Gaussian measures | Constructs i.i.d. sequences as projective limit of finite products |
| Uses mathlib's `IsProjectiveMeasureFamily` | Uses mathlib's `IsProjectiveMeasureFamily` |

**Overlap:** Both use identical mathlib infrastructure (`Measure.infinitePi`, Kolmogorov extension). The specific projective families differ (Gaussian vs product), but the machinery is the same.

**Recommendation:** No duplication needed—both correctly use mathlib upstream.

---

### 2. Martingale Theory

| brownian-motion | exchangeability |
|-----------------|-----------------|
| `Auxiliary/Martingale.lean`: congr lemmas, convex composition, submartingale operations | `Probability/Martingale/`: Reverse.lean, Convergence.lean, Crossings.lean, OrderDual.lean |
| Forward martingale focus | **Reverse martingale focus** (for de Finetti) |
| `Martingale.indicator`, `Submartingale.monotone_convex_comp` | `revFiltration`, `revCEFinite_martingale`, reverse martingale convergence |

**Overlap:** Both extend mathlib's martingale theory. Different directions:
- BM needs: forward martingales, submartingale inequalities, optional sampling
- exchangeability needs: **time-reversed martingales** (filtration reversal), Lévy convergence

**Potential sharing:** The reverse martingale infrastructure in exchangeability could benefit BM's stochastic integration (e.g., for backward stochastic differential equations).

---

### 3. Conditional Expectation Helpers

| brownian-motion | exchangeability |
|-----------------|-----------------|
| `Auxiliary/MeasureTheory.lean`: covariance, variance helpers, sigma-algebra comap | `Probability/CondExp*.lean`: 4 top-level + 3 in CondExpHelpers/ |
| `covariance_fun_add_*`, `variance_pi` | `condexp_indicator_eq_of_pair_law_eq`, `condExp_L1_lipschitz`, `condExp_mul_pullout` |
| Independence & set integral factorization | Distributional equality ⇒ condexp equality (core bridge lemma) |

**Overlap:** Both projects build condexp helper lemmas not in mathlib.

**High-value exchangeability lemmas for BM:**
- `condexp_indicator_eq_of_pair_law_eq`: Bridge from distributional equality to condexp equality
- `condExp_L1_lipschitz`: L¹ nonexpansiveness (useful for approximation arguments)
- `condExp_mul_pullout`: Pull-out property for bounded factors

**Recommendation:** These could be upstreamed to mathlib; both projects would benefit.

---

### 4. Filtration Infrastructure

| brownian-motion | exchangeability |
|-----------------|-----------------|
| `Auxiliary/Adapted.lean`: `Adapted`, `ProgMeasurable`, right-continuous adaptedness | `Tail/TailSigma.lean`, `ShiftInvariantMeasure.lean`, `CondExpShiftInvariance.lean`: `tailFamily`, `tailProcess`, reverse filtrations |
| `Adapted.progMeasurable_of_rightContinuous` | `tailProcess_eq_iInf_revFiltration` |
| Forward filtrations, progressive measurability | **Tail σ-algebras**, shift invariance |

**Overlap:** Complementary rather than duplicate.
- BM: Increasing filtrations (natural filtration of BM)
- exchangeability: Decreasing filtrations (tail σ-algebra as intersection)

**Potential sharing:** The tail σ-algebra machinery could be useful for BM's asymptotic theory (tail events of BM, 0-1 laws).

---

### 5. Stopping Times & Optional Sampling

| brownian-motion | exchangeability |
|-----------------|-----------------|
| `Auxiliary/IsStoppingTime.lean`: `IsStoppingTime`, infimum of stopping times | Limited stopping time usage |
| `Auxiliary/StoppedProcess.lean`: stopped processes | Not present |
| `StochasticIntegral/OptionalSampling.lean`: optional sampling theorem | Not present |

**Overlap:** **Minimal.** exchangeability doesn't need stopping times for de Finetti.

---

### 6. Lp Space Helpers

| brownian-motion | exchangeability |
|-----------------|-----------------|
| `StochasticIntegral/SquareIntegrable.lean`, `DoobLp.lean` | `Probability/LpNormHelpers.lean`, `CenteredVariables.lean` |
| L² martingale theory, Doob's L² inequality | `eLpNorm_two_sq_eq_integral_sq`, `memLp_of_abs_le_const` |

**Overlap:** Both build L² helpers. Different focus:
- BM: Doob's inequalities, BDG inequality (for stochastic integration)
- exchangeability: L² convergence for Cesàro averages, variance computations

**Recommendation:** The basic Lp norm lemmas could be shared/upstreamed.

---

### 7. Distribution / Law Infrastructure

| brownian-motion | exchangeability |
|-----------------|-----------------|
| `Auxiliary/HasLaw.lean`, `HasGaussianLaw.lean`: `HasLaw`, `HasGaussianLaw` predicates | Implicit via pushforward measures |
| Explicit predicate: "X has law μ under P" | Uses `Measure.map X μ` directly |
| Gaussian law preservation under linear maps | Focus on indicator functions and conditional distributions |

**Overlap:** BM has explicit `HasLaw` typeclass; exchangeability uses mathlib's pushforward directly.

**Recommendation:** The `HasLaw` abstraction from BM could simplify some exchangeability proofs about distributional equality.

---

## Medium-Overlap Areas

### 8. Gaussian-Specific vs Indicator-Specific

| brownian-motion | exchangeability |
|-----------------|-----------------|
| `Gaussian/*.lean`: 10 files | `DeFinetti/ViaL2/AlphaIic*.lean`: indicator-based CDF construction |
| Multivariate Gaussian, covariance matrices | `indIic`: indicator of `(-∞, t]` |
| `IsGaussianProcess` predicate | `alphaIicCE`: conditional expectation of indicator |

**Overlap:** **Low** in specific content, but parallel structure:
- BM constructs measures from Gaussian distributions
- exchangeability constructs measures from indicator CDFs (Stieltjes extension)

---

### 9. Stochastic Integration vs Cesàro Convergence

| brownian-motion | exchangeability |
|-----------------|-----------------|
| `StochasticIntegral/*.lean`: 18 files | `DeFinetti/ViaL2/CesaroConvergence.lean`, `MainConvergence.lean` |
| Simple processes, predictable processes, quadratic variation | Block averages, weighted sums, L² contractability bounds |
| Building toward Itô integral | Building toward directing measure |

**Overlap:** **Different goals**, but both use:
- Approximation by simple/finite objects
- L² convergence arguments
- Monotone class techniques

---

### 10. Path Space / Process Definitions

| brownian-motion | exchangeability |
|-----------------|-----------------|
| `Gaussian/StochasticProcesses.lean`: modification, indistinguishability | `PathSpace/Shift.lean`, `CylinderHelpers.lean`: shift operator, shift invariance, cylinder sets |
| `modification_of_indistinguishable` | `shift_measurable`, `isShiftInvariant_iff` |
| Continuity-based indistinguishability | Shift-based symmetry |

**Overlap:** Both define processes as `T → Ω → E`. Different focuses:
- BM: Continuity, modifications, càdlàg paths
- exchangeability: Shift invariance, tail events

---

## Low-Overlap Areas (Minimal Sharing Potential)

| brownian-motion only | exchangeability only |
|---------------------|---------------------|
| Kolmogorov-Chentsov continuity theorem | de Finetti theorem statement |
| Covering numbers, chaining | Contractability definition |
| Fernique's theorem | Conditional i.i.d. definition |
| Cadlag processes | Permutation extension |
| Local martingales | π-system uniqueness for finite marginals |
| Uniform integrability | Stieltjes CDF construction |
| Class D processes | Directing measure construction |

---

## Concrete Recommendations

### Immediate Opportunities

1. **Upstream shared condexp lemmas** to mathlib:
   - `condexp_indicator_eq_of_pair_law_eq` (exchangeability)
   - `covariance_fun_add_*` (brownian-motion)
   - `condExp_mul_pullout` (exchangeability)
   - **Note:** `isFiniteMeasure_trim` is now in mathlib (as of 4.27); `sigmaFinite_trim` for finite measures is still local

2. **Adopt `HasLaw` abstraction** in exchangeability:
   - Would simplify proofs about distributional equality
   - Already well-designed in brownian-motion

3. **Consider sharing reverse martingale infrastructure**:
   - exchangeability has mature `revFiltration`, `revCEFinite`
   - Could be useful for BM's asymptotic theory or backward SDEs

### Future Integration Points

4. **Tail σ-algebra machinery** could extend BM:
   - 0-1 laws for Brownian motion
   - Tail events of stochastic processes

5. **Gaussian process + exchangeability**:
   - Gaussian processes are exchangeable under appropriate symmetry
   - Could formalize connections (e.g., Gaussian exchangeable sequences)

---

## File-by-File Overlap Matrix

| brownian-motion file | Most similar exchangeability file | Overlap % |
|---------------------|----------------------------------|-----------|
| `ProjectiveLimit.lean` | `InfiniteProduct.lean` | 70% (same mathlib API) |
| `Martingale.lean` | `Martingale/Convergence.lean` | 40% (different direction) |
| `MeasureTheory.lean` | `CondExpBasic.lean`, `CondExpExtras.lean` | 50% |
| `HasLaw.lean` | (implicit in measure maps) | 30% |
| `Adapted.lean` | `TailSigma.lean` | 25% (complementary) |
| `IsStoppingTime.lean` | (not present) | 0% |
| `GaussianProcess.lean` | `AlphaIicCE.lean` | 20% (parallel structure) |
| `StochasticProcesses.lean` | `PathSpace/Shift.lean` | 35% |

---

## Summary Statistics

- **Total infrastructure overlap:** ~40-50% in foundational probability/measure theory
- **High-value sharing candidates:** 5-10 lemmas around condexp, Lp norms
- **Complementary (not duplicate):** Martingale directions, filtration types
- **Disjoint:** Gaussian-specific (BM), de Finetti-specific (exchangeability)

Both projects would benefit from coordinated upstreaming to mathlib.

---

## brownian-motion Repository Structure

```
BrownianMotion/
├── Auxiliary/           # 24 helper files
│   ├── Adapted.lean
│   ├── HasLaw.lean
│   ├── IsStoppingTime.lean
│   ├── Martingale.lean
│   ├── MeasureTheory.lean
│   └── ...
├── Gaussian/            # 10 files
│   ├── BrownianMotion.lean
│   ├── GaussianProcess.lean
│   ├── ProjectiveLimit.lean
│   └── ...
├── Continuity/          # 6 files (Kolmogorov-Chentsov)
│   ├── KolmogorovChentsov.lean
│   └── ...
└── StochasticIntegral/  # 18 files (in progress)
    ├── LocalMartingale.lean
    ├── OptionalSampling.lean
    ├── SimpleProcess.lean
    └── ...
```

---

## exchangeability Infrastructure Summary

```
Exchangeability/
├── Probability/              # Core probability helpers
│   ├── CondExp*.lean        # 6+ files
│   ├── Martingale/          # Reverse martingale focus
│   ├── CondIndep/           # Conditional independence
│   ├── InfiniteProduct.lean # Kolmogorov extension for i.i.d.
│   └── LpNormHelpers.lean
├── Tail/                     # Tail σ-algebra machinery
│   ├── TailSigma.lean
│   ├── ShiftInvariantMeasure.lean
│   └── CondExpShiftInvariance.lean
├── PathSpace/                # Shift operators
│   ├── Shift.lean
│   └── CylinderHelpers.lean
└── DeFinetti/ViaL2/          # L² proof infrastructure
    ├── AlphaIic*.lean       # CDF construction
    ├── DirectingMeasure*.lean
    └── CesaroConvergence.lean
```

---

## References

- **brownian-motion:** https://github.com/RemyDegenne/brownian-motion
- **arXiv preprint:** 2511.20118 (Brownian motion formalization)
- **exchangeability:** This repository
- **Kallenberg (2005):** Probabilistic Symmetries and Invariance Principles
