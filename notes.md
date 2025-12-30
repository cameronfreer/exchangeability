# Sorry Analysis by Proof Approach

**Last Updated:** 2025-12-30

---

## TheoremViaMartingale - COMPLETE

| File | Sorries | Status |
|------|---------|--------|
| ViaMartingale.lean | 0 | Complete |
| ViaMartingale/*.lean (8 submodules) | 0 | Complete |
| CondIndep/*.lean | 0 | Complete |
| TripleLawDropInfo/*.lean | 0 | Complete |
| ConditionalKernel/*.lean | 0 | Complete |
| Martingale/*.lean | 0 | Complete |
| **Total** | **0** | **Production-ready** |

**Status:** First complete proof of de Finetti's theorem. Default export in public API.

---

## TheoremViaL2

| File | Sorries | Lines |
|------|---------|-------|
| ViaL2.lean (hub) | 0 | - |
| L2Helpers.lean | 0 | - |
| ViaL2/BlockAverages.lean | 1 | 1632 |
| ViaL2/MoreL2Helpers.lean | 4 | 2311, 4089, 4117, 4139 |
| ViaL2/MainConvergence.lean | 0 | - |
| **Total** | **5** | - |

### Sorry Details

| File:Line | Context | Difficulty |
|-----------|---------|------------|
| BlockAverages.lean:1632 | Block average convergence | Medium |
| MoreL2Helpers.lean:2311 | L2 helper lemma | Medium |
| MoreL2Helpers.lean:4089 | Integration bound | Low |
| MoreL2Helpers.lean:4117 | Integration bound | Low |
| MoreL2Helpers.lean:4139 | Integration bound | Low |

**Status:** Core L² bound theorem (`l2_contractability_bound`) complete. 5 infrastructure sorries remain.

---

## TheoremViaKoopman

| File | Sorries | Lines |
|------|---------|-------|
| ViaKoopman.lean | 9 | 1627, 1705, 1771, 2430, 5297, 6251, 6729, 6801, 7089 |
| TheoremViaKoopman.lean | 2 | 196, 215 |
| Ergodic/*.lean | 0 | - |
| **Total** | **11** | - |

### Sorry Clusters

**Product Factorization (4 sorries):**
| Line | Lemma |
|------|-------|
| 1627 | `condexp_product_factorization_ax` |
| 1705 | `condexp_product_factorization_ax_integral` |
| 1771 | `condexp_product_factorization_general` |
| 2430 | `condexp_product_factorization_general_bounded` |

**Convergence/Technical (5 sorries):**
| Line | Context |
|------|---------|
| 5297 | Requires reformulation |
| 6251 | Technical step (follows from exchangeability) |
| 6729 | condExp shift invariance property |
| 6801 | MET application for bounded functions |
| 7089 | Dependent on tower_indicator_finset |

**TheoremViaKoopman.lean (2 sorries):**
| Line | Context |
|------|---------|
| 196 | Contractability implies path exchangeability |
| 215 | Contractability implies path exchangeability |

### Completed Infrastructure
| File | Lines | Status |
|------|-------|--------|
| Ergodic/KoopmanMeanErgodic.lean | 324 | Complete |
| Ergodic/InvariantSigma.lean | 1048 | Complete |
| Ergodic/ProjectionLemmas.lean | 221 | Complete |
| Ergodic/BirkhoffAvgCLM.lean | 270 | Complete |

**Status:** Ergodic infrastructure complete. Main proof needs product factorization work.

---

## Extra Files (Not on Critical Path)

| File | Sorries | Status |
|------|---------|--------|
| ContractableVsExchangeable_Extras.lean | 1 | Non-blocking |

**Details:**
- Line 260: Swap symmetry `(X j, X i) ~ (X i, X j)` - pedagogical, not on critical path

---

## Summary

| Approach | Sorries | Status |
|----------|---------|--------|
| **ViaMartingale** | **0** | **COMPLETE (Default)** |
| ViaL2 | 5 | ~90% complete |
| ViaKoopman | 11 | ~80% complete |
| Extras | 1 | Non-blocking |
| **Total** | **17** | |

**ViaMartingale is the default proof with 0 blocking issues.**
