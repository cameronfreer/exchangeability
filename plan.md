# Project Status: de Finetti Theorem Formalization

**Last Updated:** 2025-12-27

## Executive Summary

| Proof Approach | Sorries | Axioms | Admits | Build | Status |
|---------------|---------|--------|--------|-------|--------|
| **ViaMartingale** | **0** | 0 | 0 | ✅ | **COMPLETE (Default)** |
| ViaL2 | 6 | 0 | 0 | ✅ | ~85% complete |
| ViaKoopman | 12 | 0 | 1 | ✅ | ~80% complete |
| Shared/Orphan | 0 | 0 | 0 | ✅ | Complete |

**All three approaches build successfully with no errors.**

---

## ViaMartingale ✅ COMPLETE

**Status:** Production-ready. Default proof in public API.

**Main File:** `Exchangeability/DeFinetti/ViaMartingale.lean` (4,854 lines)

| Metric | Count |
|--------|-------|
| Sorries | **0** |
| Admits | **0** |
| Axioms | **0** |
| Build | ✅ Success |

### Extracted Submodules (1,261 lines total)

| File | Lines | Description |
|------|-------|-------------|
| `ViaMartingale/ShiftOperations.lean` | 126 | path, shiftRV, shiftProcess, shift_contractable |
| `ViaMartingale/RevFiltration.lean` | 142 | revFiltration, tailSigma, revFiltration_antitone |
| `ViaMartingale/FutureFiltration.lean` | 175 | futureFiltration, tailSigma_le, futureFiltration_antitone |
| `ViaMartingale/FutureRectangles.lean` | 464 | π-system machinery, measure_ext_of_future_rectangles |
| `ViaMartingale/CondExpConvergence.lean` | 186 | condexp_convergence, extreme_members_equal_on_tail |
| `ViaMartingale/DirectingMeasure.lean` | 168 | directingMeasure, conditional_law_eq_directingMeasure |

### Dependencies - All Complete
- `CondIndep/` - 0 sorries
- `TripleLawDropInfo/` - 0 sorries
- `ConditionalKernel/` - 0 sorries
- `Martingale/` - 0 sorries
- All other imports - 0 sorries

### Key Theorems
- `deFinetti_viaMartingale` - Main theorem
- `contraction_independence` - Kallenberg Lemma 1.3

---

## ViaL2 (Elementary Approach)

**Status:** 6 sorries remaining, core theorem complete

**Files:**
- `ViaL2.lean` (hub) - clean
- `L2Helpers.lean` (~930 lines) - complete
- `ViaL2/` submodules - 6 sorries

### Sorry Locations

| File | Line | Context |
|------|------|---------|
| `ViaL2/BlockAverages.lean` | 1617 | `directing_measure_eq` |
| `ViaL2/MoreL2Helpers.lean` | 511 | Stieltjes construction |
| `ViaL2/MoreL2Helpers.lean` | 568 | Bounded measurable extension |
| `ViaL2/MoreL2Helpers.lean` | 1528 | `directing_measure_bridge` |
| `ViaL2/CesaroConvergence.lean` | 3745, 3749 | Integrability of bounded functions (technical) |

### Key Completed Theorem
**Kallenberg's Lemma 1.2** (L2Helpers.lean:847) - FULLY PROVED
```lean
theorem l2_contractability_bound ...
```

### Dependencies
- Lightest of all three approaches
- No ergodic theory or martingale convergence required

---

## ViaKoopman (Ergodic Approach)

**Status:** 12 sorries + 1 admit

**File:** `ViaKoopman.lean` (7,457 lines)

### Sorry Locations (Clustered)

**Kernel Independence (3):**
| Line | Lemma |
|------|-------|
| 5169 | `kernel_indep_pair_01` |
| 5188 | `kernel_indep_pair` |
| 5208 | `kernel_indep_finset` |

**Product Factorization (4):**
| Line | Lemma |
|------|-------|
| 1627 | `condexp_product_factorization_ax` |
| 1705 | `condexp_product_factorization_ax_integral` |
| 1771 | `condexp_product_factorization_general` |
| 2430 | `condexp_product_factorization_general_bounded` |

**Convergence (3):**
| Line | Lemma |
|------|-------|
| 4518 | `ce_lipschitz_convergence` |
| 4778 | `h_tower_of_lagConst_from_one` |
| 5994 | `indep_finset_insert` |

**Other (2):**
| Line | Lemma |
|------|-------|
| 5333 | `ν_measurable_tail` |
| 7340 | `condexp_cylinder_factorizes` |

### Supporting Ergodic Files - ALL COMPLETE
| File | Lines | Sorries |
|------|-------|---------|
| `Ergodic/KoopmanMeanErgodic.lean` | 324 | 0 |
| `Ergodic/InvariantSigma.lean` | 1048 | 0 |
| `Ergodic/ProjectionLemmas.lean` | 221 | 0 |
| `Ergodic/BirkhoffAvgCLM.lean` | 270 | 0 |

---

## Extra Files (Not on Critical Path)

### `ContractableVsExchangeable_Extras.lean` ✅ COMPLETE
Pedagogical documentation of contractable↔exchangeable relationship.
Uses de Finetti theorem to prove swap invariance `(X 0, X 1) ~ (X 1, X 0)`.

### `ViaKoopman/Infrastructure.lean` ✅ COMPLETE
Supporting infrastructure for ViaKoopman.

**Deleted:**
- ~~CondIndepHelpers.lean~~ - Dead code, superseded by `CondIndep/*`.

**Complete:**
- `Tail/ShiftInvariance.lean` - Now has 0 sorries. The `cesaro_convergence_all_shifts` lemma was moved to `CesaroConvergence.lean` to resolve circular import.

---

## Quick Commands

```bash
# Build specific approach
lake build Exchangeability.DeFinetti.ViaMartingale  # ✅ Complete
lake build Exchangeability.DeFinetti.ViaL2
lake build Exchangeability.DeFinetti.ViaKoopman

# Full project build
lake build

# Check for sorries
grep -rn "^\s*sorry" Exchangeability/DeFinetti/ViaMartingale.lean
```

---

## Priority for Further Work

1. **ViaL2** - 6 sorries (all in ViaL2/*), core L² bound done
2. **ViaKoopman** - 12 sorries + 1 admit, ergodic infrastructure complete
3. **Extras** - ✅ Complete
