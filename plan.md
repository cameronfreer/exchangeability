# Project Status: de Finetti Theorem Formalization

**Last Updated:** 2025-12-26

## Executive Summary

| Proof Approach | Sorries | Axioms | Admits | Status |
|---------------|---------|--------|--------|--------|
| **ViaMartingale** | 2 | 0 | 0 | **Closest to complete** |
| ViaL2 | 10 | 0 | 0 | Moderate work remaining |
| ViaKoopman | 10 | 1 | 1 | Significant work remaining |
| Shared/Other | 6 | 0 | 0 | Mixed |

**Total:** 28 sorries, 1 axiom, 1 admit

---

## ViaMartingale (Recommended Focus)

**Status:** Only 2 sorries remain, both in `CondIndep/Bounded.lean`

### Blocking Sorries

| File | Line | Lemma | Description |
|------|------|-------|-------------|
| `CondIndep/Bounded.lean` | 255 | `condIndep_of_indep_fun_pair` | Independence → conditional independence |
| `CondIndep/Bounded.lean` | 582 | `condExp_project_of_condIndep` | Projection lemma for conditional independence |

### Recent Progress
- **Fixed:** Removed false `kernel_eval_ae_eq_of_kernel_eq` lemma (was mathematically incorrect)
- **Fixed:** `JointLawEq.lean` now uses correct drop-info lemma (Kallenberg 1.3)
- **Result:** Reduced from 3 sorries to 2 sorries

### Strategy to Complete
1. Prove `condIndep_of_indep_fun_pair` - needs to show that independence of (Y,Z) from W implies conditional independence Y ⊥⊥_W Z
2. Prove `condExp_project_of_condIndep` - projection lemma using conditional independence

---

## ViaL2 (Elementary Approach)

**Status:** 10 sorries across 2 files

### Sorries by File

**`ViaL2/MoreL2Helpers.lean`** (9 sorries):
| Line | Description |
|------|-------------|
| 293, 306 | L² norm bounds |
| 490, 553 | Convergence lemmas |
| 595, 652 | Integration helpers |
| 762 | Nested sorry in proof |
| 1356 | Cesàro index shift |
| 1445 | U-statistic expansion + collision bound |

**`ViaL2/BlockAverages.lean`** (1 sorry):
| Line | Description |
|------|-------------|
| 1618 | Block average convergence |

### Strategy
- These are mostly technical L² lemmas
- Could potentially use mathlib's `MeasureTheory.Lp` machinery more directly

---

## ViaKoopman (Ergodic Approach)

**Status:** 10 sorries + 1 axiom + 1 admit

### Sorries

**`ViaKoopman/Infrastructure.lean`**:
| Line | Type | Description |
|------|------|-------------|
| 492 | sorry | Infrastructure lemma |
| 805 | **axiom** | `condexp_precomp_iterate_eq_of_invariant` |

**`ViaKoopman.lean`**:
| Line | Type | Description |
|------|------|-------------|
| 1587 | **admit** | Active proof gap |
| 1626, 1647, 1713 | sorry | Ergodic convergence lemmas |
| 2372 | sorry | Mean ergodic application |
| 4460, 4720, 5212 | sorry | Final assembly |

**`TheoremViaKoopman.lean`**:
| Line | Description |
|------|-------------|
| 196, 215 | Contractability → path exchangeability |

### Blocking Issues
- The axiom at line 805 is a significant gap
- Heavy reliance on ergodic theory infrastructure

---

## Shared Infrastructure Sorries

### `CondIndepHelpers.lean` (4 sorries)
| Line | Description |
|------|-------------|
| 85, 120, 154, 207 | Conditional independence helper lemmas |

**Note:** These may be used by multiple proof approaches.

### `Tail/ShiftInvariance.lean` (1 sorry)
| Line | Description |
|------|-------------|
| 1327 | Blocked by circular import with CesaroConvergence |

### `ContractableVsExchangeable.lean` (1 sorry)
| Line | Description |
|------|-------------|
| 106 | Contractable ↔ Exchangeable direction |

---

## Recommended Action Plan

### Phase 1: Complete ViaMartingale (Highest Priority)
1. **Fill `condIndep_of_indep_fun_pair`** (line 255)
   - This is the core lemma connecting independence to conditional independence
   - Should follow from definitions + indicator function manipulation

2. **Fill `condExp_project_of_condIndep`** (line 582)
   - Projection property using conditional independence
   - May need tower property of conditional expectation

### Phase 2: Clean Up Shared Infrastructure
1. Review `CondIndepHelpers.lean` - 4 sorries that may be reusable
2. Fix circular import in `ShiftInvariance.lean`

### Phase 3: Choose Second Proof (Optional)
- **ViaL2:** More elementary, 10 sorries but mostly technical
- **ViaKoopman:** More elegant but has axiom dependency

---

## File Dependency Summary

```
ViaMartingale.lean
├── CondIndep/Bounded.lean (2 sorries) ← BLOCKING
├── ConditionalKernel/JointLawEq.lean (✓ fixed)
├── TripleLawDropInfo/DropInfo.lean (✓ complete)
└── Martingale/* (✓ complete)

ViaL2.lean
├── ViaL2/MoreL2Helpers.lean (9 sorries)
├── ViaL2/BlockAverages.lean (1 sorry)
└── CommonEnding.lean

ViaKoopman.lean
├── ViaKoopman/Infrastructure.lean (1 sorry + 1 axiom)
├── TheoremViaKoopman.lean (2 sorries)
└── Ergodic/* infrastructure
```

---

## Quick Commands

```bash
# Build specific proof approach
lake build Exchangeability.DeFinetti.ViaMartingale
lake build Exchangeability.DeFinetti.ViaL2
lake build Exchangeability.DeFinetti.ViaKoopman

# Check for sorries in a file
grep -n "sorry" Exchangeability/Probability/CondIndep/Bounded.lean

# Build full project
lake build
```
