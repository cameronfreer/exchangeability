# Project Status: de Finetti Theorem Formalization

**Last Updated:** 2026-01-12

## Executive Summary

| Proof Approach | Lines | Build | Status |
|---------------|------:|-------|--------|
| **ViaMartingale** | 3,770 | Pass | **COMPLETE** |
| **ViaL2** | 12,476 | Pass | **COMPLETE** |
| **ViaKoopman** | 6,893 | Pass | **COMPLETE** |
| *Shared infrastructure* | 20,373 | — | — |
| **Total** | **43,512** | Pass | **COMPLETE** |

**All three proofs complete.**

---

## The Three Proofs

### ViaMartingale (Default)
- Kallenberg's "third proof" (after Aldous)
- Reverse martingale convergence
- **Main theorem:** `deFinetti_viaMartingale`

### ViaL2
- Kallenberg's "second proof"
- Elementary L² contractability bounds
- Lightest dependencies (no ergodic theory)
- **Key lemma:** `l2_contractability_bound`

### ViaKoopman
- Kallenberg's "first proof"
- Mean Ergodic Theorem approach
- Deep connection to ergodic theory

---

## Quick Commands

```bash
# Full project build
lake build

# Build specific approach
lake build Exchangeability.DeFinetti.ViaMartingale
lake build Exchangeability.DeFinetti.ViaL2
lake build Exchangeability.DeFinetti.ViaKoopman

# Check axioms for a theorem
lake env lean -c 'import Exchangeability; #print axioms deFinetti_viaMartingale'
```

---

## Related Documentation

- [Development Chronology](DEVELOPMENT_CHRONOLOGY.md) - Project history
- [Paper Planning](paper/README.md) - AFM paper materials
- [Mathlib Contributions](WorkPlans/Deprecated/MATHLIB_CONTRIBUTIONS.md) - Historical gap analysis
