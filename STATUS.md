# Project Status: de Finetti Theorem Formalization

**Last Updated:** 2026-05-27

## Executive Summary

LOC counts below cover the `Exchangeability/` library tree (excluding the top-level
`Exchangeability.lean` umbrella and `Main.lean`):

| Proof Approach | Lines | Build | Status |
|---------------|------:|-------|--------|
| **ViaMartingale** | 2,804 | Pass | **COMPLETE** |
| **ViaL2** | 7,444 | Pass | **COMPLETE** |
| **ViaKoopman** | 5,402 | Pass | **COMPLETE** |
| *Shared infrastructure* | 11,117 | — | — |
| **Total** | **26,767** | Pass | **COMPLETE** |

**All three proofs complete.**

---

## The Three Proofs

### ViaMartingale (Default)
- Kallenberg's "third proof" (after Aldous)
- Reverse martingale convergence
- **Main theorem:** `deFinetti` (re-exported from `Exchangeability.DeFinetti.Theorem`)

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
printf 'import Exchangeability\n#print axioms Exchangeability.DeFinetti.deFinetti\n' | lake env lean --stdin
```

---

## Related Documentation

- [Development Chronology](DEVELOPMENT_CHRONOLOGY.md) - Project history
- [Paper Planning](paper/README.md) - AFM paper materials
