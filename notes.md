# Sorry/Axiom/Admit Survey by Proof Approach

**Last Updated:** 2025-12-27

---

## TheoremViaMartingale ✅ COMPLETE

| File | Sorries | Axioms | Admits |
|------|---------|--------|--------|
| ViaMartingale.lean | 0 | 0 | 0 |
| CondIndep/* | 0 | 0 | 0 |
| TripleLawDropInfo/* | 0 | 0 | 0 |
| ConditionalKernel/* | 0 | 0 | 0 |
| Martingale/* | 0 | 0 | 0 |
| **Subtotal** | **0** | **0** | **0** |

**Status:** Production-ready. First complete proof of de Finetti's theorem.

---

## TheoremViaL2

| File | Sorries | Axioms | Admits |
|------|---------|--------|--------|
| ViaL2.lean (hub) | 0 | 0 | 0 |
| L2Helpers.lean | 0 | 0 | 0 |
| ViaL2/BlockAverages.lean | 1 | 0 | 0 |
| ViaL2/MoreL2Helpers.lean | 3 | 0 | 0 |
| ViaL2/CesaroConvergence.lean | 0 | 0 | 0 |
| ViaL2/MainConvergence.lean | 0 | 0 | 0 |
| **Subtotal** | **4** | **0** | **0** |

**Sorry Locations:**
- BlockAverages.lean:1617 - `directing_measure_eq`
- MoreL2Helpers.lean:511 - Stieltjes construction
- MoreL2Helpers.lean:568 - Bounded measurable extension
- MoreL2Helpers.lean:1528 - `directing_measure_bridge`

**Status:** Core L² bound theorem complete. Infrastructure sorries remain.

---

## TheoremViaKoopman

| File | Sorries | Axioms | Admits |
|------|---------|--------|--------|
| ViaKoopman.lean | 12 | 0 | 1 |
| ViaKoopman/Infrastructure.lean | 1 | 0 | 0 |
| TheoremViaKoopman.lean | 2 | 0 | 0 |
| Ergodic/KoopmanMeanErgodic.lean | 0 | 0 | 0 |
| Ergodic/InvariantSigma.lean | 0 | 0 | 0 |
| Ergodic/ProjectionLemmas.lean | 0 | 0 | 0 |
| Ergodic/BirkhoffAvgCLM.lean | 0 | 0 | 0 |
| **Subtotal** | **15** | **0** | **1** |

**Sorry Clusters:**
- Kernel Independence: lines 5169, 5188, 5208
- Product Factorization: lines 1627, 1705, 1771, 2430
- Convergence: lines 4518, 4778, 5994
- Other: lines 5333, 7340
- Infrastructure.lean:492
- TheoremViaKoopman.lean: 196, 215

**Status:** Ergodic infrastructure complete. Main proof needs kernel independence work.

---

## Orphan Files (Not Imported by Any Theorem)

| File | Sorries | Axioms | Admits |
|------|---------|--------|--------|
| CondIndepHelpers.lean | 4 | 0 | 0 |
| Tail/ShiftInvariance.lean | 1 | 0 | 0 |
| ContractableVsExchangeable.lean | 2 | 0 | 0 |
| **Subtotal** | **7** | **0** | **0** |

**Note:** These are helper files not on the critical path for any theorem.

---

## Summary

| Approach | Total Issues | Status |
|----------|--------------|--------|
| **ViaMartingale** | **0** | ✅ Complete (Default) |
| ViaL2 | 4 sorries | ~90% complete |
| ViaKoopman | 15 sorries + 1 admit | ~80% complete |
| Orphan | 7 sorries | Not blocking |

**ViaMartingale is the default proof with 0 blocking issues.**
