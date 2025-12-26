⏺ Sorries by Proof Approach

  TheoremViaL2

  | File                      | sorries | axioms | admits |
  |---------------------------|---------|--------|--------|
  | ViaL2/MoreL2Helpers.lean  | 9       | -      | -      |
  | ViaL2/BlockAverages.lean  | 1       | -      | -      |
  | Tail/ShiftInvariance.lean | 1       | -      | -      |
  | Subtotal                  | 11      | 0      | 0      |

  TheoremViaKoopman

  | File                           | sorries | axioms | admits |
  |--------------------------------|---------|--------|--------|
  | ViaKoopman.lean                | 7       | -      | 1      |
  | ViaKoopman/Infrastructure.lean | 1       | 1      | -      |
  | TheoremViaKoopman.lean         | 2       | -      | -      |
  | Subtotal                       | 10      | 1      | 1      |

  TheoremViaMartingale

  | File                    | sorries | axioms | admits |
  |-------------------------|---------|--------|--------|
  | CondIndep/Bounded.lean  | 2       | -      | -      |
  | KernelEvalEquality.lean | 1       | -      | -      |
  | Subtotal                | 3       | 0      | 0      |

  Orphan Files (not imported by any theorem)

  | File                            | sorries | axioms | admits |
  |---------------------------------|---------|--------|--------|
  | CondIndepHelpers.lean           | 4       | -      | -      |
  | CondExpExtras.lean              | -       | -      | 3      |
  | ContractableVsExchangeable.lean | 2       | -      | -      |
  | Subtotal                        | 6       | 0      | 3      |

  ---
  Summary

  | Approach      | Total Issues         | Status                   |
  |---------------|----------------------|--------------------------|
  | ViaMartingale | 3 sorries            | 🥇 Closest to complete   |
  | ViaKoopman    | 12 (10s + 1ax + 1ad) | More work needed         |
  | ViaL2         | 11 sorries           | More work needed         |
  | Orphan        | 9 (6s + 3ad)         | Not blocking any theorem |

  ViaMartingale is the cleanest with only 3 blocking issues (2 in CondIndep/Bounded, 1 in KernelEvalEquality).
