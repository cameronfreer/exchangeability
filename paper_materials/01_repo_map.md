---
Repo: https://github.com/cameronfreer/exchangeability
Commit: aec253b69aaabbd93dd82fe1a7d9bbf34cf90ab5
Date: 2026-01-24
Built: yes
Lean: v4.27.0-rc1
Lake: v5.0.0-src+2fcce72
---

# Repository Map

## Overview

| Metric | Value |
|--------|-------|
| Total Lean files | 112 |
| Total lines of code | 43,512 |
| Main source directory | `Exchangeability/` |

## Top-Level Structure

```
exchangeability/
├── Exchangeability/                 # Main Lean 4 source
│   ├── DeFinetti/                   # Three proof routes
│   │   ├── ViaMartingale/           # Reverse martingale proof (13 files)
│   │   ├── ViaL2/                   # Elementary L² proof (12 files)
│   │   └── ViaKoopman/              # Mean ergodic theorem proof (17 files)
│   ├── Probability/                 # Measure theory infrastructure
│   │   ├── CondExpHelpers/          # Conditional expectation utilities
│   │   ├── CondIndep/               # Conditional independence
│   │   ├── ConditionalKernel/       # Kernel constructions
│   │   ├── Martingale/              # Martingale convergence
│   │   └── TripleLawDropInfo/       # Joint law manipulations
│   ├── Ergodic/                     # Ergodic theory (6 files)
│   ├── PathSpace/                   # Path space operations (2 files)
│   ├── Tail/                        # Tail σ-algebra (3 files)
│   ├── Bridge/                      # Cesaro-to-condExp bridge (1 file)
│   └── Util/                        # Combinatorial utilities (3 files)
├── ForMathlib/                      # Contributions to mathlib (1 file)
├── paper_materials/                 # This documentation
├── blueprint/                       # LaTeX blueprint documents
└── lake-manifest.json               # Dependencies
```

## Read These 5 Files First

To understand the formalization, read these files in order:

1. **`Exchangeability/Contractability.lean`** (537 lines)
   - Core definitions: `Exchangeable`, `Contractable`, `FullyExchangeable`
   - The "easy" direction: `contractable_of_exchangeable`
   - Combinatorial heart: `exists_perm_extending_strictMono`

2. **`Exchangeability/ConditionallyIID.lean`** (356 lines)
   - Definition of `ConditionallyIID`
   - The direction: `exchangeable_of_conditionallyIID`
   - Giry monad usage for conditioning

3. **`Exchangeability/DeFinetti/Theorem.lean`** (73 lines)
   - Main API entry point
   - Re-exports martingale proof as default
   - Documents all three proof routes

4. **`Exchangeability/DeFinetti/TheoremViaMartingale.lean`** (156 lines)
   - Main theorem statements for martingale proof
   - `deFinetti`, `deFinetti_equivalence`, `deFinetti_RyllNardzewski_equivalence`
   - Clean public-facing API

5. **`Exchangeability/DeFinetti/CommonEnding.lean`** (~800 lines)
   - Shared π-system/monotone class extension
   - `finite_product_formula`
   - Used by all three proofs

## Module Categories

### Core Definitions (3 files, ~1200 lines)
- `Contractability.lean` - Exchangeable, Contractable definitions
- `ConditionallyIID.lean` - Conditional i.i.d. definition
- `Core.lean` - π-system machinery

### Proof Route 1: Martingale (14 files, ~4000 lines)
- `DeFinetti/ViaMartingale.lean` - Main proof assembly
- `DeFinetti/ViaMartingale/*.lean` - Supporting lemmas

### Proof Route 2: L² (13 files, ~6500 lines)
- `DeFinetti/ViaL2.lean` - Main proof assembly
- `DeFinetti/ViaL2/*.lean` - Supporting lemmas

### Proof Route 3: Koopman (18 files, ~6000 lines)
- `DeFinetti/ViaKoopman.lean` - Main proof assembly
- `DeFinetti/ViaKoopman/*.lean` - Supporting lemmas

### Shared Infrastructure (4 files, ~1500 lines)
- `DeFinetti/CommonEnding.lean` - π-system extension
- `DeFinetti/BridgeProperty.lean` - Bridge property infrastructure
- `DeFinetti/L2Helpers.lean` - L² helpers
- `DeFinetti/MartingaleHelpers.lean` - Martingale helpers

### Probability Infrastructure (~30 files)
- `Probability/CondExp*.lean` - Conditional expectation
- `Probability/Martingale/*.lean` - Martingale convergence
- `Probability/CondIndep/*.lean` - Conditional independence
- `Probability/ConditionalKernel/*.lean` - Kernel constructions

### Ergodic Theory (6 files)
- `Ergodic/KoopmanMeanErgodic.lean` - Mean Ergodic Theorem
- `Ergodic/BirkhoffAvgCLM.lean` - Birkhoff averages
- `Ergodic/ShiftInvariant*.lean` - Shift-invariant σ-algebras

### Tail σ-Algebra (3 files)
- `Tail/TailSigma.lean` - Core definitions
- `Tail/CondExpShiftInvariance.lean` - Shift invariance properties
- `Tail/ShiftInvariantMeasure.lean` - Invariant measures

### Utilities (6 files)
- `Util/StrictMono.lean` - StrictMono helpers
- `Util/FinsetHelpers.lean` - Finite set utilities
- `PathSpace/*.lean` - Path space operations

## Import Graph

See `figures/import_graph.svg` for the full dependency graph.

Key observations:
- All three proof routes share `CommonEnding.lean`
- The martingale route has lightest dependency on ergodic theory
- The L² route has minimal measure theory dependencies
- ForMathlib files are independent of main proofs
