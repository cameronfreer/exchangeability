# exchangeability

Formalization project for **exchangeability** and **de Finetti's theorem** in Lean 4.

## Overview

The repository hosts work-in-progress formal proofs guided by detailed blueprints.  Each
proof direction from Kallenberg (2005) has its own Lean file and documentation:

- 📘 *Blueprint: Exchangeability* – high-level plan for definitions, lemmas, and proofs.
- 🔁 *Koopman approach* – Mean Ergodic Theorem route to de Finetti (`DeFinetti/KoopmanApproach.lean`).
- 📉 *L² approach* – contractability bound and Step 3 in Kallenberg’s proof (`DeFinetti/L2Approach.lean`).
- 🔄 *Contractability* – algebraic relationship between exchangeability and contractability
  (`Contractability.lean`), containing the easy implication `contractable → exchangeable`
  and the harder converse used by both blueprints.
- 📈 *Martingale approach* – Aldous’ third proof scaffold (`DeFinetti/MartingaleApproach.lean`).

See `blueprint/` for the full roadmap and status reports.

## Prerequisites

To run this project, you need:
1. [Lean 4](https://leanprover.github.io/lean4/doc/setup.html) installed
2. [elan](https://github.com/leanprover/elan) (Lean version manager)

## Installation

Install elan (Lean version manager):
```bash
curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh
```

Install Lean 4 stable:
```bash
elan default stable
```

## Building the Project

To build the project:
```bash
lake build
```

For a task-oriented overview (including the contractability lemmas), see the files in
`blueprint/` and the roadmap `EXCHANGEABILITY_TASKS.md`.
