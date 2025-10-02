# exchangeability

Formalization project for **exchangeability** and **de Finetti's theorem** in Lean 4.

## Overview

The repository hosts work-in-progress formal proofs guided by detailed blueprints:

- 📘 *Blueprint: Exchangeability* – high-level plan for definitions, lemmas, and proofs.
- 🔁 *Koopman approach* – Mean Ergodic Theorem route to de Finetti.
- 📉 *L² approach* – contractability argument for an alternative proof.

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

To run the main executable:
```bash
lake exe exchangeability
```
