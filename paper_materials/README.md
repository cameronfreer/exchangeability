---
Repo: https://github.com/cameronfreer/exchangeability
Commit: aec253b69aaabbd93dd82fe1a7d9bbf34cf90ab5
Date: 2026-01-24
Built: yes
Lean: v4.27.0-rc1
Lake: v5.0.0-src+2fcce72
---

# Paper Materials for de Finetti Theorem Formalization

This directory contains curated materials for writing an AFM-style paper about the Lean 4 formalization of de Finetti's theorem.

## Quick Links

| File | Description |
|------|-------------|
| [00_environment_and_build.md](00_environment_and_build.md) | Build environment, versions, statistics |
| [01_repo_map.md](01_repo_map.md) | Repository structure, "read these 5 files" |
| [02_main_theorems_and_interfaces.md](02_main_theorems_and_interfaces.md) | Main theorem statements and API |
| [03_definitions_exchangeable_contractable_ciid.md](03_definitions_exchangeable_contractable_ciid.md) | Core definitions |
| [04_proof_overview_three_routes.md](04_proof_overview_three_routes.md) | Comparison of three proofs |
| [05_proof_route_reverse_martingale.md](05_proof_route_reverse_martingale.md) | Martingale proof details |
| [06_proof_route_L2.md](06_proof_route_L2.md) | L² proof details |
| [07_proof_route_koopman_mean_ergodic.md](07_proof_route_koopman_mean_ergodic.md) | Koopman proof details |
| [08_common_ending_pi_system_monotone_class.md](08_common_ending_pi_system_monotone_class.md) | Shared π-system extension |
| [09_infrastructure_tail_sigma_algebra_condexp_kernels.md](09_infrastructure_tail_sigma_algebra_condexp_kernels.md) | Measure theory infrastructure |
| [10_usability_api_examples.md](10_usability_api_examples.md) | API usage examples |
| [11_commit_history_milestones.md](11_commit_history_milestones.md) | Development history |
| [12_compiler_outputs_checks_and_axioms.md](12_compiler_outputs_checks_and_axioms.md) | #check, #print, axiom verification |
| [13_snippet_library_curated.md](13_snippet_library_curated.md) | 16 curated code snippets |
| [14_figures_and_graphs_inventory.md](14_figures_and_graphs_inventory.md) | Available diagrams |
| [15_bibliography_and_math_references.md](15_bibliography_and_math_references.md) | References and BibTeX |
| [16_open_questions_and_future_extensions.md](16_open_questions_and_future_extensions.md) | Future work |

## Supporting Files

| File | Description |
|------|-------------|
| [commands_run.log](commands_run.log) | Shell commands executed during mining |
| [PaperIntrospection.lean](PaperIntrospection.lean) | Lean file for #check/#print outputs |
| `figures/` | Directory for generated graphs |

## The Formalization at a Glance

**Theorem:** de Finetti-Ryll-Nardzewski equivalence

For infinite sequences on standard Borel spaces:
```
Contractable ⟺ Exchangeable ⟺ Conditionally i.i.d.
```

**Three complete proofs:**
1. **Martingale** (default): Reverse martingale convergence
2. **L²**: Elementary correlation bounds
3. **Koopman**: Mean Ergodic Theorem

**Statistics:**
- 112 Lean files
- 43,512 lines of code
- 4,135 commits
- ~4 months development

**Axioms:** Only standard mathlib axioms (propext, Classical.choice, Quot.sound)

## How to Use These Materials

### For Paper Writing

1. Start with [04_proof_overview_three_routes.md](04_proof_overview_three_routes.md) for high-level structure
2. Use [13_snippet_library_curated.md](13_snippet_library_curated.md) for code examples
3. Reference [15_bibliography_and_math_references.md](15_bibliography_and_math_references.md) for citations
4. Check [12_compiler_outputs_checks_and_axioms.md](12_compiler_outputs_checks_and_axioms.md) for formal verification details

### For Understanding the Code

1. Read files 00-03 for orientation
2. Choose a proof route (05, 06, or 07) to study in depth
3. Use [10_usability_api_examples.md](10_usability_api_examples.md) for practical usage

### For mathlib Contributors

1. Check [09_infrastructure](09_infrastructure_tail_sigma_algebra_condexp_kernels.md) for novel infrastructure
2. Look at `ForMathlib/` directory for potential contributions
3. Review [16_open_questions](16_open_questions_and_future_extensions.md) for integration ideas

## Regenerating This Directory

To regenerate the introspection output:

```bash
lake env lean paper_materials/PaperIntrospection.lean
```

To regenerate build timing:

```bash
time lake build
```

## File Format

All markdown files begin with a standard header:

```markdown
---
Repo: https://github.com/cameronfreer/exchangeability
Commit: <full hash>
Date: <ISO date>
Built: yes
Lean: v4.x.x
Lake: v4.x.x
---
```

All code snippets include:
- Path to source file
- Line numbers
- Purpose description
- Mathematical translation
