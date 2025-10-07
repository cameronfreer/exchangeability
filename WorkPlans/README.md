# Work Plans and Development Notes

This directory contains active work plans, progress tracking, and development resources for the exchangeability formalization project.

## Active Documents

### Current Analysis
- **[AXIOMS_REPORT.md](AXIOMS_REPORT.md)** - Detailed analysis of axioms and sorry statements (updated Oct 6, 2025)
- **[AXIOMS_SUMMARY.md](AXIOMS_SUMMARY.md)** - Summary of axiom usage across the codebase (updated Oct 6, 2025)

### Development Roadmap
- **[L2Proof_ROADMAP.md](L2Proof_ROADMAP.md)** - Roadmap for the L² proof approach (ViaL2.lean)

### Resources
- **[MATHLIB_RESOURCES_FOR_EXCHANGEABILITY.md](MATHLIB_RESOURCES_FOR_EXCHANGEABILITY.md)** - Catalog of relevant mathlib lemmas and theories

## Deprecated Documents

Historical work plans and completed task summaries have been moved to [`Deprecated/`](Deprecated/):
- Completed task reports (circularity solution, projection lemma)
- Old session notes and progress reports
- Superseded implementation plans

See [`Deprecated/README.md`](Deprecated/README.md) for details.

## Current Project Structure

After the recent refactor (Oct 7, 2025):
- **Module naming**: `Exchangeability.Core` (was `Exchangeability.Exchangeability`)
- **Proof organization**: `ViaL2`, `ViaKoopman`, `ViaMartingale` (idiomatic multiple-proof pattern)
- **Public API**: `Exchangeability/DeFinetti/Theorem.lean` provides canonical `deFinetti` theorem

## Using This Directory

- For **current axiom status**: See AXIOMS_REPORT.md
- For **mathlib resources**: See MATHLIB_RESOURCES_FOR_EXCHANGEABILITY.md
- For **historical context**: See Deprecated/
- For **project overview**: See main [README](../README.md)
- For **formal blueprint**: See [blueprint/](../blueprint/)
