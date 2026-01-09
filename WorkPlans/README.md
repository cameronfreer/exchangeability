# Work Plans and Development Notes

This directory contains active work plans, progress tracking, and development resources for the exchangeability formalization project.

**Last Updated:** January 2026

## Active Documents

### Analysis (Oct 2025)
- **[AXIOMS_REPORT.md](AXIOMS_REPORT.md)** - Detailed analysis of axioms and sorry statements
- **[AXIOMS_SUMMARY.md](AXIOMS_SUMMARY.md)** - Summary of axiom usage across the codebase

### Development Roadmap
- **[L2Proof_ROADMAP.md](L2Proof_ROADMAP.md)** - Roadmap for the L² proof approach (ViaL2.lean)

### Resources
- **[MATHLIB_RESOURCES_FOR_EXCHANGEABILITY.md](MATHLIB_RESOURCES_FOR_EXCHANGEABILITY.md)** - Catalog of relevant mathlib lemmas and theories

## Deprecated Documents

Historical work plans, session notes, and superseded documents have been moved to [`Deprecated/`](Deprecated/):
- ViaKoopman planning documents
- DeFinetti-specific session notes
- Proof exploration notes
- Old implementation guides

See [`Deprecated/README.md`](Deprecated/README.md) for details.

## Current Project Status

**As of January 2026:**

| Proof | Status | Sorries |
|-------|--------|---------|
| **ViaMartingale** | **COMPLETE** | 0 |
| **ViaL2** | **COMPLETE** | 0 |
| **ViaKoopman** | **COMPLETE** | 0 |

- **Module naming**: `Exchangeability.Core`
- **Proof organization**: `ViaL2`, `ViaKoopman`, `ViaMartingale`
- **Public API**: `Exchangeability/DeFinetti/Theorem.lean` provides canonical `deFinetti` theorem

## Key Links

| Resource | Location |
|----------|----------|
| Project status | [STATUS.md](../STATUS.md) |
| Project overview | [README.md](../README.md) |
| Development history | [DEVELOPMENT_CHRONOLOGY.md](../DEVELOPMENT_CHRONOLOGY.md) |
| AFM paper planning | [paper/](../paper/) |
| Formal blueprint | [blueprint/](../blueprint/) |
