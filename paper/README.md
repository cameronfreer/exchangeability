# AFM Paper: Formalizing de Finetti's Theorem

## Current Status (January 2026)

| Proof Approach | Status | Ready for Paper? |
|---------------|--------|------------------|
| **ViaMartingale** | **COMPLETE** | Yes |
| **ViaL2** | **COMPLETE** | Yes |
| **ViaKoopman** | **COMPLETE** | Yes |

**Milestone:** All three proof approaches complete.

## Paper Title

**"Formalizing de Finetti's Theorem in Lean 4: Three Proofs and Mathematical Insights"**

## Target Venue

**Primary:** Annals of Formalized Mathematics (AFM)
- Open access, focuses on formalized mathematics
- Evaluates on 9 virtues (novelty, insights, generality, integration, reproducibility, complexity, proof assistant influence, documentation, readability)
- Requires Software Heritage persistent ID (SWHID)

**Secondary:** ITP/CPP (shorter conference version)

## Files in This Directory

| File | Purpose |
|------|---------|
| `OUTLINE.md` | Paper structure and section content |
| `NOTES.md` | Technical lessons and mathematical insights |
| `CHECKLIST.md` | AFM preparation checklist |

## Workflow

### Phase 1: Pre-Writing (Current)
- [x] Complete all three proof approaches
- [ ] Stabilize codebase
- [ ] Collect statistics (LOC, sorry evolution, build times)
- [ ] Tag stable release
- [ ] Register Software Heritage SWHID

### Phase 2: Writing
- [ ] Draft introduction (accessible to mathematicians)
- [ ] Write comparative analysis of three proofs
- [ ] Document infrastructure contributions
- [ ] Create figures (dependency graphs, architecture)
- [ ] Internal review and polish

### Phase 3: Submission
- [ ] Deposit on arXiv
- [ ] Submit to AFM

### Concurrent Work
- [ ] Begin mathlib PR submissions
- [ ] Optionally: Write ITP/CPP paper on `condExpWith` pattern

## Key Selling Points

1. **First complete Lean 4 formalization** of de Finetti's theorem
2. **Three independent proofs** (comparative study)
3. **Mathematical insights** revealed by formalization
4. **"Equation archeology"** - formalization as explanation
5. **Infrastructure contributions** designed for mathlib

## Original Planning Document

See `../NotesForLater/PUBLICATION_IDEAS.md` for the comprehensive original planning document (Oct 2025).

## Quick Links

- [Main README](../README.md)
- [Development Chronology](../DEVELOPMENT_CHRONOLOGY.md)
- [Mathlib Contributions](../MATHLIB_CONTRIBUTIONS.md)
- [Proof-specific docs](../Exchangeability/DeFinetti/)
