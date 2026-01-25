---
Repo: https://github.com/human-oriented/exchangeability
Commit: aec253b69aaabbd93dd82fe1a7d9bbf34cf90ab5
Date: 2026-01-24
Built: yes
Lean: v4.27.0-rc1
Lake: v5.0.0-src+2fcce72
---

# Commit History and Milestones

## Overview

| Metric | Value |
|--------|-------|
| Total commits | 4,135 |
| Project start | 2025-09-29 |
| Current snapshot | 2026-01-24 |
| Duration | ~4 months |

## Development Timeline

### Phase 1: Project Setup (2025-09-29 to 2025-10-01)

**Initial commits:**
```
c33c821 2025-09-29 Initial commit
1bba923 2025-09-29 Add basic Lean 4 project structure and examples
179c065 2025-09-29 Add lean-toolchain file with stable Lean 4 version
```

**de Finetti focus:**
```
e9cf171 2025-10-01 chore: focus project on de Finetti formalization
fbce95e 2025-10-01 feat: add de Finetti theorem skeleton and blueprint
42c7d39 2025-10-01 feat: implement mean-ergodic step for de Finetti theorem
```

### Phase 2: Core Infrastructure (2025-10 to 2025-11)

Development of:
- Exchangeability/Contractability definitions
- ConditionallyIID structure
- Tail σ-algebra infrastructure
- Conditional expectation helpers

### Phase 3: Three Proof Routes (2025-11 to 2025-12)

**Martingale proof route:**
- Reverse martingale convergence
- Directing measure construction
- Finite product formula

**L² proof route:**
- Block average machinery
- Kallenberg Lemma 1.2 (correlation bounds)
- Cesàro convergence

**Koopman proof route:**
- Mean Ergodic Theorem formalization
- Shift-invariant σ-algebra
- Block injection strategy

### Phase 4: Completion and Polish (2026-01)

**Recent activity:**
```
bdafa48 Merge pull request #10 from cameronfreer/golfing_4.27.0-rc1
5028af6 golf: Apply golfing patterns (transport, .of_forall, lambdas)
b8d2119 golf: Simplify proofs using term mode and unified tactics
7be032c golf: Simplify Tier 3 proofs using mathlib lemmas
```

**Documentation:**
```
cb0e035 docs: Improve accuracy and usability of documentation
5189b9e Add colored import graphs and expand blueprint
184e465 docs: Add line counts to STATUS.md
```

## Key Milestone Commits

| Date | Commit | Description |
|------|--------|-------------|
| 2025-09-29 | `c33c821` | Initial commit |
| 2025-10-01 | `fbce95e` | de Finetti skeleton |
| 2025-10-01 | `b8f7750` | Integrate mathlib mean ergodic |
| 2025-11-?? | (various) | Martingale proof complete |
| 2025-11-?? | (various) | L² proof complete |
| 2025-12-?? | (various) | Koopman proof complete |
| 2025-12-?? | (various) | CommonEnding integration |
| 2026-01-?? | (various) | Three proofs verified complete |
| 2026-01-?? | `bdafa48` | Major golfing pass |

## Commit Categories

Based on commit message prefixes:

| Category | Example | Purpose |
|----------|---------|---------|
| `feat:` | `feat: add de Finetti skeleton` | New features |
| `fix:` | `fix: Correct typeclass issues` | Bug fixes |
| `refactor:` | `refactor: Move lemmas to ForMathlib` | Code reorganization |
| `docs:` | `docs: Update README` | Documentation |
| `golf:` | `golf: Simplify proofs` | Proof simplification |
| `lint:` | `lint: Add docstrings` | Linting/style |
| `ci:` | `ci: Fix docgen deployment` | CI/CD |
| `chore:` | `chore: Clean up TODOs` | Maintenance |

## Activity Patterns

### Commits per Month (estimated)

| Month | Commits (approx) |
|-------|-----------------|
| Sep 2025 | ~50 |
| Oct 2025 | ~500 |
| Nov 2025 | ~1500 |
| Dec 2025 | ~1500 |
| Jan 2026 | ~600 |

### Development Intensity

The project shows intensive development, with:
- ~30 commits per day average during active phases
- Multiple proof routes developed in parallel
- Continuous refactoring and golfing

## Merge Pull Requests

Recent PRs merged to main:

| PR | Title | Impact |
|----|-------|--------|
| #11 | ci_docs_fixes | CI improvements |
| #10 | golfing_4.27.0-rc1 | Major proof simplification |
| #9 | docs_improvements | Documentation overhaul |
| #8 | linting_4.27.0-rc1 | Linting compliance |
| #7 | improvements_4.27.0-rc1 | General improvements |
| #6 | improvements_4.27.0-rc1 | Continued improvements |
| #5 | upgrade-4.27.0-rc1 | mathlib upgrade |

## Branching Strategy

The project uses:
- `main` branch for stable, building code
- Feature branches named by purpose (e.g., `golfing_4.27.0-rc1`)
- Pull request workflow for significant changes

## Contributors

Primary contributor: Cameron Freer

## Repository Growth

**Files over time:**
- Initial: ~5 files
- Phase 2: ~30 files
- Phase 3: ~80 files
- Current: 112 Lean files

**Lines of code:**
- Initial: ~500 lines
- Phase 2: ~5,000 lines
- Phase 3: ~30,000 lines
- Current: 43,512 lines

## Notes

- The high commit count (4,135) reflects iterative development with frequent small commits
- Many commits are proof attempts, refactoring, and incremental progress
- The project shows a mature workflow with linting, documentation, and CI integration
