---
Repo: https://github.com/human-oriented/exchangeability
Commit: aec253b69aaabbd93dd82fe1a7d9bbf34cf90ab5
Date: 2026-01-24
Built: yes
Lean: v4.27.0-rc1
Lake: v5.0.0-src+2fcce72
---

# Environment and Build Information

## Build System Versions

| Component | Version |
|-----------|---------|
| Lean | 4.27.0-rc1 |
| Lake | 5.0.0-src+2fcce72 (Lean version 4.27.0-rc1) |
| mathlib | v4.27.0-rc1 |
| Platform | darwin (arm64-apple-darwin24.6.0) |

## Repository Statistics

| Metric | Value |
|--------|-------|
| Total Lean files | 112 |
| Total lines of code | 43,512 |
| Build jobs | 3,296 |

## Build Command and Output

```bash
$ time lake build
Build completed successfully (3296 jobs).
```

**Build time:** ~5 minutes 12 seconds (wall clock)

## Build Warnings Summary

The build completes with warnings but no errors. Warning categories:
- Unused section variables (~20 occurrences)
- Deprecated lemma names (mathlib API evolution)
- Unused simp arguments (~25 occurrences)
- Minor style suggestions (simpa vs simp, etc.)

None of these affect correctness.

## Dependencies

From `lake-manifest.json`:

| Dependency | Version/Rev |
|------------|-------------|
| mathlib | v4.27.0-rc1 |
| batteries | main |
| Qq | main |
| aesop | main |
| proofwidgets | v0.0.38 |
| importGraph | main |
| LeanSearchClient | main |

## Verification

All proofs compile. No `sorry` statements remain. Axiom check passes (see `12_compiler_outputs_checks_and_axioms.md`).
