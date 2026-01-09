# CLAUDE.md

This file provides guidance to Claude Code when working with this repository.

## Quick Reference

- **Use the Lean 4 skill** (`lean4-theorem-proving`) for all Lean development
- **Use lean-lsp MCP tools** for interactive proof state, completions, and search
- **Build command:** `lake build`
- **Current status:** All three proofs complete (see STATUS.md)

## Project Overview

**Lean 4 formalization of de Finetti's theorem** - the equivalence:

```
Contractable ⟺ Exchangeable ⟺ Conditionally i.i.d.
```

Three independent proofs from Kallenberg (2005):
1. **ViaMartingale** - Reverse martingale convergence (default)
2. **ViaL2** - Elementary L² bounds (lightest dependencies)
3. **ViaKoopman** - Mean Ergodic Theorem

## Build Commands

```bash
lake build                              # Full build
lake build Exchangeability.DeFinetti    # Specific module
lake clean && lake build                # Clean rebuild
```

## Key Files

| File | Purpose |
|------|---------|
| `DeFinetti/Theorem.lean` | Public API (exports ViaMartingale) |
| `DeFinetti/BridgeProperty.lean` | Shared bridge infrastructure |
| `DeFinetti/CommonEnding.lean` | Shared final step |
| `Core.lean` | π-system machinery |
| `Contractability.lean` | Exchangeable → Contractable |

## Documentation

- **STATUS.md** - Current completion status
- **DEVELOPMENT_CHRONOLOGY.md** - Project history
- **README.md** - Full documentation and references

## Style Notes

- Follow mathlib conventions (see `StyleGuidelines/`)
- Avoid historical comments - describe what code *is*, not what it *was*
- Use `#print axioms` to verify only standard axioms (propext, quot.sound, choice)

## References

Kallenberg (2005), *Probabilistic Symmetries and Invariance Principles*, Theorem 1.1
