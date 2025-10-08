# Style Guidelines

This directory contains style guidelines for the Exchangeability project.

## Files

### Mathlib-style Guidelines

- **[MATHLIB_STYLE_CHECKLIST.md](MATHLIB_STYLE_CHECKLIST.md)**: Comprehensive checklist
  for mathlib style compliance, including formatting, naming conventions, and documentation
  requirements
- **[MATHLIB_STYLE_IMPLICIT_PARAMETERS.md](MATHLIB_STYLE_IMPLICIT_PARAMETERS.md)**:
  Detailed guide for using implicit parameters in the mathlib style

### Project-Specific Style

- **[PROJECT_STYLE.md](PROJECT_STYLE.md)**: Style conventions specific to the
  Exchangeability project

## Quick Reference

### Key Mathlib Conventions

- Line length: ≤ 100 characters
- Naming: `snake_case` for theorems/lemmas, `UpperCamelCase` for types
- Copyright headers required
- Module docstrings with `/-!` required
- Implicit parameters: `{param : Type}` when inferrable, `(param : Type)` for primary data

### Project-Specific Conventions

See [PROJECT_STYLE.md](PROJECT_STYLE.md) for:
- Documentation conventions
- Comment style
- Project-specific patterns
