---
Repo: https://github.com/cameronfreer/exchangeability
Commit: aec253b69aaabbd93dd82fe1a7d9bbf34cf90ab5
Date: 2026-01-24
Built: yes
Lean: v4.27.0-rc1
Lake: v5.0.0-src+2fcce72
---

# Figures and Graphs Inventory

## Available Figures

### Import Graph (Colored)

**File:** `blueprint/web/import_graph_colored.svg`

**Also available as:** `blueprint/web/import_graph_colored.png`

**Description:** Module dependency graph showing how Lean files import each other. Colored by module category:
- Core definitions (one color)
- Proof routes (different colors for Martingale, L², Koopman)
- Infrastructure modules

**Usage:** Demonstrates the modular structure of the formalization.

---

### Blueprint Print Document

**File:** `blueprint/print/print.pdf`

**Description:** LaTeX-rendered blueprint document with:
- Mathematical statements
- Proof outlines
- Cross-references to Lean code

---

### Symbol Definitions (Web)

**File:** `blueprint/web/symbol-defs.svg`

**Description:** SVG symbol definitions for web blueprint rendering.

---

## Blueprint Structure

```
blueprint/
├── lean_decls           # Declaration references
├── print/               # Print-ready materials
│   └── print.pdf        # Main PDF document
├── src/                 # LaTeX source
│   └── *.tex            # LaTeX files
└── web/                 # Web blueprint
    ├── import_graph_colored.svg
    ├── import_graph_colored.png
    └── symbol-defs.svg
```

## Generating New Figures

### Import Graph

The import graph can be regenerated using mathlib's `lake exe graph` tool:

```bash
lake exe graph
```

For colored output:
```bash
lake exe graph --format svg > blueprint/web/import_graph_colored.svg
```

### Module Statistics

Generate module size statistics:

```bash
wc -l $(find Exchangeability -name "*.lean") | sort -n
```

## Potential Additional Figures

### Proof Route Comparison

Could generate:
- Dependency comparison chart (complexity of imports)
- Line count by route
- Proof length distribution

### Definition Dependency

Could generate:
- DAG showing definition dependencies
- `Exchangeable → Contractable → ConditionallyIID` flow

### Mathematical Diagrams

For the paper, consider:
- Three-way equivalence diagram
- Tail σ-algebra visualization
- Martingale convergence illustration

## Figure Locations in Paper Materials

The `figures/` subdirectory is prepared for:

```
paper_materials/figures/
├── (empty, ready for generated figures)
```

## Notes

- The blueprint PDF contains all mathematical content needed for paper
- Import graphs show the formal structure
- Additional figures can be generated from the codebase as needed
- Consider using `lake exe stats` for quantitative summaries
