# DepViz

A dependency visualization tool for Lean 4 projects. DepViz extracts declaration dependencies from your project and generates dependency graphs in DOT, SVG, or PNG formats.

## Features

- **Smart Filtering**: By default, keeps only declarations from your project's root modules, producing manageable graph sizes
- **Flexible Whitelisting**: Include additional module prefixes (e.g., `Std`, `Init`) as needed
- **Multiple Output Formats**: Generate DOT files, or render directly to SVG/PNG via Graphviz
- **Edge Consistency**: Automatically filters edges to match the surviving nodes

## Building

Build the tool from the project root:

```bash
lake build depviz
```

## Usage

### Basic Usage

Generate a dependency graph for your project:

```bash
lake env depviz --roots Exchangeability --dot-out depviz.dot
```

This creates a filtered graph containing only declarations whose module names start with `Exchangeability`.

### Including Additional Modules

Whitelist extra module prefixes (comma-separated):

```bash
lake env depviz --roots Exchangeability --include-prefix Std,Init --dot-out depviz.dot
```

### Disable Filtering

To include all declarations (warning: may produce very large graphs):

```bash
lake env depviz --roots Exchangeability --keep-all --dot-out depviz.dot
```

### Direct Rendering

If Graphviz is installed, render directly to SVG or PNG:

```bash
lake env depviz --roots Exchangeability --svg-out depviz.svg
lake env depviz --roots Exchangeability --png-out depviz.png
```

## CLI Options

- `--roots <name>`: Project root name(s) for filtering (required)
- `--dot-out <file>`: Output DOT file path
- `--svg-out <file>`: Output SVG file path (requires Graphviz)
- `--png-out <file>`: Output PNG file path (requires Graphviz)
- `--include-prefix <prefixes>`: Comma-separated list of additional module prefixes to include
- `--keep-all`: Disable filtering entirely (include all declarations)

## Installing Graphviz

Graphviz is required for SVG/PNG output formats.

### macOS (Homebrew)
```bash
brew install graphviz
```

### Ubuntu/Debian
```bash
sudo apt-get install graphviz
```

### Fedora
```bash
sudo dnf install graphviz
```

### Arch Linux
```bash
sudo pacman -S graphviz
```

### Windows
```bash
choco install graphviz
```

Or download the MSI installer from [graphviz.org](https://graphviz.org/download/)

## Viewing DOT Files

If you generate a `.dot` file, you can render it manually with Graphviz:

```bash
dot -Tsvg depviz.dot -o depviz.svg
dot -Tpng depviz.dot -o depviz.png
```

Or open it with visualization tools like:
- [Graphviz Online](https://dreampuf.github.io/GraphvizOnline/)
- VS Code extensions (e.g., Graphviz Preview)
- Desktop viewers (e.g., xdot, gvedit)

## Implementation Details

The filtering logic (as of `DepViz/Main.lean:175`):

1. **Node Filtering**: Keeps only declarations from modules matching your specified root prefix(es)
2. **Edge Filtering**: Removes edges where either endpoint was filtered out
3. **Consistent Output**: Ensures the resulting DOT file references only existing nodes

Default behavior produces graphs with ~800 nodes instead of millions, making them practical to visualize with standard Graphviz tools.
