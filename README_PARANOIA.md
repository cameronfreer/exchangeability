# DepViz + LeanParanoia Integration

Complete integration for visualizing dependencies and verifying code quality in your Lean 4 project.

## ✅ What's Included

### Core Tools

1. **Enhanced DepViz** (`DepViz/Main.lean`)
   - Generates dependency graphs in DOT and JSON formats
   - JSON output includes full metadata for policy verification
   - Command: `lake env depviz --roots Exchangeability --json-out depgraph.json`

2. **Policy Runner** (`scripts/paranoia_runner.py`)
   - Runs LeanParanoia checks based on configurable policies
   - Parallel execution with `--jobs` flag
   - Generates detailed reports with pass/fail status

3. **Interactive Viewer** (`viewer/paranoia-viewer.html`)
   - Web-based dashboard for viewing results
   - Filter by status, zone, or search text
   - Click any declaration to see detailed error messages

### Policy Files

Three example policies included:

- **`depviz-policy.yaml`**: Production-ready (forbids sorry, unsafe, metavariables)
- **`depviz-policy-strict.yaml`**: Constructive-only (no Classical.choice)
- **`depviz-policy-dev.yaml`**: Development mode (tracks sorries only)

## 🚀 Quick Start

### 1. Generate Dependency Graph

```bash
lake build depviz
lake env depviz --roots Exchangeability --json-out depgraph.json --dot-out depviz.dot
```

### 2. (Optional) Run LeanParanoia Checks

**Prerequisites**:
- Add LeanParanoia to `lakefile.lean` (see setup below)
- Install PyYAML: `pip install pyyaml`

```bash
python scripts/paranoia_runner.py \
  --depgraph depgraph.json \
  --policy depviz-policy.yaml \
  --out paranoia_report.json \
  --jobs 8
```

### 3. View Results

```bash
open viewer/paranoia-viewer.html
```

Then load `depgraph.json` and (optionally) `paranoia_report.json` in the browser.

## 📊 What Gets Verified

For each declaration, the policy runner can check:

- ✗ **Sorry/Admit** - Incomplete proofs
- ✗ **Axioms** - Beyond whitelist (e.g., Classical.choice)
- ✗ **Metavariables** - Partially elaborated terms
- ✗ **Unsafe** - Unsafe constructs
- ✗ **Extern** - FFI declarations

Each zone in your policy can have different rules.

## 📁 Files Created

```
New Files:
├── scripts/paranoia_runner.py          # Policy runner script
├── viewer/paranoia-viewer.html         # Interactive web viewer
├── depviz-policy.yaml                  # Production policy
├── depviz-policy-strict.yaml           # Strict policy
├── depviz-policy-dev.yaml              # Development policy
├── PARANOIA_INTEGRATION.md             # Detailed user guide
├── INTEGRATION_SUMMARY.md              # Technical summary
└── README_PARANOIA.md                  # This file

Modified Files:
├── DepViz/Main.lean                    # Added JSON output
├── DepViz/README.md                    # Updated docs
└── .gitignore                          # Added generated files
```

## 📖 Documentation

- **[DepViz/README.md](DepViz/README.md)**: Full DepViz documentation
- **[PARANOIA_INTEGRATION.md](PARANOIA_INTEGRATION.md)**: Complete user guide with examples
- **[INTEGRATION_SUMMARY.md](INTEGRATION_SUMMARY.md)**: Technical implementation details

## 🎯 Use Cases

### Find All Sorries Before Merging

```bash
python scripts/paranoia_runner.py \
  --policy depviz-policy-dev.yaml \
  --depgraph depgraph.json \
  --out report.json
```

Exit code is 1 if any sorries found → perfect for CI.

### Identify Classical Logic Dependencies

```bash
python scripts/paranoia_runner.py \
  --policy depviz-policy-strict.yaml \
  --depgraph depgraph.json \
  --out strict-report.json
```

See which theorems require Classical.choice.

### Enforce Different Standards per Module

Edit `depviz-policy.yaml` to define zones:

```yaml
zones:
  - name: "Core - Strict"
    include: ["Exchangeability.Probability.**"]
    forbid: ["sorry", "unsafe", "metavariables"]
    
  - name: "Experimental - Lenient"
    include: ["Exchangeability.Experiments.**"]
    forbid: ["sorry"]  # Only track incomplete proofs
```

## 🔧 Customization

### Create Your Own Policy

Copy and edit any policy file:

```yaml
zones:
  - name: "My Zone"
    include: ["MyModule.**"]
    exclude: ["MyModule.Skip"]
    allowed_axioms: ["propext", "Classical.choice", "Quot.sound"]
    forbid: ["sorry", "metavariables", "unsafe"]
    trust_modules: ["Std", "Mathlib"]
```

### Modify the Viewer

Edit `viewer/paranoia-viewer.html` to:
- Change color schemes
- Add new filters
- Customize the display
- Export data in different formats

## ⚡ Performance Tips

1. **Parallel execution**: Use `--jobs` equal to your CPU count
2. **Trust Mathlib/Std**: Always include in `trust_modules`
3. **Filter the graph**: Only check relevant modules
4. **Cache results**: Runner doesn't cache yet (planned feature)

## 🐛 Troubleshooting

### Command not found: lake exe paranoia

LeanParanoia not installed. Add to `lakefile.lean`:

```lean
require paranoia from git
  "https://github.com/oOo0oOo/LeanParanoia.git" @ "main"
```

Then: 
```bash
lake update paranoia
lake build paranoia
```

If you encounter toolchain mismatches:
```bash
cp .lake/packages/mathlib/lean-toolchain ./lean-toolchain
lake clean
lake build
```

### No module named 'yaml'

Install PyYAML: `pip install pyyaml`

### Script very slow

1. Use `--jobs 16` for more parallelism
2. Ensure `trust_modules: ["Std", "Mathlib"]` in policy
3. Consider filtering to specific modules

## 🎨 Viewer Features

The HTML viewer provides:

- **Status dashboard** with pass/fail counts
- **Filterable table** by status, zone, or search
- **Details panel** showing errors, axioms, commands
- **No server needed** - pure client-side JavaScript
- **Dark theme** - easy on the eyes

## 📦 Dependencies

**Required**:
- Lean 4 + Lake
- Python 3.x

**Optional** (for LeanParanoia):
- LeanParanoia package
- PyYAML

**Optional** (for SVG/PNG):
- Graphviz

## 🔮 Future Enhancements

Planned features:
- Visual graph with colored nodes (pass/fail status)
- Axiom contamination highlighting
- Result caching (avoid re-checking)
- Git integration (check only modified files)
- LSP integration (real-time feedback)

## 📝 Notes

- LeanParanoia is in early development (use as additional verification)
- lean4checker requires consistent build environment
- Policy runner runs fresh checks each time (no caching yet)
- Large projects may need filtered graphs for browser viewing

## 🔗 Links

- [LeanParanoia](https://github.com/oOo0oOo/LeanParanoia)
- [lean4checker](https://github.com/leanprover/lean4checker)
- [Graphviz](https://graphviz.org/)

---

**Ready to use!** Start with the Quick Start section above.
