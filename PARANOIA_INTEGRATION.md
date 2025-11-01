# LeanParanoia Integration Guide

This guide shows how to use DepViz with LeanParanoia to verify code quality across your Lean project.

## Quick Start

### 1. Generate the Dependency Graph

```bash
lake build depviz
lake env depviz --roots Exchangeability --json-out depgraph.json
```

This creates `depgraph.json` with metadata about all declarations in your project.

### 2. Run Policy Checks (requires LeanParanoia)

**Note**: LeanParanoia integration is optional. Skip this step if you only want dependency visualization.

```bash
# First, add LeanParanoia to lakefile.lean and rebuild
python scripts/paranoia_runner.py \
  --depgraph depgraph.json \
  --policy depviz-policy.yaml \
  --out paranoia_report.json \
  --jobs 8
```

### 3. View Results

Open `viewer/paranoia-viewer.html` in your browser, then load:
- `depgraph.json` (required)
- `paranoia_report.json` (optional, shows verification status)

## What Gets Checked?

The policy runner checks declarations for:

- **Sorry/Admit**: Incomplete proofs
- **Axioms**: Use of axioms beyond your whitelist (e.g., Classical.choice)
- **Metavariables**: Partially elaborated terms
- **Unsafe**: Unsafe constructs
- **Extern**: External (FFI) declarations

Each "zone" in your policy file can have different rules.

## Policy File Structure

```yaml
zones:
  - name: "Zone Name"
    include: ["Module.Glob.**"]     # Which modules to check
    exclude: ["Module.Glob.Skip"]   # Exceptions
    allowed_axioms:                 # Whitelist of axioms
      - "propext"
      - "Classical.choice"
      - "Quot.sound"
    forbid:                         # What to forbid
      - "sorry"
      - "metavariables"
      - "unsafe"
    trust_modules:                  # Don't re-verify these
      - "Std"
      - "Mathlib"
```

## Example Policies Included

### `depviz-policy.yaml` (Recommended)
Balanced policy for production code:
- Forbids: `sorry`, `metavariables`, `unsafe`
- Allows: Standard axioms (propext, Classical.choice, Quot.sound)
- Zones: Separate policies for Probability, DeFinetti, Ergodic, etc.

### `depviz-policy-strict.yaml`
Constructive-only mode:
- Only allows `propext` axiom (no Classical.choice!)
- Useful for identifying which theorems require classical logic
- Very strict - expect many failures

### `depviz-policy-dev.yaml`
Development mode:
- Only tracks `sorry` (incomplete proofs)
- Allows everything else
- Use during active development

## Workflow Scenarios

### Scenario 1: Find All Sorries Before PR

```bash
# Quick check for incomplete proofs
python scripts/paranoia_runner.py \
  --policy depviz-policy-dev.yaml \
  --depgraph depgraph.json \
  --out report.json
```

Exit code will be 1 if any sorries are found.

### Scenario 2: Verify Core Module is Rigorous

Edit `depviz-policy.yaml` to make a zone ultra-strict:

```yaml
- name: "Core - Ultra Strict"
  include: ["Exchangeability.Probability.**"]
  allowed_axioms: ["propext"]  # No classical axioms!
  forbid: ["sorry", "metavariables", "unsafe", "extern"]
```

Then run the checks to see what depends on Classical.choice.

### Scenario 3: Track Axiom Usage Across Project

Use the interactive viewer:
1. Load `depgraph.json` and `paranoia_report.json`
2. Filter by "Uses Axioms" 
3. Click on any declaration to see which axioms it uses
4. Trace dependencies to find where axioms propagate

### Scenario 4: CI Integration

Add to `.github/workflows/lean.yml`:

```yaml
- name: Check for Sorries
  run: |
    lake env depviz --roots Exchangeability --json-out depgraph.json
    python scripts/paranoia_runner.py \
      --policy depviz-policy-dev.yaml \
      --depgraph depgraph.json \
      --out report.json
```

This will fail CI if any sorries are found.

## Understanding the Report

The `paranoia_report.json` file contains:

```json
{
  "results": [
    {
      "decl": "Exchangeability.Probability.someTheorem",
      "zone": "Probability Core",
      "ok": false,
      "stderr": "error: declaration uses axiom 'Classical.choice'",
      "kind": "thm",
      "module": "Exchangeability.Probability"
    }
  ],
  "summary": {
    "total": 150,
    "passed": 142,
    "failed": 8
  }
}
```

Failed checks include:
- Which declaration failed
- What zone/policy was being enforced
- Error message explaining why
- Module and kind information

## Customizing Policies

### Add a New Zone

Edit `depviz-policy.yaml`:

```yaml
zones:
  - name: "My New Zone"
    include: ["Exchangeability.MyModule.**"]
    allowed_axioms: ["propext", "Classical.choice", "Quot.sound"]
    forbid: ["sorry", "unsafe"]
    trust_modules: ["Std", "Mathlib"]
```

### Check Only Modified Files

If you only want to check declarations that changed in your PR:

```bash
# Get list of modified modules
git diff main --name-only | grep "\.lean$"

# Edit policy to include only those modules
# Then run paranoia_runner.py
```

## Performance Tips

1. **Use `--jobs` flag**: Parallelize checks
   ```bash
   python scripts/paranoia_runner.py --jobs 16 ...
   ```

2. **Trust standard libraries**: Always include in your policy:
   ```yaml
   trust_modules: ["Std", "Mathlib", "Init"]
   ```

3. **Filter the graph**: Only check relevant modules
   ```bash
   lake env depviz --roots Exchangeability.DeFinetti --json-out depgraph.json
   ```

## Troubleshooting

### "lake exe paranoia: command not found"

LeanParanoia is not installed. Add to `lakefile.lean`:

```lean
require paranoia from git
  "https://github.com/oOo0oOo/LeanParanoia.git" @ "main"
```

Then: 
```bash
lake update paranoia
lake build paranoia
```

If you get toolchain mismatches:
```bash
cp .lake/packages/mathlib/lean-toolchain ./lean-toolchain
lake clean
lake build
```

### "No module named 'yaml'"

Install PyYAML: `pip install pyyaml`

### Script runs very slowly

1. Use more parallel jobs: `--jobs 16`
2. Ensure `trust_modules` includes Std and Mathlib
3. Consider filtering to a specific submodule

### False positives

LeanParanoia is in early development. If you get unexpected failures:
1. Check the error message in the report
2. Run the failing declaration manually: `lake exe paranoia YourModule.theorem`
3. Report issues to the LeanParanoia repo

## Interactive Viewer Features

The `viewer/paranoia-viewer.html` provides:

- **Status Overview**: Total nodes, passed/failed counts
- **Filtering**: By status, zone, or search text
- **Sortable Table**: Click headers to sort by any column
- **Details Panel**: Click any row to see full error messages, commands, axiom usage
- **No Server Required**: Pure client-side JavaScript, works offline

## Future Enhancements

Planned features:
- Visual graph rendering with status colors
- Axiom contamination tracking (highlight all descendants of axiom-using nodes)
- Export filtered results to CSV
- Integration with Lean LSP for real-time feedback

## Reference

- [LeanParanoia](https://github.com/oOo0oOo/LeanParanoia) - Policy-driven verifier
- [lean4checker](https://github.com/leanprover/lean4checker) - Environment replay tool
- [DepViz README](DepViz/README.md) - Full DepViz documentation
