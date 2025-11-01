#!/usr/bin/env python3
"""
LeanParanoia Policy Runner for DepViz

Reads dependency graph and policy zones, then runs LeanParanoia checks
on declarations according to their zone policies.

Usage:
    python scripts/paranoia_runner.py \
        --depgraph depgraph.json \
        --policy depviz-policy.yaml \
        --out paranoia_report.json \
        --jobs 8
"""

import argparse
import json
import subprocess
import sys
import fnmatch
import os
import shlex
import concurrent.futures
from typing import List, Dict, Any, Set
from pathlib import Path

try:
    import yaml
except ImportError:
    print("Error: PyYAML not installed. Run: pip install pyyaml", file=sys.stderr)
    sys.exit(1)


def match_any(globs: List[str], s: str) -> bool:
    """Check if string matches any of the glob patterns."""
    return any(fnmatch.fnmatch(s, g) for g in globs)


def decls_for_zone(depgraph: Dict[str, Any], include: List[str], exclude: List[str]) -> List[Dict[str, Any]]:
    """
    Extract declarations matching zone patterns.
    Returns list of dicts with 'fullName', 'kind', 'module' for matching nodes.
    """
    decls = []
    for n in depgraph.get("nodes", []):
        kind = n.get("kind", "")
        # Focus on theorems and definitions (skip constructors, inductives, etc.)
        if kind in ("theorem", "thm", "def"):
            mod = n.get("module", "")
            if match_any(include, mod) and not match_any(exclude or [], mod):
                decls.append({
                    "fullName": n.get("fullName", ""),
                    "kind": kind,
                    "module": mod,
                    "hasSorry": n.get("hasSorry", False),
                    "isUnsafe": n.get("isUnsafe", False),
                    "axioms": n.get("axioms", [])
                })
    return sorted(decls, key=lambda x: x["fullName"])


def run_one(decl: Dict[str, Any], zone: Dict[str, Any], project_root: Path) -> Dict[str, Any]:
    """
    Run LeanParanoia on a single declaration with zone-specific flags.
    
    Returns status dict with 'ok', 'stdout', 'stderr', etc.
    """
    full_name = decl["fullName"]
    allowed = zone.get("allowed_axioms", ["propext", "Quot.sound", "Classical.choice"])
    forbid = set(zone.get("forbid", []))
    trusted = zone.get("trust_modules", [])
    
    # Build command
    cmd = ["lake", "exe", "paranoia", full_name]
    
    # Set allowed axioms
    if allowed:
        cmd += ["--allowed-axioms", ",".join(allowed)]
    
    # Set trusted modules (skip verification of dependencies)
    if trusted:
        cmd += ["--trust-modules", ",".join(trusted)]
    
    # IMPORTANT: LeanParanoia's --no-* flags DISABLE checks
    # We only add them when we want to ALLOW that feature (i.e., NOT in forbid list)
    
    # Build the disable flags for things NOT in forbid list
    # If something is not forbidden, we may want to disable its check
    # But we need to be careful: we want to CHECK things that ARE forbidden
    
    # Actually, let's think about this differently:
    # - If "sorry" is in forbid list, we WANT to check for sorry (don't add --no-sorry)
    # - If "sorry" is NOT in forbid list, we DON'T care about sorry (add --no-sorry)
    
    # Available checks in LeanParanoia:
    # --no-sorry, --no-metavariables, --no-unsafe, --no-axioms, --no-extern, --no-opaque
    
    # Actually, reading the LeanParanoia code more carefully:
    # By default, all checks are ON. The --no-* flags turn them OFF.
    # So we should ONLY add --no-* flags for things NOT in the forbid list.
    
    # Let's be explicit about what we're checking:
    check_sorry = "sorry" in forbid
    check_metavariables = "metavariables" in forbid
    check_unsafe = "unsafe" in forbid
    check_extern = "extern" in forbid
    
    # Disable checks for things NOT forbidden
    if not check_sorry:
        cmd.append("--no-sorry")
    if not check_metavariables:
        cmd.append("--no-metavariables")
    if not check_unsafe:
        cmd.append("--no-unsafe")
    if not check_extern:
        cmd.append("--no-extern")
    
    # Fail fast for efficiency
    cmd.append("--fail-fast")
    
    try:
        # Run in project directory
        p = subprocess.run(
            cmd,
            cwd=project_root,
            capture_output=True,
            text=True,
            check=False,
            timeout=300  # 5 minute timeout per declaration
        )
        
        ok = (p.returncode == 0)
        
        return {
            "decl": full_name,
            "zone": zone["name"],
            "ok": ok,
            "cmd": " ".join(shlex.quote(c) for c in cmd),
            "stdout": p.stdout.strip(),
            "stderr": p.stderr.strip(),
            "exit": p.returncode,
            "kind": decl["kind"],
            "module": decl["module"]
        }
    except subprocess.TimeoutExpired:
        return {
            "decl": full_name,
            "zone": zone["name"],
            "ok": False,
            "error": "timeout (>5 minutes)",
            "kind": decl["kind"],
            "module": decl["module"]
        }
    except Exception as e:
        return {
            "decl": full_name,
            "zone": zone["name"],
            "ok": False,
            "error": str(e),
            "kind": decl["kind"],
            "module": decl["module"]
        }


def main():
    ap = argparse.ArgumentParser(
        description="Run LeanParanoia checks on declarations based on policy zones"
    )
    ap.add_argument("--depgraph", default="depgraph.json",
                    help="Path to dependency graph JSON file")
    ap.add_argument("--policy", default="depviz-policy.yaml",
                    help="Path to policy YAML file")
    ap.add_argument("--out", default="paranoia_report.json",
                    help="Output path for report JSON")
    ap.add_argument("--jobs", type=int, default=os.cpu_count() or 4,
                    help="Number of parallel jobs")
    ap.add_argument("--project-root", default=".",
                    help="Project root directory (where lakefile.toml lives)")
    args = ap.parse_args()
    
    # Resolve paths
    project_root = Path(args.project_root).resolve()
    depgraph_path = project_root / args.depgraph
    policy_path = project_root / args.policy
    out_path = project_root / args.out
    
    # Load dependency graph
    if not depgraph_path.exists():
        print(f"Error: Dependency graph not found: {depgraph_path}", file=sys.stderr)
        print("Run: lake env depviz --roots YourProject --json-out depgraph.json", file=sys.stderr)
        sys.exit(1)
    
    with open(depgraph_path) as f:
        depgraph = json.load(f)
    
    # Load policy
    if not policy_path.exists():
        print(f"Error: Policy file not found: {policy_path}", file=sys.stderr)
        sys.exit(1)
    
    with open(policy_path) as f:
        policy = yaml.safe_load(f)
    
    zones = policy.get("zones", [])
    if not zones:
        print("Warning: No zones defined in policy file", file=sys.stderr)
        sys.exit(0)
    
    print(f"Loaded {len(depgraph.get('nodes', []))} nodes from {depgraph_path}")
    print(f"Checking {len(zones)} zone(s) with {args.jobs} parallel jobs")
    
    # Collect all work items
    results = []
    total_decls = 0
    
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as executor:
        futures = []
        
        for zone in zones:
            decls = decls_for_zone(depgraph, zone["include"], zone.get("exclude", []))
            print(f"Zone '{zone['name']}': {len(decls)} declarations")
            total_decls += len(decls)
            
            for decl in decls:
                future = executor.submit(run_one, decl, zone, project_root)
                futures.append(future)
        
        # Collect results with progress
        print(f"\nRunning checks on {total_decls} declarations...")
        completed = 0
        for future in concurrent.futures.as_completed(futures):
            result = future.result()
            results.append(result)
            completed += 1
            if completed % 10 == 0 or completed == total_decls:
                print(f"  Progress: {completed}/{total_decls}", end="\r")
        print()  # newline after progress
    
    # Write report
    report = {
        "results": results,
        "summary": {
            "total": len(results),
            "passed": sum(1 for r in results if r.get("ok", False)),
            "failed": sum(1 for r in results if not r.get("ok", False))
        }
    }
    
    with open(out_path, "w") as f:
        json.dump(report, f, indent=2)
    
    # Print summary
    passed = report["summary"]["passed"]
    failed = report["summary"]["failed"]
    total = report["summary"]["total"]
    
    print(f"\n{'='*60}")
    print(f"LeanParanoia Policy Check Results")
    print(f"{'='*60}")
    print(f"Total:  {total} declarations")
    print(f"Passed: {passed} ✓")
    print(f"Failed: {failed} ✗")
    print(f"\nReport written to: {out_path}")
    
    if failed > 0:
        print(f"\nFailing declarations:")
        for r in results:
            if not r.get("ok", False):
                error_msg = r.get("error", r.get("stderr", "unknown error"))
                print(f"  ✗ {r['decl']}")
                if error_msg:
                    # Print first line of error
                    first_line = error_msg.split('\n')[0][:100]
                    print(f"    {first_line}")
        sys.exit(1)
    else:
        print("\n✓ All checks passed!")
        sys.exit(0)


if __name__ == "__main__":
    main()
