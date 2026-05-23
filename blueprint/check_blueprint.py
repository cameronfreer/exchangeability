#!/usr/bin/env python3
"""Blueprint consistency checks.

Runs three checks against `blueprint/src/content.tex` and `blueprint/lean_decls`:

  1. Every `\\lean{X}` in content.tex has X listed in `blueprint/lean_decls`.
  2. Every entry in `blueprint/lean_decls` is `\\lean{}`-cited from content.tex.
  3. Every `\\ref{Y}` / `\\uses{Y, Z, ...}` target resolves to a `\\label{Y}`
     defined in content.tex.

Plus a duplicate-label check.

Exits 0 on clean, 1 on any drift. Designed to run in CI alongside
`lake exe checkdecls blueprint/lean_decls`.

Run with no args from any directory; resolves files relative to this script.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent
CONTENT = ROOT / "src" / "content.tex"
DECLS = ROOT / "lean_decls"

LEAN_RE = re.compile(r"\\lean\{([^}]+)\}")
LABEL_RE = re.compile(r"\\label\{([^}]+)\}")
REF_RE = re.compile(r"\\ref\{([^}]+)\}")
USES_RE = re.compile(r"\\uses\{([^}]+)\}")
COMMENT_RE = re.compile(r"(?<!\\)%.*$", re.MULTILINE)


def strip_comments(text: str) -> str:
    """Drop LaTeX `%`-comments, respecting `\\%` escapes."""
    return COMMENT_RE.sub("", text)


def parse_content(text: str) -> tuple[set[str], set[str], list[str], set[str]]:
    """Return (lean_cites, labels_defined, label_dups, label_refs).

    `label_dups` is a list (not set) so the report can show duplicates verbatim.
    `label_refs` is the union of `\\ref{...}` and the comma-separated entries
    inside each `\\uses{...}`.
    """
    text = strip_comments(text)
    lean_cites = {m.strip() for m in LEAN_RE.findall(text)}

    label_list = [m.strip() for m in LABEL_RE.findall(text)]
    labels_defined = set(label_list)
    seen: set[str] = set()
    label_dups: list[str] = []
    for lbl in label_list:
        if lbl in seen and lbl not in label_dups:
            label_dups.append(lbl)
        seen.add(lbl)

    refs: set[str] = set(m.strip() for m in REF_RE.findall(text))
    for group in USES_RE.findall(text):
        for part in group.split(","):
            part = part.strip()
            if part:
                refs.add(part)

    return lean_cites, labels_defined, label_dups, refs


def parse_decls(text: str) -> set[str]:
    return {line.strip() for line in text.splitlines() if line.strip()}


def report(title: str, items: list[str] | set[str]) -> None:
    items = sorted(items)
    print(f"  {title} ({len(items)}):")
    for x in items:
        print(f"    - {x}")


def main() -> int:
    if not CONTENT.exists():
        print(f"error: {CONTENT} not found", file=sys.stderr)
        return 2
    if not DECLS.exists():
        print(f"error: {DECLS} not found", file=sys.stderr)
        return 2

    content_text = CONTENT.read_text()
    decls_text = DECLS.read_text()

    lean_cites, labels_defined, label_dups, refs = parse_content(content_text)
    decls = parse_decls(decls_text)

    cited_not_in_decls = sorted(lean_cites - decls)
    in_decls_not_cited = sorted(decls - lean_cites)
    refs_without_label = sorted(refs - labels_defined)

    failures = 0

    if cited_not_in_decls:
        failures += 1
        print("FAIL: \\lean{...} citations missing from blueprint/lean_decls:")
        report("missing", cited_not_in_decls)
        print("  (add these to blueprint/lean_decls, or remove the \\lean{} citation)")
        print()

    if in_decls_not_cited:
        failures += 1
        print("FAIL: blueprint/lean_decls entries with no \\lean{} citation in content.tex:")
        report("orphan", in_decls_not_cited)
        print("  (cite them in content.tex, or remove them from lean_decls)")
        print()

    if refs_without_label:
        failures += 1
        print("FAIL: \\ref{} or \\uses{} targets with no matching \\label{}:")
        report("dangling", refs_without_label)
        print()

    if label_dups:
        failures += 1
        print("FAIL: duplicate \\label{} definitions:")
        report("duplicate", label_dups)
        print()

    if failures == 0:
        n_lean = len(lean_cites)
        n_labels = len(labels_defined)
        n_refs = len(refs)
        n_decls = len(decls)
        print(
            f"OK: {n_lean} \\lean cites, {n_labels} labels, "
            f"{n_refs} refs/uses, {n_decls} lean_decls — all consistent."
        )
        return 0
    return 1


if __name__ == "__main__":
    sys.exit(main())
