#!/usr/bin/env python3
"""Add clickable links to the import graph SVG.

Each node links to its corresponding Lean documentation page.
"""

import re
import sys
from pathlib import Path

DOCS_BASE = "https://cameronfreer.github.io/exchangeability/docs"


def module_to_url(module_name: str) -> str:
    """Convert a Lean module name to its documentation URL."""
    path = module_name.replace(".", "/")
    return f"{DOCS_BASE}/{path}.html"


def make_svg_clickable(svg_content: str) -> str:
    """Wrap each node group in an <a> element linking to docs."""
    # Split into lines for processing
    lines = svg_content.split('\n')
    output_lines = []

    i = 0
    node_count = 0
    while i < len(lines):
        line = lines[i]

        # Check if this is a node start (comment line with module name)
        # Pattern: <!-- Exchangeability.Module.Name -->
        node_comment_match = re.match(r'^<!-- (Exchangeability\.[^\s]+) -->$', line.strip())

        if node_comment_match:
            module_name = node_comment_match.group(1)
            # Check if next line starts a node group
            if i + 1 < len(lines) and '<g id="node' in lines[i + 1] and 'class="node"' in lines[i + 1]:
                url = module_to_url(module_name)
                output_lines.append(line)  # Keep the comment
                i += 1

                # Add opening <a> tag
                output_lines.append(f'<a xlink:href="{url}" target="_blank">')

                # Find the closing </g> for this node (it's a simple structure, no nesting in nodes)
                g_depth = 0
                while i < len(lines):
                    node_line = lines[i]
                    output_lines.append(node_line)

                    if '<g ' in node_line or '<g>' in node_line:
                        g_depth += 1
                    if '</g>' in node_line:
                        g_depth -= 1
                        if g_depth == 0:
                            # Close the <a> tag
                            output_lines.append('</a>')
                            node_count += 1
                            break
                    i += 1
            else:
                output_lines.append(line)
        else:
            output_lines.append(line)

        i += 1

    print(f"Processed {node_count} nodes")
    return '\n'.join(output_lines)


def main():
    if len(sys.argv) < 2:
        input_path = Path("blueprint/web/import_graph_colored.svg")
    else:
        input_path = Path(sys.argv[1])

    if len(sys.argv) < 3:
        output_path = input_path.with_stem(input_path.stem + "_linked")
    else:
        output_path = Path(sys.argv[2])

    print(f"Reading: {input_path}")
    svg_content = input_path.read_text()

    print("Adding clickable links...")
    linked_svg = make_svg_clickable(svg_content)

    print(f"Writing: {output_path}")
    output_path.write_text(linked_svg)


if __name__ == "__main__":
    main()
