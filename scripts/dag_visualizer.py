#!/usr/bin/env python3
"""Render DAG edges to Graphviz dot format."""

from __future__ import annotations
import json
from pathlib import Path

ROOT = Path("dag")
EDGES = ROOT / "dag_edges.json"
DOT_OUT = ROOT / "dag.dot"


def main() -> None:
    # Load edge list
    edges = json.load(EDGES.open())

    # Collect all node IDs
    nodes = set()
    for src, dst in edges:
        nodes.add(src)
        nodes.add(dst)

    with DOT_OUT.open("w", encoding="utf-8") as f:
        f.write("digraph DAG {\n")
        f.write("  rankdir=LR;\n")  # optional: left-to-right layout
        f.write("  node [shape=box, fontsize=10];\n")

        # Emit all edges
        for src, dst in edges:
            f.write(f'    "{src}" -> "{dst}";\n')

        # Emit orphan nodes (not referenced in edges)
        for node in sorted(nodes):
            f.write(f'    "{node}";\n')

        f.write("}\n")

    print(f"✅ Wrote DAG with {len(nodes)} nodes and {len(edges)} edges to {DOT_OUT}")


if __name__ == "__main__":
    main()
