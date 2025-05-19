#!/usr/bin/env python3
"""Render DAG edges to Graphviz dot."""
from __future__ import annotations

import json
from pathlib import Path

ROOT = Path("dag")
EDGES = ROOT / "dag_edges.json"
DOT_OUT = ROOT / "dag.dot"


def main() -> None:
    data = json.load(EDGES.open())
    with DOT_OUT.open("w", encoding="utf-8") as f:
        f.write("digraph DAG {\n")
        for src, dst_list in data.items():
            if not dst_list:
                f.write(f"    {src};\n")
            for dst in dst_list:
                f.write(f"    {src} -> {dst};\n")
        f.write("}\n")
    print(f"✅ wrote {DOT_OUT}")


if __name__ == "__main__":
    main()
