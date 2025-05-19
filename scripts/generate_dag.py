#!/usr/bin/env python3
"""Regenerate DAG nodes and edges from LaTeX sources."""
from __future__ import annotations

import hashlib
import json
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from tests import common

ROOT_DIR = Path("src/chapters")
NODES_OUT = Path("dag/dag_nodes.json")
EDGES_OUT = Path("dag/dag_edges.json")
ENV_DIRS = ["thms", "lems", "defs", "props", "cors", "rems"]
PREFIX_MAP = {
    "thm": "theorem",
    "lem": "lemma",
    "def": "definition",
    "prop": "proposition",
    "cor": "corollary",
    "rmk": "remark",
    "rem": "remark",
}

REF_PATTERN = re.compile(r"\\(?:[A-Za-z]*ref|eqref)\{([^}]+)\}")


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    h.update(path.read_bytes())
    return h.hexdigest()


def gather_nodes() -> dict[str, dict]:
    nodes: dict[str, dict] = {}
    for chapter in sorted(ROOT_DIR.iterdir()):
        if not chapter.is_dir():
            continue
        m = re.match(r"(\d+)", chapter.name)
        if not m:
            continue
        chapter_num = int(m.group(1))
        for env in ENV_DIRS:
            env_dir = chapter / env
            if not env_dir.is_dir():
                continue
            for tex in sorted(env_dir.glob("*.tex")):
                label = common.find_label_in_tex(str(tex))
                if not label:
                    print(f"warning: missing label in {tex}", file=sys.stderr)
                    continue
                prefix = label.split(":")[0]
                typ = PREFIX_MAP.get(prefix, prefix)
                nodes[label] = {
                    "file": str(tex),
                    "type": typ,
                    "chapter": chapter_num,
                    "hash": sha256(tex),
                }
    return dict(sorted(nodes.items()))


def gather_edges(nodes: dict[str, dict]) -> dict[str, list[str]]:
    edges: dict[str, set[str]] = {}
    for chapter in sorted(ROOT_DIR.iterdir()):
        proofs_dir = chapter / "proofs"
        if not proofs_dir.is_dir():
            continue
        for prf in sorted(proofs_dir.glob("prf_*.tex")):
            base = prf.stem[len("prf_") :]
            target = common.expected_label_from_filename(base + ".tex")
            if not target:
                print(f"warning: malformed proof file {prf}", file=sys.stderr)
                continue
            content = prf.read_text(encoding="utf-8")
            refs = {m.strip() for m in REF_PATTERN.findall(content)}
            for ref in refs:
                if ref == target:
                    continue
                prefix = ref.split(":")[0]
                if prefix in PREFIX_MAP:
                    edges.setdefault(ref, set()).add(target)
    for label in nodes:
        edges.setdefault(label, set())
    return {k: sorted(v) for k, v in sorted(edges.items())}


def main() -> None:
    nodes = gather_nodes()
    NODES_OUT.parent.mkdir(parents=True, exist_ok=True)
    with NODES_OUT.open("w", encoding="utf-8") as f:
        json.dump(nodes, f, indent=2, sort_keys=True)
    print(f"✅ wrote {NODES_OUT} ({len(nodes)} nodes)")

    edges = gather_edges(nodes)
    with EDGES_OUT.open("w", encoding="utf-8") as f:
        json.dump(edges, f, indent=2, sort_keys=True)
    edge_count = sum(len(v) for v in edges.values())
    print(f"✅ wrote {EDGES_OUT} ({edge_count} edges)")


if __name__ == "__main__":
    main()
