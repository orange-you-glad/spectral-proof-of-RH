#!/usr/bin/env python3
"""Regenerate DAG nodes and edges from LaTeX sources with file-label sync check."""
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


def gather_nodes() -> tuple[dict[str, dict], list[str]]:
    nodes: dict[str, dict] = {}
    missing_labels: list[str] = []
    mismatches: list[str] = []

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
            expected_prefix = env[:-1]  # "thms" → "thm"
            for tex in sorted(env_dir.glob("*.tex")):
                label = common.find_label_in_tex(str(tex))
                if not label:
                    print(f"warning: missing label in {tex}", file=sys.stderr)
                    missing_labels.append(str(tex))
                    continue
                try:
                    prefix, name = label.split(":")
                except ValueError:
                    print(f"⚠️ malformed label '{label}' in {tex}", file=sys.stderr)
                    mismatches.append(f"bad label: {tex}")
                    continue

                # check prefix-directory match
                if prefix != expected_prefix:
                    mismatches.append(f"mismatch in {tex} → label '{label}' not valid for dir '{env}'")
                    continue

                # check filename matches label name
                expected_filename = f"{prefix}_{name}.tex"
                if tex.name != expected_filename:
                    mismatches.append(f"filename mismatch: {tex.name} ≠ {expected_filename}")
                    continue

                # pass
                typ = PREFIX_MAP.get(prefix, prefix)
                nodes[label] = {
                    "file": str(tex),
                    "type": typ,
                    "chapter": chapter_num,
                    "hash": sha256(tex),
                }

    if mismatches:
        print("\n❌ Label-directory-filename inconsistencies detected:")
        for msg in mismatches:
            print(f"  - {msg}")
        sys.exit(1)

    return dict(sorted(nodes.items())), missing_labels


def gather_edges(nodes: dict[str, dict]) -> tuple[list[list[str]], list[str]]:
    edges = []
    missing_targets: list[str] = []
    for chapter in sorted(ROOT_DIR.iterdir()):
        proofs_dir = chapter / "proofs"
        if not proofs_dir.is_dir():
            continue
        for prf in sorted(proofs_dir.glob("prf_*.tex")):
            base = prf.stem[len("prf_") :]
            target = common.expected_label_from_filename(base + ".tex")
            if not target:
                target = f"thm:{base}"
                print(f"fallback: inferred target={target} from {prf.name}", file=sys.stderr)
            if target not in nodes:
                print(f"warning: inferred target {target} not found in node set (from {prf})", file=sys.stderr)
                missing_targets.append(f"{prf} → {target}")
                continue
            content = prf.read_text(encoding="utf-8")
            refs = {m.strip() for m in REF_PATTERN.findall(content)}
            for ref in refs:
                if ref == target:
                    continue
                prefix = ref.split(":")[0]
                if prefix in PREFIX_MAP and ref in nodes:
                    edges.append([ref, target])
    return edges, missing_targets


def main() -> None:
    nodes, missing_labels = gather_nodes()
    NODES_OUT.parent.mkdir(parents=True, exist_ok=True)
    with NODES_OUT.open("w", encoding="utf-8") as f:
        json.dump(nodes, f, indent=2, sort_keys=True)
    print(f"✅ wrote {NODES_OUT} ({len(nodes)} nodes)")

    edges, missing_targets = gather_edges(nodes)
    with EDGES_OUT.open("w", encoding="utf-8") as f:
        json.dump(edges, f, indent=2, sort_keys=True)
    print(f"✅ wrote {EDGES_OUT} ({len(edges)} edges)")

    if missing_labels:
        print(f"\n⚠️ Missing labels in {len(missing_labels)} files:")
        for path in missing_labels:
            print(f"  - {path}")

    if missing_targets:
        print(f"\n⚠️ Missing or unresolved proof targets for {len(missing_targets)} files:")
        for item in missing_targets:
            print(f"  - {item}")


if __name__ == "__main__":
    main()
