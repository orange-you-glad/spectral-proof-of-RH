#!/usr/bin/env python3
"""Regenerate DAG nodes and edges from LaTeX sources with file-label sync check."""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from tests import common

ROOT_DIR = Path("src/chapters")
ROOT_TEX = Path("src/main.tex")
FLS_FILE = ROOT_TEX.with_suffix(".fls")
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
EXCLUDED_PREFIXES = {"sec", "app"}

REF_PATTERN = re.compile(
    r"\\(?:ref|lemref|thmref|defref|propref|corref|remref|rmkref|eqref)\{([^}]+)\}"
)

def sha256(path: Path) -> str:
    h = hashlib.sha256()
    h.update(path.read_bytes())
    return h.hexdigest()


def collect_inputs_from_fls(fls_path: Path, verbose: bool = False) -> set[str]:
    included = set()
    if not fls_path.exists():
        print(f"❌ Missing {fls_path}.", file=sys.stderr)
        print("💡 Hint: recompile with `pdflatex -recorder -output-directory=... src/main.tex`", file=sys.stderr)
        sys.exit(1)
    for line in fls_path.read_text(encoding="utf-8").splitlines():
        if line.startswith("INPUT "):
            path = Path(line[6:]).resolve()
            if path.suffix == ".tex":
                if verbose:
                    print(f"[.fls] included: {path}")
                included.add(str(path))
    return included


def gather_nodes(included_paths: set[str], verbose: bool = False) -> tuple[dict[str, dict], list[str], list[str]]:
    nodes, missing_labels, mismatches, missing_inputs = {}, [], [], []

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
            expected_prefix = env[:-1]
            for tex in sorted(env_dir.glob("*.tex")):
                label = common.find_label_in_tex(str(tex))
                if not label:
                    print(f"warning: missing label in {tex}", file=sys.stderr)
                    missing_labels.append(str(tex))
                    continue
                try:
                    prefix, name = label.split(":")
                except ValueError:
                    mismatches.append(f"bad label: {tex}")
                    continue
                if prefix in EXCLUDED_PREFIXES:
                    continue
                if prefix != expected_prefix:
                    mismatches.append(f"mismatch in {tex} → label '{label}' not valid for dir '{env}'")
                    continue
                if tex.name != f"{prefix}_{name}.tex":
                    mismatches.append(f"filename mismatch: {tex.name} ≠ {prefix}_{name}.tex")
                    continue

                resolved_path = str(tex.resolve())
                if verbose:
                    print(f"[check] {resolved_path} {'✅' if resolved_path in included_paths else '❌'}")
                if resolved_path not in included_paths:
                    missing_inputs.append(resolved_path)

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

    return dict(sorted(nodes.items())), missing_labels, missing_inputs


def gather_edges(nodes: dict[str, dict]) -> tuple[list[list[str]], list[str]]:
    edges, missing_targets = [], []

    for chapter in sorted(ROOT_DIR.iterdir()):
        proofs_dir = chapter / "proofs"
        if not proofs_dir.is_dir():
            continue
        for prf in sorted(proofs_dir.glob("prf_*.tex")):
            base = prf.stem[len("prf_"):]
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

            print(f"\n[debug] {prf.name} references in {target}:")
            for ref in sorted(refs):
                if ref == target:
                    continue
                prefix = ref.split(":")[0]
                if prefix in EXCLUDED_PREFIXES:
                    print(f"  ⏭️ {ref} [skipped non-logical]")
                    continue
                if ref in nodes:
                    print(f"  → {ref} [OK]")
                    if prefix in PREFIX_MAP:
                        edges.append([ref, target])
                else:
                    print(f"  ✗ {ref} [NOT FOUND]")

    return edges, missing_targets


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--strict", action="store_true", help="Exit with code 1 on any warning.")
    parser.add_argument("--verbose", action="store_true", help="Show diagnostic file paths.")
    args = parser.parse_args()

    included_paths = collect_inputs_from_fls(FLS_FILE, verbose=args.verbose)
    nodes, missing_labels, missing_inputs = gather_nodes(included_paths, verbose=args.verbose)
    NODES_OUT.parent.mkdir(parents=True, exist_ok=True)

    with NODES_OUT.open("w", encoding="utf-8") as f:
        json.dump(nodes, f, indent=2, sort_keys=True)
    print(f"✅ wrote {NODES_OUT} ({len(nodes)} nodes)")

    edges, missing_targets = gather_edges(nodes)
    with EDGES_OUT.open("w", encoding="utf-8") as f:
        json.dump(edges, f, indent=2, sort_keys=True)
    print(f"✅ wrote {EDGES_OUT} ({len(edges)} edges)")

    any_issue = False
    if missing_labels:
        print(f"\n⚠️ Missing labels in {len(missing_labels)} files:")
        any_issue = True
        for path in missing_labels:
            print(f"  - {path}")

    if missing_inputs:
        print("\n⚠️ Unreferenced .tex files (not \\input according to .fls):")
        any_issue = True
        for path in missing_inputs:
            print(f"  - {path}")

    if missing_targets:
        print(f"\n⚠️ Missing or unresolved proof targets for {len(missing_targets)} files:")
        any_issue = True
        for item in missing_targets:
            print(f"  - {item}")

    if args.strict and any_issue:
        sys.exit(1)


if __name__ == "__main__":
    main()
