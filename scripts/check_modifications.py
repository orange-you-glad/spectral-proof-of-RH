#!/usr/bin/env python3
"""Validate modifications against DAG rules."""
from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(".").resolve()
DAG_NODES = Path("dag/dag_nodes.json")


def changed_files() -> list[Path]:
    out = subprocess.check_output(["git", "diff", "--name-only", "--cached"]).decode()
    return [Path(p) for p in out.splitlines() if p]


def load_nodes() -> dict[str, dict]:
    if not DAG_NODES.exists():
        return {}
    return json.load(DAG_NODES.open())


def main() -> None:
    nodes = load_nodes()
    chapters_allowed = {data["chapter"] for data in nodes.values() if "chapter" in data}
    errors: list[str] = []
    for path in changed_files():
        if path.parts[:2] == ("src", "chapters"):
            chapter = path.parts[2]
            if chapters_allowed and chapter not in chapters_allowed:
                errors.append(f"edit to {chapter} not in DAG")
            if path.parts[-2] == "proofs":
                base = path.stem.replace("prf_", "")
                prefix = base.split("_", 1)[0]
                if prefix not in {"thm", "lem", "prop", "cor"}:
                    errors.append(f"invalid proof prefix in {path}")
    if errors:
        for e in errors:
            print(f"❌ {e}")
        sys.exit(1)
    print("✅ Modifications conform to DAG rules.")


if __name__ == "__main__":
    main()
