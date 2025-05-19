#!/usr/bin/env python3
"""Confirm Lean theorem stubs exist for each LaTeX theorem."""
import os
import sys

from tests import common

ROOT_DIR = common.ROOT_DIR
LEAN_ROOT = "lean"


def collect_theorem_names() -> set[str]:
    names = set()
    for path in common.find_tex_files(ROOT_DIR):
        base = os.path.basename(path)
        if base.startswith("thm_"):
            names.add(os.path.splitext(base)[0])
    return names


def main() -> None:
    if not os.path.isdir(LEAN_ROOT):
        print("❌ Lean directory missing")
        sys.exit(1)
    theorems = collect_theorem_names()
    missing = []
    for thm in theorems:
        lean_file = os.path.join(LEAN_ROOT, f"{thm}.lean")
        if not os.path.isfile(lean_file):
            missing.append(thm)
    if missing:
        for m in missing:
            print(f"❌ Lean stub missing for {m}")
        sys.exit(1)
    print("✅ All Lean stubs present")


if __name__ == "__main__":
    main()
