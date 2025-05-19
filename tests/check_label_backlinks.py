#!/usr/bin/env python3
"""Ensure every label is referenced at least once."""
import os
import re
import sys

from tests import common

ROOT_DIR = common.ROOT_DIR
LABEL_PATTERN = re.compile(r"\\label\{([^}]+)\}")
REF_PATTERN = re.compile(r"\\(?:ref|eqref|cref|Cref)\{([^}]+)\}")


def collect_labels() -> set[str]:
    labels = set()
    for path in common.find_tex_files(ROOT_DIR):
        with open(path, "r", encoding="utf-8") as f:
            labels.update(m.group(1) for m in LABEL_PATTERN.finditer(f.read()))
    return labels


def collect_refs() -> set[str]:
    refs = set()
    for path in common.find_tex_files(ROOT_DIR):
        with open(path, "r", encoding="utf-8") as f:
            refs.update(m.group(1) for m in REF_PATTERN.finditer(f.read()))
    return refs


def main() -> None:
    labels = collect_labels()
    refs = collect_refs()
    missing = labels - refs
    if missing:
        for lbl in sorted(missing):
            print(f"❌ Label not referenced: {lbl}")
        sys.exit(1)
    print("✅ All labels referenced")


if __name__ == "__main__":
    main()
