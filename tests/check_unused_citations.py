#!/usr/bin/env python3
"""Identify unused citation keys in references.bib."""
import os
import re
import sys

from tests import common

ROOT_DIR = common.ROOT_DIR
BIB_PATH = os.path.join("src", "references.bib")
CITE_PATTERN = re.compile(r"\\cite\{([^}]+)\}")


def collect_cite_keys_in_tex() -> set[str]:
    keys = set()
    for path in common.find_tex_files(ROOT_DIR):
        with open(path, "r", encoding="utf-8") as f:
            for line in f:
                for m in CITE_PATTERN.finditer(line):
                    keys.add(m.group(1))
    return keys


def collect_bib_keys() -> set[str]:
    if not os.path.isfile(BIB_PATH):
        print("❌ references.bib not found")
        sys.exit(1)
    keys = set()
    with open(BIB_PATH, "r", encoding="utf-8") as f:
        for line in f:
            if line.lstrip().startswith("@"):  # entry start
                key = line.split("{", 1)[-1].split(",", 1)[0].strip()
                keys.add(key)
    return keys


def main() -> None:
    used = collect_cite_keys_in_tex()
    bib_keys = collect_bib_keys()
    unused = bib_keys - used
    if unused:
        for key in sorted(unused):
            print(f"❌ Unused citation: {key}")
        sys.exit(1)
    print("✅ No unused citations.")


if __name__ == "__main__":
    main()
