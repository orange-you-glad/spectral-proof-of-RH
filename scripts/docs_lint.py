#!/usr/bin/env python3
"""Lint Markdown documentation files.

Checks all ``*.md`` files under the repository root for:
- Proper header nesting (no level jumps > 1)
- Presence of a ``## Usage`` section
- Broken relative links
- Simple table formatting sanity

Example output::

    docs/README.md:12: header level jump 1->3
    README.md: missing '## Usage' section
"""
from __future__ import annotations

import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
HEADER_RE = re.compile(r"^(#+) ")
LINK_RE = re.compile(r"\[[^\]]+\]\(([^)]+)\)")
TABLE_DIVIDER_RE = re.compile(r"^\s*\|(?:\s*:?-+:?\s*\|)+\s*$")


def check_file(path: str) -> list[str]:
    errors: list[str] = []
    with open(path, "r", encoding="utf-8") as f:
        lines = f.readlines()

    # header nesting
    prev = 0
    for i, line in enumerate(lines, start=1):
        m = HEADER_RE.match(line)
        if m:
            level = len(m.group(1))
            if prev and level - prev > 1:
                errors.append(f"{path}:{i}: header level jump {prev}->{level}")
            prev = level

    # required section
    if "## Usage" not in "".join(lines):
        errors.append(f"{path}: missing '## Usage' section")

    # broken relative links
    for m in LINK_RE.finditer("".join(lines)):
        link = m.group(1)
        if "://" in link or link.startswith("#"):
            continue
        target = os.path.join(os.path.dirname(path), link)
        if not os.path.exists(target):
            errors.append(f"{path}: broken link {link}")

    # malformed tables - look for a header row followed by a divider
    for idx, line in enumerate(lines[:-1]):
        if "|" in line and "|" in lines[idx + 1]:
            if TABLE_DIVIDER_RE.match(lines[idx + 1]):
                continue
            if line.strip().startswith("|"):
                errors.append(f"{path}:{idx + 2}: malformed table divider")

    return errors


def main() -> None:
    all_errors: list[str] = []
    for dirpath, _, filenames in os.walk(ROOT):
        for fname in filenames:
            if fname.endswith(".md"):
                path = os.path.join(dirpath, fname)
                all_errors.extend(check_file(path))
    if all_errors:
        for err in all_errors:
            print(err)
        print("\n🔥 Documentation lint failed.")
        sys.exit(1)
    print("✅ Documentation lint passed.")


if __name__ == "__main__":
    main()
