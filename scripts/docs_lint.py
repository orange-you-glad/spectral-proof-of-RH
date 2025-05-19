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

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
HEADER_RE = re.compile(r"^(#+) ")
LINK_RE = re.compile(r"\[[^\]]+\]\(([^)]+)\)")
TABLE_DIVIDER_RE = re.compile(r"^\s*\|(?:\s*:?-+:?\s*\|)+\s*$")

EXCLUDE_DIRS = {".venv", "site-packages", "dist-info", "__pycache__"}


def should_exclude(path: Path) -> bool:
    return any(part in EXCLUDE_DIRS for part in path.parts)


def check_file(path: Path) -> list[str]:
    errors: list[str] = []
    try:
        lines = path.read_text(encoding="utf-8").splitlines()
    except Exception as e:
        return [f"{path}: ⚠️ error reading file ({e})"]

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
    if "## Usage" not in "\n".join(lines):
        errors.append(f"{path}: missing '## Usage' section")

    # broken relative links
    for m in LINK_RE.finditer("\n".join(lines)):
        link = m.group(1)
        if "://" in link or link.startswith("#"):
            continue
        target = path.parent / link
        if not target.exists():
            errors.append(f"{path}: broken link {link}")

    # malformed tables
    for idx, line in enumerate(lines[:-1]):
        if "|" in line and "|" in lines[idx + 1]:
            if TABLE_DIVIDER_RE.match(lines[idx + 1]):
                continue
            if line.strip().startswith("|"):
                errors.append(f"{path}:{idx + 2}: malformed table divider")

    return errors


def main() -> None:
    all_errors: list[str] = []
    for md_file in ROOT.rglob("*.md"):
        if should_exclude(md_file):
            continue
        all_errors.extend(check_file(md_file))

    if all_errors:
        for err in all_errors:
            print(err)
        print("\n🔥 Documentation lint failed.")
        sys.exit(1)

    print("✅ Documentation lint passed.")


if __name__ == "__main__":
    main()
