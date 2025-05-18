#!/usr/bin/env python3
"""Shared utilities for project scripts."""
import os
import re
from typing import Iterator

ROOT_DIR = "src/chapters"
VALID_PREFIXES = ["thm", "lem", "def", "prop", "cor", "rmk"]


def find_tex_files(root: str) -> Iterator[str]:
    """Yield paths to all .tex files under ``root``."""
    for dirpath, _, filenames in os.walk(root):
        for filename in filenames:
            if filename.endswith(".tex"):
                yield os.path.join(dirpath, filename)


def expected_label_from_filename(filename: str) -> str | None:
    """Return expected label ``prefix:suffix`` for a theorem-like file."""
    name = os.path.splitext(os.path.basename(filename))[0]
    for prefix in VALID_PREFIXES:
        if name.startswith(f"{prefix}_"):
            suffix = name[len(prefix) + 1 :]
            return f"{prefix}:{suffix}"
    return None


def find_label_in_tex(path: str) -> str | None:
    """Extract the first ``\\label{...}`` from ``path``, if present."""
    with open(path, "r", encoding="utf-8") as file:
        content = file.read()
    match = re.search(r"\\label\{([^}]+)\}", content)
    if match:
        return match.group(1).strip()
    return None
