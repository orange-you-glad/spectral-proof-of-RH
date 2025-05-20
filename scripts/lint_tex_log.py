#!/usr/bin/env python3
"""Parse ``src/main.log`` for common LaTeX issues."""
from __future__ import annotations

import os
import re
import sys

ROOT_DIR = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LOG_PATHS = [
    os.path.join(ROOT_DIR, "src", "main.log"),
    os.path.join(ROOT_DIR, "src", "manuscript.log"),
]

OVERFULL_RE = re.compile(r"Overfull \\hbox")
UNDERFULL_RE = re.compile(r"Underfull \\vbox")
MISSING_REF_RE = re.compile(r"Reference .* undefined")
UNCITED_RE = re.compile(r"Citation `[^']+' undefined")


def parse_log(path: str) -> list[str]:
    if not os.path.isfile(path):
        return [f"log file not found: {path}"]
    errors: list[str] = []
    with open(path, "r", encoding="utf-8", errors="ignore") as f:
        for line in f:
            if OVERFULL_RE.search(line):
                errors.append(f"overfull hbox: {line.strip()}")
            if UNDERFULL_RE.search(line):
                errors.append(f"underfull vbox: {line.strip()}")
            if MISSING_REF_RE.search(line):
                errors.append(f"missing ref: {line.strip()}")
            if UNCITED_RE.search(line):
                errors.append(f"bad citation: {line.strip()}")
    return errors


def find_log() -> str | None:
    for path in LOG_PATHS:
        if os.path.isfile(path):
            return path
    return None


def main() -> None:
    log_path = find_log()
    if log_path is None:
        print(f"❌ no log file found in: {', '.join(LOG_PATHS)}")
        print("\n🔥 LaTeX log lint failed.")
        sys.exit(1)

    issues = parse_log(log_path)
    if issues:
        for issue in issues:
            print(f"❌ {issue}")
        print("\n🔥 LaTeX log lint failed.")
        sys.exit(1)
    print("✅ LaTeX log clean.")


if __name__ == "__main__":
    main()
