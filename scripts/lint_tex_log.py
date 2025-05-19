#!/usr/bin/env python3
"""Parse ``src/main.log`` for common LaTeX issues."""
from __future__ import annotations

import os
import re
import sys

LOG_PATH = os.path.join(
    os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "src", "main.log"
)

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


def main() -> None:
    issues = parse_log(LOG_PATH)
    if issues:
        for issue in issues:
            print(f"❌ {issue}")
        print("\n🔥 LaTeX log lint failed.")
        sys.exit(1)
    print("✅ LaTeX log clean.")


if __name__ == "__main__":
    main()
