#!/usr/bin/env python3
"""Check LaTeX build log for warnings or bad boxes."""
import os
import re
import sys

# Possible locations of the LaTeX log produced by latexmk
LOG_PATHS = ["src/manuscript.log", "src/main.log"]

PATTERNS = [
    re.compile(r"LaTeX Warning"),
    re.compile(r"Overfull \\hbox"),
    re.compile(r"Underfull \\hbox"),
]


def find_log() -> str:
    for path in LOG_PATHS:
        if os.path.isfile(path):
            return path
    print("❌ No LaTeX log file found.")
    sys.exit(1)


def main() -> None:
    log_path = find_log()
    with open(log_path, "r", encoding="utf-8") as f:
        lines = f.readlines()

    issues = [
        line.strip()
        for line in lines
        if any(p.search(line) for p in PATTERNS)
    ]

    if issues:
        print("🔥 LaTeX warnings detected:")
        for line in issues:
            print(line)
        sys.exit(1)

    print("✅ LaTeX log clean: no warnings or bad boxes.")


if __name__ == "__main__":
    main()
