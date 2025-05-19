#!/usr/bin/env python3
"""Ensure each chapter appears in the table of contents."""
import os
import sys

ROOT_DIR = os.path.join("src", "chapters")
TOC_FILE = os.path.join("src", "main.toc")


def main() -> None:
    if not os.path.isfile(TOC_FILE):
        print("❌ TOC file missing")
        sys.exit(1)
    with open(TOC_FILE, "r", encoding="utf-8") as f:
        toc = f.read()
    missing = []
    for chapter in sorted(os.listdir(ROOT_DIR)):
        if chapter.startswith("00_"):
            continue
        name = chapter.split("_", 1)[-1]
        if name not in toc:
            missing.append(chapter)
    if missing:
        for ch in missing:
            print(f"❌ Chapter missing from TOC: {ch}")
        sys.exit(1)
    print("✅ All chapters in TOC")


if __name__ == "__main__":
    main()
