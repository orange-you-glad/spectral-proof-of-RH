#!/usr/bin/env python3
"""Attempt to compile the LaTeX document with latexmk."""
import subprocess
import sys
import os

MAIN_TEX = os.path.join("src", "main.tex")


def main() -> None:
    if not os.path.isfile(MAIN_TEX):
        print("❌ src/main.tex not found")
        sys.exit(1)
    cmd = ["latexmk", "-pdf", "-silent", "-f", MAIN_TEX]
    print("Running:", " ".join(cmd))
    result = subprocess.run(cmd, capture_output=True, text=True)
    if result.returncode != 0:
        print(result.stdout)
        print(result.stderr)
        print("❌ LaTeX compilation failed")
        sys.exit(1)
    print("✅ LaTeX compilation succeeded")


if __name__ == "__main__":
    main()
