#!/usr/bin/env python3
"""Basic checks on the compiled PDF output."""
import os
import sys

PDF_PATH = os.path.join("src", "main.pdf")
MAX_SIZE_MB = 20


def main() -> None:
    if not os.path.isfile(PDF_PATH):
        print("❌ PDF not found:", PDF_PATH)
        sys.exit(1)
    size_mb = os.path.getsize(PDF_PATH) / (1024 * 1024)
    if size_mb > MAX_SIZE_MB:
        print(f"❌ PDF too large: {size_mb:.1f} MB > {MAX_SIZE_MB} MB")
        sys.exit(1)
    print(f"✅ PDF exists ({size_mb:.1f} MB)")


if __name__ == "__main__":
    main()
