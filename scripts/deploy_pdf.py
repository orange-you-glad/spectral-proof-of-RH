#!/usr/bin/env python3
import os
import shutil

SRC_PDF = "src/manuscript.pdf"
DEST_DIR = "docs"
DEST_PDF = os.path.join(DEST_DIR, "manuscript.pdf")
VERSION_FILE = "VERSION"


def get_version():
    if not os.path.isfile(VERSION_FILE):
        print(f"❌ VERSION file not found at {VERSION_FILE}")
        exit(1)
    with open(VERSION_FILE, "r") as f:
        version = f.read().strip()
    if not version:
        print("❌ VERSION file is empty.")
        exit(1)
    return version


def deploy():
    if not os.path.isfile(SRC_PDF):
        print(f"❌ PDF not found at {SRC_PDF}")
        exit(1)

    version = get_version()
    DEST_VERSIONED = os.path.join(DEST_DIR, f"manuscript-v{version}.pdf")

    os.makedirs(DEST_DIR, exist_ok=True)
    shutil.copy2(SRC_PDF, DEST_PDF)
    shutil.copy2(SRC_PDF, DEST_VERSIONED)

    print(f"✅ Deployed {SRC_PDF} → {DEST_PDF}")
    print(f"📦 Versioned copy → {DEST_VERSIONED}")


if __name__ == "__main__":
    deploy()
