#!/usr/bin/env python3
import os
import sys

ROOT_DIR = "src/chapters"
TARGET_DIRS = ["thms", "lems", "props", "cors"]
PROOF_DIR = "proofs"


def list_label_basenames(section_path, subdir):
    dir_path = os.path.join(section_path, subdir)
    if not os.path.exists(dir_path):
        return []
    return [
        os.path.splitext(f)[0]
        for f in os.listdir(dir_path)
        if f.endswith(".tex") and f.startswith(subdir[:-1] + "_")
    ]


def list_proofs(section_path):
    proofs_path = os.path.join(section_path, PROOF_DIR)
    if not os.path.exists(proofs_path):
        return []
    return {
        os.path.splitext(f)[0]: f
        for f in os.listdir(proofs_path)
        if f.endswith(".tex") and f.startswith("prf_")
    }


def check_proofs():
    errors = []

    for section in os.listdir(ROOT_DIR):
        section_path = os.path.join(ROOT_DIR, section)
        if not os.path.isdir(section_path):
            continue

        expected_proofs = set()
        for label_dir in TARGET_DIRS:
            for base in list_label_basenames(section_path, label_dir):
                expected_proofs.add("prf_" + base)

        found_proofs = list_proofs(section_path)
        for missing in sorted(expected_proofs - set(found_proofs)):
            errors.append(f"❌ Missing proof file for: {missing} in {section}/proofs/")

    if errors:
        for err in errors:
            print(err)
        print("\n🔥 Proof mapping check failed.")
        sys.exit(1)
    else:
        print("✅ All labeled items have proofs.")


if __name__ == "__main__":
    check_proofs()
