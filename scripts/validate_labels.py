#!/usr/bin/env python3
import os
import re
import sys

ROOT_DIR = "src/chapters"
VALID_PREFIXES = ["thm", "lem", "def", "prop", "cor", "rmk"]

def find_tex_files(root):
    for dirpath, _, filenames in os.walk(root):
        for f in filenames:
            if f.endswith(".tex"):
                yield os.path.join(dirpath, f)

def expected_label_from_filename(filename):
    name = os.path.splitext(os.path.basename(filename))[0]
    for prefix in VALID_PREFIXES:
        if name.startswith(f"{prefix}_"):
            return f"{prefix}:{name[len(prefix)+1:]}"
    return None

def validate_labels():
    errors = []

    for path in find_tex_files(ROOT_DIR):
        with open(path, "r", encoding="utf-8") as f:
            content = f.read()

        expected = expected_label_from_filename(path)
        if expected:
            label_match = re.search(r"\\label\{([^}]+)\}", content)
            if not label_match:
                errors.append(f"❌ Missing \\label{{...}} in {path}")
                continue

            actual = label_match.group(1).strip()
            if actual != expected:
                errors.append(f"❌ Mismatched label in {path}\n   ⟶ expected: {expected}\n   ⟶ found:    {actual}")

    if errors:
        for err in errors:
            print(err)
        print("\n🔥 Label validation failed.")
        sys.exit(1)
    else:
        print("✅ All labels valid.")

if __name__ == "__main__":
    validate_labels()
