#!/usr/bin/env python3
import os
import re
import sys

ROOT_DIR = "src/chapters"
VALID_PREFIXES = ["thm", "lem", "def", "prop", "cor", "rmk"]


def find_tex_files(root):
    for dirpath, _, filenames in os.walk(root):
        for filename in filenames:
            if filename.endswith(".tex"):
                yield os.path.join(dirpath, filename)


def expected_label_from_filename(filename):
    name = os.path.splitext(os.path.basename(filename))[0]
    for prefix in VALID_PREFIXES:
        if name.startswith(f"{prefix}_"):
            suffix = name[len(prefix) + 1:]
            return f"{prefix}:{suffix}"
    return None


def validate_labels():
    errors = []

    for path in find_tex_files(ROOT_DIR):
        with open(path, "r", encoding="utf-8") as file:
            content = file.read()

        expected = expected_label_from_filename(path)
        if expected:
            match = re.search(r"\\label\{([^}]+)\}", content)
            if not match:
                errors.append(f"❌ Missing \\label{{...}} in {path}")
                continue

            actual = match.group(1).strip()
            if actual != expected:
                errors.append(
                    f"❌ Mismatched label in {path}\n"
                    f"   ⟶ expected: {expected}\n"
                    f"   ⟶ found:    {actual}"
                )

    if errors:
        for err in errors:
            print(err)
        print("\n🔥 Label validation failed.")
        sys.exit(1)

    print("✅ All labels valid.")


if __name__ == "__main__":
    validate_labels()
