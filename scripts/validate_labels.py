#!/usr/bin/env python3
import sys

from scripts import common

ROOT_DIR = common.ROOT_DIR


def validate_labels():
    errors = []

    for path in common.find_tex_files(ROOT_DIR):
        expected = common.expected_label_from_filename(path)
        if expected:
            actual = common.find_label_in_tex(path)
            if actual is None:
                errors.append(f"❌ Missing \\label{{...}} in {path}")
                continue
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
