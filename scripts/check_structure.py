#!/usr/bin/env python3
import os
import sys

ROOT_DIR = "src/chapters"
REQUIRED_FILES = ["intro.tex", "summary.tex"]
REQUIRED_SUBDIRS = ["defs", "lems", "thms", "props", "cors", "rems", "proofs"]
VALID_PREFIXES = ["thm", "lem", "def", "prop", "cor", "rmk"]

# Ignore these directories (e.g., frontmatter or non-modular sections)
IGNORE_SECTIONS = {"00_matter", "metadata", ".DS_Store"}


def check_section_structure(section_path, section_name):
    errors = []

    # Required files
    for fname in REQUIRED_FILES:
        path = os.path.join(section_path, fname)
        if not os.path.isfile(path):
            errors.append(f"❌ Missing file: {fname} in {section_name}/")

    # Required subdirectories
    for subdir in REQUIRED_SUBDIRS:
        sub_path = os.path.join(section_path, subdir)
        if not os.path.isdir(sub_path):
            errors.append(f"❌ Missing directory: {subdir}/ in {section_name}/")
        else:
            errors.extend(check_bad_filenames(sub_path))

    # Check section driver matches folder name
    slug = section_name.split("_", 1)[-1]
    expected_main = f"{slug}.tex"
    if not os.path.isfile(os.path.join(section_path, expected_main)):
        errors.append(
            f"❌ Missing section driver: {expected_main} in {section_name}/"
        )

    return errors


def check_bad_filenames(sub_path):
    errors = []
    for fname in os.listdir(sub_path):
        if not fname.endswith(".tex"):
            continue
        for prefix in VALID_PREFIXES:
            if fname.startswith(f"{prefix}:"):
                corrected = fname.replace(":", "_")
                rel_path = os.path.join(sub_path, fname)
                errors.append(
                    f"❌ Invalid filename: {rel_path}\n"
                    f"   ⟶ should be: {corrected}"
                )
                break
    return errors


def check_all_sections():
    all_errors = []
    for section in os.listdir(ROOT_DIR):
        if section in IGNORE_SECTIONS:
            print(f"⏭️ Skipping ignored section: {section}")
            continue

        section_path = os.path.join(ROOT_DIR, section)
        if not os.path.isdir(section_path):
            continue

        errors = check_section_structure(section_path, section)
        all_errors.extend(errors)

    if all_errors:
        for err in all_errors:
            print(err)
        print("\n🔥 Structural integrity check failed.")
        sys.exit(1)

    print("✅ All section directories have required structure.")


if __name__ == "__main__":
    check_all_sections()
