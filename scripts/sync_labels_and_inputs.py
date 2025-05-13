#!/usr/bin/env python3
import os
import re

ROOT_DIR = "src/chapters"
VALID_PREFIXES = ["thm", "lem", "def", "prop", "cor", "rmk"]


def find_tex_files():
    for dirpath, _, filenames in os.walk(ROOT_DIR):
        for fname in filenames:
            if fname.endswith(".tex"):
                yield os.path.join(dirpath, fname)


def expected_filename_from_label(label):
    for prefix in VALID_PREFIXES:
        if label.startswith(f"{prefix}:"):
            suffix = label[len(prefix) + 1:]
            return f"{prefix}_{suffix}.tex"
    return None


def correct_filenames_and_record_renames():
    r"""Fix filenames to match their \label{...} and record path changes."""
    renames = {}

    for path in find_tex_files():
        with open(path, "r", encoding="utf-8") as f:
            content = f.read()

        match = re.search(r"\\label\{([^}]+)\}", content)
        if not match:
            continue

        label = match.group(1)
        expected_fname = expected_filename_from_label(label)
        if not expected_fname:
            continue

        actual_fname = os.path.basename(path)
        if actual_fname != expected_fname:
            new_path = os.path.join(os.path.dirname(path), expected_fname)
            print(f"🔁 Renaming file: {actual_fname} → {expected_fname}")
            os.rename(path, new_path)
            renames[os.path.normpath(path)] = os.path.normpath(new_path)

    return renames


def update_input_paths(renames):
    r"""Update all \input{...} references to renamed .tex files."""
    input_pattern = re.compile(r"(\\input\{)([^}]+)(\})")

    for dirpath, _, filenames in os.walk("src"):
        for fname in filenames:
            if not fname.endswith(".tex"):
                continue

            tex_path = os.path.join(dirpath, fname)
            with open(tex_path, "r", encoding="utf-8") as f:
                content = f.read()

            changed = False

            def replace_input(match):
                full, path, end = match.groups()
                abs_old = os.path.normpath(os.path.join("src", path + ".tex"))
                if abs_old in renames:
                    rel_new = renames[abs_old].replace("src/", "").rstrip(".tex").replace("\\", "/")
                    print(f"📝 Updating \\input{{{path}}} → \\input{{{rel_new}}} in {tex_path}")
                    nonlocal changed
                    changed = True
                    return f"{full}{rel_new}{end}"
                return match.group(0)

            new_content = input_pattern.sub(replace_input, content)

            if changed:
                with open(tex_path, "w", encoding="utf-8") as f:
                    f.write(new_content)


def main():
    renames = correct_filenames_and_record_renames()
    if renames:
        update_input_paths(renames)
    print("✅ Label, filename, and \\input{} sync complete.")


if __name__ == "__main__":
    main()
