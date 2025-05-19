#!/usr/bin/env python3
"""Check for unresolved \ref, \eqref, or \cite commands."""
import os
import re
import sys

from tests import common

ROOT_DIR = common.ROOT_DIR
BIB_PATH = os.path.join("src", "references.bib")

LABEL_PATTERN = re.compile(r"\\label\{([^}]+)\}")
REF_PATTERN = re.compile(r"\\(?:ref|eqref|cref|Cref)\{([^}]+)\}")
CITE_PATTERN = re.compile(r"\\cite\{([^}]+)\}")


def collect_labels() -> set[str]:
    labels = set()
    for path in common.find_tex_files(ROOT_DIR):
        with open(path, "r", encoding="utf-8") as f:
            for line in f:
                for m in LABEL_PATTERN.finditer(line):
                    labels.add(m.group(1))
    return labels


def collect_citation_keys() -> set[str]:
    if not os.path.isfile(BIB_PATH):
        return set()
    keys = set()
    with open(BIB_PATH, "r", encoding="utf-8") as f:
        for line in f:
            if line.lstrip().startswith("@"):  # entry start
                key = line.split("{", 1)[-1].split(",", 1)[0].strip()
                if key:
                    keys.add(key)
    return keys


def check_refs(labels: set[str], citations: set[str]) -> list[str]:
    errors = []
    used_cites = set()
    for path in common.find_tex_files(ROOT_DIR):
        if os.path.basename(path) in {"summary.tex", "intro.tex"}:
            continue
        with open(path, "r", encoding="utf-8") as f:
            for lineno, line in enumerate(f, start=1):
                for m in REF_PATTERN.finditer(line):
                    ref = m.group(1)
                    if ref not in labels:
                        errors.append(f"{path}:{lineno} unresolved ref {ref}")
                for m in CITE_PATTERN.finditer(line):
                    cite = m.group(1)
                    used_cites.add(cite)
                    if cite not in citations:
                        errors.append(f"{path}:{lineno} unresolved citation {cite}")
    unused = citations - used_cites
    for uc in sorted(unused):
        errors.append(f"unused citation key: {uc}")
    return errors


def main() -> None:
    labels = collect_labels()
    citations = collect_citation_keys()
    errors = check_refs(labels, citations)
    if errors:
        for e in errors:
            print(f"❌ {e}")
        sys.exit(1)
    print("✅ All references and citations resolved.")


if __name__ == "__main__":
    main()
