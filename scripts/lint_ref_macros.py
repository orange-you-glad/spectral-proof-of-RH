#!/usr/bin/env python3
"""Lint for ref macro usage to ensure DAG traceability."""
import re
import sys
from pathlib import Path

ROOT_DIR = Path("src/chapters")
REF_MACRO_PATTERN = re.compile(r"\\(lem|thm|def|prop|cor|rem|rmk)ref\{([^}]+)\}")
RAW_REF_PATTERN = re.compile(r"\\ref\{([^}]+)\}")

def find_ref_macros_without_raw_refs():
    issues = []

    for chapter in sorted(ROOT_DIR.iterdir()):
        proofs_dir = chapter / "proofs"
        if not proofs_dir.exists():
            continue
        for tex_file in sorted(proofs_dir.glob("*.tex")):
            text = tex_file.read_text(encoding="utf-8")
            macro_refs = set(REF_MACRO_PATTERN.findall(text))
            raw_refs = set(RAW_REF_PATTERN.findall(text))

            for kind, label in macro_refs:
                if label not in raw_refs:
                    issues.append((str(tex_file), f"{kind}ref{{{label}}} missing raw \\ref{{{label}}}"))

    return issues

def main():
    issues = find_ref_macros_without_raw_refs()
    if issues:
        print(f"❌ {len(issues)} issues found:")
        for file, msg in issues:
            print(f"  - {file}: {msg}")
        sys.exit(1)
    else:
        print("✅ All macro references are properly backed by \\ref{...}")

if __name__ == "__main__":
    main()
