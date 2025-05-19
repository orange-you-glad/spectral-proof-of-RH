#!/usr/bin/env python3
"""Produce summary statistics per chapter."""
from __future__ import annotations

import json
import os
import sys
from collections import Counter
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from tests import common

ROOT_DIR = Path("src/chapters")
OUTPUT = Path("metadata/chapter_summary.json")

ENV_PATTERN = common.VALID_PREFIXES


def count_lines(path: Path) -> int:
    return sum(1 for _ in open(path, "r", encoding="utf-8"))


def main() -> None:
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    summary: dict[str, dict[str, int]] = {}
    for section in sorted(os.listdir(ROOT_DIR)):
        section_path = ROOT_DIR / section
        if not section_path.is_dir():
            continue
        counts = Counter()
        lines = 0
        proofs_missing = 0
        proofs_found = {Path(p).stem for p in common.find_tex_files(str(section_path / "proofs"))}
        for tex in common.find_tex_files(str(section_path)):
            expected = common.expected_label_from_filename(tex)
            if expected:
                prefix = expected.split(":")[0]
                counts[prefix] += 1
                base = Path(tex).stem
                if f"prf_{base}" not in proofs_found:
                    proofs_missing += 1
            lines += count_lines(Path(tex))
        summary[section] = {
            "lines": lines,
            "missing_proofs": proofs_missing,
        }
        for p in ENV_PATTERN:
            summary[section][p] = counts.get(p, 0)
    with OUTPUT.open("w", encoding="utf-8") as f:
        json.dump(summary, f, indent=2)
    print(f"✅ Wrote {OUTPUT}")


if __name__ == "__main__":
    main()
