#!/usr/bin/env python3
"""Generate CSV metadata for all labeled objects."""
from __future__ import annotations

import csv
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from tests import common

ROOT_DIR = Path("src/chapters")
OUTPUT = Path("metadata/labels.csv")


def proof_path(chapter: Path, base: str) -> str:
    prf = chapter / "proofs" / f"prf_{base}.tex"
    return str(prf) if prf.exists() else ""


def main() -> None:
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    with OUTPUT.open("w", newline="", encoding="utf-8") as csvfile:
        writer = csv.writer(csvfile)
        writer.writerow(["label", "type", "chapter", "file", "proof_file"])
        for tex in common.find_tex_files(str(ROOT_DIR)):
            expected = common.expected_label_from_filename(tex)
            if not expected:
                continue
            label_type = expected.split(":")[0]
            chapter = Path(tex).parts[2]  # src/chapters/<chapter>/...
            base = Path(tex).stem
            writer.writerow(
                [expected, label_type, chapter, tex, proof_path(Path(ROOT_DIR) / chapter, base)]
            )
    print(f"✅ Wrote {OUTPUT}")


if __name__ == "__main__":
    main()
