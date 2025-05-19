#!/usr/bin/env python3
"""Generate simple statistics per chapter."""
import os
import re
from collections import Counter

from tests import common

ROOT_DIR = common.ROOT_DIR
ENV_PATTERN = re.compile(r"\\begin\{(theorem|lemma|proposition|corollary|definition)\}")


def stats_for_chapter(section_path: str) -> Counter:
    c = Counter()
    for path in common.find_tex_files(section_path):
        with open(path, "r", encoding="utf-8") as f:
            for line in f:
                for m in ENV_PATTERN.finditer(line):
                    c[m.group(1)] += 1
    return c


def main() -> None:
    for section in sorted(os.listdir(ROOT_DIR)):
        section_path = os.path.join(ROOT_DIR, section)
        if not os.path.isdir(section_path):
            continue
        counts = stats_for_chapter(section_path)
        if counts:
            stats = ", ".join(f"{k}:{v}" for k, v in counts.items())
            print(f"{section}: {stats}")
        else:
            print(f"{section}: none")


if __name__ == "__main__":
    main()
