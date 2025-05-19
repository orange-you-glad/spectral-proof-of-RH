#!/usr/bin/env python3
"""Helper for environment extraction checks."""
import os
import re
import sys

from tests import common

ROOT_DIR = common.ROOT_DIR


ENV_MAP = {
    "remark": "rems",
    "proof": "proofs",
    "theorem": "thms",
    "lemma": "lems",
    "definition": "defs",
    "proposition": "props",
    "corollary": "cors",
}

PATTERN = re.compile(r"\\begin\{(remark|proof|theorem|lemma|definition|proposition|corollary)\}")


def main() -> None:
    script = os.path.basename(sys.argv[0])
    env = script.replace("check_all_", "").replace("_extracted.py", "")
    target_dir = ENV_MAP.get(env)
    if not target_dir:
        print(f"Unknown environment for {script}")
        sys.exit(1)
    errors = []
    for path in common.find_tex_files(ROOT_DIR):
        if target_dir not in path:
            with open(path, "r", encoding="utf-8") as f:
                for lineno, line in enumerate(f, 1):
                    m = PATTERN.search(line)
                    if m and m.group(1) == env:
                        errors.append(f"{path}:{lineno} contains {env} outside {target_dir}/")
    if errors:
        for e in errors:
            print(f"❌ {e}")
        sys.exit(1)
    print(f"✅ All {env}s extracted to {target_dir}/")


if __name__ == "__main__":
    main()
