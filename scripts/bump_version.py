#!/usr/bin/env python3
import os
import sys

VERSION_FILE = "VERSION"


def read_version():
    if not os.path.isfile(VERSION_FILE):
        print(f"❌ VERSION file not found at {VERSION_FILE}")
        sys.exit(1)
    with open(VERSION_FILE, "r") as f:
        content = f.read().strip()
    if not content:
        print("❌ VERSION file is empty.")
        sys.exit(1)
    return content


def write_version(v):
    with open(VERSION_FILE, "w") as f:
        f.write(v + "\n")


def bump_version(part):
    v = read_version()
    major, minor, patch = map(int, v.split("."))
    if part == "patch":
        patch += 1
    elif part == "minor":
        minor += 1
        patch = 0
    elif part == "major":
        major += 1
        minor = patch = 0
    else:
        print("❌ Unknown bump type. Use patch, minor, or major.")
        sys.exit(1)
    new_version = f"{major}.{minor}.{patch}"
    write_version(new_version)
    print(f"🔁 Bumped version: {v} → {new_version}")


if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("Usage: bump_version.py [patch|minor|major]")
        sys.exit(1)
    bump_version(sys.argv[1])
