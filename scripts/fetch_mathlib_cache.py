#!/usr/bin/env python3
"""Fetch the recorded Mathlib import cone, retaining the pinned manifest."""
from pathlib import Path
import argparse
import re
import subprocess
import sys


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lake", default="lake")
    parser.add_argument("--print-command", action="store_true")
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    record = root / "verification" / "independent-mathlib-cache-roots.txt"
    modules = record.read_text(encoding="utf-8-sig").splitlines()
    if len(modules) != 82 or len(set(modules)) != 82:
        raise SystemExit("Expected the 82 distinct recorded Mathlib cache roots")
    if not all(re.fullmatch(r"Mathlib\.[A-Za-z_0-9.]+", name) for name in modules):
        raise SystemExit("Invalid cache module in the recorded root list")
    command = [args.lake, "exe", "cache", "get", *modules]
    if args.print_command:
        print("\n".join(command))
        return 0
    return subprocess.run(command, cwd=root).returncode


if __name__ == "__main__":
    sys.exit(main())
