#!/usr/bin/env python3
"""List external imports with Lean's parser for a project-sized Mathlib cache.

Migrated from Kervaire126/scripts/mathlib-cache-roots.py (MIT).
"""

import json
from pathlib import Path
import subprocess


def main():
    sources = subprocess.check_output(
        ["git", "ls-files", "-z", "--", "*.lean"], text=True
    ).split("\0")[:-1]
    if not sources:
        raise SystemExit("No tracked Lean sources found.")
    parsed = json.loads(subprocess.check_output(
        ["lean", "--deps-json", *sources], text=True
    ))["imports"]
    if len(parsed) != len(sources):
        raise SystemExit("Lean did not return an import header for every source.")
    local_modules = {str(Path(p).with_suffix("")).replace("/", ".") for p in sources}
    toolchain_roots = {"Init", "Lean", "Std", "Lake"}
    external = set()
    for source, header in zip(sources, parsed):
        if header["errors"] or header.get("result") is None:
            raise SystemExit(f"Cannot parse imports in {source}: {header['errors']}")
        for item in header["result"]["imports"]:
            module = item["module"]
            if module not in local_modules and module.split(".", 1)[0] not in toolchain_roots:
                external.add(module)
    for module in sorted(external):
        print(module)


if __name__ == "__main__":
    main()
