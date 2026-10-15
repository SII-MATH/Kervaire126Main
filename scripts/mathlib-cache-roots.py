#!/usr/bin/env python3
"""List external imports with Lean's parser for a project-sized Mathlib cache.

Migrated from Kervaire126/scripts/mathlib-cache-roots.py (MIT).
"""

import json
from pathlib import Path
import subprocess


def main():
    root = Path(__file__).resolve().parent.parent
    # Follow the active source tree: a migration can remove tracked files and
    # introduce new modules before a commit is made.
    candidates = {root / "KIP126.lean"}
    for directory in ("KIP126", "Tests"):
        candidates.update((root / directory).rglob("*.lean"))
    sources = sorted(path.relative_to(root).as_posix() for path in candidates if path.is_file())
    if not sources:
        raise SystemExit("No active Lean sources found.")
    parsed = json.loads(subprocess.check_output(
        ["lean", "--deps-json", *sources], text=True, cwd=root
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
