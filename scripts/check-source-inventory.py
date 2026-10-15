#!/usr/bin/env python3
"""Audit every active Lean source, its imports, and the exact admitted debt.

This is a source/architecture check, not a proof-completion certificate. The
compiled dependency check lives in Tests/Trust.lean. --print-inventory prints
source locations for review; it never updates the accepted metadata itself.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parent.parent
LAYERS = {"Def", "Literature", "Computation", "Main"}
# The migrated May proof unfolds this @[no_expose] definition. This one
# explicitly reviewed exception preserves the develop proof without exposing
# Def implementation details globally or weakening its proof.
PRIVATE_IMPORT_EXCEPTIONS = [{
    "file": "KIP126/Main/Literature/SourceComparisons/May.lean",
    "module": "KIP126.Def.StableHomotopy.Context.Proofs",
}]
ALLOWED = {
    "Def": {"Def"},
    "Literature": {"Def", "Literature"},
    "Computation": {"Def", "Literature", "Computation"},
    "Main": LAYERS,
}
# These audited groups are fixed input certificates or independent background
# checks. Section 7 applications extracted from them now live in SectionSeven.
MIGRATED_OUT_OF_MAIN = (
    "Computation",
    "AdamsSynthetic/AlgebraRealization.lean",
    "AdamsSynthetic/SphereAlgebra.lean",
    "AdamsSynthetic/SphereConvergence.lean",
    "AdamsSynthetic/WeightShift.lean",
    "Literature/EtaRows",
    "Literature/HopfCofiber",
    "Literature/Near126",
    "Literature/Near126.lean",
)


def code_only(text: str) -> str:
    """Remove nested comments and strings while preserving source offsets."""
    out: list[str] = []
    i = depth = 0
    while i < len(text):
        if text[i:i + 2] == "/-":
            depth += 1
            out.append("  ")
            i += 2
        elif depth and text[i:i + 2] == "-/":
            depth -= 1
            out.append("  ")
            i += 2
        elif depth:
            out.append("\n" if text[i] == "\n" else " ")
            i += 1
        elif text[i:i + 2] == "--":
            j = text.find("\n", i)
            j = len(text) if j < 0 else j
            out.append(" " * (j - i))
            i = j
        elif text[i] == '"':
            out.append(" ")
            i += 1
            while i < len(text):
                if text[i] == "\\" and i + 1 < len(text):
                    out.append("  ")
                    i += 2
                elif text[i] == '"':
                    out.append(" ")
                    i += 1
                    break
                else:
                    out.append("\n" if text[i] == "\n" else " ")
                    i += 1
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def module_name(path: Path) -> str:
    return path.relative_to(ROOT).with_suffix("").as_posix().replace("/", ".")


def owner(name: str) -> str | None:
    parts = name.split(".")
    return parts[1] if len(parts) > 1 and parts[0] == "KIP126" and parts[1] in LAYERS else None


def imports(code: str) -> list[tuple[bool, str]]:
    found = []
    for match in re.finditer(
        r"^\s*(?:(?:public|private|meta)\s+)*import\s+(all\s+)?([^\n]+)", code, re.M
    ):
        found.extend((bool(match[1]), name) for name in match[2].split())
    return found


def private_module_selectors(code: str) -> list[str]:
    """Parse the module selector of `open private names from Module` commands."""
    return re.findall(r"\bopen\s+private\s+[\w.\s'«»]+?\bfrom\s+([\w.]+)", code)


def source_inventory(sources: dict[Path, str]) -> dict[str, list[dict]]:
    axioms, sorries = [], []
    for path, code in sorted(sources.items()):
        file = path.relative_to(ROOT).as_posix()
        for match in re.finditer(r"(?<![\w`])axiom\s+([^\s:({]+)", code):
            axioms.append({"file": file, "name": match[1], "line": code.count("\n", 0, match.start()) + 1})
        for match in re.finditer(r"(?<![\w`])sorry\b", code):
            sorries.append({"file": file, "line": code.count("\n", 0, match.start()) + 1})
    return {"axioms": axioms, "sorries": sorries}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--print-inventory", action="store_true")
    args = parser.parse_args()
    paths = set((ROOT / "KIP126").rglob("*.lean")) | {ROOT / "KIP126.lean"}
    missing = [p for p in paths if not p.is_file()]
    if missing:
        print("Missing project source: " + ", ".join(str(p.relative_to(ROOT)) for p in missing), file=sys.stderr)
        return 1
    project = {p: code_only(p.read_text()) for p in paths}
    inventory = source_inventory(project)
    if args.print_inventory:
        print(json.dumps(inventory | {"allowed_private_imports": PRIVATE_IMPORT_EXCEPTIONS}, indent=2, ensure_ascii=False))
        return 0

    errors: list[str] = []
    # Distinguish minimal input-construction proofs from substantive, checked
    # computation certificates. The latter were explicitly approved when Main
    # was restricted to Sections 6 and 7. Neither inventory exempts a folder or
    # replaces the external Adams comparison assumptions.
    try:
        boundaries = json.loads((ROOT / "metadata/layer-boundaries.json").read_text())
        construction_proofs = {entry["file"]: entry for entry in boundaries["input_construction_proofs"]}
        computation_certificates = {entry["file"]: entry for entry in boundaries["computation_certificates"]}
        if boundaries.get("schema_version") != 2:
            errors.append("Layer-boundary inventory must use schema_version 2")
        for key, entries in (("input_construction_proofs", construction_proofs),
                             ("computation_certificates", computation_certificates)):
            if len(entries) != len(boundaries[key]):
                errors.append(f"Duplicate entries in {key}")
        for file in construction_proofs.keys() & computation_certificates.keys():
            errors.append(f"Proof classified as both construction and computation: {file}")
        for file in computation_certificates:
            if not file.startswith("KIP126/Computation/") or "Certificates" not in Path(file).parts:
                errors.append(f"Computation certificate must have a separate Certificates module: {file}")
    except (OSError, ValueError, KeyError, TypeError) as exc:
        errors.append(f"Cannot read input proof inventories: {exc}")
        construction_proofs = {}
        computation_certificates = {}
    input_proofs = construction_proofs | computation_certificates
    seen_input_proofs: set[str] = set()
    active_dirs = {p.name for p in (ROOT / "KIP126").iterdir() if p.is_dir()}
    if active_dirs != LAYERS:
        errors.append(f"KIP126 must have exactly four source directories: actual {sorted(active_dirs)}")
    for layer in sorted(LAYERS):
        if not (ROOT / "KIP126" / f"{layer}.lean").is_file():
            errors.append(f"Missing public entry KIP126/{layer}.lean")
    for former in MIGRATED_OUT_OF_MAIN:
        path = ROOT / "KIP126/Main" / former
        if path.is_file() or (path.is_dir() and any(path.rglob("*.lean"))):
            errors.append(f"Background/input verification restored inside Main: {path.relative_to(ROOT)}")
    for path in paths - {ROOT / "KIP126.lean"}:
        if owner(module_name(path)) is None:
            errors.append(f"Unowned project source: {path.relative_to(ROOT)}")

    tests = {p: code_only(p.read_text()) for p in (ROOT / "Tests").rglob("*.lean")}
    for required in ("Architecture", "Trust"):
        if ROOT / f"Tests/{required}.lean" not in tests:
            errors.append(f"Missing consumer test Tests/{required}.lean")
    all_sources = project | tests
    modules = {module_name(p): p for p in all_sources}
    graph = {name: [] for name in modules}
    for path, code in all_sources.items():
        name = module_name(path)
        layer = owner(name)
        for all_, imported in imports(code):
            if imported.split(".")[0] in {"KIPBase", "Interface", "LinProgram"} or imported.startswith(
                ("KIP126.Interface", "KIP126.LinProgram", "KIP126.Checks", "KIP126.Main.Challenge")
            ):
                errors.append(f"Legacy import: {path.relative_to(ROOT)} imports {imported}")
            if imported == "KIP126" or imported.startswith(("KIP126.", "Tests.")):
                if imported not in modules:
                    errors.append(f"Missing local module: {path.relative_to(ROOT)} imports {imported}")
                else:
                    graph[name].append(imported)
                dependency_layer = owner(imported)
                if path in project and imported.startswith("Tests."):
                    errors.append(f"Mathematics imports a test: {path.relative_to(ROOT)} imports {imported}")
                elif layer and (dependency_layer is None or dependency_layer not in ALLOWED[layer]):
                    errors.append(f"Layer violation: {path.relative_to(ROOT)} imports {imported}")
                if all_ and (layer is None or layer != dependency_layer):
                    exception = {"file": path.relative_to(ROOT).as_posix(), "module": imported}
                    if exception not in PRIVATE_IMPORT_EXCEPTIONS:
                        errors.append(f"Cross-layer import all: {path.relative_to(ROOT)} imports {imported}")

        # These `from` operands are module names, not declaration names in ordinary terms.
        for selected in private_module_selectors(code):
            if selected.split(".")[0] in {"KIPBase", "Interface", "LinProgram"} or selected.startswith(
                ("KIP126.Interface", "KIP126.LinProgram", "KIP126.Checks", "KIP126.Main.Challenge")
            ):
                errors.append(f"Legacy private module selector: {path.relative_to(ROOT)} opens from {selected}")
            if selected == "KIP126" or selected.startswith(("KIP126.", "Tests.")):
                if selected not in modules:
                    errors.append(f"Missing private module selector: {path.relative_to(ROOT)} opens from {selected}")

        if layer in {"Literature", "Computation"}:
            file = path.relative_to(ROOT).as_posix()
            if re.search(r"(?<![\w`])(?:sorry|sorryAx)\b", code):
                errors.append(f"External input contains a proof hole: {file}")
            proof_count = len(re.findall(r"(?<![\w`])(?:theorem|lemma|example)\b", code))
            if proof_count:
                entry = input_proofs.get(file)
                if entry is None:
                    errors.append(f"Unregistered proof in an external input layer: {file}")
                else:
                    seen_input_proofs.add(file)
                    if entry.get("sha256") != hashlib.sha256(path.read_bytes()).hexdigest():
                        errors.append(f"Registered input proof changed: {file}")
                    if entry.get("proof_declarations") != proof_count or not entry.get("reason"):
                        errors.append(f"Input proof inventory is incomplete: {file}")
        if layer == "Def" and re.search(r"(?<![\w`])(?:axiom|sorry|sorryAx)\b", code):
            errors.append(f"Def must contain generic definitions/interfaces without external assumptions or proof holes: {path.relative_to(ROOT)}")
        if path in tests and re.search(r"(?<![\w`])(?:axiom|sorry|sorryAx)\b", code):
            errors.append(f"Consumer test contains a local axiom/hole: {path.relative_to(ROOT)}")
        if re.search(r"(?<![\w`])(?:sorryAx|admit)\b", code):
            errors.append(f"Untracked admission primitive: {path.relative_to(ROOT)}")

    for stale in sorted(input_proofs.keys() - seen_input_proofs):
        errors.append(f"Stale input proof entry: {stale}")

    visiting, visited = set(), set()

    def visit(name: str, trail: list[str]) -> None:
        if name in visiting:
            errors.append("Import cycle: " + " -> ".join(trail + [name]))
            return
        if name in visited:
            return
        visiting.add(name)
        for dependency in graph[name]:
            visit(dependency, trail + [name])
        visiting.remove(name)
        visited.add(name)

    for name in sorted(graph):
        visit(name, [])

    registry_path = ROOT / "metadata/proof-obligations.json"
    try:
        registry = json.loads(registry_path.read_text())
    except (OSError, ValueError) as exc:
        errors.append(f"Cannot read proof inventory: {exc}")
        registry = {}
    if registry.get("schema_version") != 2:
        errors.append("Proof inventory must use schema_version 2")
    if registry.get("allowed_private_imports") != PRIVATE_IMPORT_EXCEPTIONS:
        errors.append("The documented May private-import exception inventory changed")
    for kind in ("axioms", "sorries"):
        expected = registry.get(kind)
        actual = inventory[kind]
        if not isinstance(expected, list):
            errors.append(f"Proof inventory lacks a {kind} list")
            continue
        normalize = lambda entries: sorted(json.dumps(x, sort_keys=True) for x in entries)
        if normalize(expected) != normalize(actual):
            before, after = set(normalize(expected)), set(normalize(actual))
            errors.append(f"Exact {kind} inventory changed: unregistered {sorted(after - before)}; stale {sorted(before - after)}")

    external_axioms = [x for x in inventory["axioms"] if owner(x["file"].removesuffix(".lean").replace("/", ".")) in {"Literature", "Computation"}]
    expected_literature = {"adamsSyntheticResults", "hf2AdamsContext_exists", "completionModel_exists",
        "standardSyntheticContext", "standardAdamsSyntheticComparisons", "standardSphereApplicability",
        "CanonicalWeightShift.natural"}
    literature_axioms = [x for x in external_axioms if x["file"].startswith("KIP126/Literature/")]
    computation_axioms = [x for x in external_axioms if x["file"].startswith("KIP126/Computation/")]
    if len(literature_axioms) != 7 or {x["name"] for x in literature_axioms} != expected_literature:
        errors.append(f"Literature must contain the six background assumptions and its one result axiom: {literature_axioms}")
    if len(computation_axioms) != 1 or computation_axioms[0]["name"] != "adamsComputations":
        errors.append(f"Computation must contain exactly its one external-result axiom: {computation_axioms}")
    if len(inventory["axioms"]) != len(external_axioms):
        errors.append("An axiom remains outside the Literature/Computation input layers")
    if errors:
        print("\n".join(errors), file=sys.stderr)
        return 1
    print(f"Source inventory: {len(project)} project files, {len(tests)} consumer files; "
          f"acyclic four-layer imports; {len(inventory['axioms'])} registered axioms and "
          f"{len(inventory['sorries'])} registered sorry occurrences. This is not proof completion.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
