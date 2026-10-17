#!/usr/bin/env python3
"""Read-only recheck of the evidence saved beside this pending-human-review report."""
from pathlib import Path
import hashlib
import json

root = Path(__file__).resolve().parent
records = json.loads((root / "evidence/trust-after.json").read_text())
assert hashlib.sha256((root / "evidence/trust-after.json").read_bytes()).hexdigest() == "712ca51ecbdd71c8a23ca18c74e92b805cebfc8e774d6cdf35e4fc17e6f5e474"
by_name = {x["name"]: x for x in records}
name = next(n for n in by_name if n.endswith(".tmfConvergenceActualTransport"))
visited = set()
queue = [name]
while queue:
    n = queue.pop()
    if n in visited:
        continue
    visited.add(n)
    queue.extend(d for d in by_name[n]["dependencies"] if d in by_name)
assert "KIP126.Literature.Standard.tmf_convergence" not in visited
assert not any("stem62_exponent_two" in n for n in visited)
assert not by_name[name]["direct_sorry"] and not by_name[name]["is_axiom"]
helpers = [x for x in records if x["name"].startswith(name + "._proof_")]
assert len(helpers) == 19
assert all(not x["direct_sorry"] and not x["is_axiom"] for x in helpers)
assert by_name["KIP126.Literature.Standard.tmf_convergence"]["direct_sorry"]
color = {}
def visit(n):
    assert color.get(n) != 1, ("cycle", n)
    if color.get(n) == 2:
        return
    color[n] = 1
    for d in by_name[n]["dependencies"]:
        if d in visited:
            visit(d)
    color[n] = 2
visit(name)
pending = sorted(n for n in visited if by_name[n]["direct_sorry"] or by_name[n]["is_axiom"])
assert len(pending) == 33
assert not any(by_name[n]["is_axiom"] for n in visited)
assert sum(".AdamsSynthetic." in n for n in pending) == 31
assert set(n for n in pending if ".Literature." in n) == {"KIP126.Literature.Standard.tmf", "KIP126.Literature.Standard.tmfIso"}
original = json.loads((root / "evidence/original-api.json").read_text())
after = json.loads((root / "evidence/public-after.json").read_text())
a = {x["name"]: x for x in after}
b = {x["name"]: x for x in original["declarations"] + original["generated_declarations"]}
assert len(a) == 754
assert set(a) == set(original["exports"])
for n in a:
    assert a[n]["full_type"] == b[n]["full_type"], n
    assert a[n]["universes"] == b[n]["universes"], n
    assert a[n]["type_fingerprint"] == b[n]["type_fingerprint"], n
proposed = json.loads((root / "proposed-additional-exports.json").read_text())
assert proposed["not_authorized"] is True
assert {x["name"] for x in proposed["declarations"]} == {"KIP126.Literature.Standard.tmf_convergence._proof_" + str(i) for i in range(1, 20)}
assert all(x["universes"] == [] for x in proposed["declarations"])
old_body = (root / "evidence/Standard-public-candidate.lean").read_text().split("public def tmf_convergence :\n", 1)[1].split("\nend TmfConvergenceTransport", 1)[0].strip()
new_body = (root / "evidence/Standard-private-fallback.lean").read_text().split("private def tmfConvergenceActualTransport :\n", 1)[1].split("/-- The frozen public convergence responsibility", 1)[0].strip()
assert old_body == new_body
assert hashlib.sha256(old_body.encode()).hexdigest() == "0e07da064ae31f2e8dce1b092130c82cc98a6dc3f6a6b18b0ba597c065a2917c"
print("PASS: 754 original public types; same complete private transport; no direct holes in private construction; no target/stem62/cycle; 33 retained pending dependencies; proposal remains unauthorized.")
