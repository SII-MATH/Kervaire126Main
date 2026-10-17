"""Run the report's Lean audit using read-only pre-existing caches.

No lake command is used. No -o, -i, -c output option is supplied to Lean.
All output is confined to this evidence directory.
"""
from pathlib import Path
import argparse
import json
import os
import subprocess

parser = argparse.ArgumentParser()
parser.add_argument("--cache-root", type=Path,
                    default=Path("/inspire/hdd/global_user/czxs25250150/Kervaire126Main"))
parser.add_argument("--worktree", type=Path,
                    default=Path("/tmp/kip-adams-synthetic-20261017-struct"))
args = parser.parse_args()
evidence_dir = Path(__file__).resolve().parent
paths = [args.cache_root / ".lake/build/lib/lean"]
paths += [p / ".lake/build/lib/lean"
          for p in sorted((args.cache_root / ".lake/packages").iterdir())
          if p.is_dir()]
env = os.environ.copy()
env["LEAN_PATH"] = ":".join(map(str, paths))
cmd = ["/root/.elan/toolchains/leanprover--lean4---v4.32.2/bin/lean",
       str(evidence_dir / "CacheDependencyAudit.lean")]
(evidence_dir / "cache-audit-command.txt").write_text(
    "Subprocess environment entry: LEAN_PATH=" + env["LEAN_PATH"] + "\n"
    + "Arguments: " + json.dumps(cmd, ensure_ascii=False) + "\n"
    + "No -o/-i/-c option: no compiler output files requested.\n")
with (evidence_dir / "cache-dependency-audit.log").open("w") as out:
    result = subprocess.run(cmd, env=env, cwd=args.worktree,
                            stdout=out, stderr=subprocess.STDOUT, timeout=120)
if result.returncode:
    print((evidence_dir / "cache-dependency-audit.log").read_text())
    raise SystemExit(result.returncode)

raw = (evidence_dir / "cache-dependency-audit.log").read_text()
decoder = json.JSONDecoder()
parsed = []
while raw.strip():
    raw = raw.lstrip()
    obj, i = decoder.raw_decode(raw)
    parsed.append(obj)
    raw = raw[i:]
assert len(parsed) == 2
summary = []
for record in parsed:
    assert record["positive_target_in_closure"] is False
    assert record["suspension_target_in_closure"] is False
    assert "sorryAx" in record["axioms"]
    summary.append({
        "root": record["root"],
        "positive_target_in_closure": record["positive_target_in_closure"],
        "suspension_target_in_closure": record["suspension_target_in_closure"],
        "axioms": record["axioms"],
        "relevant_project_nodes": record["relevant_project_nodes"],
        "pending_node_count": len(record["pending_source_nodes"])
    })
(evidence_dir / "cache-audit-summary.json").write_text(
    json.dumps(summary, ensure_ascii=False, indent=2) + "\n")
print("PASS: two cached proof dependency closures inspected; neither uses the two targets.")
print("LIMIT: both closures contain sorryAx and registered pending source obligations.")
