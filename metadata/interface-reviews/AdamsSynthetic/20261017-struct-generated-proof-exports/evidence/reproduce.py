#!/usr/bin/env python3
"""Run only assigned review evidence; never writes the project .lake directory."""
from pathlib import Path
import json, os, subprocess, sys
root = Path(__file__).resolve().parent
lean = "/root/.elan/toolchains/leanprover--lean4---v4.32.2/bin/lean"
env = os.environ.copy()
env["LEAN_PATH"] = str(root)
toys = [
    (["ProducerDisabled.lean"], 1),
    (["ProducerEnabled.lean", "-o", "ProducerEnabled.olean"], 0),
    (["ProducerPlain.lean", "-o", "ProducerPlain.olean"], 0),
    (["OrdinaryConsumer.lean"], 0),
    (["NestedExtraction.lean"], 0),
    (["ProducerExposure.lean", "-o", "ProducerExposure.olean"], 0),
    (["ExposureConsumer.lean"], 0),
]
failures = []
for args, expected in toys:
    run = subprocess.run([lean, *args], cwd=root, env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    print(args[0], "exit", run.returncode, "expected", expected)
    print(run.stdout)
    if run.returncode != expected:
        failures.append(args[0])
if "--toys-only" not in sys.argv:
    env["LEAN_PATH"] = json.loads((root / "replay-results.json").read_text())["LEAN_PATH"]
    for source in ["FinalProductionReplay63.lean", "ComposeCandidateReplay.lean", "OriginalHelperSignature.lean"]:
        run = subprocess.run([lean, source], cwd=root, env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        print(source, "exit", run.returncode)
        print(run.stdout)
        if run.returncode:
            failures.append(source)
if failures:
    raise SystemExit("Unexpected evidence outcome: " + ", ".join(failures))
