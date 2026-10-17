#!/usr/bin/env python3
"""Read-only source audit + finite arithmetic check. No Lean/Lake/freeze.
Run with python3 reproduce.py [worktree]; outputs evidence to stdout.
This does NOT construct an element of the project's HomotopyGroup.
"""
import hashlib, json, subprocess, sys
from pathlib import Path
root=Path(sys.argv[1] if len(sys.argv)>1 else "/tmp/kip-literature-20261017-01")
base="bef90640c4594af4db32c86837f9d95340d1e171"
old="a484b981fad612eabe2bc7a01b54e049e9a01ce4"
def git(*args):
 return subprocess.check_output(["git","-C",str(root),*args],text=True)
def show(commit,path): return git("show",commit+":"+path)
def excerpt(content,lo,hi):
 return "\n".join(f"{i}: {s}" for i,s in enumerate(content.splitlines(),1) if lo<=i<=hi)
requests=[
 (base,"KIP126/Literature/Standard.lean",139,211),
 (base,"KIP126/Literature/Classical.lean",109,160),
 (base,"KIP126/AdamsSynthetic/Context.lean",77,84),
 (base,"KIP126/AdamsSynthetic/Standard/Source.lean",20,35),
 (base,"KIP126/AdamsSynthetic/Internal/Source/Recognition.lean",30,89),
 (base,"KIP126/AdamsSynthetic/Internal/Source/Prespectrum.lean",110,180),
 (old,"KIP126/Literature/Source.lean",55,80),
 (old,"KIP126/Literature/Hypotheses.lean",53,78),
 (old,"KIP126/Literature/Standard.lean",1,15),
 (old,"KIP126/Literature/Standard/ClassicalContext.lean",1,18),
 (old,"KIP126/Literature/Standard/Foundation.lean",1,14),
 (old,"KIP126/Literature/Background/ClassicalAdams.lean",1,22),
 (old,"KIP126/Literature/Background/HF2Completion.lean",1,27),
 (old,"KIP126/Def/ClassicalAdams/Context/Data.lean",284,311),
 (old,"KIP126/Def/StableHomotopy/Spectra/Comparison.lean",15,65),
 (old,"KIP126/Main/Literature/SourceComparisons/Theorems.lean",64,85),
 (old,"KIP126/Main/Literature/AdamsSynthetic/Theorems.lean",85,101),
]
out={"baseline":base,"historical":old,"head":git("rev-parse","HEAD").strip(),"snapshots":[]}
for commit,path,lo,hi in requests:
 content=show(commit,path)
 out["snapshots"].append({"commit":commit,"path":path,"sha256":hashlib.sha256(content.encode()).hexdigest(),"excerpt":excerpt(content,lo,hi)})
for name in ["metadata/literature-api.json","metadata/literature-contracts.json","metadata/literature-sources.json","metadata/proof-obligations.json"]:
 content=(root/name).read_bytes()
 out.setdefault("live_metadata_hashes",{})[name]=hashlib.sha256(content).hexdigest()
api=json.loads((root/"metadata/literature-api.json").read_text())
def search(v):
 if isinstance(v,dict):
  if v.get("name")=="KIP126.Literature.Standard.stem62_exponent_two":out["api_target"]=v
  for z in v.values():search(z)
 elif isinstance(v,list):
  for z in v:search(z)
search(api)
out["direct_references"]=git("grep","-n","stem62_exponent_two",base,"--","KIP126","Tests")
# Algebraic coordinates supplied by the published decomposition, not a project object.
moduli=(2,2,2,2,3)
a=(0,0,0,0,1)
def add(x,y):return tuple((i+j)%m for i,j,m in zip(x,y,moduli))
zero=(0,0,0,0,0);two=add(a,a);three=add(two,a)
assert a!=zero and two!=zero and three==zero
out["finite_arithmetic"]={"moduli":moduli,"a":a,"a_plus_a":two,"a_plus_a_plus_a":three,"zero":zero,"result":"PASS; arithmetic only, not a Lean/project counterexample"}
print(json.dumps(out,ensure_ascii=False,indent=2))
