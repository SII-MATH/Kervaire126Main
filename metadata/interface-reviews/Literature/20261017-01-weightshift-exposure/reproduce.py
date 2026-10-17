#!/usr/bin/env python3
"""Read-only snapshot/capture analysis. Does not run Lean, Lake, or freeze."""
import hashlib,json,subprocess,sys
from pathlib import Path
root=Path(sys.argv[1] if len(sys.argv)>1 else "/tmp/kip-literature-20261017-01")
run=root/"metadata/proof-sessions/runs/Literature/20261017-01"
base="bef90640c4594af4db32c86837f9d95340d1e171"
old="a484b981fad612eabe2bc7a01b54e049e9a01ce4"
target="KIP126.Literature.Standard.nuPage_weightShift"
def git(*a):return subprocess.check_output(["git","-C",str(root),*a],text=True)
def snap(path,content,lo,hi,commit=None):
 return {"path":path,"commit":commit,"sha256":hashlib.sha256(content.encode()).hexdigest(),"excerpt":"\n".join(f"{i}: {s}" for i,s in enumerate(content.splitlines(),1) if lo<=i<=hi)}
requests=[
 (base,"KIP126/Literature/Standard.lean",20,28),
 (base,"KIP126/Literature/Standard.lean",350,380),
 (base,"KIP126/Literature/Rigidity.lean",38,64),
 (base,"KIP126/AdamsSynthetic/Standard/Operations.lean",265,280),
 (base,"KIP126/AdamsSynthetic/Families.lean",55,92),
 (base,"KIP126/SpectralSequence/Basic/Data.lean",320,326),
 (old,"KIP126/Def/Comparison/ClassicalSynthetic/RealizationWeights/Data.lean",23,46),
 (old,"KIP126/Def/Synthetic/EInfty/Shift/Canonical/Proofs.lean",180,220),
 (old,"KIP126/Literature/Standard/Sphere/EInfty.lean",1,24),
]
out={"baseline":base,"historical":old,"snapshots":[]}
for commit,path,lo,hi in requests:out["snapshots"].append(snap(path,git("show",commit+":"+path),lo,hi,commit))
for path in ["validation/worker-comparison-WeightShiftProbe-3.lean","validation/worker-comparison-WeightShiftProbe-3.json","validation/worker-comparison-WeightShiftProbe-3.log","validation/VisibilityProbe.lean","validation/production-batch-2.log","validation/VisibilityPrivateDeclProbe-1.lean","validation/VisibilityPrivateDeclProbe-1.json","validation/VisibilityPrivateDeclProbe-1.log","validation/VisibilityPrivateDeclConsumerProbe-1.lean","validation/VisibilityPrivateDeclConsumerProbe-1.json","validation/VisibilityPrivateDeclConsumerProbe-1.log"]:
 content=(run/path).read_text();out["snapshots"].append(snap(str(run/path),content,185 if path.endswith("batch-2.log") else 1,208 if path.endswith("batch-2.log") else 80))
lean=Path("/root/.elan/toolchains/leanprover--lean4---v4.32.2/src/lean/Lean")
for path,lo,hi in [("Elab/MutualDef.lean",20,51),("Elab/MutualDef.lean",1342,1388),("Environment.lean",844,849),("Elab/BuiltinTerm.lean",464,485),("Elab/SyntheticMVars.lean",458,463),("Meta/AbstractNestedProofs.lean",38,67),("Elab/PreDefinition/Basic.lean",120,128)]:
 content=(lean/path).read_text();out["snapshots"].append(snap(str(lean/path),content,lo,hi))
pubpath=run/"auditor/capture-history/literature-capture-initial-ae4e787c690c6f55.json"
trustpath=run/"auditor/capture-history/literature-trust-capture-initial-4e8792ea3d739af3.json"
public={v["name"]:v for v in json.loads(pubpath.read_text())}
trust={v["name"]:v for v in json.loads(trustpath.read_text())}
api=json.loads(git("show",base+":metadata/literature-api.json"))
oldrows={v["name"]:v for v in api["declarations"]+api["generated_declarations"]}
out["baseline_target"]=oldrows[target]
out["candidate_target_public"]=public[target]
out["candidate_target_trust"]=trust[target]
out["capture_hashes"]={str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in [pubpath,trustpath]}
extra=sorted(n for n in public if n.startswith(target+"._proof_") and n not in oldrows)
out["extra_public_target_helpers"]=[{"public":public[n],"trust":trust[n]} for n in extra]
assert len(extra)==8
seen=set();todo=list(trust[target]["dependencies"])
while todo:
 n=todo.pop()
 if n in seen:continue
 seen.add(n)
 if n in trust:todo.extend(trust[n]["dependencies"])
out["candidate_dependency_summary"]={
 "cycle_back_to_target":target in seen,
 "reaches_stem62":"KIP126.Literature.Standard.stem62_exponent_two" in seen,
 "transitive_pending":[{"name":n,"module":trust[n]["module"]} for n in sorted(seen) if n in trust and trust[n]["direct_sorry"]],
}
out["direct_baseline_references"]=git("grep","-n","nuPage_weightShift",base,"--","KIP126","Tests")
print(json.dumps(out,ensure_ascii=False,indent=2))
