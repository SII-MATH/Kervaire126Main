from pathlib import Path
import json,collections,hashlib
rows=json.loads(Path('/tmp/kip-main-final-all-trust.json').read_text())
registry=json.loads(Path('metadata/proof-obligations.json').read_text())
api=json.loads(Path('metadata/main-api.json').read_text())
byname={r['name']:r for r in rows}
direct={r['name']:r for r in rows if r['direct_sorry']}
registered={r['name']:r for r in registry['obligations']}
assert set(direct)==set(registered)
for n,row in direct.items():
 for key in ['module','type_fingerprint','body_fingerprint']:
  assert row[key]==registered[n][key],(n,key)
assert not any(r['synthetic_sorry'] or r['is_axiom'] for r in rows)
roots=[r['name'] for r in api['declarations']]
assert len(roots)==17

def closure(roots):
 visited=set();todo=list(roots);unresolved_project=set()
 while todo:
  n=todo.pop()
  if n in visited:continue
  visited.add(n)
  r=byname.get(n)
  if r is None:
   if n.startswith('KIP126.') or n.startswith('_private.KIP126.'):
    unresolved_project.add(n)
   continue
  todo.extend(r['dependencies'])
 known=visited & byname.keys()
 holes=sorted(known & direct.keys())
 local=[n for n in holes if byname[n]['module'].split('.')[1] in ['Main','ProofTools']]
 forbidden=sorted(known & {'KIP126.ProofTools.Standard.generalizedMahowald','KIP126.ProofTools.Standard.generalizedLeibniz'})
 assert not unresolved_project,sorted(unresolved_project)
 assert not local,local
 assert not forbidden,forbidden
 return {'roots':roots,'reachable_project_constants':len(known),'registered_upstream_direct_dependencies':len(holes),'direct_dependencies_by_module':dict(sorted(collections.Counter(byname[n]['module'].split('.')[1] for n in holes).items())),'Main_or_ProofTools_direct_pending_dependencies':local,'old_MH2_GL_dependencies':forbidden,'missing_project_dependencies':sorted(unresolved_project),'upstream_pending_names':holes}
goal=closure(['KIP126.Main.h6_sq_permanent'])
union=closure(roots)
result={'status':'passed','capture':'kip-main-final-all-trust.json','capture_sha256':hashlib.sha256(Path('/tmp/kip-main-final-all-trust.json').read_bytes()).hexdigest(),'production_math_module_imports':467,'captured_project_constants':len(rows),'registered_direct_pending':len(direct),'registered_types_and_bodies_all_match':True,'direct_by_module':dict(sorted(collections.Counter(r['module'].split('.')[1] for r in direct.values()).items())),'synthetic_sorry':0,'project_axiom_declarations':0,'Main_direct_pending':sum(r['module'].startswith('KIP126.Main') for r in direct.values()),'fixed_main_goal':goal,'all_public_named_roots':union,'scope':'Full actual mathematical proof bodies; six InternalAudit modules are separately checked by the successful default build. Existing upstream duties remain pending.'}
Path('/tmp/kip-main-final-observer-summary.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ['fixed_main_goal','all_public_named_roots']},ensure_ascii=False,indent=2))
for label,data in [('Fixed main goal',goal),('All public roots',union)]:
 print(label,json.dumps({k:v for k,v in data.items() if k!='upstream_pending_names'},ensure_ascii=False))
