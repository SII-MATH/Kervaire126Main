#!/usr/bin/env python3
import json,collections,sqlite3
from pathlib import Path
O=Path('/tmp/SS-All-Results-Audit-20261016');rs=json.loads((O/'logs-full-synthetic-rows.json').read_text());br={r['id']:r for r in json.loads((O/'E2-branch-classification.json').read_text())['rows']};cs=[r for r in rs if r['reason']=='SynCs'];perm=[r for r in rs if r['reason']=='SynCsIn'];D=sqlite3.connect('file:/tmp/mh2-machine-proof-audit/proofs.db?mode=ro',uri=True);D.row_factory=sqlite3.Row;byid={r['id']:r for r in cs};pairs=[]
for p in perm:
 n=D.execute("select * from log where id>? and reason in ('SynCs','SynCsIn') order by id limit 1",(p['id'],)).fetchone();n=dict(n) if n else None
 if n and n['reason']=='SynCs':
  n=byid[n['id']];s,t=n['map_degree'];targetS=n['s']+n['r'];targetT=n['t']+n['r']+t-s
  pairs.append({'permanent_id':p['id'],'extension_id':n['id'],'degree_match':(p['s'],p['t'])==(targetS,targetT),'vector_match':p['x']==n['dx'],'target_object':p['name'],'extension_top_branch':br[n['id']]['branch']})
(O/'logs-permanence-companions.json').write_text(json.dumps(pairs,ensure_ascii=False,indent=2)+'\n')
def count(xs):return dict(collections.Counter(map(str,xs)))
out={'branch_counts':count(br[r['id']]['branch'] for r in cs),'permanence_companion_branch':count(br[r['extension_id']]['branch'] for r in pairs),'positive_rows':[{**r,'E2_classification':br[r['id']]} for r in cs if any(r['direct_M0_parameters'][k] for k in ('l1','m1'))],'branch_by_excess':count((br[r['id']]['branch'],r['output_extension_excess']) for r in cs),'M0_parameters':count((r['direct_M0_parameters']['l1'],r['direct_M0_parameters']['m1']) for r in cs if br[r['id']]['branch']=='M0'),'M0_r_xtop':count(r['direct_M0_parameters']['r_xtop'] for r in cs if br[r['id']]['branch']=='M0'),'M1_maps':count(r['map'] for r in cs if br[r['id']]['branch']=='M1'),'M1_directions':count(r['name'] for r in cs if br[r['id']]['branch']=='M1')}
(O/'logs-branch-summary.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n');print({k:v for k,v in out.items() if k not in ('positive_rows','M1_maps','M1_directions')})
