#!/usr/bin/env python3
import json,sqlite3
from pathlib import Path
O=Path('/tmp/SS-All-Results-Audit-20261016');root=O/'full-inputs/kervaire-49'
rs=json.loads((O/'logs-full-synthetic-rows.json').read_text());ps=[r for r in rs if r['reason']=='SynCs' and any(r['direct_M0_parameters'][k] for k in ('l1','m1'))]
d=sqlite3.connect('file:/tmp/mh2-machine-proof-audit/proofs.db?mode=ro',uri=True);d.row_factory=sqlite3.Row
cfg=json.load(open(O/'inputs-decoded.json')) if (O/'inputs-decoded.json').exists() else None
# All 12 exceptional arrows target either sphere (projection) or named cofiber (inclusion).
for r in ps:
 f=r['map'];src,tgt=f.split('__')[:2];s,t=r['map_degree'];ys=r['s']+r['r'];yt=r['t']+r['r']+t-s
 r['target_degree']=[ys,yt];r['target_name']=tgt;r['target_vector']=r['dx']
 r['prior_exact_target_sources']=[dict(p) for p in d.execute('select * from log where name=? and s=? and t=? and x=? and id<? order by id',(tgt,ys,yt,r['dx'],r['id']))]
 r['prior_independent_zero_cycle_rows']=[p for p in r['prior_exact_target_sources'] if p['depth']==0 and p['reason'] not in (None,'T','TI','SynCsIn') and p['r']>=2 and p['dx']=='']
 # Find incoming exact target rows with all possible differential lengths, unrelated to the immediately produced SynCsIn.
 r['prior_exact_target_boundaries']=[dict(p) for p in d.execute('select * from log where name=? and dx=? and s+r=? and t+r-1=? and id<? order by id',(tgt,r['dx'],ys,yt,r['id']))]
 pfiles=list(root.glob(tgt+'_AdamsSS_*.db'))
 if pfiles:
  db=sqlite3.connect('file:'+str(pfiles[0])+'?mode=ro',uri=True);db.row_factory=sqlite3.Row
  table=tgt+'_AdamsE2_basis';bs=[dict(x) for x in db.execute('select * from '+table+' where s=? and t=? order by id',(ys,yt))]
  r['target_raw_d2_basis']=[bs[int(i)] for i in r['dx'].split(',') if i]
  image=set()
  known=True
  for p in r['target_raw_d2_basis']:
   if p.get('d2') is None:known=False;continue
   for x in p['d2'].split(','):
    if x:image.symmetric_difference_update([int(x)])
  r['target_raw_d2_image']=sorted(image) if known else None
  r['target_raw_d2_present']=all('d2' in p for p in r['target_raw_d2_basis'])
(O/'logs-positive-directions.json').write_text(json.dumps(ps,ensure_ascii=False,indent=2)+'\n')
for r in ps:
 print(r['id'],r['name'],'target',r['target_name'],r['target_degree'],r['target_vector'],'d2',r.get('target_raw_d2_image'),'prior sources',[(p['id'],p['reason'],p['r'],p['dx']) for p in r['prior_exact_target_sources']],'prior boundaries',[(p['id'],p['reason'],p['r']) for p in r['prior_exact_target_boundaries']])
