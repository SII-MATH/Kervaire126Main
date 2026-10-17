#!/usr/bin/env python3
import sys,json,sqlite3
from pathlib import Path
sys.path.insert(0,'/tmp/SS-All-Results-Audit-20261016')
import evaluate_e2 as E
O=Path('/tmp/SS-All-Results-Audit-20261016');D=sqlite3.connect('file:/tmp/mh2-machine-proof-audit/proofs.db?mode=ro',uri=True);D.row_factory=sqlite3.Row
checks=[]
for name,degree,vec in [('S0__C2sigma',(40,135),(0,)),('S0__C2sigma',(40,135),(1,)),('S0__C2sigma',(40,135),(0,1)),('S0__S0_by_2sigma',(41,128),(1,))]:
 m=E.first[name];out=E.evaluate(m['ordinal'],degree,vec);checks.append({'map':name,'source_degree':degree,'source_vector':vec,'target_degree':out[0],'target_vector':out[1]})
rows=[dict(r) for r in D.execute("select * from log where id in (328504,328510,41405,2414551)")]
result={'E2_square':checks,'earlier_log_evidence':rows,'derived_d3':{'name':'S0','degree':[40,135],'source':[1],'target':[0],'reason':'log328504 gives d3[0]=[0]; log328510 gives [0,1] survives to d4, hence d3[0,1]=0 and by linearity d3[1]=[0].'},'scope':'Static E2 maps and independent prior differential/cycle evidence; does not reconstruct chosen historical staircase top preimage or prove no-crossing/ESS domains.'}
(O/'logs-positive-m0-square.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n');print(json.dumps(result,ensure_ascii=False,indent=2))
