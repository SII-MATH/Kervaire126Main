#!/usr/bin/env python3
import sys,json,sqlite3
from pathlib import Path
sys.path.insert(0,'/tmp/SS-All-Results-Audit-20261016');import evaluate_e2 as E
O=Path('/tmp/SS-All-Results-Audit-20261016');D=sqlite3.connect('file:/tmp/mh2-machine-proof-audit/proofs.db?mode=ro',uri=True);D.row_factory=sqlite3.Row
requests=[('S0__C2',(14,100),(1,)),('C2__S0',(12,99),(0,)),('S0__S0_by_2',(12,98),(0,))];checks=[]
for n,d,x in requests:
 m=E.first[n];dt,im=E.evaluate(m['ordinal'],d,x);checks.append({'map':n,'source_degree':d,'source_vector':x,'target_degree':dt,'target_vector':im})
records=[dict(r) for r in D.execute('select * from log where id in (11892,2413041)')]
out={'checks':checks,'records':records,'scope':'Example of actual M1 in the ordinary AF1 2-cofiber triangle. First incoming d2 is explicit. Subsequent internal child details require historical GetDiffAndLevel state; checks do not reconstruct that state.'};(O/'logs-M1-example.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n');print(json.dumps(out,ensure_ascii=False,indent=2))
