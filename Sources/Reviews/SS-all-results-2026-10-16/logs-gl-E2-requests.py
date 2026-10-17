#!/usr/bin/env python3
import json
from pathlib import Path
O=Path('/tmp/SS-All-Results-Audit-20261016');rs=json.loads((O/'logs-full-synthetic-rows.json').read_text());requests=[];metadata=[]
for row in rs:
 if row['reason']!='Syn':continue
 parent=row.get('adjacent_grey_parent') or row.get('unique_grey_parent')
 if not parent:continue
 if 'adjacent_grey_parent' in row:
  source=row['previous_row'];confidence='adjacent'
 else:
  source={**parent,'s':row['s']-parent['m'],'t':row['s']-parent['m']+row['expected_source_stem']};confidence='unique-compatible-historical'
 r=parent['r'];ps,pt=source['s'],source['t']
 for which,s,t,x in [(0,ps,pt,source['x']),(1,ps+r,pt+r-1,source['dx'])]:
  requests.append({'id':2*row['id']+which,'map':row['map'],'s':s,'t':t,'x':x})
  metadata.append({'request_id':2*row['id']+which,'log_id':row['id'],'edge':'first' if which==0 else 'second','parent_id':source['id'],'parent_confidence':confidence,'expected_output_degree':[row['s']+which*row['r'],row['t']+which*(row['r']-1)],'expected_output_vector':row['x'] if which==0 else row['dx'],'output_length':parent['m'] if which==0 else parent['l'],'map_AF':row['map_degree'][0]})
(O/'logs-gl-E2-requests.json').write_text(json.dumps(requests,ensure_ascii=False,indent=2)+'\n');(O/'logs-gl-E2-request-metadata.json').write_text(json.dumps(metadata,ensure_ascii=False,indent=2)+'\n');print(len(requests))
