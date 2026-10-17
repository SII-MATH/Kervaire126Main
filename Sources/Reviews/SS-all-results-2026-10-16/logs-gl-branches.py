#!/usr/bin/env python3
import json,collections
from pathlib import Path
O=Path('/tmp/SS-All-Results-Audit-20261016');raw=json.loads((O/'native-GL-E2-classification.json').read_text());native={r['id']:r for r in raw['rows']};meta=json.loads((O/'logs-gl-E2-request-metadata.json').read_text());rows=[];pairs=collections.defaultdict(dict)
for m in meta:
 n=native[m['request_id']];image=n['E2_image'];expected=[int(i) for i in m['expected_output_vector'].split(',') if i]
 if not image:branch='M0'
 elif list(n['target_degree'])==m['expected_output_degree'] and image==expected:branch='D-candidate'
 else:branch='M1'
 row={**m,'E2_image':image,'E2_image_degree':n['target_degree'],'branch':branch};rows.append(row);pairs[m['log_id']][m['edge']]=row
summary={'rows':len(pairs),'edge_counts':dict(collections.Counter(r['branch'] for r in rows)),'pair_counts':dict(collections.Counter(str((p['first']['branch'],p['second']['branch'])) for p in pairs.values())),'by_parent_confidence':{},'D_caveat':'D-candidate means actual logged output agrees with nonzero direct E2 image; historical boundary-level test is not reconstructed, so D vs M1 is not certified solely by this equality.'}
for confidence in ('adjacent','unique-compatible-historical'):
 pp=[p for p in pairs.values() if p['first']['parent_confidence']==confidence];summary['by_parent_confidence'][confidence]={'rows':len(pp),'pair_counts':dict(collections.Counter(str((p['first']['branch'],p['second']['branch'])) for p in pp))}
result={'summary':summary,'rows':rows};(O/'logs-GL-branch-summary.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n');print(json.dumps(summary,ensure_ascii=False,indent=2))
