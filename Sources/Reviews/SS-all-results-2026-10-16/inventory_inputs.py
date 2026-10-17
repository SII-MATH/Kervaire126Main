#!/usr/bin/env python3
"""Read-only cw49 config inventory; faithfully resolve names by first prior map."""
import collections,hashlib,json,pathlib,sys
cfg=pathlib.Path(sys.argv[1] if len(sys.argv)>1 else '/tmp/mh2-machine-proof-audit/database-subset/kervaire-49/ss.json')
out=pathlib.Path('/tmp/SS-All-Results-Audit-20261016')
a=json.loads(cfg.read_text()); loaded=[]; first={}; decoded=[]
for section in ['maps','maps_v2']:
 for item in a[section]:
  m=dict(item);m['section']=section;m['ordinal']=len(loaded)
  if 'factor' in m:
   m['AF']=m['factor'][1];m['deg_t']=sum(m['factor'][:2]);m['kind']='factor'
  elif 'composition' in m:
   children=[first[n] for n in m['composition']]
   assert all(children[i]['to']==children[i+1]['from'] for i in range(len(children)-1))
   assert children[0]['from']==m['from'] and children[-1]['to']==m['to']
   m['AF']=sum(z['AF'] for z in children);m['deg_t']=sum(z['deg_t'] for z in children);m['kind']='composition'
   m['resolved_children']=[z['ordinal'] for z in children]
  else:
   m['AF']=m.get('fil',0);m['deg_t']=m['AF']-m.get('sus',0);m['kind']='file'
  loaded.append(m); first.setdefault(m['name'],m)
rows=[]
for c in a['cofseqs']:
 ns=[c[k] for k in ['i','q','d']];ms=[first[n] for n in ns];afs=[m['AF'] for m in ms]
 assert sum(x>0 for x in afs)==1
 assert all(ms[i]['to']==ms[(i+1)%3]['from'] for i in range(3))
 assert sum(m['deg_t']-m['AF'] for m in ms)==-1,(c,ms)
 for rotation in range(3):
  rs=[ms[(rotation+i)%3] for i in range(3)];ds=[m['AF'] for m in rs];es=[int(d>0) for d in ds]
  rows.append(dict(cof=c['name'],rotation=rotation,objects=[m['from'] for m in rs],maps=[m['name'] for m in rs],AF=ds,e=es,l1_M0=ds[2]-es[2],m1_M0=ds[1]-es[1]))
archive=json.load(open('/tmp/mh2-machine-proof-audit/database-inventory.json'))['entries'];dbnames={e['name'].split('/')[-1] for e in archive if e['name'].endswith('.db')};refs={x['path'] for section in ['rings','modules','maps','cofseqs'] for x in a[section] if 'path'in x}; extra=sorted(dbnames-refs)
summary=dict(config=str(cfg),sha256=hashlib.sha256(cfg.read_bytes()).hexdigest(),counts={k:len(v) for k,v in a.items() if isinstance(v,list)},maps_unique=len(first),map_kinds=dict(collections.Counter(m['kind'] for m in loaded)),duplicates={n:[m for m in loaded if m['name']==n] for n,v in collections.Counter(m['name'] for m in loaded).items() if v>1},triangles=len(a['cofseqs']),triangle_AF_histogram={str(k):v for k,v in sorted(collections.Counter(tuple(r['AF']) for r in rows if r['rotation']==0).items())},directions=len(rows),M0_counts={str(k):v for k,v in sorted(collections.Counter((r['l1_M0'],r['m1_M0']) for r in rows).items())},exceptional=[r for r in rows if r['l1_M0'] or r['m1_M0']],cofiber_objects=sorted(set(z for r in rows for z in r['objects'])),archive_db_count=len(dbnames),referenced_db_count=len(refs),archive_extra_db_count=len(extra),archive_extra_spectra=[n for n in extra if not n.startswith('map_')],archive_extra_maps=[n for n in extra if n.startswith('map_')],missing_archive_refs=sorted(refs-dbnames))
(out/'input-inventory.json').write_text(json.dumps(summary,ensure_ascii=False,indent=2)+'\n');(out/'input-map-decoding.json').write_text(json.dumps(loaded,ensure_ascii=False,indent=2)+'\n');(out/'input-M0-directions.json').write_text(json.dumps(rows,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({k:v for k,v in summary.items() if k not in ['duplicates','exceptional','cofiber_objects','archive_extra_maps','archive_extra_spectra']},ensure_ascii=False,indent=2))
