#!/usr/bin/env python3
import collections,hashlib,json,pathlib,sqlite3
R=pathlib.Path('/tmp/SS-All-Results-Audit-20261016');D=R/'full-inputs/kervaire-49';a=json.load(open(D/'ss.json'));out={'config_sha256':hashlib.sha256((D/'ss.json').read_bytes()).hexdigest(),'spectra':[],'file_maps':[],'cofseqs':[]}
def con(p):return sqlite3.connect('file:'+str(D/p)+'?mode=ro',uri=True)
for k in ['rings','modules']:
 for x in a[k]:
  c=con(x['path']);meta=dict(c.execute('select name,value from version'));n=x['name'];p=n+'_AdamsE2'; bs=c.execute('select count(*),max(s),max(t) from '+p+'_basis').fetchone();sc=c.execute('select count(*),min(level),max(level),sum(diff is null) from '+p+'_ss').fetchone();out['spectra'].append(dict(name=n,path=x['path'],metadata=meta,basis=dict(zip(['rows','max_s','max_t'],bs)),ss=dict(zip(['rows','min_level','max_level','unknown_diff'],sc))));c.close()
for x in a['maps']:
 if 'path' not in x:continue
 c=con(x['path']);meta=dict(c.execute('select name,value from version'));ts=c.execute("select name from sqlite_master where type='table' and name like 'map_AdamsE2_%'").fetchall();assert len(ts)==1;t=ts[0][0];out['file_maps'].append(dict(name=x['name'],path=x['path'],metadata=meta,configured_fil=x.get('fil',0),configured_sus=x.get('sus',0),configured_t_max=x['t_max'],rows=c.execute('select count(*) from '+t).fetchone()[0]));c.close()
for x in a['cofseqs']:
 c=con(x['path']);t='cofseq_'+x['name'];out['cofseqs'].append(dict(name=x['name'],path=x['path'],rows=c.execute('select count(*) from '+t).fetchone()[0],schema=c.execute('select sql from sqlite_master where name=?',(t,)).fetchone()[0]));c.close()
mis=[]
for x in out['file_maps']:
 for field,key in [('configured_fil','filtration'),('configured_sus','suspension')]:
  if key in x['metadata'] and int(x['metadata'][key])!=x[field]:mis.append(dict(map=x['name'],field=field,configured=x[field],metadata=x['metadata'][key]))
out['metadata_mismatch']=mis
(R/'full-input-metadata.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n');print('spectra',len(out['spectra']),'file_maps',len(out['file_maps']),'cofseqs',len(out['cofseqs']),'fil/sus mismatches',len(mis));print(mis)
