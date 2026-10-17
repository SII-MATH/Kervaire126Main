#!/usr/bin/env python3
"""Read-only full proofs.db synthetic-output census; never infer internal branches from output rows."""
import sqlite3,json,re,hashlib,collections
from pathlib import Path
OUT=Path('/tmp/SS-All-Results-Audit-20261016');ROOT=Path('/tmp/mh2-machine-proof-audit')
raw=(ROOT/'database-subset/kervaire-49/ss.json').read_text()
cfg=json.loads(re.sub(r'("(?:\\.|[^"\\])*"|//[^\n]*|/\*[\s\S]*?\*/)',lambda m:m[0] if m[0].startswith('"') else '',raw))
maps={}
for k in ('maps','maps_v2'):
 for m in cfg[k]: maps.setdefault(m['name'],m)
def degree(n):
 m=maps[n]
 if 'factor' in m:
  stem,s=m['factor'][:2];return s,stem+s
 if 'composition' in m:
  ds=[degree(x) for x in m['composition']];return tuple(sum(d[k] for d in ds) for k in (0,1))
 s=m.get('fil',0);return s,s-m.get('sus',0)
cofs={c['name']:[c[k] for k in ('i','q','d')] for c in cfg['cofseqs']}
def hist(xs):return dict(collections.Counter(map(str,xs)).most_common())
def rang(xs):return [min(xs),max(xs)] if xs else None
D=sqlite3.connect('file:'+str(ROOT/'proofs.db')+'?mode=ro',uri=True);D.row_factory=sqlite3.Row
rows=[dict(r) for r in D.execute("select * from log where reason in ('Syn','SynCs','SynCsIn') order by id")]
summary={'database':str(ROOT/'proofs.db'),'sha256':hashlib.sha256((ROOT/'proofs.db').read_bytes()).hexdigest(),'tables':[dict(r) for r in D.execute("select name,sql from sqlite_master where type='table'")], 'row_count':D.execute('select count(*) from log').fetchone()[0]}
for reason in ('Syn','SynCs','SynCsIn'):
 rs=[r for r in rows if r['reason']==reason]
 summary[reason]={'count':len(rs),'names':hist(r['name'] for r in rs),'depth':hist(r['depth'] for r in rs),'info_present':sum(bool(r['info']) for r in rs),'r':hist(r['r'] for r in rs),'s_range':rang([r['s'] for r in rs]),'t_range':rang([r['t'] for r in rs]),'stem_range':rang([r['stem'] for r in rs]),'zero_target_count':sum(r['dx']=='' for r in rs)}
greys=collections.defaultdict(list)
for gr in D.execute('select * from log where reason is null order by id'):
 gr=dict(gr);greys[(gr['name'],gr['stem'])].append(gr)
# GL parent hint: Logger emits Grey then first Syn contiguously. Other predecessor matches remain only candidates.
pat=re.compile(r'Apply General Leibniz with map `([^`]+)` and k=(\d+) where the Adams differential has( no)? crossing')
for row in rows:
 if row['reason']=='Syn':
  match=pat.fullmatch(row['info'] or '')
  if not match:row['decode_error']='proof format';continue
  name,k,no=match.groups();row.update(map=name,kappa=int(k),adams_no_crossing=bool(no))
  if name not in maps:
   row['decode_error']='map absent from current config';continue
  deg=degree(name);row['map_degree']=deg;row['e']=int(deg[0]>0)
  previous=D.execute('select * from log where id<? order by id desc limit 1',(row['id'],)).fetchone();previous=dict(previous)
  row['previous_row']=previous
  source=maps[name]['from'];source_stem=row['stem']-(deg[1]-deg[0]);row['expected_source_name']=source;row['expected_source_stem']=source_stem
  good=previous['reason'] is None and previous['name']==source and previous['stem']==source_stem and previous['dx'] not in ('',None,'-1')
  if good:
   r=previous['r'];m=row['s']-previous['s'];l=m+row['r']-r;e=row['e']
   row['adjacent_grey_parent']={'id':previous['id'],'r':r,'m':m,'l':l,'e':e,'bound':r-2+e,'visibility_bound_holds':m<=r-2+e,'excess_m':m-deg[0],'excess_l':l-deg[0]}
  # bounded candidate origins in prior log, same source object and stem, not proof of parenthood.
  candidates=[p for p in greys[(source,source_stem)] if p['id']<row['id']][::-1]
  row['prior_grey_candidates']=[{'id':p['id'],'r':p['r'],'s':p['s'],'x':p['x'],'dx':p['dx'],'m':row['s']-p['s'],'l':row['s']+row['r']-p['s']-p['r']} for p in candidates]
  known=[p for p in row['prior_grey_candidates'] if p['r']>=2 and p['dx'] not in ('',None,'-1')]
  row['mechanical_parent_candidates']=known
  if not good and len(known)==1:
   p=known[0];row['unique_grey_parent']={**p,'e':row['e'],'bound':p['r']-2+row['e'],'visibility_bound_holds':p['m']<=p['r']-2+row['e']}
 elif row['reason']=='SynCs':
  cname,it=row['name'].rsplit(':',1);it=int(it);
  if cname not in cofs:
   row['decode_error']='cofseq absent from current config';continue
  ns=cofs[cname];f,g,h=[ns[(it+j)%3] for j in range(3)]
  dfs={n:degree(n) for n in (f,g,h)};fs,ft=dfs[f];gs,gt=dfs[g];hs,ht=dfs[h]
  row.update(map=f,next_map=g,previous_map=h,map_degree=dfs[f],output_extension_excess=row['r']-fs,
    direct_M0_parameters={'l1':hs-int(hs>0),'m1':gs-int(gs>0),'warning':'Conditional: applies only IF this output used M0. Internal branch absent from log.'})
  # For M0 only: output s=xtop.s+r_xtop-gs; xtop.s=x.s-hs => r_xtop=output.r+hs+gs.
  row['direct_M0_parameters']['r_xtop']=row['r']+hs+gs
  row['direct_M0_parameters']['xtop_s']=row['s']-hs
  row['direct_M0_parameters']['xtop_t']=row['t']-ht
syn=[r for r in rows if r['reason']=='Syn'];synCs_all=[r for r in rows if r['reason']=='SynCs'];synCs=[r for r in synCs_all if 'direct_M0_parameters' in r];adj=[r for r in syn if 'adjacent_grey_parent' in r]
summary['Syn'].update(maps=hist(r['map'] for r in syn),kappa=hist(r['kappa'] for r in syn),no_crossing=hist(r['adams_no_crossing'] for r in syn),adjacent_parent_count=len(adj),adjacent_bound_results=hist(r['adjacent_grey_parent']['visibility_bound_holds'] for r in adj),adjacent_bound_fail_ids=[r['id'] for r in adj if not r['adjacent_grey_parent']['visibility_bound_holds']],adjacent_mlr=hist(tuple(r['adjacent_grey_parent'][k] for k in ('m','l','r','e')) for r in adj))
summary['Syn'].update(unique_nonadj_parent_count=sum('unique_grey_parent' in r for r in syn),unique_nonadj_bound_results=hist(r['unique_grey_parent']['visibility_bound_holds'] for r in syn if 'unique_grey_parent' in r),unresolved_count=sum('unique_grey_parent' not in r and 'adjacent_grey_parent' not in r for r in syn),map_count=len(set(r['map'] for r in syn)),adjacent_hidden_types=hist((r['adjacent_grey_parent']['m']>r['map_degree'][0],r['adjacent_grey_parent']['l']>r['map_degree'][0]) for r in adj))
unresolved=[r for r in syn if 'unique_grey_parent' not in r and 'adjacent_grey_parent' not in r]
summary['Syn'].update(parameter_tuple_determined=summary['Syn']['adjacent_parent_count']+summary['Syn']['unique_nonadj_parent_count'],all_candidate_bound_count=sum(all(p['m']<=p['r']-2+r['e'] for p in r['mechanical_parent_candidates']) for r in unresolved),mixed_candidate_bound_count=sum(not all(p['m']<=p['r']-2+r['e'] for p in r['mechanical_parent_candidates']) for r in unresolved),parent_candidate_max=max(len(r['mechanical_parent_candidates']) for r in syn),parenthood_caveat='Reconstruction assumes released source logging and current static map degrees; no dependency IDs. Adjacent grey parent is forced by source code. Unique nonadj grey parent is forced by exhaustive earlier same-name/stem nonempty-differential hints. No theoretical visibility bound is used to filter parent candidates.')
summary['SynCs'].update(config_decodeable=len(synCs),output_excess=hist(r['output_extension_excess'] for r in synCs),outside_config=[r for r in synCs_all if 'decode_error' in r],directions=len(set(r['name'] for r in synCs)),triangles=len(set(r['name'].rsplit(':',1)[0] for r in synCs)),conditional_M0_lm=hist((r['direct_M0_parameters']['l1'],r['direct_M0_parameters']['m1']) for r in synCs),positive_M0_direction_rows=[{k:r[k] for k in ('id','name','s','t','r','x','dx','map','direct_M0_parameters')} for r in synCs if any(r['direct_M0_parameters'][k] for k in ('l1','m1'))])
(OUT/'logs-full-synthetic-rows.json').write_text(json.dumps(rows,ensure_ascii=False,indent=2)+'\n')
(OUT/'logs-summary.json').write_text(json.dumps(summary,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({k:({a:b for a,b in v.items() if a not in ('names','positive_M0_direction_rows','adjacent_mlr')} if isinstance(v,dict) else v) for k,v in summary.items()},ensure_ascii=False,indent=2))
