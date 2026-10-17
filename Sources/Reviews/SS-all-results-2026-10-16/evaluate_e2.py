#!/usr/bin/env python3
"""Independent F2 E2 evaluator from exported Groebner bases; opens all DBs mode=ro."""
import collections,functools,json,pathlib,re,sqlite3,sys,time
ROOT=pathlib.Path('/tmp/SS-All-Results-Audit-20261016');DATA=pathlib.Path(sys.argv[1] if len(sys.argv)>1 else ROOT/'full-inputs/kervaire-49')
a=json.loads((DATA/'ss.json').read_text()); specs={x['name']:(x,k=='rings') for k in ['rings','modules'] for x in a[k]}; maps=json.loads((ROOT/'input-map-decoding.json').read_text()); first={}
traces=[]
for m in maps:first.setdefault(m['name'],m)
def mon(s):
 z=[int(i) for i in s.split(',') if i];assert len(z)%2==0;return tuple(zip(z[::2],z[1::2]))
def term(s,ring):
 if ring:return (-1,mon(s))
 z=s.split(',');return (int(z[-1]),mon(','.join(z[:-1])))
def poly(s,ring):
 if not s:return frozenset()
 if ring and s==';':return frozenset([(-1,())])
 return frozenset(term(t,ring) for t in s.split(';'))
def mulmon(a,b):
 z=dict(a)
 for g,e in b:z[g]=z.get(g,0)+e
 return tuple(sorted(z.items()))
def quotient(a,b):
 d=dict(a)
 for g,e in b:
  if d.get(g,0)<e:return None
  d[g]-=e
 return tuple((g,e) for g,e in sorted(d.items()) if e)
def xoritems(ps):
 z=set()
 for p in ps:z.symmetric_difference_update(p)
 return frozenset(z)
class Spectrum:
 def __init__(self,name):
  self.name=name;cfg,self.ring=specs[name];self.conn=sqlite3.connect('file:'+str(DATA/cfg['path'])+'?mode=ro',uri=True);p=name+'_AdamsE2';self.basis=collections.defaultdict(list)
  for s,t,txt in self.conn.execute('select s,t,mon from '+p+'_basis order by id'):self.basis[(s,t)].append(term(txt,self.ring))
  self.byterm={d:{m:i for i,m in enumerate(bs)} for d,bs in self.basis.items()};self.rules=collections.defaultdict(list)
  for txt, in self.conn.execute('select rel from '+p+'_relations'):
   parts=txt.split(';');lead=term(parts[0],self.ring);tail=poly(';'.join(parts[1:]),self.ring) if len(parts)>1 else frozenset();self.rules[lead[0]].append((lead[1],tail))
  self.parent=None if self.ring else getsp(cfg['over'])
 @functools.lru_cache(maxsize=None)
 def reduce_term(self,t):
  v,m=t
  for lm,tail in self.rules[v]:
   q=quotient(m,lm)
   if q is not None:return xoritems(self.reduce_term((w,mulmon(n,q))) for w,n in tail)
  if self.parent:
   for lm,tail in self.parent.rules[-1]:
    q=quotient(m,lm)
    if q is not None:return xoritems(self.reduce_term((v,mulmon(n,q))) for _,n in tail)
  return frozenset([t])
 def red(self,p):return xoritems(self.reduce_term(t) for t in p)
 def fromvec(self,x,d):
  bs=self.basis[d];assert all(0<=i<len(bs) for i in x),(self.name,d,x,len(bs));return xoritems([frozenset([bs[i]]) for i in x])
 def tovec(self,p,d):
  try:return tuple(sorted(self.byterm[d][t] for t in p))
  except KeyError as e:raise ValueError((self.name,d,'nonbasis',p)) from e
@functools.lru_cache(None)
def getsp(n):return Spectrum(n)
@functools.lru_cache(None)
def mapimages(ordinal):
 m=maps[ordinal];c=sqlite3.connect('file:'+str(DATA/m['path'])+'?mode=ro',uri=True);names=[r[0] for r in c.execute("select name from sqlite_master where type='table' and name like 'map_AdamsE2_%'")];assert len(names)==1
 return tuple(poly(txt,specs[m['to']][1]) for txt, in c.execute('select map from '+names[0]+' order by id'))
@functools.lru_cache(None)
def evaluate(ordinal,d,x):
 m=maps[ordinal];src=getsp(m['from']);dst=getsp(m['to']);target=(d[0]+m['AF'],d[1]+m['deg_t'])
 if not x:return target,()
 if m['kind']=='composition':
  for n in m['resolved_children']:d,x=evaluate(n,d,x)
  assert d==target;return d,x
 p=src.fromvec(x,d)
 if m['kind']=='factor':
  stem,s,indices=m['factor'];indices=[indices] if isinstance(indices,int) else indices
  if src.ring:q=dst.fromvec(tuple(indices),(s,stem+s))
  else:q=getsp(specs[m['from']][0]['over']).fromvec(tuple(indices),(s,stem+s))
  raw=xoritems(frozenset([(v if w==-1 else w,mulmon(n,k))]) for v,n in p for w,k in q)
 else:
  assert not src.ring,(m['name'],'ring substitution unused by cof')
  assert 'over' not in m,(m['name'],'nonidentity scalar unused by cof')
  images=mapimages(ordinal);raw=xoritems(frozenset([(w,mulmon(n,k))]) for v,n in p for w,k in images[v])
 result=dst.red(raw);answer=dst.tovec(result,target);traces.append(dict(map=m['name'],ordinal=ordinal,name=m['to'],ring=dst.ring,source_degree=d,source_x=x,target_degree=target,raw=list(raw),reduced=list(result),target_vector=answer));return target,answer
def vec(s):return tuple(int(i) for i in s.split(',') if i)
if __name__=='__main__':
 rows=json.loads((ROOT/'logs-full-synthetic-rows.json').read_text());out=[];counts=collections.Counter();start=time.time()
 for row in rows:
  if row['reason']!='SynCs':continue
  m=first[row['map']];d=(row['s'],row['t']);x=vec(row['x'])
  try:
   target,fx=evaluate(m['ordinal'],d,x);branch='M1' if fx else 'M0';counts[branch]+=1
   out.append(dict(id=row['id'],map=m['name'],source_degree=d,source_x=x,target_degree=target,E2_image=fx,branch=branch,direct_M0_parameters=row.get('direct_M0_parameters')))
  except Exception as e:
   counts['failed']+=1;out.append(dict(id=row['id'],map=m['name'],error=repr(e)))
  if len(out)%100==0:print(len(out),dict(counts),'seconds',round(time.time()-start,1),flush=True)
 summary=dict(counts=counts,elapsed=time.time()-start,rows=len(out),all_classified=counts['failed']==0)
 (ROOT/'E2-reduction-traces.json').write_text(json.dumps(traces,ensure_ascii=False)+'\n');(ROOT/'E2-branch-classification.json').write_text(json.dumps(dict(summary=summary,rows=out),ensure_ascii=False,indent=2)+'\n');print(summary)
