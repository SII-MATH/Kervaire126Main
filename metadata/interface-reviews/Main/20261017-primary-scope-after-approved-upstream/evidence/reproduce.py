#!/usr/bin/env python3
"""Read saved evidence only; no Lean build or writes outside the review directory."""
from pathlib import Path
import json,hashlib
base=Path(__file__).resolve().parent
m=json.loads((base/'snapshot-manifest.json').read_text())
count=0
for p,h in m['files'].items():
    q=base/p.replace('/','__')
    if q.exists():
        assert hashlib.sha256(q.read_bytes()).hexdigest()==h,p
        count+=1
print(f'Snapshot SHA-256: PASS ({count} saved Lean files); HEAD={m["HEAD"]}')
for rel,decl,ty in [
 ('KIP126/Main/Internal/Choice/OrderTwo.lean','theta_degree_order_two','(theta : BiHom 62 64 (S_0_0 : SyntheticSpectrum))'),
 ('KIP126/Main/Internal/Theta/OrderTwo.lean','two_torsion_62_70','(b : BiHom 62 70 (S_0_0 : SyntheticSpectrum))')]:
    s=(base/rel.replace('/','__')).read_text(); a=s.index('private theorem '+decl); b=s.index(':= by',a)
    assert ty in s[a:b]
    assert '∃' not in s[a:b] and 'ThetaChoice' not in s[a:b]
    print('Exact premise audit:',s[a:b].strip())
# Finite algebra check of the lifting argument, not a synthetic-spectrum model.
cases=0
for n in range(1,25):
 for d in range(1,25):
  for c in range(d):
   if (n*c)%d: continue
   f=lambda x:(c*x)%d
   image={f(x) for x in range(n)}
   if any((2*x)%n for x in range(n) if f(x)==0): continue
   if any((2*y)%d not in image for y in range(d)): continue
   for b in range(1,d):
    if 3*b%d: continue
    lifts=[x for x in range(n) if f(x)==b]
    assert lifts
    x=lifts[0]; xp=(-2*x)%n
    assert f(xp)==b and 3*xp%n==0 and xp!=0
    assert sum(f(y)==b and 3*y%n==0 for y in range(n))==1
    cases+=1
assert cases>0
print(f'Finite algebra sanity check: PASS ({cases} order-three lifts).')
print('No Lean counterexample or fixed-background identification is asserted.')
