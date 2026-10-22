"""Bounded read-only probes for the stem-62 hidden-square question.

Run with python3 -B probe.py. All source databases are opened read-only by
the existing probe_data helper. Only --output writes a generated report.
"""
import argparse
import csv
import hashlib
import importlib.util
import json
import resource
import sys
from pathlib import Path

resource.setrlimit(resource.RLIMIT_AS, (4 << 30, 4 << 30))
resource.setrlimit(resource.RLIMIT_CPU, (110, 110))
source = Path('/inspire/hdd/global_user/czxs25250150/ops/tmp/d3-x126-6-evidence/probe_data.py')
spec = importlib.util.spec_from_file_location('existing_probe_data', source)
p = importlib.util.module_from_spec(spec)
old_argv = sys.argv
sys.argv = [str(source)]
spec.loader.exec_module(p)
sys.argv = old_argv
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output', type=Path)
args = parser.parse_args()
sphere = p.alg('S0')
database = p.DATA / p.PATHS['S0']
einfty = Path('/inspire/hdd/global_user/czxs25250150/Kervaire126/Source/IWX/data/Adams-classical-Einfty.csv')
report = {'helper_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
          'database': {'path': str(database), 'sha256': hashlib.sha256(database.read_bytes()).hexdigest(),
                       'mode': 'ro'},
          'published_classical_einfty': {'path': str(einfty),
              'sha256': hashlib.sha256(einfty.read_bytes()).hexdigest()}}
with einfty.open(newline='') as stream:
    report['published_classical_einfty']['rows'] = [
        row for row in csv.DictReader(stream) if row['stem'] in ('31', '61', '62', '93')]
report['generators'] = list(sphere.db.execute(
    'select id,name,s,t from S0_AdamsE2_generators where id in (18,24,82,89,90,251,438,439,440)'))
report['stem61'] = list(sphere.db.execute(
    'select s,t,base,diff,level from S0_AdamsE2_ss where t-s=61 order by s,level'))
report['stem62'] = list(sphere.db.execute(
    'select s,t,base,diff,level from S0_AdamsE2_ss where t-s=62 order by s,level'))
report['stem31'] = list(sphere.db.execute(
    'select s,t,base,diff,level from S0_AdamsE2_ss where t-s=31 order by s,level'))
report['squares'] = {}
for label, terms, degree in [('a6', ['18,1,24,1'], (12,136)),
                            ('a8', ['82,1'], (16,140)),
                            ('a10', ['89,1','90,1'], (20,144))]:
    value = set()
    for m in terms:
        value.symmetric_difference_update(sphere.normal(p.mul(p.mon(m), p.mon(m))))
    report['squares'][label] = {'normal_form': sorted(value), 'degree': degree,
        'basis': [(i,r[1]) for i,r in enumerate(sphere.bydeg[degree])],
        'staircase': list(sphere.db.execute(
            'select s,t,base,diff,level from S0_AdamsE2_ss where s=? and t=? order by level,id', degree))}
report['correction'] = {'basis': [(i,r[1]) for i,r in enumerate(sphere.bydeg[(13,137)])],
    'staircase': list(sphere.db.execute(
        'select s,t,base,diff,level from S0_AdamsE2_ss where s=13 and t=137 order by level,id'))}
report['small_products'] = {label: sorted(sphere.normal(p.mul(p.mon(a),p.mon(b))))
    for label,a,b in [('h0_n','0,1','24,1'),('n_h4sq','24,1','7,2'),
                      ('n_sq','24,1','24,1'),('h1_c13','1,1','9,1,251,1'),
                      ('h1_n','1,1','24,1'),('h5sq_n','18,2','24,1'),
                      ('n_x92_4','24,1','163,1'),('d1_h4sq','25,1','7,2')]}
report['initial_massey_indeterminacy'] = {
    'left_degree': [4,36], 'right_degree': [1,32],
    'left_basis': [(i,r[1]) for i,r in enumerate(sphere.bydeg[(4,36)])],
    'right_basis': [(i,r[1]) for i,r in enumerate(sphere.bydeg[(1,32)])],
    'left_times_h4sq': [sorted(sphere.normal(p.mul(p.mon(r[1]),p.mon('7,2'))))
                        for r in sphere.bydeg[(4,36)]],
    'right_staircase': list(sphere.db.execute(
        'select base,diff,level from S0_AdamsE2_ss where s=1 and t=32'))}
report['factor_image_tests'] = []
for g,s,t in [(1,1,2),(2,1,4),(3,1,8),(8,4,18),(13,4,24)]:
    degree = (6-s,68-t)
    cols = [sphere.coords((6,68),p.mul(p.mon(str(g)+',1'),p.mon(r[1])))
            for r in sphere.bydeg.get(degree,[])]
    report['factor_image_tests'].append({'generator':g,'source_degree':degree,
        'columns':cols,'remainder':p.reduce_vec(1,cols)})
report['stem93_low'] = []
for s in range(1, 10):
    degree = (s,93+s)
    basis = sphere.bydeg.get(degree, [])
    products = []
    for i,r in enumerate(basis):
        product = sphere.normal(p.mul(p.mon('24,1'),p.mon(r[1])))
        products.append({'index':i,'monomial':r[1],'n_product':sorted(product),
            'target_coordinates':p.indices(sphere.coords((s+5,129+s),p.mul(p.mon('24,1'),p.mon(r[1]))))})
    report['stem93_low'].append({'degree':degree,'basis_products':products,
        'staircase':list(sphere.db.execute(
            'select base,diff,level from S0_AdamsE2_ss where s=? and t=? order by level,id',degree))})
report['moss_crossing_windows'] = {}
for stem,max_s in [(31,2),(32,4),(93,5)]:
    report['moss_crossing_windows'][str(stem)] = list(sphere.db.execute(
        'select s,t,base,diff,level from S0_AdamsE2_ss where t-s=? and s<=? order by s,level,id',
        (stem,max_s)))
report['stem32'] = list(sphere.db.execute(
    'select s,t,base,diff,level from S0_AdamsE2_ss where t-s=32 order by s,level,id'))
report['x92_4'] = {'generator':list(sphere.db.execute(
    'select id,name,s,t from S0_AdamsE2_generators where id=163')),
    'basis':[(i,r[1]) for i,r in enumerate(sphere.bydeg[(4,96)])],
    'staircase':list(sphere.db.execute(
        'select s,t,base,diff,level from S0_AdamsE2_ss where t-s=92 and s<=5 order by s,level,id'))}
report['crossing_d4_target'] = {'basis':[(i,r[1]) for i,r in enumerate(sphere.bydeg[(9,101)])],
    'n_products':[(i,sorted(sphere.normal(p.mul(p.mon('24,1'),p.mon(r[1])))))
                  for i,r in enumerate(sphere.bydeg[(9,101)])]}
report['stem93_differential_targets'] = {}
for s,r in [(3,4),(4,4),(5,4),(6,5),(7,3),(8,3),(8,5),(9,5)]:
    degree = (s+r,92+s+r)
    report['stem93_differential_targets'][f'{s}_d{r}'] = {
        'degree': degree,
        'basis': [(i,row[1]) for i,row in enumerate(sphere.bydeg.get(degree,[]))]}
payload = json.dumps(report, indent=2)
if args.output:
    args.output.write_text(payload + '\n')
    print(json.dumps({'output':str(args.output),'stem93_low':report['stem93_low']}))
else:
    print(payload)
