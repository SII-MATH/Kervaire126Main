#!/usr/bin/env python3
"""Read only: inventory the AF data of cw49 cofiber directions.

Counts configuration directions, never historical successful algorithm calls.
e is inferred from the single positive AF map in each actual cofiber triangle;
the other two maps are homology mono/epi by its cofiber long exact sequence.
No mutable spectral-sequence tables are read or modified.
"""
import argparse
import collections
import json

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('config', nargs='?', default='/tmp/mh2-machine-proof-audit/database-subset/kervaire-49/ss.json')
args = parser.parse_args()
with open(args.config, encoding='utf-8') as handle:
    config = json.load(handle)
maps = {item['name']: item for key in ('maps', 'maps_v2') for item in config[key]}

def filtration(name, ancestors=()):
    assert name not in ancestors, ('cyclic composition', name, ancestors)
    item = maps[name]
    if 'factor' in item:
        return item['factor'][1]
    if 'composition' in item:
        return sum(filtration(child, (*ancestors, name)) for child in item['composition'])
    return item.get('fil', 0)

histogram = collections.Counter()
directions = collections.Counter()
exceptional = []
for cof in config['cofseqs']:
    names = [cof[key] for key in ('i', 'q', 'd')]
    af = [filtration(name) for name in names]
    assert sum(value > 0 for value in af) == 1, (cof['name'], names, af)
    e = [int(value > 0) for value in af]
    histogram[tuple(af)] += 1
    for rotation in range(3):
        i_f, i_g, i_h = rotation, (rotation + 1) % 3, (rotation + 2) % 3
        k, m1 = af[i_h] - e[i_h], af[i_g] - e[i_g]
        directions[k, m1] += 1
        if k or m1:
            exceptional.append((cof['name'], rotation, [names[index] for index in (i_f, i_g, i_h)],
                                [af[index] for index in (i_f, i_g, i_h)],
                                [e[index] for index in (i_f, i_g, i_h)], k, m1))

print('cw49 configuration inventory; these are NOT historical call counts.')
print('Config:', args.config)
print('Cofiber triangles:', len(config['cofseqs']))
print('AF(i,q,d) histogram:')
for signature, count in sorted(histogram.items()):
    print(' ', signature, ':', count)
print('Directions:', sum(directions.values()))
print('Direct-preimage M0 directions by (k,m1):')
for signature, count in sorted(directions.items()):
    print(' ', signature, ':', count)
print('All exceptional M0 directions (f,g,h ordered):')
for name, rotation, arrow_names, af, e, k, m1 in exceptional:
    print(f'  {name}, rotation={rotation}, k={k}, m1={m1}')
    for letter, arrow_name, d_value, e_value in zip('fgh', arrow_names, af, e):
        print(f'    {letter}: {arrow_name}; AF={d_value}; e={e_value}')
print('M1 recursive boundary-image paths are NOT certified by these M0 counts.')
