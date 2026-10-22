"""Read-only C2 h7 differential probes; all claims are relative to archived inputs."""
import functools
import hashlib
import json
from pathlib import Path
import resource
import sqlite3

import json5

resource.setrlimit(resource.RLIMIT_AS, (4 * 1024**3, 4 * 1024**3))
ROOT = Path(__file__).resolve().parent
DATA = Path('/inspire/hdd/global_user/czxs25250150/ops/tmp/d3-x126-6-evidence/unique-propagation/cw210-original/kervaire')
CONFIG = json5.loads((DATA / 'ss.json').read_text())
PATHS = {x['name']: x['path'] for key in ['rings', 'modules'] for x in CONFIG[key]}
READ = set()


def connect(path):
    READ.add(path)
    return sqlite3.connect(f'file:{path}?mode=ro&immutable=1', uri=True)


def vec(raw):
    if raw is None:
        return None
    value = 0
    for i in raw.split(','):
        if i:
            value ^= 1 << int(i)
    return value


def indices(value):
    return [i for i in range(value.bit_length()) if value >> i & 1]


def echelon(columns):
    pivots = {}
    for col in columns:
        while col:
            k = col.bit_length() - 1
            if k in pivots:
                col ^= pivots[k]
            else:
                pivots[k] = col
                break
    return pivots


def reduce(value, columns):
    for k, col in sorted(echelon(columns).items(), reverse=True):
        if value >> k & 1:
            value ^= col
    return value


def solve(columns, value):
    pivots = {}
    for i, col in enumerate(columns):
        witness = 1 << i
        while col:
            k = col.bit_length() - 1
            if k in pivots:
                a, b = pivots[k]
                col ^= a
                witness ^= b
            else:
                pivots[k] = col, witness
                break
    witness = 0
    while value:
        k = value.bit_length() - 1
        if k not in pivots:
            return None
        a, b = pivots[k]
        value ^= a
        witness ^= b
    return witness


def mon(raw):
    if not raw:
        return (), None
    nums = list(map(int, raw.split(',')))
    n = len(nums) // 2 * 2
    return tuple(zip(nums[:n:2], nums[1:n:2])), nums[-1] if len(nums) % 2 else None


def multiply(a, b):
    assert a[1] is None or b[1] is None
    coef = dict(a[0])
    for g, e in b[0]:
        coef[g] = coef.get(g, 0) + e
    return tuple(sorted(coef.items())), a[1] if b[1] is None else b[1]


def divide(a, b):
    if b[1] is not None and a[1] != b[1]:
        return None
    coef = dict(a[0])
    for g, e in b[0]:
        if coef.get(g, 0) < e:
            return None
        coef[g] -= e
    return tuple((g, e) for g, e in sorted(coef.items()) if e), a[1] if b[1] is None else None


@functools.lru_cache(None)
def algebra(name):
    return Algebra(name)


class Algebra:
    def __init__(self, name):
        self.name = name
        self.db = connect(DATA / PATHS[name])
        self.prefix = name + '_AdamsE2_'
        self.bydeg = {}
        self.lookup = {}
        for row in self.db.execute(f'SELECT id,mon,s,t FROM {self.prefix}basis ORDER BY id'):
            deg = row[2], row[3]
            group = self.bydeg.setdefault(deg, [])
            self.lookup[deg, mon(row[1])] = len(group)
            group.append(row)
        self.rules = [] if name in ['S0', 'tmf'] else list(algebra('S0').rules)
        for raw, s, t in self.db.execute(f'SELECT rel,s,t FROM {self.prefix}relations'):
            terms = list(map(mon, raw.split(';')))
            self.rules.append((terms[0], terms[1:]))
        self.byvar = {}
        for lead, tail in self.rules:
            key = ('v', lead[1]) if lead[1] is not None else ('g', lead[0][0][0])
            self.byvar.setdefault(key, []).append((lead, tail))

    @functools.lru_cache(None)
    def normal(self, m):
        keys = [('g', g) for g, _ in m[0]] + ([('v', m[1])] if m[1] is not None else [])
        for key in keys:
            for lead, tail in self.byvar.get(key, []):
                q = divide(m, lead)
                if q is not None:
                    out = set()
                    for term in tail:
                        out.symmetric_difference_update(self.normal(multiply(q, term)))
                    return frozenset(out)
        return frozenset([m])

    def coords(self, deg, m):
        out = 0
        for term in self.normal(m):
            out ^= 1 << self.lookup[deg, term]
        return out

    @functools.lru_cache(None)
    def rows(self, deg):
        return list(self.db.execute(f'SELECT base,diff,level FROM {self.prefix}ss WHERE s=? AND t=? ORDER BY level,id', deg))

    def boundaries(self, deg, r):
        return [vec(b) for b, d, level in self.rows(deg) if level < r]

    def residue(self, deg, x, r):
        return reduce(x, self.boundaries(deg, r))

    def info(self, deg, x, r=11):
        rows = self.rows(deg)
        coeff = solve([vec(b) for b, d, level in rows], x)
        assert coeff is not None, (self.name, deg, x)
        active = [rows[i] for i in indices(coeff)]
        differential = 0
        unknown = []
        earlier = []
        for base, diff, level in active:
            if level < 5000:
                continue
            first = 10000 - level
            if first < r:
                earlier.append([base, diff, level])
            elif first == r:
                if diff is None:
                    unknown.append(base)
                else:
                    differential ^= vec(diff)
        return {'residue_mod_recorded_prior_boundaries': indices(self.residue(deg, x, r)),
                'decomposition': active, 'earlier_outgoing_rows': earlier,
                'unknown_at_page': unknown, 'known_differential_part': indices(differential)}


class Map:
    def __init__(self, cfg):
        self.cfg = cfg
        self.A, self.B = algebra(cfg['from']), algebra(cfg['to'])
        self.fil, self.sus = cfg.get('fil', 0), cfg.get('sus', 0)
        self.db = connect(DATA / cfg['path'])
        tables = [r[0] for r in self.db.execute("SELECT name FROM sqlite_master WHERE type='table' AND name!='version'")]
        assert len(tables) == 1
        self.images = dict(self.db.execute(f'SELECT id,map FROM {tables[0]}'))
        self.meta = dict(self.db.execute('SELECT name,value FROM version'))
        assert self.meta.get('filtration', self.fil) == self.fil
        if 'over' in cfg:
            raise ValueError('semilinear map not implemented')

    def degree(self, deg):
        return deg[0] + self.fil, deg[1] + self.fil - self.sus

    def image(self, deg, x):
        assert deg[1] <= self.cfg['t_max']
        out = 0
        for i in indices(x):
            coef, module = mon(self.A.bydeg[deg][i][1])
            raw = self.images[module]
            if raw is None:
                raise ValueError('unknown generator image')
            for term in [''] if raw == ';' else raw.split(';') if raw else []:
                out ^= self.B.coords(self.degree(deg), multiply((coef, None), mon(term)))
        return out


def main():
    c, s = algebra('C2'), algebra('S0')
    report = {'scope': 'finite read-only probes relative to cw210 input; no automatic identification with actual homotopy',
              'source': {'degree': [1, 128], 'basis': c.bydeg[1, 128], 'rows': c.rows((1, 128))},
              'target': {'degree': [12, 138], 'basis': c.bydeg[12, 138], 'rows': c.rows((12, 138))},
              'incoming': [], 'outgoing_maps': [], 'incoming_maps': [], 'products': [], 'errors': []}
    for r in range(2, 12):
        deg = 12-r, 139-r
        report['incoming'].append({'r': r, 'degree': deg, 'basis': c.bydeg.get(deg, []), 'rows': c.rows(deg),
                                   'unknown_or_unsettled_at_r': [row for row in c.rows(deg) if 9000 < row[2] <= 10000 and row[2] >= 10000-r and row[1] is None]})
    for cfg in CONFIG['maps']:
        if cfg['from'] != 'C2' and cfg['to'] != 'C2':
            continue
        try:
            m = Map(cfg)
            if cfg['from'] == 'C2':
                ds, dt = m.degree((1, 128)), m.degree((12, 138))
                xs, xt = m.image((1, 128), 1), m.image((12, 138), 1)
                report['outgoing_maps'].append({'name': cfg['name'], 'filtration': m.fil, 'degrees': [ds, dt],
                    'source_E2_image': indices(xs), 'target_E2_image': indices(xt),
                    'source_info': m.B.info(ds, xs), 'target_info': m.B.info(dt, xt), 'config': cfg})
            if cfg['to'] == 'C2':
                ds = 1-m.fil, 128-m.fil+m.sus
                if ds[0] < 0 or ds[1] > cfg['t_max']:
                    continue
                n = len(m.A.bydeg.get(ds, []))
                cols = [m.image(ds, 1 << i) for i in range(n)]
                pre = solve(cols, 1)
                report['incoming_maps'].append({'name': cfg['name'], 'degree': ds, 'E2_dim': n,
                    'preimage': None if pre is None else indices(pre),
                    'preimage_info': None if pre is None else m.A.info(ds, pre), 'config': cfg})
        except Exception as error:
            report['errors'].append({'map': cfg, 'error': repr(error)})
    for gen in [0, 1, 2, 3, 8, 18]:
        row = s.db.execute('SELECT id,name,s,t FROM S0_AdamsE2_generators WHERE id=?', (gen,)).fetchone()
        ds, dt = (1+row[2], 128+row[3]), (12+row[2], 138+row[3])
        xs = c.coords(ds, multiply(mon(f'{gen},1'), mon('324,1,0')))
        xt = c.coords(dt, multiply(mon(f'{gen},1'), mon('368')))
        report['products'].append({'factor': row, 'degrees': [ds,dt], 'source_E2_product': indices(xs),
             'target_E2_product': indices(xt), 'source_info': c.info(ds,xs), 'target_info': c.info(dt,xt)})
    report['bottom_target_E2_columns'] = []
    for row in s.bydeg.get((12,138), []):
        out = c.coords((12,138), multiply(mon(row[1]), mon('0')))
        report['bottom_target_E2_columns'].append({'sphere_basis': row, 'image': indices(out),
                                                   'E4_residue': indices(c.residue((12,138),out,4))})
    report['high_targets'] = []
    for r in range(11, 63):
        deg = 1+r, 127+r
        rows = c.rows(deg)
        # An earlier unknown outgoing differential may be zero. Retain every
        # row not already a recorded boundary; this deliberately overestimates.
        remaining = [row for row in rows if r <= row[2]]
        if remaining:
            report['high_targets'].append({'r':r,'degree':deg,'remaining_rows':remaining,
                                           'interpretation':'E2 modulo recorded earlier boundaries; not an E_r dimension',
                                           'basis':c.bydeg.get(deg,[])})
    report['sha256'] = {str(path): hashlib.sha256(path.read_bytes()).hexdigest() for path in sorted(READ)}
    (ROOT / 'probe-results.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({'output': str(ROOT / 'probe-results.json'),
                      'outgoing_maps': len(report['outgoing_maps']),
                      'incoming_maps': len(report['incoming_maps']),
                      'errors': report['errors']}, indent=2))


if __name__ == '__main__':
    main()
