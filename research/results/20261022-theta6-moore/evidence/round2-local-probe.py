"""Focused read-only certificates for the two early C2 incoming sources."""
import json
from pathlib import Path
import sys

OUT = Path(__file__).resolve().parent
LATEST = Path('/inspire/hdd/global_user/czxs25250150/ops/tmp/d3-x126-6-evidence/data/kervaire-49')
sys.path.insert(0, str(OUT.parents[1] / 'theta6'))
import probe as p


def package(a, deg):
    return {'degree': deg, 'basis': a.bydeg.get(deg, []), 'rows': a.rows(deg)}


def product(a, deg, vector, factor, factor_deg):
    target = tuple(x+y for x, y in zip(deg, factor_deg))
    value = 0
    for i in p.indices(vector):
        value ^= a.coords(target, p.multiply(p.mon(a.bydeg[deg][i][1]), p.mon(factor)))
    return {'degree': target, 'coords': p.indices(value),
            'info_E5': a.info(target, value, 5),
            'info_E6': a.info(target, value, 6)}


def h0_preimages(a, deg, value):
    source = deg[0]-1, deg[1]-1
    columns = [a.coords(deg, p.multiply(p.mon(row[1]), p.mon('0,1')))
               for row in a.bydeg.get(source, [])]
    witness = p.solve(columns, value)
    return {'source': package(a, source), 'columns': list(map(p.indices, columns)),
            'witness': None if witness is None else p.indices(witness)}


def main():
    s, c = p.algebra('S0'), p.algebra('C2')
    q = p.Map(next(cfg for cfg in p.CONFIG['maps'] if cfg['name'] == 'C2__S0'))
    sphere_target = (11, 137)
    c2_target = (11, 137)
    T = (1 << 1) ^ (1 << 2)
    iT = 0
    for i in p.indices(T):
        iT ^= c.coords(c2_target, p.multiply(p.mon(s.bydeg[sphere_target][i][1]), p.mon('0')))
    assert p.indices(iT) == [3, 4]
    assert p.indices(c.residue(c2_target, iT, 5)) == [3, 4]
    # Every possible d4 source has its first outgoing differential at d5 or later.
    assert all(level >= 5000 and 10000-level >= 5
               for _, _, level in c.rows((7, 134)))
    bottom_target = [c.coords((12, 138), p.multiply(p.mon(row[1]), p.mon('0')))
                     for row in s.bydeg[(12, 138)]]
    assert all(c.residue((12, 138), value, 4) == 0 for value in bottom_target)
    early_sources = [(11-r, 138-r) for r in [2, 3, 4]]
    result = {
        'source': 'cw210 immutable originals; inherited algebra normalizer from Round1',
        'sphere_source': package(s, (6, 133)),
        'sphere_d5_target': package(s, sphere_target),
        'C2_d5_target': package(c, c2_target),
        'T_bottom_image': p.indices(iT),
        'C2_d5_target_prior_sources': [package(c, deg) for deg in early_sources],
        'C2_source': package(c, (6, 133)),
        'C2_possible_d5_source': package(c, (7, 134)),
        'C2_possible_d5_source_prior_sources': [package(c, deg) for deg in [(5, 133), (4, 132), (3, 131)]],
        'sphere_d6_target': package(s, (12, 138)),
        'sphere_d6_target_bottom_columns': list(map(p.indices, bottom_target)),
        'C2_d6_target': package(c, (12, 138)),
        'sphere_x1268_d3_target': package(s, (11, 136)),
        'h0_preimage_of_x1268_d3_target': h0_preimages(s, (11, 136), 1 << 1),
        'sphere_sum_d3_target': package(s, (10, 136)),
        'h0_preimage_of_sphere_sum_d3_target': h0_preimages(s, (10, 136), 1 << 2),
        'low_products_T': {str(g): product(s, sphere_target, T, f'{g},1', deg)
                           for g, deg in [(0, (1, 1)), (1, (1, 2)), (2, (1, 4)), (3, (1, 8)), (8, (4, 18))]},
        'low_products_w': {str(g): product(s, (6, 133), 1, f'{g},1', deg)
                           for g, deg in [(0, (1, 1)), (1, (1, 2)), (2, (1, 4)), (3, (1, 8)), (8, (4, 18))]},
        'low_products_z': {str(g): product(c, (12, 138), 1, f'{g},1', deg)
                           for g, deg in [(0, (1, 1)), (1, (1, 2)), (2, (1, 4)), (3, (1, 8)), (8, (4, 18))]},
        'low_products_a': {str(g): product(c, (7, 134), 1 << 1, f'{g},1', deg)
                           for g, deg in [(0, (1, 1)), (1, (1, 2)), (2, (1, 4)), (3, (1, 8)), (8, (4, 18))]},
    }
    b_degree, h0b_degree = (8, 134), (9, 135)
    h0_columns = [s.coords(h0b_degree, p.multiply(p.mon(row[1]), p.mon('0,1')))
                  for row in s.bydeg[b_degree]]
    h0b = h0_columns[3]
    corrected = []
    for candidate in range(1 << len(h0_columns)):
        value = 0
        for j in p.indices(candidate):
            value ^= h0_columns[j]
        info = s.info(b_degree, candidate, 6)
        if value == h0b and not info['earlier_outgoing_rows']:
            corrected.append({'coords': p.indices(candidate), 'E6_info': info})
    cof = p.connect(p.DATA / 'cofseq_S0__C2__S0.db')
    result['Moore_secondary_data'] = {
        'sphere_a_degree': package(s, (7, 134)),
        'sphere_b_degree': package(s, b_degree),
        'h0_b_columns': list(map(p.indices, h0_columns)),
        'h0b_coords': p.indices(h0b),
        'E6_cycles_with_same_E2_h0_product_as_b': corrected,
        'q_columns': {str(deg): {'source': package(c, deg), 'target_degree': q.degree(deg),
                                'images': [p.indices(q.image(deg, 1 << j)) for j in range(len(c.bydeg.get(deg, [])))]}
                      for deg in [(7, 134), (8, 135), (11, 137), (12, 138)]},
        'cofseq_rows_near_b': list(cof.execute('SELECT * FROM cofseq_S0__C2__S0 WHERE t-s=126 AND s BETWEEN 7 AND 14 ORDER BY iC,s,t,level')),
    }
    result['cw49_comparison'] = {}
    for name, old, filename, degrees in [
        ('S0', s, 'S0_AdamsSS_t261.db', [(6, 132), (6, 133), (7, 134), (8, 134), (10, 136), (11, 136), (11, 137), (12, 138)]),
        ('C2', c, 'C2_AdamsSS_t200.db', [(1, 128), (5, 133), (4, 132), (3, 131), (6, 133), (7, 134), (8, 134), (9, 135), (10, 136), (11, 137), (12, 138)]),
    ]:
        latest = p.connect(LATEST / filename)
        comparison = {}
        for deg in degrees:
            basis = list(latest.execute(f'SELECT id,mon,s,t FROM {name}_AdamsE2_basis WHERE s=? AND t=? ORDER BY id', deg))
            rows = list(latest.execute(f'SELECT base,diff,level FROM {name}_AdamsE2_ss WHERE s=? AND t=? ORDER BY level,id', deg))
            comparison[str(deg)] = {'basis': basis, 'rows': rows,
                                     'rows_with_ids': list(latest.execute(f'SELECT * FROM {name}_AdamsE2_ss WHERE s=? AND t=? ORDER BY id', deg)),
                                     'cw210_rows_with_ids': list(old.db.execute(f'SELECT * FROM {name}_AdamsE2_ss WHERE s=? AND t=? ORDER BY id', deg)),
                                     'basis_matches_cw210': basis == old.bydeg.get(deg, []),
                                     'staircase_matches_cw210_up_to_row_order': sorted(rows, key=repr) == sorted(old.rows(deg), key=repr)}
        result['cw49_comparison'][name] = {'path': str(LATEST / filename), 'degrees': comparison}
    (OUT / 'local-results.json').write_text(json.dumps(result, indent=2) + '\n')
    print('Verified i(T)=[3,4] and nonzero modulo prior recorded boundaries; source d4 rows all zero.')


if __name__ == '__main__':
    main()
