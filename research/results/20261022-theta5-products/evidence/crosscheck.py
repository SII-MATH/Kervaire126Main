"""Compare only the sphere inputs used by the mixed-product proof."""
import csv
import hashlib
import importlib.util
import json
from pathlib import Path
import resource

resource.setrlimit(resource.RLIMIT_AS, (4 << 30, 4 << 30))
resource.setrlimit(resource.RLIMIT_CPU, (110, 110))
ROOT = Path(__file__).resolve().parent
helper = ROOT.parents[1] / 'theta6' / 'probe.py'
spec = importlib.util.spec_from_file_location('round1_probe', helper)
p = importlib.util.module_from_spec(spec)
spec.loader.exec_module(p)
CW49 = Path('/inspire/hdd/global_user/czxs25250150/ops/tmp/d3-x126-6-evidence/data/kervaire-49')
IWX = Path('/inspire/hdd/global_user/czxs25250150/Kervaire126/Source/IWX/data/Adams-classical-Einfty.csv')


def package(a, degree):
    rows = sorted(a.rows(degree), key=lambda row: (row[2], row[0], row[1] or ''))
    return {'degree': degree, 'basis': a.bydeg.get(degree, []), 'rows': rows}


def snapshot(a):
    return {
        'stem124': [package(a, (s, 124+s)) for s in range(14)],
        'stem93': [package(a, (s, 93+s)) for s in range(6, 11)],
        'stem63': [package(a, (s, 63+s)) for s in range(1, 5)],
        'gamma_times_theta4': [
            {'basis': row, 'value': sorted(a.normal(p.multiply(p.mon(row[1]), p.mon('7,2'))))}
            for row in a.bydeg.get((10, 103), [])],
        'h1_theta5_theta4': sorted(a.normal(p.mon('1,1,7,2,18,2'))),
        'theta5_a8': sorted(a.normal(p.mon('18,2,82,1'))),
        'generator_names': list(a.db.execute(
            'SELECT id,name,s,t FROM S0_AdamsE2_generators WHERE id IN (1,7,18,82,174,192,367)'))}


def main():
    old = p.Algebra('S0')
    p.DATA = CW49
    new = p.Algebra('S0')
    before, after = snapshot(old), snapshot(new)
    comparisons = {key: before[key] == after[key] for key in before}
    per_degree = {str(a['degree']): a == b for a, b in zip(before['stem124'], after['stem124'])}
    with IWX.open(newline='') as handle:
        low_rows = [row for row in csv.DictReader(handle)
                    if (int(row['stem']) == 93 and 6 <= int(row['Adams filtration']) <= 10)
                    or (int(row['stem']) == 63 and 1 <= int(row['Adams filtration']) <= 4)]
    result = {'cw210': before, 'cw49': after, 'identical_fields': comparisons,
              'stem124_identical_degrees': per_degree, 'IWX_low_Einfty': low_rows,
              'sha256': {str(path): hashlib.sha256(path.read_bytes()).hexdigest()
                         for path in sorted(p.READ | {helper, IWX})}}
    (ROOT / 'crosscheck-result.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'identical_fields': comparisons, 'stem124_identical_degrees': per_degree,
                      'IWX_low_Einfty': low_rows}, indent=2))


if __name__ == '__main__':
    main()
