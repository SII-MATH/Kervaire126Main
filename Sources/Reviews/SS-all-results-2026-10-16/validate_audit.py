"""Check consistency of independent audit outputs, without claiming theorem certification."""
import collections
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
def read(name):
    return json.loads((ROOT / name).read_text())

py = {r['id']: r for r in read('E2-branch-classification.json')['rows']}
cpp = {r['id']: r for r in read('native-E2-classification.json')['rows']}
assert len(py) == len(cpp) == 3736
assert py.keys() == cpp.keys()
for ident in py:
    for field in ('target_degree', 'E2_image', 'branch'):
        assert py[ident][field] == cpp[ident][field], (ident, field)
assert collections.Counter(r['branch'] for r in cpp.values()) == {'M0': 3430, 'M1': 306}
assert read('native-E2-crosscheck.json')['mismatches'] == []
composition = read('native-E2-cofiber-composition.json')['rows']
assert len(composition) == 306
assert all(r['E2_image'] == [] for r in composition)
gl = read('native-GL-E2-classification.json')
assert len(gl['rows']) == 998 and gl['summary']['failed'] == 0
pairs = read('logs-GL-branch-summary.json')['summary']['pair_counts']
assert sum(pairs.values()) == 499
assert not any('D-candidate' in name and name.count('D-candidate') == 2 for name in pairs)
rows = read('logs-full-synthetic-rows.json')
assert collections.Counter(r['reason'] for r in rows) == {'Syn': 573, 'SynCs': 3736, 'SynCsIn': 306}
assert read('full-inputs-verified.json')['database_count'] == 362
assert read('full-inputs-verified.json')['all_sqlite_quick_check_ok']
result = {'independent_E2_rows_equal': 3736, 'E2_mismatches': 0,
          'M0': 3430, 'M1': 306, 'next_map_composites_zero': 306,
          'additional_GL_map_evaluations': 998, 'GL_parent_hint_records': 499,
          'Syn': 573, 'SynCs': 3736, 'SynCsIn': 306,
          'verified_input_databases': 362,
          'scope': 'Consistency and static E2 checks only; no full historical dependency or theorem certification.'}
(ROOT / 'validation.json').write_text(json.dumps(result, ensure_ascii=False, indent=2))
print(json.dumps(result, ensure_ascii=False))
