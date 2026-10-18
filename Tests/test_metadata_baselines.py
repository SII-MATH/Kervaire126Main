"""Check that compact baselines retain their review boundaries."""
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location('freezer', ROOT / 'scripts/freeze-interfaces.py')
freezer = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(freezer)


def fixture():
    permitted = {
        'name': 'KIP126.Literature.pending', 'module': 'KIP126.Literature.Example',
        'type_fingerprint': '123', 'body_fingerprint': '456', 'status': 'pending-proof',
        'full_type': 'historical rendering', 'reason': 'historical review',
    }
    previous = {
        'obligations': [permitted],
        freezer.ROUTE_KEY: {'public_main_roots': ['KIP126.Main.root'],
                           'proofTools_boundary_declarations': ['KIP126.ProofTools.done']},
    }
    actual = {**permitted, 'is_axiom': False, 'synthetic_sorry': False,
              'direct_sorry': True, 'axioms': ['sorryAx']}
    return previous, actual


class MinimalBaselineTests(unittest.TestCase):
    def test_compaction_preserves_type_universes_trust_and_export_partition(self):
        item = {'name': 'KIP126.Main.result', 'type_fingerprint': '999',
                'universes': ['u'], 'axioms': ['Classical.choice'],
                'full_type': 'large generated rendering', 'type_dependencies': ['helper']}
        data = {'module': 'Main', 'entry_module': 'KIP126.Main',
                'declarations': [item], 'generated_declarations': [],
                'exports': [item['name']]}
        result = freezer.minimal_api(data)
        self.assertEqual(result['exports'], data['exports'])
        self.assertEqual(result['declarations'],
                         [{key: item[key] for key in freezer.API_FIELDS}])
        with self.assertRaisesRegex(ValueError, 'export partition'):
            freezer.minimal_api({**data, 'exports': []})
        with self.assertRaisesRegex(ValueError, 'export partition'):
            freezer.minimal_api({**data, 'generated_declarations': [item]})

    def test_new_holes_and_missing_declarations_are_rejected(self):
        previous, actual = fixture()
        with self.assertRaisesRegex(ValueError, 'New obligation'):
            freezer.reviewed_obligations(
                [actual, {**actual, 'name': 'KIP126.Literature.newHole'}], previous)
        with self.assertRaisesRegex(ValueError, 'disappeared'):
            freezer.reviewed_obligations([], previous)

    def test_changed_registered_objects_are_rejected(self):
        previous, actual = fixture()
        for field in ('module', 'type_fingerprint', 'body_fingerprint'):
            with self.subTest(field=field), self.assertRaisesRegex(ValueError, 'changed'):
                freezer.reviewed_obligations([{**actual, field: 'different'}], previous)

    def test_axioms_and_elaboration_error_placeholders_are_rejected(self):
        previous, actual = fixture()
        for change in ({'is_axiom': True}, {'synthetic_sorry': True},
                       {'axioms': ['unexpectedAxiom']}):
            with self.subTest(change=change), self.assertRaises(ValueError):
                freezer.reviewed_obligations([{**actual, **change}], previous)

    def test_completion_removes_only_the_completed_permission(self):
        previous, actual = fixture()
        result = freezer.reviewed_obligations(
            [{**actual, 'direct_sorry': False, 'body_fingerprint': 'newProof', 'axioms': []}],
            previous)
        self.assertEqual(result['obligations'], [])
        self.assertEqual(result[freezer.ROUTE_KEY], previous[freezer.ROUTE_KEY])
        with self.assertRaisesRegex(ValueError, 'type_fingerprint'):
            freezer.reviewed_obligations(
                [{**actual, 'direct_sorry': False, 'type_fingerprint': 'weakerStatement',
                  'body_fingerprint': 'trivialProof', 'axioms': []}], previous)

    def test_compact_output_round_trips_all_permitted_values(self):
        previous, actual = fixture()
        result = freezer.reviewed_obligations([actual], previous)
        self.assertEqual(result['obligations'],
                         [{key: actual[key] for key in freezer.HOLE_FIELDS}])
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'baseline.json'
            freezer.write_baseline(path, result)
            self.assertEqual(json.loads(path.read_text()), result)

    def test_update_command_requires_no_contract_source_or_history_files(self):
        previous, actual = fixture()
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'metadata').mkdir()
            (root / '.lake').mkdir()
            source = root / 'KIP126/Main/Example.lean'
            source.parent.mkdir(parents=True)
            source.write_text('module\nnamespace KIP126.Main\n'
                              'public theorem result : True := trivial\nend KIP126.Main\n')
            item = {'name': 'KIP126.Main.result', 'module': 'KIP126.Main.Example',
                    'type_fingerprint': '999', 'universes': []}
            (root / 'metadata/proof-obligations.json').write_text(json.dumps(previous))
            (root / '.lake/main-capture.json').write_text(json.dumps([item]))
            (root / '.lake/trust-capture.json').write_text(json.dumps([
                actual, {**item, 'axioms': [], 'is_axiom': False,
                         'synthetic_sorry': False, 'direct_sorry': False}]))
            subprocess.run([sys.executable, str(ROOT / 'scripts/freeze-interfaces.py'), 'main'],
                           cwd=root, check=True, capture_output=True, text=True)
            result = json.loads((root / 'metadata/main-api.json').read_text())
            self.assertEqual(result['declarations'][0]['name'], item['name'])
            self.assertEqual(result['exports'], [item['name']])


if __name__ == '__main__':
    unittest.main()
