"""Lossless audit inputs and cache isolation for the canonical proof ledger."""
from collections import Counter
from contextlib import redirect_stderr
import copy
import importlib.util
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / 'scripts/project-proof-obligations.py'
SPEC = importlib.util.spec_from_file_location('audit_inputs', SCRIPT)
audit_inputs = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(audit_inputs)


def refresh_summary(ledger):
    rows = ledger['obligations']
    ledger['summary'] = {
        'total': len(rows),
        'by_module': dict(Counter(audit_inputs.module_owner(row['module']) for row in rows)),
        'by_kind': dict(Counter(row['status'] for row in rows)),
    }
    return ledger


def fixture():
    # Historical Computation names intentionally do not identify their owner.
    return refresh_summary({
        'schema_version': 2,
        'obligations': [
            {'name': 'KIP126.Computation.e2Pending',
             'module': 'KIP126.E2Computation.Standard',
             'type_fingerprint': '11', 'body_fingerprint': '12', 'status': 'pending-proof'},
            {'name': 'KIP126.Computation.adamsPending',
             'module': 'KIP126.AdamsCalculations.Standard',
             'type_fingerprint': '21', 'body_fingerprint': '22', 'status': 'pending-proof'},
            {'name': 'KIP126.Literature.pending', 'module': 'KIP126.Literature.Standard',
             'type_fingerprint': '31', 'body_fingerprint': '32', 'status': 'pending-construction'},
        ],
        audit_inputs.ROUTE_KEY: {
            'public_main_roots': ['KIP126.Main.established'],
            # The real ledger has such differently-namespaced ProofTools-owned helpers.
            'proofTools_boundary_declarations': ['KIP126.Synthetic.Context.boundary'],
        },
    })


def projections(ledger):
    return {module: audit_inputs.projection_bytes(ledger, module)
            for module in audit_inputs.MODULES}


class AuditInputTests(unittest.TestCase):
    def test_complete_rows_partition_by_source_and_preserve_extra_row_metadata(self):
        ledger = fixture()
        ledger['obligations'][0]['review_note'] = {'approved': True, 'detail': '完整保留'}
        shards = {module: audit_inputs.project_ledger(ledger, module)
                  for module in audit_inputs.MODULES}
        combined = [row for shard in shards.values() for row in shard['obligations']]
        self.assertEqual(sorted(combined, key=lambda row: row['name']),
                         sorted(ledger['obligations'], key=lambda row: row['name']))
        self.assertEqual(shards['E2Computation']['obligations'], [ledger['obligations'][0]])
        self.assertEqual(shards['AdamsCalculations']['obligations'], [ledger['obligations'][1]])
        for module, shard in shards.items():
            self.assertEqual(shard['audit_module'], module)
            self.assertNotIn('summary', shard)
            self.assertNotIn('source_hash', shard)

    def test_other_module_change_only_rewrites_its_own_shard(self):
        old = fixture()
        new = copy.deepcopy(old)
        new['obligations'][2]['body_fingerprint'] = '999'
        with tempfile.TemporaryDirectory() as directory:
            paths = {module: Path(directory) / (module + '.json')
                     for module in audit_inputs.MODULES}
            for module, path in paths.items():
                audit_inputs.write_if_changed(path, audit_inputs.projection_bytes(old, module))
                os.utime(path, ns=(1_500_000_000, 1_500_000_000))
            previous = {module: (path.read_bytes(), path.stat().st_mtime_ns)
                        for module, path in paths.items()}
            changed = [module for module, path in paths.items()
                       if audit_inputs.write_if_changed(path,
                                                        audit_inputs.projection_bytes(new, module))]
            self.assertEqual(changed, ['Literature'])
            for module, path in paths.items():
                if module != 'Literature':
                    self.assertEqual((path.read_bytes(), path.stat().st_mtime_ns), previous[module])
            self.assertEqual(paths['Literature'].read_bytes(),
                             audit_inputs.projection_bytes(new, 'Literature'))
            self.assertNotEqual(paths['Literature'].stat().st_mtime_ns,
                                previous['Literature'][1])

    def test_completing_a_hole_does_not_copy_global_summary_to_other_inputs(self):
        old = fixture()
        new = copy.deepcopy(old)
        new['obligations'].pop(2)
        refresh_summary(new)
        before, after = projections(old), projections(new)
        self.assertEqual([module for module in before if before[module] != after[module]],
                         ['Literature'])

    def test_main_roots_only_change_main_input(self):
        old = fixture()
        new = copy.deepcopy(old)
        new[audit_inputs.ROUTE_KEY]['public_main_roots'].append('KIP126.Main.other')
        before, after = projections(old), projections(new)
        self.assertEqual([module for module in before if before[module] != after[module]], ['Main'])

    def test_shared_boundary_changes_exactly_main_and_proof_tools(self):
        old = fixture()
        new = copy.deepcopy(old)
        new[audit_inputs.ROUTE_KEY]['proofTools_boundary_declarations'].append('KIP126.ProofTools.other')
        before, after = projections(old), projections(new)
        self.assertEqual({module for module in before if before[module] != after[module]},
                         {'Main', 'ProofTools'})
        self.assertNotIn('public_main_roots',
                         audit_inputs.project_ledger(old, 'ProofTools')[audit_inputs.ROUTE_KEY])
        self.assertNotIn(audit_inputs.ROUTE_KEY, audit_inputs.project_ledger(old, 'Literature'))

    def test_empty_boundary_lists_and_empty_ledger_are_valid(self):
        ledger = fixture()
        ledger['obligations'] = []
        ledger[audit_inputs.ROUTE_KEY] = {field: [] for field in audit_inputs.ROUTE_FIELDS}
        refresh_summary(ledger)
        audit_inputs.validate_ledger(ledger)
        self.assertTrue(all(not audit_inputs.project_ledger(ledger, module)['obligations']
                            for module in audit_inputs.MODULES))

    def test_main_and_geometry_permissions_are_not_silently_discarded(self):
        # The independent source/Lean audits must reject these permissions or holes;
        # projection must faithfully expose them rather than turn them into [].
        for module in ('Main', 'Geometry'):
            with self.subTest(module=module):
                ledger = fixture()
                row = {'name': 'KIP126.' + module + '.forbidden',
                       'module': 'KIP126.' + module + '.Example',
                       'type_fingerprint': '41', 'body_fingerprint': '42', 'status': 'pending-proof'}
                ledger['obligations'].append(row)
                refresh_summary(ledger)
                self.assertEqual(audit_inputs.project_ledger(ledger, module)['obligations'], [row])

    def test_spectral_permissions_cannot_bypass_its_independent_sorry_free_audit(self):
        ledger = fixture()
        ledger['obligations'].append({
            'name': 'KIP126.SpectralSequence.forbidden',
            'module': 'KIP126.SpectralSequence.Example',
            'type_fingerprint': '41', 'body_fingerprint': '42', 'status': 'pending-proof',
        })
        refresh_summary(ledger)
        with self.assertRaisesRegex(ValueError, 'SpectralSequence permits no'):
            audit_inputs.project_ledger(ledger, 'Geometry')

    def test_invalid_global_metadata_is_rejected_even_for_unrelated_projection(self):
        cases = []
        bad = fixture(); bad['future_unassigned_audit_boundary'] = []
        cases.append(('unknown top-level metadata', bad))
        bad = fixture(); bad['schema_version'] = True
        cases.append(('boolean schema', bad))
        bad = fixture(); bad['summary']['total'] += 1
        cases.append(('wrong global total', bad))
        bad = fixture(); bad['summary']['by_module']['Literature'] = 9
        cases.append(('wrong module count', bad))
        bad = fixture(); bad['summary']['by_kind']['pending-proof'] = True
        cases.append(('boolean kind count', bad))
        bad = fixture(); del bad[audit_inputs.ROUTE_KEY]['public_main_roots']
        cases.append(('missing boundary field', bad))
        bad = fixture(); bad[audit_inputs.ROUTE_KEY]['proofTools_boundary_declarations'] *= 2
        cases.append(('duplicate boundary', bad))
        bad = fixture(); bad[audit_inputs.ROUTE_KEY]['public_main_roots'] = 'not an array'
        cases.append(('wrong boundary type', bad))
        for description, ledger in cases:
            with self.subTest(description=description), self.assertRaises(ValueError):
                audit_inputs.project_ledger(ledger, 'Geometry')

    def test_invalid_rows_are_rejected_globally(self):
        changes = [
            {'module': 'KIP126.Computation.Legacy'},
            {'module': 'KIP126.Literature.'},
            {'module': 12},
            {'name': ''},
            {'name': ['wrong type']},
            {'type_fingerprint': 12},
            {'body_fingerprint': '-12'},
            {'status': 'completed'},
        ]
        for change in changes:
            with self.subTest(change=change), self.assertRaises(ValueError):
                ledger = fixture()
                ledger['obligations'][0].update(change)
                audit_inputs.project_ledger(ledger, 'Geometry')
        ledger = fixture(); del ledger['obligations'][0]['body_fingerprint']
        with self.assertRaisesRegex(ValueError, 'missing fields'):
            audit_inputs.validate_ledger(ledger)
        ledger = fixture(); ledger['obligations'].append(dict(ledger['obligations'][0]))
        with self.assertRaisesRegex(ValueError, 'Duplicate obligation'):
            audit_inputs.validate_ledger(ledger)

    def test_cli_rejects_invalid_input_without_replacing_previous_output(self):
        with tempfile.TemporaryDirectory() as directory:
            ledger_path = Path(directory) / 'ledger.json'
            output = Path(directory) / 'Literature.json'
            output.write_bytes(b'previous healthy output\n')
            os.utime(output, ns=(1_500_000_000, 1_500_000_000))
            before = output.read_bytes(), output.stat().st_mtime_ns
            bad = fixture(); bad['summary']['total'] += 1
            ledger_path.write_text(json.dumps(bad))
            result = subprocess.run([sys.executable, str(SCRIPT), '--ledger', str(ledger_path),
                                     '--module', 'Literature', '--output', str(output)],
                                    capture_output=True, text=True)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn('summary', result.stderr)
            self.assertEqual((output.read_bytes(), output.stat().st_mtime_ns), before)
            self.assertEqual(sorted(path.name for path in Path(directory).iterdir()),
                             ['Literature.json', 'ledger.json'])

    def test_cli_validates_every_field_and_cannot_overwrite_canonical_input(self):
        with tempfile.TemporaryDirectory() as directory:
            ledger_path = Path(directory) / 'ledger.json'
            ledger_path.write_text(json.dumps(fixture()))
            original = ledger_path.read_bytes()
            command = [sys.executable, str(SCRIPT), '--ledger', str(ledger_path)]
            checked = subprocess.run(command + ['--check'], capture_output=True, text=True)
            self.assertEqual(checked.returncode, 0, checked.stderr)
            overwritten = subprocess.run(command + ['--module', 'Literature',
                                                    '--output', str(ledger_path)],
                                         capture_output=True, text=True)
            self.assertNotEqual(overwritten.returncode, 0)
            self.assertEqual(ledger_path.read_bytes(), original)
            ledger_path.write_text('{"schema_version":2,"schema_version":2}')
            duplicate = subprocess.run(command + ['--check'], capture_output=True, text=True)
            self.assertNotEqual(duplicate.returncode, 0)
            self.assertIn('Duplicate JSON object key', duplicate.stderr)

    def test_projection_is_deterministic_and_does_not_mutate_input(self):
        ledger = fixture()
        original = copy.deepcopy(ledger)
        reordered = dict(reversed(list(ledger.items())))
        for module in audit_inputs.MODULES:
            self.assertEqual(audit_inputs.projection_bytes(ledger, module),
                             audit_inputs.projection_bytes(reordered, module))
        self.assertEqual(ledger, original)

    def test_custom_input_cannot_be_projected_over_the_default_canonical_ledger(self):
        with tempfile.TemporaryDirectory() as directory:
            custom = Path(directory) / 'custom.json'
            canonical = Path(directory) / 'canonical.json'
            custom.write_text(json.dumps(fixture()))
            canonical.write_bytes(b'reviewed canonical ledger\n')
            errors = io.StringIO()
            with patch.object(audit_inputs, 'DEFAULT_LEDGER', canonical), redirect_stderr(errors):
                with self.assertRaises(SystemExit) as rejected:
                    audit_inputs.main(['--ledger', str(custom), '--module', 'Literature',
                                       '--output', str(canonical)])
            self.assertNotEqual(rejected.exception.code, 0)
            self.assertIn('Refusing to replace the canonical ledger', errors.getvalue())
            self.assertEqual(canonical.read_bytes(), b'reviewed canonical ledger\n')


if __name__ == '__main__':
    unittest.main()
