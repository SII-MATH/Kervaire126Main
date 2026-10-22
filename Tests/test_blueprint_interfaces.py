"""Baseline provenance and read-only native interface presentation."""
import json
import re
from pathlib import Path
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
import blueprint_interfaces as interfaces
from blueprint_boundaries import MODULES


class InterfacePageTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data = interfaces.read_interfaces(ROOT)

    def test_complete_exports_preserve_baseline_fields_and_actual_owner(self):
        self.assertEqual([m['name'] for m in self.data['modules']], list(MODULES))
        for path in (ROOT / 'interface/baselines').glob('*-api.json'):
            lock = json.loads(path.read_text())
            records = [r for r in self.data['records']
                       if r['owner'] == lock['module'] and r['kind'] != 'obligation']
            self.assertEqual(sorted(r['name'] for r in records), sorted(lock['exports']))
            by_name = {r['name']: r for r in records}
            for kind in ('declarations', 'generated_declarations'):
                for row in lock[kind]:
                    for key, value in row.items():
                        self.assertEqual(by_name[row['name']][key], value)
        # The namespace is historical; the source module determines ownership.
        self.assertTrue(any(r['owner'] == 'E2Computation' and r['name'].startswith('KIP126.Computation.')
                            for r in self.data['records']))

    def test_registry_private_responsibilities_and_audit_boundaries_are_retained(self):
        registry = json.loads((ROOT / 'interface/baselines/proof-obligations.json').read_text())
        records = [r for r in self.data['records'] if r['kind'] == 'obligation']
        self.assertEqual(len(records), len(registry['obligations']))
        for row, original in zip(records, registry['obligations']):
            self.assertEqual(row['obligation'], original)
            for key, value in original.items():
                self.assertEqual(row[key], value)
        for key, value in registry.items():
            if key not in ('schema_version', 'summary', 'obligations'):
                self.assertEqual(self.data['audit_boundaries'][key], value)
        self.assertEqual(self.data['naming'], json.loads(
            (ROOT / 'interface/baselines/mathematical-naming-restoration.json').read_text()))

    def test_deploy_uses_the_same_immutable_hgraph_version_as_local_installation(self):
        import yaml
        requirement = (ROOT / 'requirements-blueprint.txt').read_text()
        match = re.search(r'hgraph.git@([0-9a-f]{40})', requirement)
        self.assertIsNotNone(match)
        workflow = yaml.safe_load((ROOT / '.github/workflows/pages.yml').read_text())
        steps = workflow['jobs']['export']['steps']
        self.assertEqual(workflow['jobs']['export']['runs-on'], 'kip126-blueprint')
        self.assertTrue(any('.github/runner/check-blueprint-env.py' in step.get('run', '') and
                            'GITHUB_PATH' in step.get('run', '')
                            for step in steps))
        import importlib.util
        spec = importlib.util.spec_from_file_location('blueprint_env', ROOT / '.github/runner/check-blueprint-env.py')
        environment = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(environment)
        self.assertEqual(environment.PIN, match[1])
        self.assertFalse(any('apt-get' in step.get('run', '') or 'pip install' in step.get('run', '')
                             for step in steps))

    def test_layout_has_one_canonical_source(self):
        self.assertTrue((ROOT / 'interface/baselines').is_dir())
        self.assertTrue((ROOT / 'interface/proposals/TEMPLATE.md').is_file())
        self.assertFalse((ROOT / 'metadata').exists())
        self.assertFalse((ROOT / 'interface-proposals').exists())
        self.assertEqual(len(list((ROOT / 'interface/baselines').glob('*.json'))), 10)

    def test_single_native_tab_contains_both_sections(self):
        import yaml
        config = yaml.safe_load((ROOT / 'hgraph/config.yaml').read_text())
        tabs = config['site']['tabs']
        self.assertEqual(sum(t['id'] == 'interfaces' for t in tabs), 1)
        self.assertFalse(any(t['id'] == 'proposals' for t in tabs))

    def test_source_statements_include_context_and_correct_source_line(self):
        row = next(r for r in self.data['records'] if r['name'] == 'KIP126.Main.h6_sq_permanent')
        source = row['source']
        self.assertIn('NonzeroSurvival', source['statement'])
        self.assertIn('namespace KIP126.Main', source['context'])
        self.assertIn('public theorem h6_sq_permanent',
                      (ROOT / source['file']).read_text().splitlines()[source['line'] - 1])
        self.assertTrue(source['href'].endswith('#L' + str(source['line'])))
        self.assertTrue(any(r['source_is_parent'] for r in self.data['records']))

    def test_native_source_flags_distinguish_direct_and_dependency_gaps(self):
        for name in ('KIP126.Main.h6_sq_permanent',):
            row = next(r for r in self.data['records'] if r['name'] == name)
            self.assertEqual(row['source']['kind'], 'theorem')
            self.assertFalse(row['source']['sorry'])
            self.assertIn('sorryAx', row['axioms'])
            self.assertIsNone(row['obligation'])

    def test_export_downloads_are_exact_and_mathematical_payload_is_unchanged(self):
        originals = {p: p.read_bytes() for p in (ROOT / 'interface/baselines').glob('*.json')}
        with tempfile.TemporaryDirectory() as folder:
            out = Path(folder)
            (out / 'Kervaire126').mkdir()
            payload = b'{"entries":[{"lean_status":"sorry"}]}'
            (out / 'Kervaire126/data.json').write_bytes(payload)
            result = interfaces.export_interfaces(ROOT, out)
            self.assertEqual(result['modules'], 8)
            self.assertEqual((out / 'Kervaire126/data.json').read_bytes(), payload)
            data = json.loads((out / 'interfaces/data.json').read_text())
            self.assertEqual(len(data['downloads']), 10)
            self.assertIn('aria-current="page">Baselines', (out / 'interfaces/baselines.html').read_text())
            self.assertTrue((out / 'interfaces/docs/corrections.md').is_file())
            for relative in data['downloads']:
                self.assertEqual((out / 'interfaces' / relative).read_bytes(), (ROOT / relative).read_bytes())
            interfaces.stage_interfaces(ROOT, out / 'workspace')
            self.assertIn('src="interfaces/index.html"',
                          (out / 'workspace/site/interfaces.html').read_text())
        for path, content in originals.items():
            self.assertEqual(path.read_bytes(), content)


if __name__ == '__main__':
    unittest.main()
