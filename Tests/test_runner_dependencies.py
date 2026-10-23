"""A successful dependency cache can be reused until imports or artifacts change."""
import importlib.util
import json
import subprocess
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('runner_mathlib', ROOT / '.github/runner/ensure-mathlib.py')
cache = importlib.util.module_from_spec(spec)
spec.loader.exec_module(cache)


class DependencyTests(unittest.TestCase):
    def test_source_digests_include_uncommitted_changes_additions_and_deletions(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            subprocess.run(['git', 'init', '-q', str(root)], check=True)
            (root / 'KIP126.lean').write_text('import Mathlib.A')
            subprocess.run(['git', 'add', '.'], cwd=root, check=True)
            first = cache.source_digests(root)
            (root / 'KIP126.lean').write_text('import Mathlib.B')
            self.assertNotEqual(cache.source_digests(root), first)
            (root / 'Checks').mkdir()
            (root / 'Checks/Extra.lean').write_text('import Mathlib.C')
            self.assertIn('Checks/Extra.lean', cache.source_digests(root))
            (root / 'KIP126.lean').unlink()
            self.assertNotIn('KIP126.lean', cache.source_digests(root))

    def test_repeat_skips_network_but_new_import_and_deleted_artifact_refetch(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            (root / 'lean-toolchain').write_text('fixed')
            (root / 'lake-manifest.json').write_text('{}')
            directory = root / '.lake/packages/mathlib/.lake/build/lib/lean/Mathlib'
            directory.mkdir(parents=True)
            calls = []
            def fetch(args, **kwargs):
                calls.append(args)
                for module in args[4:]:
                    p = directory.parent / (module.replace('.', '/') + '.olean')
                    p.parent.mkdir(parents=True, exist_ok=True)
                    p.write_text('cached')
            with patch.object(cache, 'import_roots', return_value=['Mathlib.A']):
                cache.ensure(root, fetch)
                cache.ensure(root, fetch)
                self.assertEqual(len(calls), 1)
                (directory / 'A.olean').unlink()
                cache.ensure(root, fetch)
                self.assertEqual(len(calls), 2)
            with patch.object(cache, 'import_roots', return_value=['Mathlib.A', 'Mathlib.B']):
                cache.ensure(root, fetch)
                self.assertEqual(len(calls), 3)
                cache.ensure(root, fetch)
                self.assertEqual(len(calls), 3)

    def test_failed_fetch_does_not_record_success(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            (root / 'lean-toolchain').write_text('fixed')
            (root / 'lake-manifest.json').write_text('{}')
            (root / '.lake/packages').mkdir(parents=True)
            with patch.object(cache, 'import_roots', return_value=['Mathlib.Missing']):
                with self.assertRaises(ValueError):
                    cache.ensure(root, lambda *args, **kwargs: None)
            self.assertEqual(list((root / '.lake/packages').glob('.runner-mathlib-*')), [])

    def test_warm_artifact_check_uses_recorded_paths_without_package_walk(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            (root / 'lean-toolchain').write_text('fixed')
            (root / 'lake-manifest.json').write_text('{}')
            artifact = root / '.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/A.olean'
            artifact.parent.mkdir(parents=True)
            def fetch(*args, **kwargs):
                artifact.write_text('cached')
            with patch.object(cache, 'import_roots', return_value=['Mathlib.A']):
                cache.ensure(root, fetch)
                with patch.object(cache.Path, 'iterdir', side_effect=AssertionError('unexpected package walk')):
                    cache.ensure(root, lambda *args, **kwargs: self.fail('unexpected fetch'))


class ImportHeaderTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        (self.root / 'lean-toolchain').write_text('fixed')
        (self.root / 'lake-manifest.json').write_text('{}')
        (self.root / '.lake/packages').mkdir(parents=True)
        self.sources = {'KIP126.lean': 'a', 'KIP126/Local.lean': 'b'}
        self.imports = {'KIP126.lean': ['KIP126.Local', 'Mathlib.A', 'Lean'],
                        'KIP126/Local.lean': ['Mathlib.B']}
        self.parses = []
        def native(args, **kwargs):
            self.assertEqual(args[:4], ['lake', 'env', 'lean', '--deps-json'])
            self.parses.append(args[4:])
            return json.dumps({'imports': [{'errors': [], 'result': {
                'imports': [{'module': m} for m in self.imports[name]]}} for name in args[4:]]})
        self.addCleanup(patch.stopall)
        patch.object(cache, 'source_digests', side_effect=lambda root: dict(self.sources)).start()
        patch.object(cache.subprocess, 'check_output', side_effect=native).start()

    def test_unchanged_headers_skip_lean_and_changed_files_parse_individually(self):
        self.assertEqual(cache.import_roots(self.root), ['Mathlib.A', 'Mathlib.B'])
        self.assertEqual(cache.import_roots(self.root), ['Mathlib.A', 'Mathlib.B'])
        self.assertEqual(len(self.parses), 1)
        self.sources['KIP126/Local.lean'] = 'proof changed, imports unchanged'
        self.assertEqual(cache.import_roots(self.root), ['Mathlib.A', 'Mathlib.B'])
        self.assertEqual(self.parses[-1], ['KIP126/Local.lean'])
        self.sources['KIP126/Local.lean'] = 'new external import'
        self.imports['KIP126/Local.lean'].append('Mathlib.C')
        self.assertIn('Mathlib.C', cache.import_roots(self.root))
        self.assertEqual(self.parses[-1], ['KIP126/Local.lean'])

    def test_added_deleted_sources_and_lock_changes_invalidate_correctly(self):
        cache.import_roots(self.root)
        self.sources['Checks/New.lean'] = 'new file'
        self.imports['Checks/New.lean'] = ['Mathlib.C']
        self.assertIn('Mathlib.C', cache.import_roots(self.root))
        self.assertEqual(self.parses[-1], ['Checks/New.lean'])
        del self.sources['KIP126/Local.lean']
        modules = cache.import_roots(self.root)
        self.assertIn('KIP126.Local', modules)
        self.assertNotIn('Mathlib.B', modules)
        (self.root / 'lake-manifest.json').write_text('{"new":"lock"}')
        cache.import_roots(self.root)
        self.assertEqual(set(self.parses[-1]), set(self.sources))

    def test_parse_failure_is_not_cached(self):
        with patch.object(cache.subprocess, 'check_output', return_value=json.dumps({
                'imports': [{'errors': ['bad import'], 'result': None}, {'errors': [], 'result': None}]})):
            with self.assertRaisesRegex(ValueError, 'Cannot parse'):
                cache.import_roots(self.root)
        self.assertEqual(list((self.root / '.lake/packages').glob('.runner-import-headers-*')), [])
        cache.import_roots(self.root)
        self.assertEqual(len(self.parses), 1)
