"""A successful dependency cache can be reused until imports or artifacts change."""
import importlib.util
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('runner_mathlib', ROOT / '.github/runner/ensure-mathlib.py')
cache = importlib.util.module_from_spec(spec)
spec.loader.exec_module(cache)


class DependencyTests(unittest.TestCase):
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
            with patch.object(cache.subprocess, 'check_output', return_value='Mathlib.A\n'):
                cache.ensure(root, fetch)
                cache.ensure(root, fetch)
                self.assertEqual(len(calls), 1)
                (directory / 'A.olean').unlink()
                cache.ensure(root, fetch)
                self.assertEqual(len(calls), 2)
            with patch.object(cache.subprocess, 'check_output', return_value='Mathlib.A\nMathlib.B\n'):
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
            with patch.object(cache.subprocess, 'check_output', return_value='Mathlib.Missing\n'):
                with self.assertRaises(ValueError):
                    cache.ensure(root, lambda *args, **kwargs: None)
            self.assertEqual(list((root / '.lake/packages').glob('.runner-mathlib-*')), [])
