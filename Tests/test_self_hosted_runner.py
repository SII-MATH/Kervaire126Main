"""Host admission must reject foreign code; cache switches must preserve isolation."""
import importlib.util
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]


def load(name, filename):
    spec = importlib.util.spec_from_file_location(name, ROOT / '.github/runner' / filename)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


policy = load('runner_policy', 'job-start.py')
cache = load('runner_cache', 'prepare-cache.py')
blueprint_policy = load('blueprint_policy', 'blueprint-job-start.py')


class AdmissionTests(unittest.TestCase):
    def test_blueprint_slot_only_accepts_main_export(self):
        env = {'GITHUB_REPOSITORY': policy.REPOSITORY,
               'GITHUB_WORKFLOW_REF': policy.REPOSITORY + '/.github/workflows/pages.yml@refs/heads/main',
               'GITHUB_EVENT_NAME': 'push', 'GITHUB_REF': 'refs/heads/main'}
        self.assertTrue(blueprint_policy.allowed(env, {'ref': 'refs/heads/main'}))
        for key, value in [('GITHUB_REF', 'refs/heads/develop'),
                           ('GITHUB_EVENT_NAME', 'pull_request'),
                           ('GITHUB_REPOSITORY', 'foreign/repo'),
                           ('GITHUB_WORKFLOW_REF', policy.REPOSITORY + '/.github/workflows/ci.yml@refs/heads/main')]:
            self.assertFalse(blueprint_policy.allowed({**env, key: value}, {'ref': 'refs/heads/main'}))
        self.assertTrue(blueprint_policy.allowed({**env, 'GITHUB_EVENT_NAME': 'workflow_dispatch'}, {}))

    def env(self, event):
        return {'GITHUB_REPOSITORY': policy.REPOSITORY, 'GITHUB_EVENT_NAME': event,
                'GITHUB_WORKFLOW_REF': policy.REPOSITORY + '/.github/workflows/ci.yml@refs/pull/1/merge'}

    def test_same_repository_pr_and_queue(self):
        self.assertTrue(policy.allowed(self.env('pull_request'), {
            'pull_request': {'head': {'repo': {'full_name': policy.REPOSITORY}}}}))
        self.assertTrue(policy.allowed(self.env('merge_group'), {
            'merge_group': {'base_ref': 'refs/heads/main'}}))

    def test_fork_missing_payload_other_workflow_and_target_event_rejected(self):
        for event in ({}, {'pull_request': {'head': {'repo': {'full_name': 'fork/repo'}}}}):
            self.assertFalse(policy.allowed(self.env('pull_request'), event))
        env = self.env('workflow_dispatch')
        env['GITHUB_WORKFLOW_REF'] = policy.REPOSITORY + '/.github/workflows/other.yml@refs/heads/main'
        self.assertFalse(policy.allowed(env, {}))
        self.assertFalse(policy.allowed(self.env('pull_request_target'), {}))
        self.assertFalse(policy.allowed(self.env('merge_group'), {'merge_group': {'base_ref': 'refs/heads/other'}}))


class PersistentCacheTests(unittest.TestCase):
    def make(self, root):
        root.mkdir(parents=True, exist_ok=True)
        (root / 'lean-toolchain').write_text('pinned')
        (root / 'lake-manifest.json').write_text('{}')

    def test_workflow_keeps_release_bootstrap_and_full_build_without_copy_step(self):
        workflow = (ROOT / '.github/workflows/ci.yml').read_text()
        ordered = ['Prepare isolated persistent cache', 'Reuse a verified Release build across branches',
                   'Fetch only imported Mathlib dependencies', 'Build all modules and checks']
        self.assertEqual([workflow.index(name) for name in ordered],
                         sorted(workflow.index(name) for name in ordered))
        self.assertNotIn('--seed-baseline', workflow)
        self.assertIn("steps.local_cache.outputs.restore_release == 'true'", workflow)

    def test_source_changes_keep_one_build_directory_and_partial_progress(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary) / 'checkout'; self.make(root)
            archives = Path(temporary) / 'cache'
            first = cache.prepare(root, archives)
            (root / '.lake/build').mkdir()
            result = root / '.lake/build/result'; result.write_text('partial build')
            inode = result.stat().st_ino
            (root / 'A.lean').write_text('new source version')
            second = cache.prepare(root, archives)
            self.assertEqual(first, second)
            self.assertEqual(result.stat().st_ino, inode)
            self.assertEqual(result.read_text(), 'partial build')
            result.write_text('updated incrementally')
            (root / 'A.lean').write_text('another source version')
            self.assertEqual(cache.prepare(root, archives), first)
            self.assertEqual(result.read_text(), 'updated incrementally')
            self.assertFalse((first / 'inputs').exists())

    def test_environment_switch_retains_each_locked_cache(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary) / 'checkout'; self.make(root)
            archives = Path(temporary) / 'cache'
            first = cache.prepare(root, archives)
            (first / 'build').mkdir(); (first / 'build/progress').write_text('old environment')
            (root / 'lake-manifest.json').write_text('{"changed":true}')
            second = cache.prepare(root, archives)
            self.assertNotEqual(first, second)
            self.assertFalse((second / 'build').exists())
            self.assertEqual((first / 'build/progress').read_text(), 'old environment')
            (root / 'lake-manifest.json').write_text('{}')
            self.assertEqual(cache.prepare(root, archives), first)
            self.assertEqual((root / '.lake/build/progress').read_text(), 'old environment')

    def test_legacy_migration_renames_current_build_and_preserves_older_build(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary) / 'checkout'; self.make(root)
            archives = Path(temporary) / 'cache'
            environment = archives / cache.environment_key(root)
            old = environment / 'inputs' / ('a' * 64)
            (old / 'build').mkdir(parents=True)
            (old / 'build/result').write_text('latest CI progress')
            inode = (old / 'build/result').stat().st_ino
            (environment / 'build').mkdir()
            (environment / 'build/result').write_text('older baseline')
            (root / '.lake').symlink_to(old, target_is_directory=True)
            self.assertEqual(cache.prepare(root, archives), environment)
            self.assertEqual((environment / 'build/result').stat().st_ino, inode)
            self.assertFalse((old / 'build').exists())
            backup = next(environment.glob('build.before-single-slot-*'))
            self.assertEqual((backup / 'result').read_text(), 'older baseline')
            self.assertEqual((root / '.lake/build/result').read_text(), 'latest CI progress')

    def test_checkout_recreation_keeps_persistent_build(self):
        import shutil
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary) / 'checkout'; self.make(root)
            archives = Path(temporary) / 'cache'
            cache.prepare(root, archives)
            (root / '.lake/build').mkdir(); (root / '.lake/build/result').write_text('compiled')
            shutil.rmtree(root); self.make(root)
            cache.prepare(root, archives)
            self.assertEqual((root / '.lake/build/result').read_text(), 'compiled')

    def test_development_link_is_rejected(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary) / 'checkout'; self.make(root)
            (root / '.lake').symlink_to(Path(temporary) / 'development')
            with self.assertRaises(ValueError):
                cache.prepare(root, Path(temporary) / 'cache')

    def test_build_and_dependency_links_cannot_escape_into_development(self):
        for name in ('build', 'packages'):
            with self.subTest(name=name), tempfile.TemporaryDirectory() as temporary:
                root = Path(temporary) / 'checkout'; self.make(root)
                archives = Path(temporary) / 'cache'
                target = archives / cache.environment_key(root); target.mkdir(parents=True)
                (target / name).symlink_to(Path(temporary) / 'development')
                with self.assertRaises(ValueError):
                    cache.prepare(root, archives)

    def test_unclassified_checkout_cache_is_preserved_without_adopting_it(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary) / 'checkout'; self.make(root)
            (root / '.lake/build').mkdir(parents=True)
            (root / '.lake/build/progress').write_text('unknown owner inputs')
            archives = Path(temporary) / 'cache'
            cache.prepare(root, archives)
            self.assertFalse((root / '.lake/build').exists())
            backup = next(archives.glob('previous-checkout-*'))
            self.assertEqual((backup / 'build/progress').read_text(), 'unknown owner inputs')

    def test_environment_ancestor_symlink_is_rejected(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary) / 'checkout'; self.make(root)
            archives = Path(temporary) / 'cache'; archives.mkdir()
            (archives / cache.environment_key(root)).symlink_to(Path(temporary) / 'development')
            with self.assertRaises(ValueError):
                cache.prepare(root, archives)

    def test_source_cleanup_preserves_persistent_build(self):
        import subprocess
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary) / 'checkout'; self.make(root)
            subprocess.run(['git', 'init', '-q', str(root)], check=True)
            subprocess.run(['git', 'add', '.'], cwd=root, check=True)
            cache.prepare(root, Path(temporary) / 'cache')
            (root / '.lake/build').mkdir(); (root / '.lake/build/progress').write_text('compiled')
            (root / 'stale.tmp').write_text('stale')
            subprocess.run(['git', 'clean', '-ffdx', '-e', '.lake', '-e', '.lake/'],
                           cwd=root, check=True, capture_output=True)
            self.assertTrue((root / '.lake').is_symlink())
            self.assertEqual((root / '.lake/build/progress').read_text(), 'compiled')
            self.assertFalse((root / 'stale.tmp').exists())
