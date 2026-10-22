"""Host admission must reject foreign code; cache switches must preserve isolation."""
import importlib.util
from pathlib import Path
import tempfile
import unittest

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
    def test_source_variants_keep_independent_builds_and_shared_locked_dependencies(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary) / 'checkout'; root.mkdir()
            archives = Path(temporary) / 'archives'
            (root / 'lean-toolchain').write_text('pinned')
            (root / 'lake-manifest.json').write_text('{}')
            cache.prepare(root, archives, 'a' * 64)
            (root / '.lake/build').mkdir()
            (root / '.lake/build/result').write_text('version A')
            (root / '.lake/packages/dependency').write_text('locked dependency')
            cache.prepare(root, archives, 'b' * 64)
            self.assertFalse((root / '.lake/build').exists())
            self.assertEqual((root / '.lake/packages/dependency').read_text(), 'locked dependency')
            (root / '.lake/build').mkdir()
            (root / '.lake/build/result').write_text('version B')
            cache.prepare(root, archives, 'a' * 64)
            self.assertEqual((root / '.lake/build/result').read_text(), 'version A')
            cache.prepare(root, archives, 'b' * 64)
            self.assertEqual((root / '.lake/build/result').read_text(), 'version B')

    def test_corrupt_fingerprint_cannot_escape_cache(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary); (root / 'lean-toolchain').write_text('pinned')
            (root / 'lake-manifest.json').write_text('{}')
            with self.assertRaises(ValueError):
                cache.prepare(root, root / 'cache', '../development')

    def test_matching_environment_keeps_files_and_lock_change_archives_them(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary) / 'checkout'; root.mkdir()
            archives = Path(temporary) / 'archives'
            (root / 'lean-toolchain').write_text('pinned')
            (root / 'lake-manifest.json').write_text('{}')
            cache.prepare(root, archives)
            artifact = root / '.lake/artifact'; artifact.write_text('compiled')
            cache.prepare(root, archives)
            self.assertEqual(artifact.read_text(), 'compiled')
            (root / 'lake-manifest.json').write_text('{"changed":true}')
            cache.prepare(root, archives)
            self.assertFalse(artifact.exists())
            self.assertEqual(next(archives.glob('*/artifact')).read_text(), 'compiled')
            (root / 'lake-manifest.json').write_text('{}')
            cache.prepare(root, archives)
            self.assertEqual(artifact.read_text(), 'compiled')

    def test_checkout_recreation_does_not_delete_persistent_build(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary) / 'checkout'; root.mkdir()
            archives = Path(temporary) / 'archives'
            (root / 'lean-toolchain').write_text('pinned')
            (root / 'lake-manifest.json').write_text('{}')
            cache.prepare(root, archives)
            (root / '.lake/artifact').write_text('compiled')
            # Checkout's directory removal must only remove the symlink.
            import shutil
            shutil.rmtree(root)
            root.mkdir()
            (root / 'lean-toolchain').write_text('pinned')
            (root / 'lake-manifest.json').write_text('{}')
            cache.prepare(root, archives)
            self.assertEqual((root / '.lake/artifact').read_text(), 'compiled')

    def test_symlink_cannot_redirect_into_development_cache(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            (root / 'lean-toolchain').write_text('pinned')
            (root / 'lake-manifest.json').write_text('{}')
            (root / '.lake').symlink_to(root / 'development')
            with self.assertRaises(ValueError):
                cache.prepare(root, root / 'archives')

    def test_source_cleanup_preserves_cache_link_and_removes_stale_files(self):
        import subprocess
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary) / 'checkout'; root.mkdir()
            (root / 'lean-toolchain').write_text('pinned')
            (root / 'lake-manifest.json').write_text('{}')
            subprocess.run(['git', 'init', '-q', str(root)], check=True)
            subprocess.run(['git', 'add', 'lean-toolchain', 'lake-manifest.json'], cwd=root, check=True)
            cache.prepare(root, Path(temporary) / 'archives')
            (root / '.lake/artifact').write_text('compiled')
            (root / 'stale.tmp').write_text('old source')
            subprocess.run(['git', 'clean', '-ffdx', '-e', '.lake', '-e', '.lake/'],
                           cwd=root, check=True, capture_output=True)
            self.assertTrue((root / '.lake').is_symlink())
            self.assertEqual((root / '.lake/artifact').read_text(), 'compiled')
            self.assertFalse((root / 'stale.tmp').exists())
