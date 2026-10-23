"""CI must retain validation coverage and reject incompatible or unsafe caches."""

import importlib.util
import io
import json
import os
from pathlib import Path
import shutil
import subprocess
import tarfile
import tempfile
import textwrap
import unittest
from unittest.mock import patch


ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('ci_cache', ROOT / 'scripts/ci-cache.py')
ci = importlib.util.module_from_spec(spec)
spec.loader.exec_module(ci)


def pull():
    return {'state': 'open', 'head': {'ref': 'develop', 'sha': 'a' * 40,
            'repo': {'full_name': 'owner/repo'}},
            'base': {'ref': 'main', 'repo': {'full_name': 'owner/repo'}}}


class EventPolicyTests(unittest.TestCase):
    def test_only_exact_develop_push_is_redundant(self):
        args = ('push', 'refs/heads/develop', 'owner/repo', 'a' * 40)
        self.assertFalse(ci.needs_build(*args, [pull()]))
        self.assertTrue(ci.needs_build(*args, []))
        for event, ref in [('pull_request', 'refs/pull/1/merge'), ('push', 'refs/heads/main'),
                           ('workflow_dispatch', 'refs/heads/develop'),
                           ('merge_group', 'refs/heads/gh-readonly-queue/main/pr-12-abc')]:
            self.assertTrue(ci.needs_build(event, ref, 'owner/repo', 'a' * 40, [pull()]))

    def test_stale_foreign_closed_or_other_base_pr_cannot_suppress_build(self):
        variants = []
        for field, value in [('sha', 'b' * 40), ('ref', 'another-branch'), ('repo', None),
                              ('repo', {'full_name': 'fork/repo'})]:
            pr = pull(); pr['head'][field] = value; variants.append(pr)
        pr = pull(); pr['state'] = 'closed'; variants.append(pr)
        pr = pull(); pr['base']['ref'] = 'another-base'; variants.append(pr)
        variants.extend([{}, None])
        for pr in variants:
            with self.subTest(pr=pr):
                self.assertTrue(ci.needs_build('push', 'refs/heads/develop', 'owner/repo', 'a' * 40, [pr]))

    def test_api_failure_retains_build(self):
        with tempfile.TemporaryDirectory() as temporary:
            out = Path(temporary) / 'output'
            with patch.dict(os.environ, {'GITHUB_EVENT_NAME': 'push', 'GITHUB_REF': 'refs/heads/develop',
                    'GITHUB_REPOSITORY': 'owner/repo', 'GITHUB_SHA': 'a' * 40, 'GITHUB_OUTPUT': str(out)}), \
                    patch.object(ci, 'api', side_effect=subprocess.CalledProcessError(1, 'gh')):
                ci.plan()
            self.assertEqual(out.read_text(), 'build=true\n')


    def test_merge_group_always_builds_without_a_pr_lookup(self):
        with tempfile.TemporaryDirectory() as temporary:
            out = Path(temporary) / 'output'
            with patch.dict(os.environ, {
                    'GITHUB_EVENT_NAME': 'merge_group',
                    'GITHUB_REF': 'refs/heads/gh-readonly-queue/main/pr-12-abc',
                    'GITHUB_REPOSITORY': 'owner/repo', 'GITHUB_SHA': 'a' * 40,
                    'GITHUB_OUTPUT': str(out)}), patch.object(ci, 'api') as lookup:
                ci.plan()
            lookup.assert_not_called()
            self.assertEqual(out.read_text(), 'build=true\n')


class MergeQueuePolicyTests(unittest.TestCase):
    def test_queue_is_main_only_and_all_checks_are_required(self):
        rule = json.loads((ROOT / '.github/merge-queue-ruleset.json').read_text())
        self.assertEqual(rule['conditions']['ref_name'],
                         {'include': ['refs/heads/main'], 'exclude': []})
        self.assertEqual(rule['bypass_actors'], [])
        self.assertEqual(rule['enforcement'], 'active')
        self.assertEqual([r['type'] for r in rule['rules']], ['merge_queue'])
        queue = rule['rules'][0]['parameters']
        self.assertEqual(queue['grouping_strategy'], 'ALLGREEN')
        self.assertGreaterEqual(queue['check_response_timeout_minutes'], 90)
        self.assertGreaterEqual(queue['max_entries_to_build'], 1)
        self.assertLessEqual(queue['min_entries_to_merge'], queue['max_entries_to_merge'])


class AutoMergeWorkflowTests(unittest.TestCase):
    def invoke(self, queue_id='', api_failure=False):
        workflow = (ROOT / '.github/workflows/auto-merge.yml').read_text()
        script = textwrap.dedent(workflow.split('        run: |\n', 1)[1])
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            executable = directory / 'gh'
            executable.write_text('''#!/usr/bin/env python3
import json, os, sys
from pathlib import Path
with Path(os.environ['MOCK_LOG']).open('a') as stream:
    stream.write(json.dumps(sys.argv[1:]) + '\\n')
if sys.argv[1:3] == ['api', 'graphql']:
    if os.environ['MOCK_API_FAILURE'] == '1':
        sys.exit(1)
    print(os.environ['MOCK_QUEUE_ID'])
''')
            executable.chmod(0o755)
            log = directory / 'calls.jsonl'
            env = {**os.environ, 'PATH': str(directory) + os.pathsep + os.environ['PATH'],
                   'GH_REPO': 'owner/repo', 'PR_NUMBER': '12', 'PR_HEAD_SHA': 'a' * 40,
                   'MOCK_LOG': str(log), 'MOCK_QUEUE_ID': queue_id,
                   'MOCK_API_FAILURE': '1' if api_failure else '0'}
            result = subprocess.run(['bash', '-euo', 'pipefail', '-c', script], env=env,
                                    capture_output=True, text=True)
            calls = [json.loads(row) for row in log.read_text().splitlines()]
            return result, [call for call in calls if call[:2] == ['pr', 'merge']]

    def test_queue_uses_native_enqueue_with_the_exact_pr_head(self):
        result, merges = self.invoke('queue-id')
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(merges, [['pr', 'merge', '12', '--auto',
                                 '--match-head-commit', 'a' * 40]])

    def test_bootstrap_without_a_queue_preserves_merge_commit_auto_merge(self):
        result, merges = self.invoke()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(merges, [['pr', 'merge', '12', '--auto', '--merge',
                                 '--match-head-commit', 'a' * 40]])

    def test_queue_lookup_failure_does_not_attempt_a_merge(self):
        result, merges = self.invoke(api_failure=True)
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(merges, [])


class InputTests(unittest.TestCase):
    def test_fingerprint_tracks_lean_baselines_scripts_modes_and_locked_dependencies(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            subprocess.run(['git', 'init', '-q', str(root)], check=True)
            for name in ['A.lean', 'interface/baselines/a.json', 'scripts/helper.py', 'README.md', 'lean-toolchain', 'lake-manifest.json']:
                path = root / name; path.parent.mkdir(parents=True, exist_ok=True); path.write_text('first')
            subprocess.run(['git', 'add', '.'], cwd=root, check=True)
            original = ci.build_inputs(root)
            self.assertEqual(len(original['files']), 5)
            (root / 'README.md').write_text('documentation change')
            self.assertEqual(ci.build_inputs(root), original)
            for name in ['A.lean', 'interface/baselines/a.json', 'scripts/helper.py', 'lean-toolchain', 'lake-manifest.json']:
                with self.subTest(name=name):
                    (root / name).write_text('second')
                    self.assertNotEqual(ci.build_inputs(root)['fingerprint'], original['fingerprint'])
                    (root / name).write_text('first')
            subprocess.run(['git', 'update-index', '--chmod=+x', 'scripts/helper.py'], cwd=root, check=True)
            self.assertNotEqual(ci.build_inputs(root)['fingerprint'], original['fingerprint'])
            (root / 'A.lean').unlink(); (root / 'A.lean').symlink_to('README.md')
            with self.assertRaisesRegex(ValueError, 'Symlink'):
                ci.build_inputs(root)


def compressed_tar(directory, members):
    raw = io.BytesIO()
    with tarfile.open(fileobj=raw, mode='w') as tar:
        for name, kind in members:
            info = tarfile.TarInfo(name)
            if kind == 'file':
                info.size = 7; tar.addfile(info, io.BytesIO(b'checked'))
            else:
                info.type = {'symlink': tarfile.SYMTYPE, 'hardlink': tarfile.LNKTYPE,
                             'device': tarfile.CHRTYPE}[kind]
                info.linkname = '/tmp/escape'
                tar.addfile(info)
    archive = directory / 'project-build.tar.zst'
    archive.write_bytes(subprocess.check_output(['zstd', '-q', '-c'], input=raw.getvalue()))
    return archive


class ExtractionTests(unittest.TestCase):
    def test_regular_project_files_restore(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            ci.extract_archive(compressed_tar(root, [('.lake/build/lib/A.olean', 'file')]), root / 'staged')
            self.assertEqual((root / 'staged/.lake/build/lib/A.olean').read_bytes(), b'checked')

    def test_escape_links_devices_duplicates_and_oversized_archives_rejected(self):
        cases = [[('../escape', 'file')], [('/tmp/escape', 'file')],
                 [('.lake/packages/tool', 'file')], [('.lake/build/../../escape', 'file')],
                 [('.lake/build/link', 'symlink')], [('.lake/build/link', 'hardlink')],
                 [('.lake/build/device', 'device')],
                 [('.lake/build/same', 'file'), ('.lake/build/same', 'file')]]
        for members in cases:
            with self.subTest(members=members), tempfile.TemporaryDirectory() as temporary:
                root = Path(temporary)
                with self.assertRaises(ValueError):
                    ci.extract_archive(compressed_tar(root, members), root / 'staged')
        with tempfile.TemporaryDirectory() as temporary, patch.object(ci, 'MAX_EXPANDED', 1):
            root = Path(temporary)
            with self.assertRaises(ValueError):
                ci.extract_archive(compressed_tar(root, [('.lake/build/A', 'file')]), root / 'staged')

    def test_active_writer_blocks_replacement(self):
        with tempfile.TemporaryDirectory() as temporary, patch.object(ci, 'active_build', return_value=True):
            root = Path(temporary); old = root / '.lake/build'; old.mkdir(parents=True)
            (old / 'progress').write_text('newer work')
            with self.assertRaisesRegex(ValueError, 'Active'):
                ci.install_build(root / 'staged', root, root / 'backup')
            self.assertEqual((old / 'progress').read_text(), 'newer work')

    def test_only_explicitly_validated_lake_link_can_be_installed(self):
        with tempfile.TemporaryDirectory() as temporary, patch.object(ci, 'active_build', return_value=False):
            root = Path(temporary) / 'checkout'; root.mkdir()
            target = Path(temporary) / 'input-cache'; target.mkdir()
            (root / '.lake').symlink_to(target, target_is_directory=True)
            staged = Path(temporary) / 'staged'; staged.mkdir()
            (staged / 'compiled').write_text('verified')
            with self.assertRaises(ValueError):
                ci.install_build(staged, root, Path(temporary) / 'backup')
            with self.assertRaises(ValueError):
                ci.install_build(staged, root, Path(temporary) / 'backup', allowed_lake=root / 'other')
            ci.install_build(staged, root, Path(temporary) / 'backup', allowed_lake=target)
            self.assertEqual((root / '.lake/build/compiled').read_text(), 'verified')

    def test_install_failure_rolls_back(self):
        with tempfile.TemporaryDirectory() as temporary, patch.object(ci, 'active_build', return_value=False):
            root = Path(temporary); old = root / '.lake/build'; old.mkdir(parents=True)
            (old / 'progress').write_text('retained')
            with self.assertRaises(OSError):
                ci.install_build(root / 'missing-staged', root, root / 'backup')
            self.assertEqual((old / 'progress').read_text(), 'retained')


class ReleaseDiscoveryTests(unittest.TestCase):
    def tag(self, commit):
        return f'build-cache-{commit}-{ci.platform.system().lower()}-{ci.platform.machine()}'

    def test_queue_uses_raw_shallow_parents_before_any_release_listing(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            def git(*args, data=None):
                return subprocess.check_output(['git', '-C', str(root), *args], input=data).decode().strip()
            git('init', '-q')
            git('config', 'user.name', 'Cache test')
            git('config', 'user.email', 'cache-test@example.invalid')
            tree = git('mktree', data=b'')
            base = git('commit-tree', tree, '-m', 'base')
            head = git('commit-tree', tree, '-p', base, '-m', 'incoming')
            merge = git('commit-tree', tree, '-p', base, '-p', head, '-m', 'queue')
            git('update-ref', 'HEAD', merge)
            # Match actions/checkout's depth-one history boundary.
            (root / '.git/shallow').write_text(merge + '\n')
            self.assertEqual(git('show', '-s', '--format=%P', 'HEAD'), '')
            original_run = ci.run
            with patch.dict(os.environ, {'GITHUB_SHA': merge}), \
                    patch.object(ci, 'run', side_effect=lambda *args: original_run(*args, cwd=root)), \
                    patch.object(ci, 'api') as lookup:
                tags = ci.release_tags('owner/repo')
                self.assertEqual([next(tags), next(tags), next(tags)],
                                 [self.tag(merge), self.tag(head), self.tag(base)])
                lookup.assert_not_called()

    def test_paginated_lookup_passes_old_cutoffs_and_orders_by_publication(self):
        rows = [{'tag_name': self.tag(f'{i:040x}'), 'published_at': f'2026-01-01T00:{i:02d}:00Z'}
                for i in range(31)]
        first_page = rows + [{'tag_name': f'unrelated-{i}'} for i in range(69)]
        older = {'tag_name': self.tag('e' * 40), 'published_at': '2025-01-01T00:00:00Z'}
        newest = {'tag_name': self.tag('f' * 40), 'published_at': '2026-10-18T00:00:00Z'}
        with patch.dict(os.environ, {'GITHUB_SHA': ''}), \
                patch.object(ci, 'api', side_effect=[first_page, [older, newest, rows[0]]]) as lookup:
            tags = list(ci.release_tags('owner/repo'))
        self.assertEqual(tags[0], rows[-1]['tag_name'])
        self.assertEqual(tags[31:], [newest['tag_name'], older['tag_name']])
        self.assertEqual(len(tags), 33)
        self.assertEqual([c.args[0] for c in lookup.call_args_list],
                         ['repos/owner/repo/releases?per_page=100&page=1',
                          'repos/owner/repo/releases?per_page=100&page=2'])

    def test_discovery_deadline_and_api_failure_are_cache_misses(self):
        with patch.dict(os.environ, {'GITHUB_SHA': ''}), \
                patch.object(ci.time, 'monotonic', side_effect=[0, 91]), \
                patch.object(ci, 'api') as lookup:
            self.assertEqual(list(ci.release_tags('owner/repo')), [])
            lookup.assert_not_called()
        with patch.dict(os.environ, {'GITHUB_SHA': ''}), \
                patch.object(ci, 'api', side_effect=subprocess.CalledProcessError(1, 'gh')):
            self.assertEqual(list(ci.release_tags('owner/repo')), [])


class ReleaseTests(unittest.TestCase):
    def fixture(self, root, split=False, manifest_list=False):
        assets = root / 'assets'; assets.mkdir()
        archive = compressed_tar(assets, [('.lake/build/A.olean', 'file')])
        inputs = {'algorithm': 'sha256', 'fingerprint': 'c' * 64,
                  'files': [{'path': 'A.lean', 'mode': '100644', 'sha256': ci.sha256(b'source')}]}
        (assets / 'build-inputs.json').write_text(json.dumps(inputs['files'] if manifest_list else inputs))
        parts = [archive.name]
        if split:
            raw = archive.read_bytes(); parts = [archive.name + '.part0', archive.name + '.part1']
            for name, content in zip(parts, [raw[:len(raw)//2], raw[len(raw)//2:]]):
                (assets / name).write_bytes(content)
        metadata = {'schema_version': 1, 'repository': 'owner/repo', 'source_commit': 'a' * 40,
            'os': ci.platform.system().lower(), 'arch': ci.platform.machine(),
            'lean_toolchain': 'lean-test', 'lake_manifest_sha256': ci.sha256(b'lock'),
            'build_inputs': {'fingerprint_sha256': inputs['fingerprint'], 'working_tree_matches_commit': True,
                             'manifest': 'build-inputs.json', 'manifest_sha256': ci.sha256((assets / 'build-inputs.json').read_bytes())},
            'build': {'status': 'passed', 'command': 'lake build'},
            'archive': {'root': '.lake/build', 'format': 'tar.zst', 'filename': archive.name,
                        'bytes': archive.stat().st_size, 'sha256': ci.sha256(archive.read_bytes()),
                        'parts': [{'filename': n, 'sha256': ci.sha256((assets / n).read_bytes())} for n in parts]}}
        (assets / 'metadata.json').write_text(json.dumps(metadata))
        (assets / 'SHA256SUMS').write_text(''.join(f'{ci.sha256(p.read_bytes())}  {p.name}\n' for p in assets.iterdir()))
        return assets, inputs, metadata

    def restore(self, root, assets, inputs, releases=None, source_commit='', self_hosted=False):
        checkout = root / 'checkout'; checkout.mkdir(); (checkout / '.lake/build').mkdir(parents=True)
        (checkout / '.lake/build/old').write_text('existing cache')
        (checkout / 'lean-toolchain').write_text('lean-test\n'); (checkout / 'lake-manifest.json').write_bytes(b'lock')
        if self_hosted:
            digest = ci.hashlib.sha256()
            for name in ('lean-toolchain', 'lake-manifest.json'):
                digest.update(name.encode() + b'\0' + (checkout / name).read_bytes() + b'\0')
            target = root / 'home/cache/environments' / digest.hexdigest() / 'inputs' / inputs['fingerprint']
            target.parent.mkdir(parents=True)
            (checkout / '.lake').rename(target)
            (target / 'runner-build-inputs').write_text(inputs['fingerprint'])
            (checkout / '.lake').symlink_to(target, target_is_directory=True)
        requests = []
        def download(repo, tag, filename, directory):
            requests.append(filename)
            if tag != expected_tag:
                # A real, valid older snapshot must fail compatibility before
                # any large archive download, while search continues.
                self.assertEqual(filename, 'metadata.json')
                metadata = json.loads((assets / filename).read_text())
                metadata['build_inputs']['fingerprint_sha256'] = 'd' * 64
                path = directory / filename; path.write_text(json.dumps(metadata))
                return path
            return Path(shutil.copyfile(assets / filename, directory / filename))
        tag = f'build-cache-{"a" * 40}-{ci.platform.system().lower()}-{ci.platform.machine()}'
        expected_tag = tag
        with patch.object(ci, 'ROOT', checkout), patch.object(ci, 'build_inputs', return_value=inputs), \
                patch.object(ci, 'api', return_value=releases if releases is not None else [{'tag_name': tag}]) as lookup, \
                patch.object(ci, 'download', side_effect=download), \
                patch.object(ci, 'active_build', return_value=False), \
                patch.object(ci.Path, 'home', return_value=root / 'home'), patch.dict(os.environ, {
                    'GITHUB_ACTIONS': 'true', 'GITHUB_WORKSPACE': str(checkout), 'GITHUB_REPOSITORY': 'owner/repo',
                    'GITHUB_SHA': source_commit, 'RUNNER_ENVIRONMENT': 'self-hosted' if self_hosted else 'github-hosted'}):
            ci.restore_release()
            if source_commit:
                lookup.assert_not_called()
        return checkout, requests

    def test_self_hosted_exact_input_directory_restores_verified_archive(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            assets, inputs, metadata = self.fixture(root)
            checkout, requests = self.restore(root, assets, inputs, self_hosted=True)
            self.assertTrue((checkout / '.lake').is_symlink())
            self.assertFalse((checkout / '.lake/build/old').exists())
            self.assertIn('metadata.json', requests)

    def test_queue_restores_parent_cache_without_listing_releases(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary); assets, inputs, _ = self.fixture(root)
            headers = f'tree {"d" * 40}\nparent {"b" * 40}\nparent {"a" * 40}\n\nqueue'
            with patch.object(ci, 'run', return_value=headers.encode()):
                checkout, requests = self.restore(root, assets, inputs, source_commit='c' * 40)
            self.assertEqual(requests.count('metadata.json'), 2)
            self.assertEqual(requests.count('project-build.tar.zst'), 1)
            self.assertEqual((checkout / '.lake/build/A.olean').read_bytes(), b'checked')

    def test_restore_finds_matching_cache_tenth_in_api_order(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary); assets, inputs, _ = self.fixture(root)
            suffix = f'-{ci.platform.system().lower()}-{ci.platform.machine()}'
            releases = [{'tag_name': f'build-cache-{i:040x}{suffix}'} for i in range(9)]
            releases.append({'tag_name': f'build-cache-{"a" * 40}{suffix}'})
            checkout, requests = self.restore(root, assets, inputs, releases)
            self.assertEqual(requests.count('metadata.json'), 10)
            self.assertEqual(requests.count('project-build.tar.zst'), 1)
            self.assertEqual((checkout / '.lake/build/A.olean').read_bytes(), b'checked')

    def test_matching_single_and_split_archives_restore(self):
        for split in [False, True]:
            for manifest_list in [False, True]:
                with self.subTest(split=split, manifest_list=manifest_list), tempfile.TemporaryDirectory() as temporary:
                    root = Path(temporary); assets, inputs, _ = self.fixture(root, split, manifest_list)
                    checkout, _ = self.restore(root, assets, inputs)
                    self.assertEqual((checkout / '.lake/build/A.olean').read_bytes(), b'checked')

    def test_validly_checksummed_different_file_list_is_rejected(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary); assets, inputs, metadata = self.fixture(root, manifest_list=True)
            different = [{**inputs['files'][0], 'mode': '100755'}]
            manifest = assets / 'build-inputs.json'
            manifest.write_text(json.dumps(different))
            metadata['build_inputs']['manifest_sha256'] = ci.sha256(manifest.read_bytes())
            (assets / 'metadata.json').write_text(json.dumps(metadata))
            (assets / 'SHA256SUMS').write_text(''.join(
                f'{ci.sha256(p.read_bytes())}  {p.name}\n'
                for p in assets.iterdir() if p.name != 'SHA256SUMS'))
            checkout, requests = self.restore(root, assets, inputs)
            self.assertNotIn('project-build.tar.zst', requests)
            self.assertTrue((checkout / '.lake/build/old').exists())

    def test_incompatible_metadata_does_not_download_archive_or_replace_cache(self):
        for field in ['repository', 'os', 'arch', 'lean_toolchain', 'lake_manifest_sha256']:
            with self.subTest(field=field), tempfile.TemporaryDirectory() as temporary:
                root = Path(temporary); assets, inputs, metadata = self.fixture(root)
                metadata[field] = 'different'; (assets / 'metadata.json').write_text(json.dumps(metadata))
                checkout, requests = self.restore(root, assets, inputs)
                self.assertEqual(requests, ['metadata.json'])
                self.assertTrue((checkout / '.lake/build/old').exists())

    def test_corruption_retains_existing_cache(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary); assets, inputs, _ = self.fixture(root)
            (assets / 'project-build.tar.zst').write_bytes(b'corrupted')
            checkout, _ = self.restore(root, assets, inputs)
            self.assertEqual((checkout / '.lake/build/old').read_text(), 'existing cache')

    def test_unpassed_dirty_or_wrong_inputs_do_not_download_archive(self):
        variants = [('build', 'status', 'failed'), ('build_inputs', 'working_tree_matches_commit', False),
                    ('build_inputs', 'fingerprint_sha256', 'd' * 64)]
        for group, field, value in variants:
            with self.subTest(field=field), tempfile.TemporaryDirectory() as temporary:
                root = Path(temporary); assets, inputs, metadata = self.fixture(root)
                metadata[group][field] = value; (assets / 'metadata.json').write_text(json.dumps(metadata))
                checkout, requests = self.restore(root, assets, inputs)
                self.assertEqual(requests, ['metadata.json'])
                self.assertTrue((checkout / '.lake/build/old').exists())


if __name__ == '__main__':
    unittest.main()
