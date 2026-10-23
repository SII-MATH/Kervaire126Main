"""Asynchronous publication must preserve provenance, retries and CI priority."""
import importlib.util
import json
from pathlib import Path
import subprocess
import tarfile
import tempfile
import unittest
from unittest.mock import Mock, patch

ROOT = Path(__file__).resolve().parents[1]


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, ROOT / path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


worker = load('async_release_worker', '.github/runner/cache-publisher.py')
pub = load('async_release_library', 'scripts/release-cache.py')
A, B = 'a' * 40, 'b' * 40


def run_info():
    return {'head_sha': A, 'head_branch': 'main', 'event': 'push',
            'path': '.github/workflows/ci.yml', 'head_repository': {'full_name': worker.REPO},
            'status': 'completed', 'conclusion': 'success', 'id': 123, 'run_attempt': 2}


def job_info():
    return {'id': 456, 'name': 'Lean checks', 'conclusion': 'success',
            'runner_name': 'inspire-kip126-01',
            'steps': [{'name': n, 'conclusion': 'success'} for n in
                      ['Check source inventory', 'Build all modules and checks']]}


class QueueTests(unittest.TestCase):
    def test_only_successful_main_push_can_publish(self):
        self.assertTrue(worker.eligible_run(run_info(), A))
        for key, value in [('event', 'pull_request'), ('event', 'merge_group'),
                           ('event', 'workflow_dispatch'), ('head_branch', 'develop'),
                           ('head_sha', B), ('status', 'in_progress'), ('conclusion', 'failure'),
                           ('conclusion', 'cancelled'), ('path', '.github/workflows/pages.yml'),
                           ('head_repository', {'full_name': 'fork/repo'}), ('run_attempt', '2')]:
            with self.subTest(key=key, value=value):
                self.assertFalse(worker.eligible_run({**run_info(), key: value}, A))

    def test_required_checks_and_isolated_runner_are_evidence(self):
        self.assertEqual(worker.build_job([job_info()])['id'], 456)
        for job in [{**job_info(), 'runner_name': 'another-runner'},
                    {**job_info(), 'conclusion': 'failure'}, {**job_info(), 'steps': []},
                    {**job_info(), 'steps': [{'name': 'Build all modules and checks', 'conclusion': 'skipped'}]}]:
            with self.assertRaises(ValueError):
                worker.build_job([job])

    def test_continuous_commits_coalesce_and_identical_polls_do_not_extend_wait(self):
        first = worker.observe({}, A, 100)
        self.assertEqual(first['ready_after'], 160)
        self.assertEqual(worker.observe(first, A, 130), first)
        newest = worker.observe({**first, 'attempts': 4, 'next_retry': 999}, B, 135)
        self.assertEqual(newest['head_sha'], B)
        self.assertEqual(newest['ready_after'], 195)
        self.assertEqual(newest['attempts'], 0)
        self.assertEqual(newest['next_retry'], 0)

    def test_persistent_retry_backoff_caps_and_survives_reload(self):
        queue = worker.observe({}, A, 0)
        with tempfile.TemporaryDirectory() as td:
            path = Path(td) / 'queue.json'
            for delay in [30, 120, 300, 900, 900]:
                queue = worker.failed(queue, OSError('network unavailable'), 1000)
                worker.atomic_json(path, queue)
                queue = worker.read_json(path)
                self.assertEqual(queue['next_retry'], 1000 + delay)
                self.assertEqual(queue['status'], 'retrying')
                self.assertIn('network unavailable', queue['error'])

    def test_ci_job_preempts_capture_without_locking_ci(self):
        with patch.object(worker, 'runner_busy', return_value=True), patch.object(worker.subprocess, 'check_output') as git:
            with self.assertRaises(worker.Deferred):
                worker.read_guard(A)(force=True)
            git.assert_not_called()

    def test_checkout_change_preempts_capture(self):
        with patch.object(worker, 'runner_busy', return_value=False), patch.object(worker.subprocess, 'check_output', return_value=(B+'\n').encode()):
            with self.assertRaises(worker.Deferred):
                worker.read_guard(A)(force=True)

    def test_waiting_for_ci_never_calls_publisher_or_fails_build(self):
        with tempfile.TemporaryDirectory() as td, patch.object(worker, 'STATE', Path(td)):
            worker.atomic_json(Path(td) / 'queue.json', worker.observe({}, A, 0))
            with patch.object(worker, 'api', side_effect=[{'object': {'sha': A}}, {'workflow_runs': []}]), patch.object(worker, 'process') as publish:
                worker.once()
            result = worker.read_json(Path(td) / 'queue.json')
            self.assertEqual(result['status'], 'waiting')
            self.assertEqual(result['attempts'], 0)
            publish.assert_not_called()

    def test_failed_publication_is_durable_and_newer_main_replaces_it(self):
        with tempfile.TemporaryDirectory() as td, patch.object(worker, 'STATE', Path(td)):
            path = Path(td) / 'queue.json'
            worker.atomic_json(path, worker.observe({}, A, 0))
            with patch.object(worker, 'api', side_effect=[{'object': {'sha': A}}, {'workflow_runs': [run_info()]}, {'jobs': [job_info()]}]), patch.object(worker, 'process', side_effect=OSError('upload failed')):
                worker.once()
            self.assertEqual(worker.read_json(path)['status'], 'retrying')
            with patch.object(worker, 'api', return_value={'object': {'sha': B}}), patch.object(worker, 'process') as publish:
                worker.once()
            self.assertEqual(worker.read_json(path)['head_sha'], B)
            self.assertEqual(worker.read_json(path)['status'], 'debouncing')
            publish.assert_not_called()

    def test_success_has_verified_receipt_and_is_not_published_repeatedly(self):
        with tempfile.TemporaryDirectory() as td, patch.object(worker, 'STATE', Path(td)):
            path = Path(td) / 'queue.json'
            worker.atomic_json(path, worker.observe({}, A, 0))
            result = {'status': 'published', 'uploaded_sha256_verified': True}
            with patch.object(worker, 'api', side_effect=[{'object': {'sha': A}}, {'workflow_runs': [run_info()]}, {'jobs': [job_info()]}]), patch.object(worker, 'process', return_value=result):
                worker.once()
            self.assertEqual(worker.read_json(path)['status'], 'published')
            self.assertEqual(worker.read_json(Path(td) / 'published.json')['run_attempt'], 2)
            with patch.object(worker, 'api', return_value={'object': {'sha': A}}), patch.object(worker, 'process') as publish:
                worker.once()
            publish.assert_not_called()

    def test_build_log_is_from_successful_build_step(self):
        log = b'Lean checks\tBuild all modules and checks\t2026-01-01T00:00:00Z Build completed successfully (4115 jobs).\n'
        with tempfile.TemporaryDirectory() as td, patch.object(worker.subprocess, 'check_output', return_value=log):
            path = Path(td) / 'build.log'
            worker.capture_log(run_info(), job_info(), path)
            self.assertIn('4115 jobs', path.read_text())
        with tempfile.TemporaryDirectory() as td, patch.object(worker.subprocess, 'check_output', return_value=log.replace(b'Build all modules and checks', b'Another step')):
            with self.assertRaises(ValueError):
                worker.capture_log(run_info(), job_info(), Path(td) / 'build.log')

    def test_restart_resumes_immutable_bundle_while_ci_uses_another_checkout(self):
        with tempfile.TemporaryDirectory() as td, patch.object(worker, 'STATE', Path(td)):
            output = Path(td) / 'builds' / A
            directory = output / ('package-' + A)
            directory.mkdir(parents=True)
            worker.atomic_json(output / 'package-result.json', {'directory': str(directory)})
            publisher = Mock()
            def publish(args, current):
                worker.atomic_json(output / 'publish-result.json', {'status': 'published'})
            publisher.publish.side_effect = publish
            with patch.object(worker, 'load_publisher', return_value=publisher), patch.object(worker, 'bundle_context', return_value={'head': A}), patch.object(worker, 'api', return_value={'object': {'sha': A}}), patch.object(worker, 'read_guard') as guard, patch.object(worker, 'capture_log') as capture:
                self.assertEqual(worker.process(run_info(), job_info())['status'], 'published')
            guard.assert_not_called()
            capture.assert_not_called()
            publisher.snapshot.assert_not_called()
            publisher.package.assert_not_called()
            publisher.publish.assert_called_once()

    def test_watchdog_restores_publisher_and_failure_cannot_prevent_runner_start(self):
        supervisor = load('async_runner_supervisor', '.github/runner/service.py')
        with patch.object(supervisor.Path, 'is_file', return_value=True), patch.object(supervisor.subprocess, 'run', side_effect=subprocess.TimeoutExpired('publisher', 10)):
            supervisor.cache_publisher('start')
        source = (ROOT / '.github/runner/service.py').read_text()
        self.assertLess(source.index("cache_publisher('start')"), source.index("if live():", source.index("elif action == 'start':")))
        self.assertIn("cache_publisher('stop')", source)

    def test_runtime_imports_only_installed_publisher_code(self):
        self.assertIn("HERE / 'release-cache.py'", (ROOT / '.github/runner/cache-publisher.py').read_text())
        with patch.object(pub.importlib.util, 'spec_from_file_location', wraps=pub.importlib.util.spec_from_file_location) as spec:
            pub.load_ci(Path('/untrusted/job/checkout'))
            self.assertEqual(spec.call_args.args[1], ROOT / 'scripts/ci-cache.py')


class ArtifactTests(unittest.TestCase):
    def test_archive_verifies_every_file_and_rejects_corruption(self):
        with tempfile.TemporaryDirectory() as td:
            p = Path(td); data = b'compiled olean payload'
            plain = p / 'build.tar'
            import io
            with tarfile.open(plain, 'w') as tf:
                root = tarfile.TarInfo('.lake/build'); root.type = tarfile.DIRTYPE; tf.addfile(root)
                item = tarfile.TarInfo('.lake/build/test.olean'); item.size = len(data); tf.addfile(item, io.BytesIO(data))
            archive = p / 'build.tar.zst'
            with archive.open('wb') as out:
                subprocess.run(['zstd', '-q', '-c', str(plain)], check=True, stdout=out)
            inventory = [{'path': '.lake/build/test.olean', 'bytes': len(data), 'sha256': pub.digest_bytes(data)}]
            metadata = {'format': 'tar.zst', 'root': '.lake/build', 'bytes': archive.stat().st_size,
                        'sha256': pub.digest_file(archive), 'uncompressed_files': 1, 'uncompressed_bytes': len(data)}
            self.assertTrue(pub.verify_archive(archive, inventory, metadata)['every_file_sha256'])
            with self.assertRaises(ValueError):
                pub.verify_archive(archive, [{**inventory[0], 'sha256': '0'*64}], metadata)
            archive.write_bytes(archive.read_bytes()[:-1] + b'x')
            with self.assertRaises(ValueError):
                pub.verify_archive(archive, inventory, metadata)

    def test_archive_rejects_links_even_with_correct_outer_checksum(self):
        with tempfile.TemporaryDirectory() as td:
            p = Path(td); plain = p / 'bad.tar'
            with tarfile.open(plain, 'w') as tf:
                root = tarfile.TarInfo('.lake/build'); root.type = tarfile.DIRTYPE; tf.addfile(root)
                item = tarfile.TarInfo('.lake/build/link'); item.type = tarfile.SYMTYPE; item.linkname = '/tmp/escape'; tf.addfile(item)
            archive = p / 'bad.tar.zst'
            with archive.open('wb') as out:
                subprocess.run(['zstd', '-q', '-c', str(plain)], check=True, stdout=out)
            meta = {'format': 'tar.zst', 'root': '.lake/build', 'bytes': archive.stat().st_size,
                    'sha256': pub.digest_file(archive), 'uncompressed_files': 0, 'uncompressed_bytes': 0}
            with self.assertRaises(ValueError):
                pub.verify_archive(archive, [], meta)

    def test_unsafe_checksum_names_are_rejected(self):
        for name in ['../cache', '/tmp/cache', 'cache/x', 'cache\\x']:
            with self.assertRaises(ValueError):
                pub.safe_name(name)

    def test_partial_draft_retries_only_missing_assets_and_verifies_server_digests(self):
        with tempfile.TemporaryDirectory() as td:
            p=Path(td); directory=p/'package'; directory.mkdir()
            files={'metadata.json': b'metadata', 'part-0000': b'one', 'part-0001': b'two'}
            for name, data in files.items(): (directory/name).write_bytes(data)
            sums={name:pub.digest_bytes(data) for name,data in files.items()}
            (directory/'SHA256SUMS').write_text(''.join(f'{value}  {name}\n' for name,value in sums.items()))
            expected={**sums,'SHA256SUMS':pub.digest_file(directory/'SHA256SUMS')}
            tag='build-cache-'+A+'-linux-x86_64'
            def assets(names):
                return [{'id':i+1,'name':name,'size':(directory/name).stat().st_size,'digest':'sha256:'+expected[name],'state':'uploaded'} for i,name in enumerate(names)]
            initial={'id':7,'draft':True,'tag_name':tag,'target_commitish':A,'assets':assets(['part-0000'])}
            uploaded={**initial,'assets':assets(expected)}
            final={**uploaded,'draft':False}
            metadata={'source_commit':A,'archive':{'sha256':'f'*64},'lean_toolchain':'pinned','lake_manifest_sha256':'e'*64}
            current={'head':A,'inputs':{'fingerprint':'d'*64}}
            responses=[{'sha':A}, initial, uploaded, final]
            with patch.object(pub,'validate_bundle',return_value=(metadata,tag,{})), patch.object(pub,'probe',return_value=None), patch.object(pub,'remote_tag_commit',return_value=A), patch.object(pub,'draft_release',return_value=initial), patch.object(pub,'api',side_effect=responses), patch.object(pub,'run') as command:
                pub.publish(type('Args',(),{'package_dir':directory,'output':p,'release_id':None})(),current)
            uploads=[c.args for c in command.call_args_list if c.args[:3]==('gh','release','upload')]
            self.assertEqual({Path(c[4]).name for c in uploads},set(expected)-{'part-0000'})
            self.assertTrue(json.loads((p/'publish-result.json').read_text())['uploaded_sha256_verified'])


if __name__ == '__main__':
    unittest.main()
