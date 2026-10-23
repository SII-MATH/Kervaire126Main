"""Exercise the local handoff, archive boundary and live-publication rollback."""
import importlib.util
import io
import json
from pathlib import Path
import subprocess
import tarfile
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]


def load(name, filename):
    spec = importlib.util.spec_from_file_location(name, ROOT / '.github/runner' / filename)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


client = load('direct_client', 'publish-blueprint.py')
host = load('direct_host', 'blueprint-publisher.py')


class DirectPublicationTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        root = Path(self.temporary.name)
        self.spool, self.state, self.site = root / 'spool', root / 'state', root / 'site'
        for directory in (self.spool / 'incoming', self.spool / 'results', self.state / 'queue'):
            directory.mkdir(parents=True)
        for name in ('index.html', 'Kervaire126/data.json', '.hgraph-runtime/config.yaml'):
            path = self.site / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text('{}')
        self.info = {'repository': host.REPO, 'head_sha': 'a' * 40, 'id': 42, 'run_attempt': 1}
        self.addCleanup(patch.stopall)
        patch.object(host, 'SPOOL', self.spool).start()
        patch.object(host, 'STATE', self.state).start()

    def stage(self):
        return client.stage(self.site, self.info, self.spool)

    def test_stage_capture_and_receipt_survive_watcher_restart(self):
        key, request = self.stage()
        host.capture(key)
        # Captured bytes are independent of runner-owned files.
        (self.spool / 'incoming' / f'{key}.tar').unlink()
        host.capture(key)
        with patch.object(host, 'verify_run'), patch.object(host, 'publish', return_value={'run_id': 42}) as publish:
            host.once()
            publish.assert_called_once()
        result = client.wait_receipt(key, request, self.spool, timeout=1)
        self.assertEqual(result['status'], 'success')
        with patch.object(host, 'publish') as publish:
            host.once()
            publish.assert_not_called()
        self.assertFalse((self.state / 'queue' / key).exists())

    def test_checksum_mismatch_and_symlink_handoff_rejected(self):
        key, _ = self.stage()
        archive = self.spool / 'incoming' / f'{key}.tar'
        archive.write_bytes(b'corrupted')
        with self.assertRaisesRegex(ValueError, 'checksum'):
            host.capture(key)
        archive.unlink()
        archive.symlink_to(self.site / 'index.html')
        with self.assertRaises(OSError):
            host.capture(key)

    def test_unsafe_tar_paths_links_and_duplicates_rejected(self):
        archive = self.state / 'bad.tar'
        for names, symbolic in [(['../escape'], False), (['link'], True), (['duplicate', 'duplicate'], False)]:
            with self.subTest(names=names, symbolic=symbolic):
                with tarfile.open(archive, 'w') as tar:
                    for name in names:
                        member = tarfile.TarInfo(name)
                        if symbolic:
                            member.type = tarfile.SYMTYPE
                            member.linkname = '/etc/passwd'
                        tar.addfile(member, io.BytesIO())
                with self.assertRaisesRegex(ValueError, 'unsafe'):
                    host.extract(archive, self.state / 'extract')

    def api_data(self, path):
        if path.endswith('/jobs?per_page=100'):
            return {'jobs': [{'name': 'Export main Blueprint', 'runner_name': 'inspire-kip126-web-01',
                              'conclusion': None, 'steps': [{'name': name, 'conclusion': 'success'}
                                                          for name in host.REQUIRED_STEPS]}]}
        return {**self.info, 'head_branch': 'main', 'head_repository': {'full_name': host.REPO},
                'path': '.github/workflows/pages.yml', 'event': 'push', 'status': 'in_progress',
                'conclusion': None}

    def test_main_run_and_successful_export_steps_are_required(self):
        _, request = self.stage()
        with patch.object(host, 'api', side_effect=self.api_data):
            host.verify_run(request)
        for field, value in [('head_branch', 'develop'), ('head_sha', 'b' * 40),
                             ('event', 'pull_request'), ('conclusion', 'cancelled'), ('run_attempt', 2)]:
            with self.subTest(field=field):
                def api(path):
                    value_json = self.api_data(path)
                    if '/jobs?' not in path:
                        value_json[field] = value
                    return value_json
                with patch.object(host, 'api', side_effect=api), self.assertRaises(ValueError):
                    host.verify_run(request)
        def lagging(path):
            value = self.api_data(path)
            if '/jobs?' in path:
                value['jobs'][0]['steps'].pop()
            return value
        with patch.object(host, 'api', side_effect=lagging), self.assertRaises(host.NotReady):
            host.verify_run(request)

    def test_transient_network_failure_keeps_queue_for_retry(self):
        key, _ = self.stage()
        with patch.object(host, 'verify_run'), patch.object(host, 'publish', side_effect=subprocess.TimeoutExpired('ssh', 1)):
            host.once()
        self.assertTrue((self.state / 'queue' / key / 'site.tar').is_file())
        self.assertFalse((self.spool / 'results' / f'{key}.json').exists())
        with patch.object(host, 'verify_run'), patch.object(host, 'publish', return_value={}):
            host.once()
        self.assertEqual(json.loads((self.spool / 'results' / f'{key}.json').read_text())['status'], 'success')

    def test_old_run_and_newer_main_cannot_replace_live_site(self):
        self.stage()
        host.atomic_json(self.state / 'deployed.json', {'run_id': 43, 'run_attempt': 1})
        with patch.object(host, 'verify_run'), patch.object(host, 'publish') as publish:
            host.once()
            publish.assert_not_called()
        self.assertEqual(json.loads((self.spool / 'results/42-1.json').read_text())['status'], 'failed')
        with patch.object(host, 'verify_run'), patch.object(host, 'api', return_value={'sha': 'b' * 40}):
            with self.assertRaisesRegex(ValueError, 'superseded'):
                host.prepare_activation(self.info)

    def test_health_failure_rolls_back_and_does_not_issue_success_receipt(self):
        key, request = self.stage()
        host.capture(key)
        previous = 'releases/' + 'b' * 40 + '-41'
        commands = []
        def run(args, **kwargs):
            commands.append(args)
            text = args[-1]
            return subprocess.CompletedProcess(args, 0, stdout='yes' if 'is-enabled' in text else previous)
        with patch.object(host, 'ssh_args', return_value=['ssh']), patch.object(host, 'run', side_effect=run), \
                patch.object(host, 'prepare_activation'), patch.object(host.time, 'sleep'), \
                patch.object(host.urllib.request, 'urlopen', side_effect=ValueError('unhealthy')):
            with self.assertRaisesRegex(ValueError, 'unhealthy'):
                host.publish(request, self.state / 'queue' / key / 'site.tar')
        self.assertTrue(any('/rollback' in str(command) and previous in str(command) for command in commands))
        self.assertFalse((self.state / 'deployed.json').exists())
        self.assertFalse((self.spool / 'results' / f'{key}.json').exists())

    def test_receipt_must_match_the_export_bytes(self):
        key, request = self.stage()
        host.receipt(key, {**request, 'sha256': 'b' * 64}, status='success')
        with self.assertRaisesRegex(ValueError, 'does not match'):
            client.wait_receipt(key, request, self.spool, timeout=1)


if __name__ == '__main__':
    unittest.main()
