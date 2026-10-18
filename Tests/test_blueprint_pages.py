"""Evidence-seed integrity, archive safety and independent Pages publication."""
import importlib.util
import io
import json
from pathlib import Path
from types import SimpleNamespace
import tarfile
import tempfile
import unittest
from unittest.mock import patch

spec = importlib.util.spec_from_file_location('blueprint_pages',
    Path(__file__).resolve().parents[1] / 'scripts/blueprint-pages.py')
pages = importlib.util.module_from_spec(spec)
spec.loader.exec_module(pages)


def seed_files():
    inputs = {'KIP126/Main.lean': 'a' * 64}
    evidence = {'source_commit': '1' * 40, 'inputs': inputs,
        'input_fingerprint': pages.fingerprint(inputs), 'source_declarations': 1,
        'checks': {name: True for name in pages.REQUIRED_CHECKS},
        'full_project_build': {'status': 'passed', 'log_sha256': 'b' * 64,
                              'input_fingerprint': pages.fingerprint(inputs)}}
    snapshot = pages.json_bytes({'sources': {'result': {
        'file': 'KIP126/Main.lean', 'row': {'name': 'result'}}},
        'dependencies': {'result': []}, 'evidence': evidence})
    return {'verified-source-snapshot.json': snapshot,
            'verified-source-snapshot.sha256': pages.sha256(snapshot).encode(),
            'paper-binding-baseline/validation.json': pages.json_bytes(evidence)}


def write_archive(path, files, extra=()):
    with tarfile.open(path, 'w:gz', format=tarfile.USTAR_FORMAT) as archive:
        for name, content in files.items():
            member = tarfile.TarInfo(name)
            member.size = len(content)
            archive.addfile(member, io.BytesIO(content))
        for member, content in extra:
            archive.addfile(member, io.BytesIO(content) if content is not None else None)


class PagesSeedTests(unittest.TestCase):
    def test_valid_seed_round_trip_and_archive_hash_are_required(self):
        with tempfile.TemporaryDirectory() as directory:
            archive = Path(directory) / 'seed.tar.gz'
            expected = seed_files()
            write_archive(archive, expected)
            self.assertEqual(pages.read_seed(archive, pages.sha256(archive.read_bytes())), expected)
            with self.assertRaisesRegex(ValueError, 'checksum'):
                pages.read_seed(archive, '0' * 64)

    def test_unexpected_paths_duplicates_links_and_oversized_members_are_rejected(self):
        unsafe = []
        for name in ('../escape', '/escape', 'unexpected.json', 'verified-source-snapshot.json'):
            member = tarfile.TarInfo(name)
            member.size = 1
            unsafe.append((member, b'x'))
        for kind in (tarfile.SYMTYPE, tarfile.LNKTYPE, tarfile.DIRTYPE):
            member = tarfile.TarInfo('extra')
            member.type, member.linkname = kind, '/tmp/escape'
            unsafe.append((member, None))
        with tempfile.TemporaryDirectory() as directory:
            archive = Path(directory) / 'seed.tar.gz'
            for member, content in unsafe:
                with self.subTest(name=member.name, kind=member.type):
                    write_archive(archive, seed_files(), [(member, content)])
                    with self.assertRaises(ValueError):
                        pages.read_seed(archive, pages.sha256(archive.read_bytes()))
            write_archive(archive, seed_files())
            with patch.object(pages, 'MAX_MEMBER_BYTES', 64):
                with self.assertRaisesRegex(ValueError, 'unsafe'):
                    pages.read_seed(archive, pages.sha256(archive.read_bytes()))
            with patch.object(pages, 'MAX_TOTAL_BYTES', 64):
                with self.assertRaisesRegex(ValueError, 'expanded-size'):
                    pages.read_seed(archive, pages.sha256(archive.read_bytes()))

    def test_snapshot_checksum_and_verification_cannot_be_forged_by_inner_edits(self):
        files = seed_files()
        files['verified-source-snapshot.json'] += b' '
        with self.assertRaisesRegex(ValueError, 'snapshot checksum'):
            pages.validate_seed(files)
        files = seed_files()
        snapshot = json.loads(files['verified-source-snapshot.json'])
        snapshot['evidence']['checks']['lake_build'] = False
        files['verified-source-snapshot.json'] = pages.json_bytes(snapshot)
        files['verified-source-snapshot.sha256'] = pages.sha256(files['verified-source-snapshot.json']).encode()
        with self.assertRaisesRegex(ValueError, 'verification checks'):
            pages.validate_seed(files)

    def test_installation_refuses_symlink_destinations(self):
        with tempfile.TemporaryDirectory() as directory, patch.object(pages, 'ROOT', Path(directory)):
            root = Path(directory)
            (root / '.lake').mkdir()
            (root / 'outside').mkdir()
            (root / '.lake/blueprint').symlink_to(root / 'outside', target_is_directory=True)
            with self.assertRaisesRegex(ValueError, 'symlink'):
                pages.install_seed(seed_files())
            self.assertEqual(list((root / 'outside').iterdir()), [])

    def test_only_fixed_repository_release_https_urls_are_downloaded(self):
        for url in ('http://github.com/SII-MATH/Kervaire126Main/releases/download/v1/seed.tar.gz',
                    'https://example.com/seed.tar.gz',
                    'https://github.com/other/repo/releases/download/v1/seed.tar.gz',
                    'https://github.com/SII-MATH/Kervaire126Main/releases/latest/download/seed.tar.gz'):
            with self.subTest(url=url), self.assertRaisesRegex(ValueError, 'fixed HTTPS'):
                pages.download_seed(url, Path('/unused'))

    def test_receipt_branch_uses_actions_ref_or_actual_local_branch(self):
        with patch.dict(pages.os.environ, {'GITHUB_REF_NAME': 'main'}, clear=True), \
                patch.object(pages.subprocess, 'check_output') as git:
            self.assertEqual(pages.source_branch(), 'main')
            git.assert_not_called()
        with patch.dict(pages.os.environ, {}, clear=True), \
                patch.object(pages.subprocess, 'check_output', return_value='configure-main-pages\n'):
            self.assertEqual(pages.source_branch(), 'configure-main-pages')

    def test_refresh_failure_falls_back_without_claiming_full_build_success(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            site = root / '_site'
            site.mkdir()
            (root / 'chapter.tex').write_text('current blueprint')
            site_inputs = {'chapter.tex': pages.sha256((root / 'chapter.tex').read_bytes())}
            validation = {'source_commit': '1' * 40, 'checks': {'mappings_verified': True},
                'site_inputs': site_inputs, 'site_input_fingerprint': pages.fingerprint(site_inputs),
                'unverified_source_labels': ['decl:changed'],
                'full_project_build': {'status': 'unknown'}}
            (site / 'validation.json').write_bytes(pages.json_bytes(validation))
            archive = root / 'seed.tar.gz'
            write_archive(archive, seed_files())

            def download(_url, destination):
                destination.write_bytes(archive.read_bytes())

            with patch.object(pages, 'ROOT', root), \
                    patch.object(pages, 'download_seed', side_effect=download), \
                    patch.object(pages.subprocess, 'run', side_effect=[SimpleNamespace(returncode=1), SimpleNamespace(returncode=0)]) as run, \
                    patch.object(pages.subprocess, 'check_output', return_value='2' * 40 + '\n'), \
                    patch.dict(pages.os.environ, {'GITHUB_REPOSITORY': 'SII-MATH/Kervaire126Main', 'GITHUB_RUN_ID': '123',
                                                 'GITHUB_REF_NAME': 'configure-main-pages'}, clear=True):
                pages.publish('https://github.com/SII-MATH/Kervaire126Main/releases/download/v1/seed.tar.gz',
                              pages.sha256(archive.read_bytes()))
            self.assertEqual(len(run.call_args_list), 2)
            self.assertIn('--refresh-source-evidence', run.call_args_list[0].args[0])
            self.assertNotIn('--refresh-source-evidence', run.call_args_list[1].args[0])
            self.assertTrue(run.call_args_list[1].kwargs['check'])
            receipt = json.loads((site / 'pages-deployment.json').read_text())
            self.assertEqual(receipt['source_branch'], 'configure-main-pages')
            self.assertEqual(receipt['source_commit'], '2' * 40)
            self.assertEqual(receipt['baseline_source_commit'], '1' * 40)
            self.assertEqual(receipt['unverified_source_labels'], ['decl:changed'])
            self.assertFalse(receipt['refreshed_all_mathematical_source_evidence'])
            self.assertEqual(json.loads((site / 'validation.json').read_text())['full_project_build']['status'], 'unknown')


if __name__ == '__main__':
    unittest.main()
