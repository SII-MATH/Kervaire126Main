"""Research metadata, safe evidence exports, and the two canonical reports."""
from datetime import date
from pathlib import Path
import sys
import tempfile
import unittest

import yaml

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
import blueprint_proposals as proposals
import blueprint_research as research


def metadata(identity='example', **changes):
    result = {
        'result_id': identity,
        'title': 'A conditional mathematical statement',
        'summary': 'The precise conclusion and remaining hypothesis.',
        'topic': 'theta6',
        'status': 'reviewed-informal',
        'evidence_level': 'Independently reviewed informal argument',
        'formalization_status': 'not-formalized',
        'novelty_status': 'not-assessed',
        'baseline_commit': '34fb925fd3c30304832e40e1c87938ff00908b67',
        'updated': '2026-10-22',
        'authors': ['proof-worker'],
        'reviewers': ['independent-reviewer'],
    }
    result.update(changes)
    return result


def write_report(root, meta=None, body='# Statement\n\nA result with $h_6^2$.', directory=None):
    meta = metadata() if meta is None else meta
    path = root / 'research/results' / (directory or meta['result_id']) / 'report.md'
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text('---\n' + yaml.safe_dump(meta, sort_keys=False) + '---\n' + body + '\n',
                    encoding='utf-8')
    return path


def site_fixture(root, out=None):
    (root / 'site').mkdir(exist_ok=True)
    (root / 'site/research.html').write_text(
        '<!doctype html><title>Research</title><!-- RESEARCH_MATH -->'
        '<main><span><!-- RESEARCH_COUNT --></span><!-- RESEARCH_CARDS --></main>',
        encoding='utf-8')
    for name in ('research.css', 'research.js', 'proposals.css'):
        (root / 'site' / name).write_text('/* fixture */', encoding='utf-8')
    if out:
        (out / 'assets').mkdir(parents=True)
        (out / 'assets/katexLoader-fixture.js').write_text('export default ()=>{}', encoding='utf-8')
        (out / 'assets/katexLoader-fixture.css').write_text('/* fixture */', encoding='utf-8')


class ResearchReportTests(unittest.TestCase):
    def test_metadata_accepts_free_topics_and_keeps_statuses_separate(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            path = write_report(root, metadata(topic='A new research direction'))
            reports = research.read_reports(root)
            self.assertEqual(len(reports), 1)
            self.assertEqual(reports[0]['meta']['topic'], 'A new research direction')
            self.assertEqual(reports[0]['path'], 'research/results/example/report.md')
            self.assertEqual(reports[0]['raw'], path.read_text())
            self.assertEqual(reports[0]['meta']['formalization_status'], 'not-formalized')
            write_report(root, metadata(status='draft', reviewers=[]))
            self.assertEqual(research.read_reports(root)[0]['meta']['reviewers'], [])

    def test_missing_or_mistyped_metadata_and_bad_dates_fail(self):
        invalid = [
            {'title': 1}, {'summary': []}, {'topic': ' '}, {'evidence_level': None},
            {'status': 'approved'}, {'formalization_status': 'verified'},
            {'novelty_status': 'proven-new'}, {'baseline_commit': ''},
            {'updated': date(2026, 10, 22)}, {'updated': '20261022'},
            {'updated': '2026-02-30'}, {'updated': '2026-10-22T00:00:00'},
            {'authors': 'worker'}, {'authors': []}, {'authors': [False]},
            {'reviewers': ['']}, {'reviewers': []}, {'reviewers': None},
        ]
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            for changes in invalid:
                with self.subTest(changes=changes):
                    write_report(root, metadata(**changes))
                    with self.assertRaises(ValueError):
                        research.read_reports(root)
            for field in metadata():
                with self.subTest(missing=field):
                    meta = metadata()
                    del meta[field]
                    write_report(root, meta, directory='example')
                    with self.assertRaises(ValueError):
                        research.read_reports(root)

    def test_duplicate_keys_identifiers_directory_and_empty_body_fail(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            path = write_report(root)
            original = path.read_text()
            path.write_text(original.replace('title:', 'result_id: example\ntitle:', 1))
            with self.assertRaisesRegex(ValueError, 'Duplicate or invalid research key'):
                research.read_reports(root)
            path.write_text(original)
            write_report(root, directory='second')
            with self.assertRaisesRegex(ValueError, 'duplicate result_id'):
                research.read_reports(root)
            (root / 'research/results/second/report.md').unlink()
            write_report(root, metadata(result_id='mismatch'), directory='example')
            with self.assertRaisesRegex(ValueError, 'directory'):
                research.read_reports(root)
            write_report(root, body='')
            with self.assertRaisesRegex(ValueError, 'empty report body'):
                research.read_reports(root)

    def test_canonical_reports_cannot_be_symlinks_or_have_symlink_ancestors(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            path = write_report(root)
            external = root / 'original.md'
            external.write_bytes(path.read_bytes())
            path.unlink()
            path.symlink_to(external)
            with self.assertRaisesRegex(ValueError, 'symlinks'):
                research.read_reports(root)
            path.unlink()
            path.parent.rmdir()
            directory = root / 'external-example'
            directory.mkdir()
            (directory / 'report.md').write_bytes(external.read_bytes())
            path.parent.symlink_to(directory, target_is_directory=True)
            with self.assertRaisesRegex(ValueError, 'symlinks'):
                research.read_reports(root)

    def test_markdown_reuse_escapes_html_and_keeps_proposal_defaults(self):
        text = ('# Heading\n\n<script>alert(1)</script>\n\n'
                '| Claim | Evidence |\n| --- | --- |\n| `P` | $x^2$ |\n\n'
                '```lean\nx < 2\n```\n\n[paper](https://example.org/paper)')
        rendered = research.markdown(text, 'research/results/example/report.md', ROOT)
        self.assertNotIn('<script>', rendered)
        self.assertIn('<table>', rendered)
        self.assertIn('<pre><code>x &lt; 2</code></pre>', rendered)
        self.assertIn('href="https://example.org/paper"', rendered)
        self.assertEqual(proposals.markdown(text, 'docs/example.md', ROOT),
                         proposals.markdown(text, 'docs/example.md', ROOT,
                                            link_renderer=proposals.reading_link))
        self.assertEqual(proposals.reading_link.__module__, 'blueprint_proposals')

    def test_rendered_cards_escape_metadata_and_expose_downloads_and_boundaries(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            site_fixture(root)
            write_report(root, metadata(title='<img src=x>', summary='A & B', topic='theta6" autofocus'))
            rendered = research.render_reports(root)
            self.assertIn('class="research-card" id="example"', rendered)
            self.assertIn('data-topic="theta6&quot; autofocus"', rendered)
            self.assertIn('data-status="reviewed-informal"', rendered)
            self.assertIn('&lt;img src=x&gt;', rendered)
            self.assertNotIn('<img src=x>', rendered)
            self.assertIn('A &amp; B', rendered)
            self.assertIn('尚未形式化', rendered)
            self.assertIn('新颖性未核查', rendered)
            self.assertIn('展开完整报告', rendered)
            self.assertIn('来源与复核记录', rendered)
            self.assertIn('下载完整报告', rendered)
            self.assertIn('class="proposal-report"', rendered)
            self.assertIn('class="proposal-body"', rendered)
            self.assertIn('class="research-permalink" href="#example"', rendered)
            self.assertIn('href="reports/research/results/example/report.md" download', rendered)
            self.assertNotIn('RESEARCH_CARDS', rendered)
            self.assertNotIn('RESEARCH_COUNT', rendered)

    def test_export_allowlists_evidence_and_preserves_canonical_bytes(self):
        with tempfile.TemporaryDirectory() as folder:
            root, out = Path(folder) / 'source', Path(folder) / 'export'
            root.mkdir()
            site_fixture(root, out)
            report = write_report(root)
            evidence = report.parent / 'evidence'
            evidence.mkdir()
            for suffix in research.EVIDENCE_SUFFIXES:
                (evidence / ('valid' + suffix)).write_text('small evidence\n', encoding='utf-8')
            (evidence / 'too-large.txt').write_bytes(b'x' * (research.MAX_EVIDENCE_BYTES + 1))
            (evidence / 'unsupported.html').write_text('<script>unsafe</script>')
            (root / 'secret.txt').write_text('private')
            (evidence / 'outside.txt').symlink_to(root / 'secret.txt')
            (evidence / 'inside.txt').symlink_to(evidence / 'valid.txt')
            (evidence / 'linked-dir').symlink_to(evidence, target_is_directory=True)
            links = [
                ('python', 'evidence/valid.py'), ('json', 'evidence/valid.json'),
                ('absolute', str(evidence / 'valid.txt')), ('parent', '../../../secret.txt'),
                ('encoded-parent', '%2e%2e/secret.txt'), ('symlink', 'evidence/outside.txt'),
                ('inside-symlink', 'evidence/inside.txt'), ('symlink-dir', 'evidence/linked-dir/valid.txt'),
                ('large', 'evidence/too-large.txt'), ('html', 'evidence/unsupported.html'),
                ('unsafe', 'javascript:alert'), ('data', 'data:text/html,unsafe'),
            ]
            body = '\n\n'.join(f'[{label}]({url})' for label, url in links)
            write_report(root, body=body)
            # CRLF canonical input must be downloadable byte-for-byte.
            report.write_bytes(report.read_bytes().replace(b'\n', b'\r\n'))
            payload = out / 'untouched.json'
            payload.write_text('{"lean_status":"sorry"}')
            result = research.export_research(root, out)
            self.assertEqual(result['reports'], 1)
            self.assertEqual(result['source'], research.SOURCE)
            self.assertIn('not verified proof states', result['scope'])
            self.assertEqual(payload.read_text(), '{"lean_status":"sorry"}')
            exported = out / 'research'
            self.assertEqual((exported / 'reports/research/results/example/report.md').read_bytes(),
                             report.read_bytes())
            for suffix in research.EVIDENCE_SUFFIXES:
                self.assertTrue((exported / 'reports/research/results/example/evidence' /
                                 ('valid' + suffix)).is_file())
            for name in ('too-large.txt', 'unsupported.html', 'outside.txt', 'inside.txt', 'linked-dir'):
                self.assertFalse((exported / 'reports/research/results/example/evidence' / name).exists())
            content = (exported / 'index.html').read_text()
            self.assertIn('href="reports/research/results/example/evidence/valid.py" download', content)
            self.assertIn('href="reports/research/results/example/evidence/valid.json" download', content)
            for label, _ in links[2:]:
                self.assertRegex(content, rf'>{label} <small>.*?</small></span>')
            self.assertNotIn('href="javascript:', content)
            self.assertNotIn('href="data:', content)
            self.assertIn('../assets/katexLoader-fixture.js', content)
            self.assertIn('../assets/katexLoader-fixture.css', content)
            self.assertNotIn('RESEARCH_MATH', content)
            self.assertNotIn('cdn.', content)
            self.assertIn('window.renderProposalMath', content)
            for name in ('research.css', 'research.js', 'proposals.css'):
                self.assertTrue((exported / name).is_file())

    def test_export_requires_local_math_and_staging_uses_research_frame(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            site_fixture(root)
            write_report(root)
            with self.assertRaisesRegex(ValueError, 'local hgraph KaTeX'):
                research.export_research(root, root / 'export')
            research.stage_research(root, root / 'stage')
            frame = (root / 'stage/site/research.html').read_text()
            self.assertIn('class="research-frame"', frame)
            self.assertIn('title="Research"', frame)
            self.assertIn('src="research/index.html"', frame)

    def test_canonical_cross_report_links_do_not_allow_general_parent_paths(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            first = write_report(root)
            write_report(root, metadata('other'))
            (first.parent.parent / 'notes.txt').write_text('not a canonical report')
            (first.parent / 'alias').symlink_to(first.parent.parent / 'other', target_is_directory=True)
            body = ('[sibling](../other/report.md) [encoded](%2e%2e/other/report.md) '
                    '[anchor](#other) [unknown](../missing/report.md) '
                    '[not-report](../notes.txt) [alias](alias/report.md) '
                    '[symlink-parent](alias/../other/report.md) '
                    f'[absolute]({first.parent.parent / "other/report.md"})')
            rendered = research.markdown(body, 'research/results/example/report.md', root)
            for label in ('sibling', 'encoded', 'anchor'):
                self.assertIn(f'<a href="#other">{label}</a>', rendered)
            for label in ('unknown', 'not-report', 'alias', 'symlink-parent', 'absolute'):
                self.assertRegex(rendered, rf'>{label} <small>.*?</small></span>')

    def test_two_live_reports_are_canonical_and_explicitly_not_formalized(self):
        reports = {report['meta']['result_id']: report for report in research.read_reports(ROOT)}
        for identity, topic in [('20261022-theta5-products', 'theta5'),
                                ('20261022-theta6-moore', 'theta6')]:
            self.assertIn(identity, reports)
            report = reports[identity]
            self.assertEqual(report['meta']['topic'], topic)
            self.assertEqual(report['meta']['formalization_status'], 'not-formalized')
            self.assertTrue(report['body'])
            self.assertTrue((ROOT / report['path']).is_file())
            self.assertNotIn('local-history', report['path'])


if __name__ == '__main__':
    unittest.main()
