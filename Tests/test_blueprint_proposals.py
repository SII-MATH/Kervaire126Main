"""Proposal provenance, approval boundaries and native export integration."""
import hashlib
import json
import shutil
from pathlib import Path
import sys
import tempfile
import unittest

import yaml

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
import blueprint_proposals as proposals


class InterfaceProposalTests(unittest.TestCase):
    def test_migrated_reports_preserve_complete_metadata_and_body(self):
        reports = proposals.read_reports(ROOT)
        self.assertGreaterEqual(len(reports), 17)
        self.assertEqual(sum('archived_from' in r['meta'] for r in reports), 17)
        # Migration has no runtime dependency on the ignored archive. When it is
        # present, also compare every original field and the whole report body.
        for report in reports:
            m = report['meta']
            if 'archived_from' not in m:
                continue
            self.assertRegex(m['archived_sha256'], r'^[a-f0-9]{64}$')
            archived = ROOT / m['archived_from']
            if archived.exists():
                self.assertEqual(hashlib.sha256(archived.read_bytes()).hexdigest(), m['archived_sha256'])
                _, front, body = archived.read_text().split('---', 2)
                for key, value in yaml.safe_load(front).items():
                    self.assertEqual(m[key], value)
                self.assertEqual(report['body'], body.strip())
        gl = next(r for r in reports if r['meta']['issue_id'] == 'ProofTools-20261018-GL-fixed-object-counterexample')
        self.assertEqual(gl['meta']['status'], 'pending-human-review')
        self.assertIsNone(gl['meta']['human_decision'])
        self.assertIn('no Lean negation certificate', gl['meta']['evidence_level'])

    def test_invalid_reports_and_unjustified_approvals_fail(self):
        template = (ROOT / 'interface-proposals/TEMPLATE.md').read_text()
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            path = root / 'interface-proposals/Main/example/report.md'
            path.parent.mkdir(parents=True)
            for content in (template.replace('status: draft', 'status: approved-interface-change'),
                            template.replace('status: draft', 'status: typo'),
                            template.replace('targets:', 'status: draft\ntargets:'),
                            template.replace('independent_of_discoverer_and_implementer: true',
                                             'independent_of_discoverer_and_implementer: false'),
                            template.replace('human_decision: null\n', ''),
                            template.replace('targets:\n  - KIP126.Main.example', 'targets: []')):
                with self.subTest(content=content[:140]):
                    path.write_text(content)
                    with self.assertRaises(ValueError):
                        proposals.read_reports(root)
            path.write_text(template)
            self.assertEqual(len(proposals.read_reports(root)), 1)
            duplicate = path.parent.parent / 'duplicate/report.md'
            duplicate.parent.mkdir()
            duplicate.write_text(template)
            with self.assertRaisesRegex(ValueError, 'duplicate issue_id'):
                proposals.read_reports(root)

    def test_unavailable_evidence_and_unsafe_links_are_not_published(self):
        text = ('[external](https://example.com/paper) '
                '[unsafe](javascript:alert) [relative](evidence/not-present.json) '
                '[archived](local-history/missing.md) '
                '[node](#/Kervaire126#paper:6.1)\n\n<script>alert(1)</script>')
        rendered = proposals.markdown(text, 'interface-proposals/Main/x/report.md', ROOT)
        self.assertIn('href="https://example.com/paper"', rendered)
        self.assertIn('data-blueprint="paper:6.1"', rendered)
        self.assertNotIn('href="javascript:', rendered)
        self.assertNotIn('href="evidence/', rendered)
        self.assertNotIn('href="local-history/', rendered)
        self.assertNotIn('<script>', rendered)
        self.assertIn('本地证据', rendered)

    def test_code_and_tables_preserve_formal_signatures(self):
        rendered = proposals.markdown('```lean\n∀ x, x < 2 → P x\n```\n\n'
                                     '| 原 | 新 |\n| --- | --- |\n| `P x` | `Q x` |',
                                     'interface-proposals/Main/x/report.md', ROOT)
        self.assertIn('<pre><code>∀ x, x &lt; 2 → P x</code></pre>', rendered)
        self.assertIn('<table>', rendered)
        self.assertIn('<code>Q x</code>', rendered)

    def test_export_is_self_contained_and_leaves_mathematical_payloads_unchanged(self):
        with tempfile.TemporaryDirectory() as folder:
            root, out = Path(folder) / 'source', Path(folder) / 'export'
            # Simulate a fresh checkout with no ignored historical archive.
            shutil.copytree(ROOT / 'interface-proposals', root / 'interface-proposals')
            (root / 'site').mkdir()
            for name in ('proposals.html', 'proposals.css', 'proposals.js'):
                shutil.copyfile(ROOT / 'site' / name, root / 'site' / name)
            (root / 'docs').mkdir()
            shutil.copyfile(ROOT / 'docs/interface-proposals.md', root / 'docs/interface-proposals.md')
            out.mkdir()
            (out / 'assets').mkdir()
            (out / 'assets/katexLoader-test.js').write_text('export default ()=>{}')
            (out / 'assets/katexLoader-test.css').write_text('')
            (out / 'Kervaire126').mkdir()
            payload = json.dumps({'entries': [{'id': 'unchanged', 'lean_status': 'sorry'}]})
            (out / 'Kervaire126/data.json').write_text(payload)
            result = proposals.export_proposals(root, out)
            self.assertEqual(result['reports'], len(proposals.read_reports(root)))
            self.assertEqual((out / 'Kervaire126/data.json').read_text(), payload)
            self.assertIn('../assets/katexLoader-test.js', (out / 'proposals/index.html').read_text())
            self.assertTrue((out / 'proposals/TEMPLATE.md').is_file())
            for report in proposals.read_reports(root):
                self.assertEqual((out / 'proposals/reports' / report['path']).read_text(), report['raw'])
            proposals.stage_proposals(root, out / 'staged')
            self.assertIn('src="proposals/index.html"', (out / 'staged/site/proposals.html').read_text())


if __name__ == '__main__':
    unittest.main()
