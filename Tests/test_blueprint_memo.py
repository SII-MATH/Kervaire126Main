"""Keep correction records complete and their reading links honest."""
import json
import hashlib
from pathlib import Path
import sys
import tempfile
import unittest

import yaml

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
import blueprint_memo as memo


class MemoPresentationTests(unittest.TestCase):
    def test_all_authored_sections_are_present_without_claiming_global_completion(self):
        records = memo.read_corrections(ROOT / 'corrections.yaml')
        page = memo.render_memo(ROOT)
        self.assertEqual(len(records), 11)
        typing = next(r for r in records if r['id'] == 'original-statement-typing')
        self.assertEqual(typing['original']['statements'], ['2.17', '5.14'])
        self.assertEqual(typing['status']['kind'], 'partial')
        compactness = next(r for r in records if r['id'] == 'exact-extension-compactness')
        self.assertEqual(compactness['original']['statements'], ['2.20'])
        self.assertEqual(compactness['status']['kind'], 'revised')
        self.assertEqual(compactness['revision']['nodes'],
                         ['sem:ProofTools:complete-exact-extension-boundaries'])
        self.assertIn('形式化遗漏背景条件', compactness['problem'])
        self.assertIn('这不另行证明任意模型或固定 Standard 满足所列收敛条件', compactness['progress'])
        comparison = next(r for r in records if r['id'] == 'lambda-inversion-adams-comparison')
        self.assertEqual(comparison['original']['statements'], ['5.14'])
        self.assertEqual(comparison['status']['kind'], 'partial')
        self.assertEqual(comparison['revision']['nodes'],
                         ['sem:ProofTools:lambda-inversion-homotopy-extension'])
        self.assertEqual(comparison['revision']['definitions'],
                         ['sem:Literature:lambda-inversion-object-comparison',
                          'sem:Literature:lambda-inversion-adams-comparison'])
        self.assertIn('标准对象上的 hcomp producer 尚未构造', comparison['progress'])
        self.assertIn('不能算作标准比较已完成', comparison['progress'])
        for record in records:
            for key in memo.TEXT_FIELDS:
                self.assertIn(memo.markdown(record.get(key, '')), page)
        self.assertNotIn('主目标仍是', page)
        self.assertNotIn('MEMO.md', page)
        self.assertIn('修正版完整定理已公开并证明', page)
        self.assertIn('proposals/index.html#ProofTools-20261018-mh-finite-level-target', page)
        self.assertNotIn('以下为原文的完整英文陈述', page)
        self.assertNotIn('直接从 AimPaper 读取', page)
        self.assertNotIn('修正后的陈述以中文完整写出', page)
        self.assertIn(memo.markdown(typing['revision']['note']), page)
        self.assertNotIn('原两个待补位置保持不变', page)
        self.assertIn('没有本地证明洞', page)
        self.assertNotIn('href="local-history/', page)
        self.assertIn('source/KIP126/ProofTools/Paper/ExtensionDescent.lean.html#L83', page)

    def test_invalid_structure_cannot_silently_drop_or_replace_evidence(self):
        source = (ROOT / 'corrections.yaml').read_text()
        data = yaml.safe_load(source)
        cases = []
        unknown = json.loads(json.dumps(data)); unknown['corrections'][0]['typo'] = 'Evidence'
        cases.append(yaml.safe_dump(unknown))
        duplicate_id = json.loads(json.dumps(data)); duplicate_id['corrections'][1]['id'] = duplicate_id['corrections'][0]['id']
        cases.append(yaml.safe_dump(duplicate_id))
        invalid_line = json.loads(json.dumps(data)); invalid_line['corrections'][0]['original']['source_line'] = True
        cases.append(yaml.safe_dump(invalid_line))
        missing_gap = json.loads(json.dumps(data)); del missing_gap['corrections'][0]['revision']['note']
        cases.append(yaml.safe_dump(missing_gap))
        cases.append(source + '\nversion: 1\n')
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'corrections.yaml'
            for case in cases:
                with self.subTest(case=case[:100]):
                    path.write_text(case)
                    with self.assertRaises(ValueError):
                        memo.read_corrections(path)

    def test_originals_include_every_hypothesis_and_conclusion_from_actual_source(self):
        originals, refs = memo.original_statements(ROOT)
        page = memo.render_memo(ROOT)
        for number in ('6.12', '6.20', '5.10', '6.1', '1.5', '2.17', '2.20', '5.14', '7.9', '7.16', '7.18'):
            self.assertIn(memo.original_html(originals[number]['raw'], refs), page)
        self.assertIn('the differential in (3) has no crossing.', page)
        self.assertIn('for some $b', page)
        with self.assertRaisesRegex(ValueError, 'Unsupported original prose'):
            memo.original_html(r'Text \unsupported{essential hypothesis}', refs)

    def test_revised_statements_follow_the_actual_node_body_without_memo_edits(self):
        records = memo.read_corrections(ROOT / 'corrections.yaml')
        labels = {label for r in records for label in r['revision']['nodes'] + r['revision'].get('definitions', [])}
        project = {'entries': [{'label': label, 'title': label, 'body': 'Original node body.'} for label in labels]}
        page = memo.render_memo(ROOT, project)
        entry = next(e for e in project['entries'] if e['label'] == 'sem:ProofTools:generalized-leibniz-at-level')
        entry['body'] = 'Updated upstream statement with $k\\ge0$ and its full conclusion.'
        updated = memo.render_memo(ROOT, project)
        self.assertNotEqual(page, updated)
        self.assertIn(memo.original_html(entry['body'], {}), updated)
        self.assertIn(hashlib.sha256(entry['body'].encode()).hexdigest(), updated)
        self.assertNotIn('**候选陈述（待证）。**', (ROOT / 'corrections.yaml').read_text())

    def test_blueprint_targets_must_exist_without_exporting_the_old_markdown(self):
        records = memo.read_corrections(ROOT / 'corrections.yaml')
        labels = {link['node'] for r in records for link in r['links']}
        labels.update(label for r in records for label in r['revision']['nodes'] + r['revision'].get('definitions', []))
        labels = sorted(labels)
        payload = {'entries': [{'label': label, 'title': label, 'body': 'Actual node statement.'} for label in labels],
                   'customTabs': [{'id': 'memo', 'html': 'Staged placeholder'}]}
        with tempfile.TemporaryDirectory() as directory:
            out = Path(directory)
            (out / 'Kervaire126').mkdir()
            data = out / 'Kervaire126/data.json'
            data.write_text(json.dumps(payload))
            (out / 'Kervaire126/project.json').write_text(json.dumps(payload))
            (out / 'memo').mkdir()
            (out / 'memo/MEMO.md').write_text('Obsolete download')
            (out / 'memo/MEMO.md.gz').write_bytes(b'obsolete')
            result = memo.export_memo(ROOT, out)
            self.assertEqual(result['records'], 11)
            self.assertEqual(result['content_source'], 'corrections.yaml')
            self.assertFalse((out / 'memo/MEMO.md').exists())
            self.assertFalse((out / 'memo/MEMO.md.gz').exists())
            exported = json.loads(data.read_text())['customTabs'][0]['html']
            self.assertNotIn('节点正文将在', exported)
            for identity in ('exact-extension-compactness', 'lambda-inversion-adams-comparison'):
                record = next(r for r in records if r['id'] == identity)
                self.assertIn(memo.markdown(record['progress']), exported)
                for label in record['revision']['nodes'] + record['revision'].get('definitions', []):
                    self.assertIn(label, exported)
            data.write_text(json.dumps({'entries': [{'label': label} for label in labels[1:]]}))
            with self.assertRaisesRegex(ValueError, 'missing from the exported Blueprint'):
                memo.export_memo(ROOT, out)


if __name__ == '__main__':
    unittest.main()
