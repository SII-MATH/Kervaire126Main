"""Check that authored proofs reach the native reader as separate proof blocks."""
from pathlib import Path
import tempfile
import unittest

from hgraph.sync import parse_blueprint, parse_document, read_blueprint

ROOT = Path(__file__).resolve().parents[1]


def proof_blocks(text):
    result = {}
    for chapter in parse_document(text):
        preceding = None
        for block in chapter['blocks']:
            if block['t'] == 'stmt':
                preceding = block['label']
            elif block['t'] == 'proof':
                if preceding in result:
                    raise AssertionError(f'Duplicate proof for {preceding}')
                result[preceding] = block['tex']
    return result


class NativeProofPresentationTests(unittest.TestCase):
    def test_every_aimpaper_result_has_a_visible_separate_proof(self):
        text = read_blueprint(ROOT / 'blueprint/content.tex')
        statements, proofs = parse_blueprint(text)
        visible = proof_blocks(text)
        # A proof nested in a statement is parsed for metadata but skipped by
        # the native reader, so checking parse_blueprint alone is insufficient.
        self.assertEqual(len(visible), len(proofs))
        targets = [row for row in statements
                   if row['label'].startswith('paper:')
                   and row['content_type'] != 'definition']
        self.assertEqual(len(targets), 54)
        for row in targets:
            with self.subTest(label=row['label']):
                self.assertIn(row['label'], visible)
                self.assertTrue(visible[row['label']].strip())
                self.assertNotIn(r'\begin{proof}', row['body'])
                self.assertNotIn(r'\emph{Proof.}', row['body'])

    def test_existing_main_proofs_are_visible_and_outside_the_statement(self):
        text = read_blueprint(ROOT / 'blueprint/content.tex')
        visible = proof_blocks(text)
        statements, _ = parse_blueprint(text)
        by_label = {row['label']: row for row in statements}
        for label in ('sem:Main:remark-7.5', 'sem:Main:any-choice-criterion',
                      'paper:1.5', 'paper:7.8', 'paper:7.9'):
            with self.subTest(label=label):
                self.assertIn(label, visible)
                self.assertNotIn(r'\emph{Proof.}', by_label[label]['body'])
        self.assertIn(r'q_n(a)=0', visible['sem:Main:any-choice-criterion'])
        self.assertIn(r'\lambda^{10}a', visible['paper:7.8'])
        self.assertIn(r'\lambda^5\eta(\theta_5 b)=0', visible['paper:7.9'])
        self.assertNotIn('sem:Main:weak-representative-route', by_label)
        # The retained incompatibility proof must remain independent of the
        # two conditional statements now deduced from it.
        from hgraph.sync import _assoc_proofs
        _, proofs = parse_blueprint(text)
        used = set(by_label['paper:7.9']['uses']) | _assoc_proofs(statements, proofs)['paper:7.9']
        self.assertFalse({'paper:7.16', 'paper:7.18', 'paper:7.9'} & used)

    def test_web_copy_keeps_proofs_attached_and_gap_explanations_visible(self):
        from blueprint_paper import prepare_web_blueprint
        authored = proof_blocks(read_blueprint(ROOT / 'blueprint/content.tex'))
        with tempfile.TemporaryDirectory() as directory:
            web = prepare_web_blueprint(ROOT, Path(directory) / 'web')
            rendered = proof_blocks(read_blueprint(web / 'content.tex'))
        self.assertEqual(set(authored), set(rendered))
        for label in authored:
            with self.subTest(label=label):
                self.assertTrue(rendered[label].strip())
                self.assertNotIn(r'\xymatrix', rendered[label])
        # These source arguments have known missing steps. A proof panel must
        # not erase those qualifications or present them as completed proofs.
        for label, qualification in {
            'sem:ProofTools:finite-lambda-division': 'low-filtration',
            'paper:6.12': 'No $\\lambda$ layer is cancelled',
            'paper:6.20': 'domain condition',
            'paper:6.23': 'not the full printed corollary',
            'paper:7.16': 'still the pending step',
            'paper:7.18': 'remaining responsibility',
        }.items():
            with self.subTest(label=label):
                self.assertIn(qualification, rendered[label])


if __name__ == '__main__':
    unittest.main()
