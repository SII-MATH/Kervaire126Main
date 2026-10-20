"""Authoring metadata must stay accessible without entering mathematical prose."""
from pathlib import Path
import importlib.util
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
from blueprint_annotations import authoring_notes, sync_authoring_notes
from hgraph.graph import Graph, node_id
from hgraph.sync import parse_blueprint, read_blueprint


class AnnotationTests(unittest.TestCase):
    def fixture(self, root):
        bp = root / 'blueprint'
        (bp / 'chapters').mkdir(parents=True)
        (bp / 'content.tex').write_text('\\input{chapters/Main.tex}\n')
        (bp / 'chapters/Main.tex').write_text(
            '\\chapter{Main}\n% Blueprint note: The same fixed sphere is used.\n'
            '% Blueprint note: Fixed source: \\cite{Source}.\n'
            '\\begin{theorem}[A mathematical identity]\n\\label{paper:1.1}\n'
            'For every $x$, $x=x$.\n% Correspondence: Partial correspondence.\n'
            '% Blueprint note: The general comparison remains unproved.\n'
            '\\sketch\n\\end{theorem}\n')
        (bp / 'references.bib').write_text(
            '@article{Source, title={Source theorem}, author={A}, year={2026}, '
            'url={https://example.org/theorem}\n}\n')
        graph = Graph.open(root)
        target = node_id('bp', 'paper:1.1')
        graph.add_node('A mathematical identity', id=target, type='tex', content='For every $x$, $x=x$.')
        return graph, target

    def test_notes_are_native_comments_and_not_statement_body(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            graph, target = self.fixture(root)
            self.assertEqual(sync_authoring_notes(graph, root), 1)
            notes = graph.comments(target)
            self.assertEqual(len(notes), 1)
            self.assertIn('general comparison remains unproved', notes[0].content)
            self.assertIn('[Source](https://example.org/theorem)', notes[0].content)
            self.assertIn('same fixed sphere', notes[0].content)
            rows, _ = parse_blueprint(read_blueprint(root / 'blueprint/content.tex'))
            self.assertNotIn('Correspondence', rows[0]['body'])
            self.assertNotIn('unproved', rows[0]['body'])
            self.assertTrue(rows[0]['sketch'])

    def test_repeat_and_update_preserve_human_comments_and_node(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            graph, target = self.fixture(root)
            graph.add_comment(target, 'Human review stays here.', author='reviewer')
            node_before = graph.get_node(target)
            self.assertEqual(sync_authoring_notes(graph, root), 1)
            self.assertEqual(sync_authoring_notes(graph, root), 0)
            path = root / 'blueprint/chapters/Main.tex'
            path.write_text(path.read_text().replace('remains unproved', 'still requires a bridge'))
            self.assertEqual(sync_authoring_notes(graph, root), 1)
            notes = graph.comments(target)
            self.assertEqual(len(notes), 2)
            self.assertEqual(notes[0].content, 'Human review stays here.')
            self.assertIn('still requires a bridge', notes[1].content)
            self.assertEqual(graph.get_node(target), node_before)

    def test_notes_do_not_make_native_structure_warnings_fatal(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            graph, _ = self.fixture(root)
            path = root / 'blueprint/chapters/Main.tex'
            path.write_text(path.read_text().replace('paper:1.1', 'paper:missing'))
            self.assertEqual(sync_authoring_notes(graph, root), 0)
            path.write_text(path.read_text() * 2)
            self.assertEqual(set(authoring_notes(root)), {'paper:missing'})


if __name__ == '__main__':
    unittest.main()
