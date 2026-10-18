"""Exercise the actual native synchronizer without a repository evidence layer."""
import importlib.util
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from hgraph.analysis import Analysis
from hgraph.graph import Graph, node_id

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('native_blueprint_builder', ROOT / 'scripts/build-blueprint.py')
builder = importlib.util.module_from_spec(spec)
spec.loader.exec_module(builder)


class NativeDependencyTests(unittest.TestCase):
    def setUp(self):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)
        (self.root / 'KIP126/Main').mkdir(parents=True)
        (self.root / 'blueprint').mkdir()
        (self.root / 'KIP126/Main/Result.lean').write_text(
            'module\nnamespace KIP126.Main\n'
            'public theorem pending : True := by sorry\n'
            'public theorem result : True := pending\n'
            'public theorem extra : True := by trivial\nend KIP126.Main\n')

    def sync(self, text):
        (self.root / 'blueprint/content.tex').write_text(text)
        with patch.object(builder, 'ROOT', self.root):
            report = builder.sync_project(self.root)
        return Graph.open(self.root), report

    def test_lean_dependency_does_not_invent_a_mathematical_edge_or_rewrite_local_status(self):
        graph, _ = self.sync(
            r'\chapter{Main}\begin{theorem}\label{pending}\lean{KIP126.Main.pending}P.\end{theorem}'
            r'\begin{theorem}\label{result}\lean{KIP126.Main.result}R.\end{theorem}')
        result = node_id('bp', 'result')
        self.assertEqual(graph.get_node(result).meta['lean_status'], 'lean_ok')
        self.assertEqual(graph.edges(source=result, hard=True), [])
        self.assertTrue(Analysis(graph).closed[result])
        self.assertNotIn('internal_obligations', graph.get_node(result).meta)

    def test_ordinary_statement_and_proof_uses_control_native_closure(self):
        graph, _ = self.sync(
            r'\chapter{Main}\begin{theorem}\label{pending}\label{alias}\lean{KIP126.Main.pending}P.\end{theorem}'
            r'\begin{theorem}\label{result}\lean{KIP126.Main.result}R.\end{theorem}'
            r'\begin{proof}\uses{alias}The proof uses P.\end{proof}')
        result, pending = node_id('bp', 'result'), node_id('bp', 'pending')
        self.assertEqual([edge.target for edge in graph.edges(source=result, hard=True)], [pending])
        self.assertFalse(Analysis(graph).closed[result])
        self.assertEqual(Analysis(graph).states[result], 'formalized_open')
        graph, _ = self.sync(
            r'\chapter{Main}\begin{theorem}\label{pending}\lean{KIP126.Main.pending}P.\end{theorem}'
            r'\begin{theorem}\label{result}\lean{KIP126.Main.result}\uses{pending}R.\end{theorem}')
        self.assertFalse(Analysis(graph).closed[result])

    def test_partial_multibinding_uses_and_unformalized_statements_are_native(self):
        graph, _ = self.sync(
            r'\chapter{Main}\begin{theorem}\label{group}\lean{KIP126.Main.pending,KIP126.Main.extra}P and E.\end{theorem}'
            r'\begin{theorem}\label{informal}\uses{group}A mathematical claim.\end{theorem}')
        group, informal = node_id('bp', 'group'), node_id('bp', 'informal')
        self.assertEqual(len(graph.edges(source=group, type='formalizes')), 2)
        self.assertEqual(graph.get_node(informal).meta['lean_status'], 'empty')
        self.assertEqual([edge.target for edge in graph.edges(source=informal, hard=True)], [group])

    def test_native_warnings_are_reported_without_a_fatal_repository_policy(self):
        graph, report = self.sync(r'\chapter{Main}\begin{theorem}\label{a}\uses{unknown}A.\end{theorem}')
        self.assertTrue(graph.has_node(node_id('bp', 'a')))
        self.assertTrue(any('unknown' in warning for warning in report['warnings']))
        self.assertFalse((self.root / '.lake/blueprint/verified-source-snapshot.json').exists())

    def test_native_mathlibok_and_same_chapter_cycles_are_accepted(self):
        graph, _ = self.sync(
            r'\chapter{Main}\begin{theorem}\label{a}\lean{Nat.add_comm}\mathlibok\uses{b}A.\end{theorem}'
            r'\begin{theorem}\label{b}\lean{Nat.mul_comm}\mathlibok\uses{a}B.\end{theorem}')
        self.assertEqual(graph.get_node(node_id('bp', 'a')).meta['lean_status'], 'mathlib_ok')
        self.assertTrue(Analysis(graph).closed[node_id('bp', 'b')])

    def test_retired_dependency_uses_native_reconciliation_even_with_an_attachment(self):
        first = (r'\chapter{Main}\begin{theorem}\label{a}\uses{b}A.\end{theorem}'
                 r'\begin{theorem}\label{b}B.\end{theorem}')
        graph, _ = self.sync(first)
        edge = graph.edges(source=node_id('bp', 'a'), hard=True)[0]
        # Native edge attachments live in the edge directory, not node comments.
        attachment = graph.base / 'edges' / edge.id / 'comment-1.md'
        attachment.parent.mkdir()
        attachment.write_text('A note on the old dependency.')
        graph, _ = self.sync(first.replace(r'\uses{b}', ''))
        self.assertEqual(graph.edges(source=node_id('bp', 'a'), hard=True), [])


if __name__ == '__main__':
    unittest.main()
