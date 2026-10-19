"""Exercise the actual native synchronizer without a repository evidence layer."""
import importlib.util
from pathlib import Path
import re
import tempfile
import unittest
from unittest.mock import patch

from hgraph.analysis import Analysis
from hgraph.graph import Graph, node_id
from hgraph.sync import parse_lean, parse_blueprint, read_blueprint, _tex_lean_status
from blueprint_paper import load_paper

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('native_blueprint_builder', ROOT / 'scripts/build-blueprint.py')
builder = importlib.util.module_from_spec(spec)
spec.loader.exec_module(builder)


class ProofToolsBindingTests(unittest.TestCase):
    def test_public_bindings_resolve_to_actual_declarations_with_native_status(self):
        declarations = {
            d['fqname']: d
            for path in (ROOT / 'KIP126/ProofTools').rglob('*.lean')
            for d in parse_lean(path.read_text())
        }
        states = {name: 'sorry' if d['sorry'] else 'lean_ok'
                  for name, d in declarations.items()}
        rows, _ = parse_blueprint(read_blueprint(ROOT / 'blueprint/content.tex'))
        rows = [r for r in rows if r['chapter'].startswith('ProofTools')]
        self.assertTrue(rows)
        for row in rows:
            for name in row['lean']:
                with self.subTest(label=row['label'], declaration=name):
                    self.assertIn(name, declarations)
                    self.assertFalse(declarations[name]['private'])
                    self.assertIn('public ', declarations[name]['body'].splitlines()[0])
                    self.assertNotIn('.Operations.', name)
            if row['lean']:
                self.assertNotEqual(_tex_lean_status(row, states)[0], 'empty')
        # Removed original GL/MH laws must not reappear as mathematical nodes.
        by_label = {r['label']: r for r in rows}
        removed = {'paper:6.1', 'frontier:ProofTools:003e9deb7ec5',
                   'sem:ProofTools:leibniz-law', 'thm:e73f481e', 'thm:158d451a'}
        self.assertFalse(removed.intersection(label for row in rows for label in row['labels']))
        obsolete = {'KIP126.ProofTools.GeneralizedLeibnizLaw',
                    'KIP126.ProofTools.GeneralizedMahowaldLaw',
                    'KIP126.ProofTools.Standard.generalizedLeibniz',
                    'KIP126.ProofTools.Standard.generalizedMahowald'}
        self.assertFalse(obsolete.intersection(name for row in rows for name in row['lean']))
        # The revised assertion definition and its complete theorem have distinct
        # bindings; neither restores the retired zero-layer Mahowald law.
        self.assertEqual(by_label['sem:ProofTools:mahowald-law']['lean'],
                         ['KIP126.ProofTools.Standard.FiniteMahowaldAtLevelStatement'])
        self.assertEqual(by_label['paper:6.12']['lean'],
                         ['KIP126.ProofTools.Standard.generalizedMahowaldAtLevel'])
        for label in ('sem:ProofTools:mahowald-law', 'paper:6.12',
                      'sem:ProofTools:mh-common-source',
                      'sem:ProofTools:mh-target-preserving-lift',
                      'sem:ProofTools:mh-lifted-target-permanent',
                      'sem:ProofTools:generalized-leibniz-at-level',
                      'sem:ProofTools:nu-zero-layer'):
            self.assertEqual(_tex_lean_status(by_label[label], states)[0], 'lean_ok')
        all_rows, _ = parse_blueprint(read_blueprint(ROOT / 'blueprint/content.tex'))
        for row in all_rows:
            self.assertFalse(removed.intersection(row['uses']), row['label'])
        original_statements = {'2.6': 'adamsFiltrationVanishing', '2.12': 'extensionSquare', '2.15': 'noCrossingExtensionSquare', '2.16': 'extensionTriangle', '2.17': 'extensionComposition', '2.18': 'extensionSpectralSequenceMorphism', '2.19': 'permanentCycle_of_nullComposite', '5.10': 'finiteCrossing_iff_syntheticCrossing'}
        pending = {'5.10'}
        for number, name in original_statements.items():
            row = by_label['paper:' + number]
            self.assertEqual(row['lean'], ['KIP126.ProofTools.Paper.' + name])
            self.assertEqual(_tex_lean_status(row, states)[0],
                             'sorry' if number in pending else 'lean_ok')
        # Original quotations retain the article's exact statement. Only the
        # separate entries with all approved premises bind the conditional proofs.
        originals = {row['number']: row for row in load_paper(ROOT)}
        conditional = {
            '2.20': ('sem:ProofTools:complete-exact-extension-boundaries',
                     'extensionBoundary_of_exact'),
            '5.14': ('sem:ProofTools:lambda-inversion-homotopy-extension',
                     'infiniteExtension_to_classicalExtension'),
        }
        for number, (label, name) in conditional.items():
            original, revised = by_label['paper:' + number], by_label[label]
            self.assertEqual(original['lean'], [])
            source = re.sub(r'\\label\{[^}]+\}', '', originals[number]['raw'])
            self.assertIn(' '.join(source.split()), ' '.join(original['body'].split()))
            self.assertIn(label, original['body'])
            self.assertEqual(revised['lean'], ['KIP126.ProofTools.Paper.' + name])
            self.assertEqual(_tex_lean_status(revised, states)[0], 'lean_ok')
        complete = by_label['sem:ProofTools:complete-exact-extension-boundaries']['body']
        for condition in (r'\varprojlim', 'finite for every', r'\bigcap_{n\geq0}'):
            self.assertIn(condition, complete)
        comparison = by_label['sem:ProofTools:lambda-inversion-homotopy-extension']
        self.assertIn('Fix realization coordinates $R$', comparison['body'])
        self.assertIn('sem:Literature:lambda-inversion-adams-comparison', comparison['uses'])
        self.assertIn('fixed Standard model is still', by_label['paper:5.14']['body'])


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
