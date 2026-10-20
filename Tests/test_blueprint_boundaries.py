"""The two retained repository rules apply to native statement/proof bindings."""
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
import blueprint_boundaries as boundaries
from hgraph.sync import parse_blueprint

ROOT = Path(__file__).resolve().parents[1]


class BindingOwnershipTests(unittest.TestCase):
    def test_namespace_does_not_override_actual_module_ownership(self):
        name = 'KIP126.Computation.label'
        sources = {name: {'file': 'KIP126/E2Computation/Labels.lean', 'owner': 'E2Computation'}}
        row = {'label': 'result', 'chapter': 'AdamsCalculations', 'lean': [name]}
        with self.assertRaisesRegex(ValueError, 'Cross-module Blueprint binding'):
            boundaries.validate_binding_owners([row], sources, {name: 'E2Computation'})
        sources[name]['owner'] = 'AdamsCalculations'
        with self.assertRaisesRegex(ValueError, 'Invalid source module ownership'):
            boundaries.validate_binding_owners([row], sources, {name: 'AdamsCalculations'})

    def test_only_locked_public_interfaces_are_bindable(self):
        name = 'KIP126.Main.internal'
        sources = {name: {'file': 'KIP126/Main/Result.lean', 'owner': 'Main'}}
        for label in ('paper:7.16', 'sem:Main:remark-7.4', 'ordinary-label'):
            with self.assertRaisesRegex(ValueError, 'Non-public Blueprint binding'):
                boundaries.validate_binding_owners([
                    {'label': label, 'chapter': 'Main', 'lean': [name]}], sources, {})
        result = boundaries.validate_binding_owners([
            {'label': 'unformalized', 'chapter': 'Main', 'lean': []}], sources, {})
        self.assertTrue(result['public_interfaces_verified'])

    def test_every_current_binding_is_a_public_export_of_its_source_chapter(self):
        result = boundaries.check(ROOT)
        self.assertTrue(result['bindings']['same_module_verified'])
        self.assertEqual(len(result['chapters']['chapters']), 8)


class ChapterOrderTests(unittest.TestCase):
    def check(self, text):
        rows, proofs = parse_blueprint(text)
        return boundaries.validate_chapter_dependencies(rows, proofs)

    def test_statement_and_proof_dependencies_obey_chapter_order(self):
        source = (r'\chapter{E2Computation}\begin{theorem}\label{input}\label{alias}'
                  r'Input.\end{theorem}'
                  r'\chapter{ProofTools}\begin{theorem}\label{result}Result.\end{theorem}'
                  r'\begin{proof}\uses{alias}Proof.\end{proof}')
        self.assertEqual(self.check(source)['dependency_edges'], [['ProofTools', 'E2Computation']])
        with self.assertRaisesRegex(ValueError, 'Chapter dependency points forward'):
            self.check(source.replace(r'Input.\end{theorem}', r'\uses{result}Input.\end{theorem}'))

    def test_same_chapter_cycles_and_unresolved_uses_are_left_to_native_hgraph(self):
        source = (r'\chapter{Main}\begin{theorem}\label{a}\uses{b,missing}A.\end{theorem}'
                  r'\begin{theorem}\label{b}\uses{a}B.\end{theorem}')
        self.assertEqual(self.check(source)['dependency_edges'], [])

    def test_ownership_index_locates_an_alias_without_changing_native_inputs(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'KIP126/Main').mkdir(parents=True)
            path = root / 'KIP126/Main/Alias.lean'
            text = 'module\nnamespace KIP126.Main\npublic alias copied := original\nend KIP126.Main\n'
            path.write_text(text)
            indexed = boundaries.source_owners(root, {'KIP126.Main.copied': 'Main'})
            self.assertEqual(indexed['KIP126.Main.copied']['file'], 'KIP126/Main/Alias.lean')
            self.assertEqual(path.read_text(), text)


if __name__ == '__main__':
    unittest.main()
