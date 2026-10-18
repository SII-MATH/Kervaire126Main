"""Independent regressions for the mathematical Blueprint's dependency quotient.

The oracle follows the original source graph, independently of the grouping and
edge reduction used by the publisher. Native frontend closure is checked too:
its entry-only dependency graph is the graph a reader actually sees.
"""
import importlib.util
import json
from pathlib import Path
import re
import random
import sys
import tempfile
import unittest

from hgraph.layout import _Model

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
SPEC = importlib.util.spec_from_file_location(
    'blueprint_semantic_under_test', ROOT / 'scripts/blueprint_semantic.py')
semantic = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(semantic)


def fixture(dependencies, *, holes=(), unknown=(), owners=None, kinds=None):
    """Small actual-source graph, with explicit independent producer identities."""
    holes, unknown = set(holes), set(unknown)
    owners, kinds = owners or {}, kinds or {}
    sources = {}
    for name in dependencies:
        source = {'owner': owners.get(name, 'SpectralSequence'),
                  'label': 'decl:' + name, 'fqname': name,
                  'file': 'KIP126/SpectralSequence/' + name + '.lean',
                  'row': {'direct_sorry': name in holes}}
        if name in unknown:
            source['lean_status'] = 'empty'
        sources[name] = source
    obligations = {name: {'status': kinds.get(name, 'pending-proof')} for name in holes}
    return sources, {n: set(ds) for n, ds in dependencies.items()}, obligations


def statement(label, *names):
    return {'label': label, 'title': label, 'lean': list(names)}


def reached(start, adjacency):
    """Breadth-first oracle; does not use the projection's ancestry function."""
    todo, seen = list(start), set()
    while todo:
        name = todo.pop()
        if name in seen:
            continue
        seen.add(name)
        todo.extend(adjacency[name])
    return seen


def native_model(projection):
    return _Model({'entries': [
        {'id': label, 'lean_status': row['local_status'],
         'deps': [{'id': target, 'type': 'uses'}
                  for target in projection['uses'][label]]}
        for label, row in projection['entries'].items()]})


class MainRemarkBindingTests(unittest.TestCase):
    def fixture(self):
        from hgraph.sync import parse_blueprint
        sources, _, _ = fixture({'_private.A.proof': [], '_private.B.proof': []},
                                owners={'_private.A.proof': 'Main', '_private.B.proof': 'Main'})
        for name, source in sources.items():
            source['fqname'] = 'KIP126.Main.local_proof'
            source['lean_name'] = name
        rows, _ = parse_blueprint(
            r'\begin{remark}\label{sem:Main:remark-7.4}'
            r'\lean{KIP126.Main.local_proof}\uses{decl:_private.A.proof}'
            r'A mathematical consequence.\end{remark}')
        return rows[0], sources

    def test_private_remark_uses_explicit_source_identity(self):
        statement, sources = self.fixture()
        self.assertEqual(semantic.resolve_main_remark(statement, sources), ['_private.A.proof'])
        statement['uses'] = ['decl:_private.B.proof']
        self.assertEqual(semantic.resolve_main_remark(statement, sources), ['_private.B.proof'])
        statement['uses'].append('decl:_private.A.proof')
        with self.assertRaisesRegex(ValueError, 'does not uniquely match'):
            semantic.resolve_main_remark(statement, sources)

    def test_remark_cannot_move_ownership_or_assert_completion(self):
        statement, sources = self.fixture()
        sources['_private.A.proof']['owner'] = 'Literature'
        with self.assertRaisesRegex(ValueError, 'own implementation proofs'):
            semantic.resolve_main_remark(statement, sources)
        sources['_private.A.proof']['owner'] = 'Main'
        statement['leanok'] = True
        with self.assertRaisesRegex(ValueError, 'compiled evidence'):
            semantic.resolve_main_remark(statement, sources)
        statement['leanok'] = False
        statement['content_type'] = 'theorem'
        with self.assertRaisesRegex(ValueError, 'Invalid Main remark binding'):
            semantic.resolve_main_remark(statement, sources)


class ProjectionTests(unittest.TestCase):
    def assert_matches_source(self, projection, sources, dependencies):
        """Check every entry against raw source reachability and native closure."""
        labels = list(projection['entries'])
        model = native_model(projection)
        for index, label in enumerate(labels):
            row = projection['entries'][label]
            actual = reached(row['lean'], dependencies)
            expected = bool(row['lean']) and all(
                not sources[n]['row']['direct_sorry'] and
                sources[n].get('lean_status', 'lean_ok') in {'lean_ok', 'mathlib_ok'}
                for n in actual)
            self.assertEqual(row['expected_closed'], expected, label)
            self.assertEqual(model.closed[index], expected, label)
            # Expanding visible frontier dependencies must neither hide an
            # upstream producer nor import an unrelated group's obligations.
            visible = reached(projection['uses'][label], projection['uses'])
            represented = set()
            for target in visible:
                represented.update(projection['frontiers'].get(target, ()))
            external = actual - set(row['lean'])
            expected_pending = external.intersection(projection['producer_names'])
            # A root bound by this entry can also occur upstream of another
            # bound root; it is then legitimately reached through that path.
            # Such own producers are already reflected in the local status.
            self.assertEqual(represented - set(row['lean']), expected_pending, label)
            self.assertLessEqual(represented, actual, label)

    def test_hidden_private_proof_remains_a_visible_dependency(self):
        sources, deps, obligations = fixture(
            {'_private.pending': [], '_private.helper': ['_private.pending'],
             'public.result': ['_private.helper']}, holes=['_private.pending'])
        projection = semantic.make_projection(sources, deps, obligations,
            [statement('sem:result', 'public.result')])
        self.assertEqual(projection['entries']['sem:result']['local_status'], 'lean_ok')
        self.assertFalse(projection['entries']['sem:result']['expected_closed'])
        self.assertEqual(set(sum(projection['frontiers'].values(), [])), {'_private.pending'})
        self.assert_matches_source(projection, sources, deps)

    def test_multibinding_does_not_make_an_independent_result_incomplete(self):
        sources, deps, obligations = fixture(
            {'pending': [], 'open': ['pending'], 'closed': []}, holes=['pending'])
        projection = semantic.make_projection(sources, deps, obligations,
            [statement('sem:combined', 'open', 'closed'),
             statement('sem:independent', 'closed')])
        self.assertFalse(projection['entries']['sem:combined']['expected_closed'])
        self.assertTrue(projection['entries']['sem:independent']['expected_closed'])
        self.assertNotIn('sem:combined', projection['uses']['sem:independent'])
        self.assert_matches_source(projection, sources, deps)

    def test_producer_incidence_preserves_a_pending_producers_prerequisites(self):
        sources, deps, obligations = fixture(
            {'earlier': [], 'later': ['earlier'], 'result': ['later']},
            holes=['earlier', 'later'])
        projection = semantic.make_projection(sources, deps, obligations,
            [statement('sem:result', 'result')])
        # Both holes have the same mathematical consumer. They still cannot
        # share a frontier because the later producer requires the earlier one.
        self.assertEqual(sorted(map(len, projection['frontiers'].values())), [1, 1])
        earlier = next(k for k, v in projection['frontiers'].items() if v == ['earlier'])
        later = next(k for k, v in projection['frontiers'].items() if v == ['later'])
        self.assertIn(earlier, reached(projection['uses'][later], projection['uses']))
        self.assert_matches_source(projection, sources, deps)

    def test_partial_consumption_splits_a_group_and_keeps_consumer_incidence(self):
        sources, deps, obligations = fixture(
            {'left': [], 'right': [], 'one': ['left'], 'both': ['left', 'right']},
            holes=['left', 'right'])
        projection = semantic.make_projection(sources, deps, obligations,
            [statement('sem:one', 'one'), statement('sem:both', 'both')])
        self.assertEqual(sorted(map(len, projection['frontiers'].values())), [1, 1])
        self.assert_matches_source(projection, sources, deps)

    def test_exact_partition_includes_unused_responsibilities_once(self):
        sources, deps, obligations = fixture(
            {'used': [], 'unusedA': [], 'unusedB': [], 'result': ['used']},
            holes=['used', 'unusedA', 'unusedB'])
        projection = semantic.make_projection(sources, deps, obligations,
            [statement('sem:producer', 'used'), statement('sem:result', 'result')])
        members = sum(projection['frontiers'].values(), [])
        self.assertCountEqual(members, obligations)
        self.assertEqual(len(members), len(set(members)))
        self.assertEqual(projection['frontiers']['sem:producer'], ['used'])
        self.assert_matches_source(projection, sources, deps)

    def test_owner_and_responsibility_kind_are_never_merged(self):
        sources, deps, obligations = fixture(
            {'proof': [], 'construction': [], 'otherModule': []},
            holes=['proof', 'construction', 'otherModule'],
            owners={'otherModule': 'Main'}, kinds={'construction': 'pending-construction'})
        projection = semantic.make_projection(sources, deps, obligations, [])
        self.assertEqual(len(projection['frontiers']), 3)
        self.assert_matches_source(projection, sources, deps)

    def test_unknown_verification_stays_empty_without_a_new_proof_obligation(self):
        sources, deps, obligations = fixture(
            {'unverified': [], 'result': ['unverified']}, unknown=['unverified'])
        projection = semantic.make_projection(sources, deps, obligations,
            [statement('sem:result', 'result')])
        self.assertEqual(obligations, {})
        frontier = next(r for r in projection['entries'].values() if r['frontier'])
        self.assertEqual(frontier['local_status'], 'empty')
        self.assertEqual(frontier['obligation_kind'], 'unverified')
        self.assertFalse(projection['entries']['sem:result']['expected_closed'])
        self.assert_matches_source(projection, sources, deps)

    def test_own_pending_multibindings_are_locally_incomplete(self):
        sources, deps, obligations = fixture(
            {'first': [], 'second': [], 'result': ['first']}, holes=['first', 'second'])
        projection = semantic.make_projection(sources, deps, obligations,
            [statement('sem:combined', 'first', 'second', 'result')])
        self.assertEqual(projection['entries']['sem:combined']['local_status'], 'sorry')
        self.assertFalse(projection['entries']['sem:combined']['expected_closed'])
        self.assert_matches_source(projection, sources, deps)

    def test_adversarial_dags_match_source_closure_after_edge_reduction(self):
        # Overlapping multi-bindings and mixtures of direct holes and unknowns
        # exercise quotient edges that are absent in simple chain fixtures.
        rng = random.Random(126)
        names = [f'n{i}' for i in range(8)]
        for case in range(100):
            raw = {name: [prior for prior in names[:i] if rng.random() < .23]
                   for i, name in enumerate(names)}
            holes = rng.sample(names, rng.randrange(5))
            candidates = [name for name in names if name not in holes]
            unknown = rng.sample(candidates, rng.randrange(min(3, len(candidates)) + 1))
            sources, deps, obligations = fixture(raw, holes=holes, unknown=unknown)
            rows = [statement(f'sem:{i}', *rng.sample(names, rng.randrange(5)))
                    for i in range(5)]
            with self.subTest(case=case):
                projection = semantic.make_projection(sources, deps, obligations, rows)
                self.assert_matches_source(projection, sources, deps)
                self.assertCountEqual(sum(projection['frontiers'].values(), []),
                                      set(holes) | set(unknown))

    def test_cycles_and_missing_source_dependencies_are_rejected(self):
        sources, deps, obligations = fixture({'a': ['b'], 'b': ['a']})
        with self.assertRaisesRegex(ValueError, 'Cyclic compiled'):
            semantic.make_projection(sources, deps, obligations, [statement('sem:a', 'a')])
        sources, deps, obligations = fixture({'a': ['absent']})
        with self.assertRaisesRegex(ValueError, 'Missing compiled'):
            semantic.make_projection(sources, deps, obligations, [statement('sem:a', 'a')])


class AuthoredPublicBindingTests(unittest.TestCase):
    def test_curated_entries_bind_real_locked_public_declarations(self):
        import hashlib
        from hgraph.sync import parse_blueprint, parse_lean
        public = {r['name'] for path in (ROOT / 'metadata').glob('*-api.json')
                  for r in json.loads(path.read_text()).get('declarations', [])}
        private_main = {}
        for path in (ROOT / 'KIP126/Main').rglob('*.lean'):
            module = '.'.join(path.relative_to(ROOT).with_suffix('').parts)
            for declaration in parse_lean(path.read_text()):
                if not declaration.get('private'):
                    continue
                name = module + ':' + declaration['fqname']
                private_main[name] = {'owner': 'Main', 'fqname': declaration['fqname'],
                    'lean_name': name, 'label': 'decl:' + hashlib.sha256(
                        (module + ':' + declaration['fqname']).encode()).hexdigest()[:16]}
        files, visited = set(), set()
        def collect(path):
            path = path.resolve()
            if path.parent == ROOT / 'blueprint/generated':
                return  # Generated output is not curated public authoring.
            if path in visited:
                return
            visited.add(path)
            self.assertTrue(path.exists(), str(path))
            if path.parent == ROOT / 'blueprint/semantic':
                files.add(path)
            active = semantic.active_tex(path.read_text())
            for target in re.findall(r'\\input\{([^}]+)\}', active):
                child = path.parent / target.strip()
                collect(child if child.suffix else child.with_suffix('.tex'))
        collect(ROOT / 'blueprint/content.tex')
        self.assertTrue(files, 'The primary Blueprint must include mathematical statements')
        for path in files:
            rows, _ = parse_blueprint(semantic.active_tex(path.read_text()))
            for row in rows:
                if (row['label'].startswith('sem:Main:remark-')
                        and any(name not in public for name in row['lean'])):
                    self.assertTrue(semantic.resolve_main_remark(row, private_main))
                else:
                    for name in row['lean']:
                        self.assertIn(name, public, str(path) + ': ' + name)


class FrontierAuthoringTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        (self.root / 'blueprint/frontier').mkdir(parents=True)
        (self.root / 'metadata').mkdir()
        (self.root / 'metadata/spectral-sequence-api.json').write_text(json.dumps({
            'declarations': [{'name': 'public.result'}]}))
        (self.root / 'blueprint/content.tex').write_text(
            '\\chapter{Spectral sequences}\n'
            '\\begin{theorem}[A consequence]\n\\label{sem:result}\n'
            '\\lean{public.result}\nThe consequence holds.\n\\end{theorem}\n'
            '\\input{generated/frontier-SpectralSequence.tex}\n')
        self.sources, self.deps, self.obligations = fixture({
            '_private.pending': [], 'public.result': ['_private.pending']},
            holes=['_private.pending'])
        self.sources['_private.pending']['fqname'] = 'Local.pending'
        self.sources['_private.pending']['lean_name'] = '_private.pending'
        self.baseline = semantic.make_projection(self.sources, self.deps,
            self.obligations, [statement('sem:result', 'public.result')])
        self.label = next(label for label, row in self.baseline['entries'].items()
                          if row['frontier'])
        self.path = self.root / 'blueprint/frontier/SpectralSequence.tex'

    def write_entry(self, *, label=None, binding='Local.pending', flags=''):
        self.path.write_text('\\begin{theorem}[Vanishing in positive degrees]\n'
            '\\label{' + (label or self.label) + '}\n'
            '\\lean{' + binding + '}\n' + flags + '\n'
            '% Blueprint note: This proof remains unfinished.\n'
            'For every $n>0$, the specified group in degree $n$ is zero.\n'
            '\\end{theorem}\n')

    def test_mathematical_prose_preserves_private_binding_and_compiled_closure(self):
        self.write_entry()
        projection = semantic.prepare(self.root, self.sources, self.deps,
                                      self.obligations, [])
        for label, expected in self.baseline['entries'].items():
            for key in ('lean', 'ancestors', 'local_status', 'frontier', 'expected_closed'):
                self.assertEqual(projection['entries'][label][key], expected[key])
        self.assertEqual(projection['uses'], self.baseline['uses'])
        self.assertEqual(projection['frontiers'], self.baseline['frontiers'])
        self.assertEqual(projection['producer_names'], self.baseline['producer_names'])
        generated = (self.root / 'blueprint/generated/frontier-SpectralSequence.tex').read_text()
        self.assertIn('\\begin{theorem}[Vanishing in positive degrees]', generated)
        self.assertIn('For every $n>0$', generated)
        self.assertIn('\\lean{_private.pending}', generated)
        self.assertNotIn('% Blueprint note:', generated)
        self.assertNotIn('Supply the specified', generated)
        self.assertNotIn('Construction and proof frontier', generated)
        self.assertEqual(projection['entries'][self.label]['local_status'], 'sorry')
        self.assertFalse(projection['entries']['sem:result']['expected_closed'])

    def test_missing_group_is_rejected_by_prepare(self):
        with self.assertRaisesRegex(ValueError, 'Missing frontier mathematical entries'):
            semantic.prepare(self.root, self.sources, self.deps, self.obligations, [])

    def test_unknown_group_and_wrong_binding_are_rejected(self):
        self.write_entry(label='frontier:SpectralSequence:invented')
        with self.assertRaisesRegex(ValueError, 'Unexpected frontier mathematical label'):
            semantic.read_frontier_authoring(self.root, self.baseline, self.sources)
        self.write_entry(binding='public.result')
        with self.assertRaisesRegex(ValueError, 'bindings differ from compiled group'):
            semantic.read_frontier_authoring(self.root, self.baseline, self.sources)

    def test_ambiguous_private_spelling_and_duplicate_members_are_rejected(self):
        self.sources['public.result']['fqname'] = 'Local.pending'
        self.write_entry()
        with self.assertRaisesRegex(ValueError, 'ambiguous frontier Lean binding'):
            semantic.read_frontier_authoring(self.root, self.baseline, self.sources)
        self.write_entry(binding='_private.pending,_private.pending')
        with self.assertRaisesRegex(ValueError, 'bindings differ from compiled group'):
            semantic.read_frontier_authoring(self.root, self.baseline, self.sources)

    def test_authored_completion_and_dependencies_are_rejected(self):
        for flag in ('\\leanok', '\\mathlibok'):
            self.write_entry(flags=flag)
            with self.assertRaisesRegex(ValueError, 'status must be derived'):
                semantic.read_frontier_authoring(self.root, self.baseline, self.sources)
        self.write_entry(flags='\\uses{sem:result}')
        with self.assertRaisesRegex(ValueError, 'dependencies must be derived'):
            semantic.read_frontier_authoring(self.root, self.baseline, self.sources)

    def test_unverified_mathematical_statement_stays_unverified(self):
        self.sources['_private.pending']['row']['direct_sorry'] = False
        self.sources['_private.pending']['lean_status'] = 'empty'
        self.write_entry()
        projection = semantic.prepare(self.root, self.sources, self.deps, {}, [])
        row = projection['entries'][self.label]
        self.assertEqual(row['obligation_kind'], 'unverified')
        self.assertEqual(row['local_status'], 'empty')
        self.assertFalse(row['expected_closed'])
        self.assertFalse(projection['entries']['sem:result']['expected_closed'])

    def test_commented_bindings_and_status_flags_are_not_active_authoring(self):
        self.write_entry(flags='% Blueprint note: \\leanok \\lean{unrelated} '
                               '\\label{frontier:invented}')
        rows = semantic.read_frontier_authoring(self.root, self.baseline, self.sources)
        self.assertEqual(set(rows), {self.label})
        self.assertFalse(rows[self.label]['leanok'])
        self.assertEqual(rows[self.label]['lean'], ['Local.pending'])


class ChapterDependencyTests(unittest.TestCase):
    def check(self, uses, chapter_rows):
        projection = {'entries': dict.fromkeys(uses), 'uses': uses}
        return semantic.validate_chapter_dependencies(projection, [
            {'label': label, 'chapter': chapter} for label, chapter in chapter_rows])

    def test_fine_dag_can_collapse_into_a_chapter_cycle(self):
        # Each fine edge is acyclic, but putting a/c in one chapter and b/d
        # in another creates A -> B -> A. It must fail publication.
        with self.assertRaisesRegex(ValueError, 'Chapter dependency points forward'):
            self.check({'a': {'b'}, 'b': set(), 'c': set(), 'd': {'c'}},
                       [('a', 'A'), ('c', 'A'), ('b', 'B'), ('d', 'B')])

    def test_e2_tools_calculations_order_and_internal_edges(self):
        result = self.check({'e2': set(), 'tools': {'e2'}, 'calc': {'tools'},
                             'main': {'calc', 'local'}, 'local': {'e2'}},
                            [('e2', 'E2'), ('tools', 'Tools'), ('calc', 'Calculations'),
                             ('main', 'Main'), ('local', 'Main')])
        self.assertTrue(result['topological_order_verified'])
        self.assertEqual(result['chapters'], ['E2', 'Tools', 'Calculations', 'Main'])
        self.assertEqual(len(result['dependency_edges']), 4)

    def test_missing_display_partition_cannot_skip_validation(self):
        with self.assertRaisesRegex(ValueError, 'missing from primary chapters'):
            self.check({'a': set()}, [])


if __name__ == '__main__':
    unittest.main()
