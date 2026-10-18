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
                  'file': 'KIP126/' + owners.get(name, 'SpectralSequence') + '/' + name + '.lean',
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

    def test_private_remark_is_rejected_even_with_an_explicit_source_identity(self):
        statement, sources = self.fixture()
        for target in ('decl:_private.A.proof', 'decl:_private.B.proof'):
            statement['uses'] = [target]
            with self.assertRaisesRegex(ValueError, 'Non-public Blueprint binding'):
                semantic.resolve_main_remark(statement, sources, {})
        statement['uses'].append('decl:_private.A.proof')
        with self.assertRaisesRegex(ValueError, 'does not uniquely match'):
            semantic.resolve_main_remark(statement, sources, {})

    def test_public_remark_retains_its_source_identity(self):
        row, sources = self.fixture()
        source = sources['_private.A.proof']
        source['lean_name'] = 'public.proof'
        sources = {'public.proof': source}
        self.assertEqual(semantic.resolve_main_remark(row, sources, {'public.proof': 'Main'}),
                         ['public.proof'])

    def test_remark_cannot_move_ownership_or_assert_completion(self):
        statement, sources = self.fixture()
        sources['_private.A.proof']['owner'] = 'Literature'
        with self.assertRaisesRegex(ValueError, 'own implementation proofs'):
            semantic.resolve_main_remark(statement, sources, {})
        sources['_private.A.proof']['owner'] = 'Main'
        statement['leanok'] = True
        with self.assertRaisesRegex(ValueError, 'compiled evidence'):
            semantic.resolve_main_remark(statement, sources, {})
        statement['leanok'] = False
        statement['content_type'] = 'theorem'
        with self.assertRaisesRegex(ValueError, 'Invalid Main remark binding'):
            semantic.resolve_main_remark(statement, sources, {})


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


class PublicProjectionTests(unittest.TestCase):
    def check(self, sources, deps, obligations, rows, public):
        projection = semantic.make_projection(sources, deps, obligations, rows,
                                             public_names=public)
        model = native_model(projection)
        for index, (label, row) in enumerate(projection['entries'].items()):
            self.assertLessEqual(set(row['lean']), set(public), label)
            actual = reached(row['lean'], deps)
            closed = bool(row['lean']) and all(
                semantic.local_status([name], sources) in semantic.DONE for name in actual)
            self.assertEqual(row['expected_closed'], closed, label)
            self.assertEqual(model.closed[index], closed, label)
        return projection

    def test_private_holes_remain_recorded_and_block_the_public_result(self):
        sources, deps, obligations = fixture({'_private.pending': [],
            '_private.helper': ['_private.pending'], 'public.result': ['_private.helper'],
            'public.independent': [], '_private.unused': []},
            holes=['_private.pending', '_private.unused'])
        rows = [statement('result', 'public.result'), statement('independent', 'public.independent')]
        p = self.check(sources, deps, obligations, rows, {'public.result', 'public.independent'})
        self.assertEqual(p['frontiers'], {})
        self.assertCountEqual(p['private_producer_names'], obligations)
        self.assertEqual(p['entries']['result']['source_local_status'], 'lean_ok')
        self.assertEqual(p['entries']['result']['local_status'], 'sorry')
        self.assertEqual(p['entries']['result']['internal_producers'], ['_private.pending'])
        self.assertEqual(p['entries']['independent']['local_status'], 'lean_ok')
        self.assertEqual(semantic.local_status(['public.result'], sources), 'lean_ok')
        sources['_private.pending']['row']['direct_sorry'] = False
        sources['_private.pending']['lean_status'] = 'empty'
        p = self.check(sources, deps, {}, rows, {'public.result', 'public.independent'})
        self.assertEqual(p['entries']['result']['local_status'], 'empty')

    def test_adversarial_private_public_dags_preserve_exact_compiled_closure(self):
        rng = random.Random(126126)
        names = [f'n{i}' for i in range(10)]
        for case in range(100):
            deps = {name: [prior for prior in names[:i] if rng.random() < .3]
                    for i, name in enumerate(names)}
            public = set(rng.sample(names, rng.randrange(1, len(names) + 1)))
            sources, deps, obligations = fixture(deps, holes=rng.sample(names, rng.randrange(6)))
            rows = [statement(f'result:{i}', *rng.sample(sorted(public), rng.randrange(len(public) + 1)))
                    for i in range(4)]
            with self.subTest(case=case):
                p = self.check(sources, deps, obligations, rows, public)
                self.assertCountEqual(p['producer_names'], obligations)
                self.assertCountEqual(sum(p['frontiers'].values(), []), set(obligations) & public)
                self.assertCountEqual(p['private_producer_names'], set(obligations) - public)

    def test_native_graph_retains_private_implementation_without_a_private_blueprint_binding(self):
        import importlib.util
        from hgraph.analysis import Analysis
        from hgraph.graph import Graph, node_id
        spec = importlib.util.spec_from_file_location('private_obligation_builder', ROOT / 'scripts/build-blueprint.py')
        builder = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(builder)
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            builder.ROOT = root
            path = root / 'KIP126/Main/Result.lean'
            path.parent.mkdir(parents=True)
            path.write_text('module\nnamespace KIP126.Main\n'
                'private theorem internal_proof : True := by sorry\n'
                'public theorem result : True := internal_proof\nend KIP126.Main\n')
            private = '_private.KIP126.Main.Result.0.KIP126.Main.internal_proof'
            public = 'KIP126.Main.result'
            sources = builder.index_sources([
                {'module': 'KIP126.Main.Result', 'source_name': 'KIP126.Main.internal_proof',
                 'name': private, 'dependencies': [], 'direct_sorry': True, 'line': 3},
                {'module': 'KIP126.Main.Result', 'source_name': public,
                 'name': public, 'dependencies': [private], 'direct_sorry': False, 'line': 4}])
            (root / 'metadata').mkdir()
            (root / 'metadata/main-api.json').write_text(json.dumps({
                'module': 'Main', 'declarations': [{'name': public}], 'exports': [public]}))
            deps = {private: set(), public: {private}}
            obligations = {private: {'status': 'pending-proof'}}
            builder.generate_blueprint(sources, deps, obligations)
            (root / 'blueprint/content.tex').write_text(
                '\\chapter{Main}\n\\begin{theorem}[A result]\\label{sem:result}'
                '\\lean{' + public + '}The result holds.\\end{theorem}\n')
            projection = semantic.prepare(root, sources, deps, obligations, [])
            graph = Graph.open(root)
            builder.sync_kernel_graph(graph, sources, deps, projection)
            builder.annotate_graph(graph, sources, deps, obligations)
            analysis = Analysis(graph)
            evidence = semantic.validate(graph, projection, analysis)
            self.assertTrue(evidence['binding_owners']['public_interfaces_verified'])
            self.assertEqual(evidence['unique_unfinished_producers'], 1)
            self.assertEqual(evidence['private_implementation_producers'], 1)
            self.assertTrue(graph.has_node(node_id('lean', private)))
            self.assertTrue(graph.has_node(node_id('bp', sources[private]['label'])))
            self.assertEqual(graph.get_node(node_id('lean', public)).meta['lean_status'], 'lean_ok')
            self.assertEqual(graph.get_node(node_id('bp', 'sem:result')).meta['lean_status'], 'sorry')
            for edge in graph.edges():
                if edge.type == 'formalizes' and graph.get_node(edge.source).type == 'tex':
                    self.assertEqual(edge.target, node_id('lean', public))


class AuthoredPublicBindingTests(unittest.TestCase):
    def test_every_authored_binding_is_a_locked_interface_of_the_same_module(self):
        from hgraph.sync import parse_blueprint
        interfaces = semantic.public_interfaces(ROOT)
        for folder in ('semantic', 'paper', 'frontier'):
            for path in (ROOT / 'blueprint' / folder).glob('*.tex'):
                for row in parse_blueprint(semantic.active_tex(path.read_text()))[0]:
                    for name in row['lean']:
                        self.assertEqual(interfaces.get(name), path.stem,
                                         str(path) + ': ' + row['label'] + ': ' + name)


class BindingOwnershipTests(unittest.TestCase):
    def test_namespace_and_dependency_do_not_make_an_upstream_object_local(self):
        sources, _, _ = fixture({'KIP126.Computation.label': [], 'differential': []},
            owners={'KIP126.Computation.label': 'E2Computation',
                    'differential': 'AdamsCalculations'})
        row = {**statement('later-result', 'differential'),
               'chapter': 'AdamsCalculations --- Differentials'}
        self.assertTrue(semantic.validate_binding_owners([row], sources, {'differential': 'AdamsCalculations', 'KIP126.Computation.label': 'E2Computation'})['same_module_verified'])
        row['lean'].append('KIP126.Computation.label')
        with self.assertRaisesRegex(ValueError, 'Cross-module Blueprint binding.*E2Computation'):
            semantic.validate_binding_owners([row], sources, {'differential': 'AdamsCalculations', 'KIP126.Computation.label': 'E2Computation'})
        # An inaccurate owner field cannot override the actual source location.
        sources['KIP126.Computation.label']['owner'] = 'AdamsCalculations'
        with self.assertRaisesRegex(ValueError, 'Invalid source module ownership'):
            semantic.validate_binding_owners([row], sources, {'differential': 'AdamsCalculations', 'KIP126.Computation.label': 'E2Computation'})

    def test_private_and_paper_bindings_obey_the_same_rule(self):
        sources, _, _ = fixture({'_private.helper': []}, owners={'_private.helper': 'Main'})
        for label in ('paper:7.16', 'frontier:Main:group', 'sem:Main:remark-7.4'):
            row = {**statement(label, '_private.helper'), 'chapter': 'Main — Argument'}
            with self.assertRaisesRegex(ValueError, 'Non-public Blueprint binding'):
                semantic.validate_binding_owners([row], sources, {})
            row['chapter'] = 'ProofTools — Operations'
            with self.assertRaisesRegex(ValueError, 'Cross-module Blueprint binding'):
                semantic.validate_binding_owners([row], sources, {})
        row['chapter'] = 'Geometry'
        with self.assertRaisesRegex(ValueError, 'must name its mathematical module'):
            semantic.validate_binding_owners([row], sources, {})
        self.assertTrue(semantic.validate_binding_owners([
            {**statement('geometry'), 'chapter': 'Geometry'}], sources, {})['same_module_verified'])

    def test_exposed_private_name_without_kernel_prefix_is_rejected(self):
        sources, _, _ = fixture({'KIP126.ProofTools.Internal.Leibniz.square_frames': []},
            owners={'KIP126.ProofTools.Internal.Leibniz.square_frames': 'ProofTools'})
        row = {**statement('paper:2.12', *sources), 'chapter': 'ProofTools'}
        with self.assertRaisesRegex(ValueError, 'Non-public Blueprint binding'):
            semantic.validate_binding_owners([row], sources, {})

    def test_every_authored_binding_belongs_to_its_source_module(self):
        """Read current sources; no generated site or compiled snapshot is required."""
        from collections import defaultdict
        from hgraph.sync import parse_blueprint, parse_lean
        import importlib.util
        spec = importlib.util.spec_from_file_location('ownership_builder', ROOT / 'scripts/build-blueprint.py')
        builder = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(builder)
        sources, aliases, labels = {}, defaultdict(set), {}
        interfaces = semantic.public_interfaces(ROOT)
        scoped_interfaces = {}
        for path in (ROOT / 'KIP126').rglob('*.lean'):
            module = '.'.join(path.relative_to(ROOT).with_suffix('').parts)
            # The lexical parser handles namespace scopes but omits `alias`.
            # Present only that command as a named theorem to recover its name.
            lexical = re.sub(r'^([ \t]*(?:(?:public|private|protected)[ \t]+)*)'
                             r'alias[ \t]+([^\s:=]+)[ \t]*:=.*$',
                             r'\1theorem \2 : True := by trivial', path.read_text(), flags=re.M)
            for decl in parse_lean(lexical):
                name = module + ':' + decl['fqname']
                sources[name] = {'owner': module.split('.')[1],
                    'file': str(path.relative_to(ROOT))}
                aliases[decl['fqname']].add(name)
                labels[builder.label(module, decl['fqname'])] = name
        for folder in ('semantic', 'paper', 'frontier'):
            for path in (ROOT / 'blueprint' / folder).glob('*.tex'):
                rows, _ = parse_blueprint(semantic.active_tex(path.read_text()))
                for row in rows:
                    names = []
                    for spelling in row['lean']:
                        private = re.fullmatch(r'_private\.(KIP126\..+)\.\d+\.(.+)', spelling)
                        if private:
                            matches = {private[1] + ':' + private[2]} & sources.keys()
                        else:
                            matches = aliases[spelling]
                            refs = {labels[label] for label in row['uses'] if label in labels}
                            if refs:
                                matches = matches & refs
                        self.assertEqual(len(matches), 1, str(path) + ': ' + spelling)
                        names.append(next(iter(matches)))
                        if spelling in interfaces:
                            scoped_interfaces[names[-1]] = interfaces[spelling]
                    semantic.validate_binding_owners([
                        {**row, 'chapter': path.stem, 'lean': names}], sources, scoped_interfaces)

    def test_result_bindings_exclude_background_and_partial_proof_steps(self):
        from hgraph.sync import parse_blueprint
        rows = {}
        for folder in ('semantic', 'paper'):
            for path in (ROOT / 'blueprint' / folder).glob('*.tex'):
                for row in parse_blueprint(semantic.active_tex(path.read_text()))[0]:
                    rows[row['label']] = row
        self.assertEqual(rows['sem:Computation:d7-source']['lean'],
                         ['KIP126.Computation.Standard.d7_source'])
        self.assertEqual(rows['sem:E2Computation:d7-label']['lean'],
                         ['KIP126.Computation.Standard.d7Source'])
        self.assertEqual(rows['paper:3.2']['lean'], ['KIP126.Synthetic.Context.Smn'])
        self.assertEqual(rows['paper:6.1']['lean'],
                         ['KIP126.ProofTools.Standard.generalizedLeibniz'])
        for label in ('paper:2.12', 'paper:2.15', 'paper:5.10', 'paper:7.16', 'paper:7.18'):
            self.assertEqual(rows[label]['lean'], [], label)
            self.assertFalse(any(target.startswith('decl:') for target in rows[label]['uses']), label)
            self.assertTrue(rows[label]['uses'], label)
            self.assertTrue(rows[label]['sketch'], label)


class FrontierAuthoringTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        (self.root / 'blueprint/frontier').mkdir(parents=True)
        (self.root / 'metadata').mkdir()
        (self.root / 'metadata/spectral-sequence-api.json').write_text(json.dumps({
            'module': 'SpectralSequence',
            'declarations': [{'name': 'public.result'}, {'name': 'public.pending'}]}))
        (self.root / 'blueprint/content.tex').write_text(
            '\\chapter{SpectralSequence --- Spectral sequences}\n'
            '\\begin{theorem}[A consequence]\n\\label{sem:result}\n'
            '\\lean{public.result}\nThe consequence holds.\n\\end{theorem}\n'
            '\\input{generated/frontier-SpectralSequence.tex}\n')
        self.sources, self.deps, self.obligations = fixture({
            'public.pending': [], 'public.result': ['public.pending']},
            holes=['public.pending'])
        self.sources['public.pending']['fqname'] = 'Local.pending'
        self.sources['public.pending']['lean_name'] = 'public.pending'
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

    def test_mathematical_prose_preserves_public_binding_and_compiled_closure(self):
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
        self.assertIn('\\lean{public.pending}', generated)
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

    def test_private_frontier_cannot_be_reintroduced_with_a_scoped_name(self):
        self.sources['_private.hidden'] = {
            **self.sources['public.pending'], 'lean_name': '_private.hidden',
            'fqname': 'Private.hidden'}
        self.write_entry(binding='Private.hidden')
        with self.assertRaisesRegex(ValueError, 'Non-public or wrong-module frontier'):
            semantic.read_frontier_authoring(self.root, self.baseline, self.sources)

    def test_ambiguous_source_spelling_and_duplicate_members_are_rejected(self):
        self.sources['public.result']['fqname'] = 'Local.pending'
        self.write_entry()
        with self.assertRaisesRegex(ValueError, 'ambiguous frontier Lean binding'):
            semantic.read_frontier_authoring(self.root, self.baseline, self.sources)
        self.write_entry(binding='public.pending,public.pending')
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
        self.sources['public.pending']['row']['direct_sorry'] = False
        self.sources['public.pending']['lean_status'] = 'empty'
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


class AuthoredPaperDependencyTests(unittest.TestCase):
    def projection(self):
        sources, deps, obligations = fixture(
            {'left': [], 'right': [], 'consumer': ['left']})
        return semantic.make_projection(sources, deps, obligations, [
            statement('sem:group', 'left', 'right'),
            statement('paper:result', 'consumer'), statement('paper:unformalized')])

    def test_partial_consumption_and_unbound_math_use_survive_without_all_bindings(self):
        projection = self.projection()
        self.assertNotIn('sem:group', projection['uses']['paper:result'])
        original = {label: set(targets) for label, targets in projection['uses'].items()}
        semantic.add_paper_dependencies(projection, [
            {'label': 'paper:result', 'mathematical_uses': ['sem:group']},
            {'label': 'paper:unformalized', 'mathematical_uses': ['paper:result']}])
        self.assertEqual(projection['compiled_uses'], original)
        self.assertIn('sem:group', projection['uses']['paper:result'])
        self.assertIn('paper:result', projection['uses']['paper:unformalized'])
        self.assertFalse(projection['entries']['paper:unformalized']['expected_display_closed'])

    def test_mathematical_prerequisite_can_block_a_locally_proved_formal_counterpart(self):
        projection = self.projection()
        semantic.add_paper_dependencies(projection, [
            {'label': 'paper:result', 'mathematical_uses': ['paper:unformalized']},
            {'label': 'paper:unformalized', 'mathematical_uses': []}])
        row = projection['entries']['paper:result']
        self.assertTrue(row['expected_closed'])  # Original compiled oracle retained.
        self.assertEqual(row['local_status'], 'lean_ok')
        self.assertFalse(row['expected_display_closed'])

    def test_alias_references_resolve_to_one_node_without_a_self_edge(self):
        projection = self.projection()
        semantic.add_paper_dependencies(projection, [
            {'label': 'paper:result', 'mathematical_uses': ['sem:group']},
            {'label': 'paper:repeat', 'canonical_label': 'paper:result',
             'mathematical_uses': ['paper:result']},
            {'label': 'paper:unformalized', 'mathematical_uses': ['paper:repeat']}])
        self.assertEqual(projection['uses']['paper:unformalized'], {'paper:result'})
        self.assertNotIn('paper:repeat', projection['uses'])

    def test_cycles_unknown_targets_and_self_dependencies_are_rejected(self):
        cases = [([{'label': 'paper:result', 'mathematical_uses': ['paper:unformalized']},
                   {'label': 'paper:unformalized', 'mathematical_uses': ['paper:result']}], 'Cyclic'),
                 ([{'label': 'paper:result', 'mathematical_uses': ['paper:unknown']}], 'Unknown'),
                 ([{'label': 'paper:result', 'mathematical_uses': ['paper:result']}], 'Self-dependent')]
        for records, error in cases:
            with self.subTest(error=error), self.assertRaisesRegex(ValueError, error):
                semantic.add_paper_dependencies(self.projection(), records)

    def test_authored_paper_chain_uses_results_not_circular_condition_references(self):
        from hgraph.sync import parse_blueprint, read_blueprint
        rows = parse_blueprint(read_blueprint(ROOT / 'blueprint/content.tex'))[0]
        paper = {row['label']: row for row in rows if row['label'].startswith('paper:')}
        self.assertEqual(len(paper), 56)
        aliases = {alias: row['label'] for row in paper.values() for alias in row['labels']}
        self.assertEqual(aliases['paper:7.1'], 'paper:1.4')
        self.assertEqual(aliases['thm:126survives'], 'paper:1.4')
        for label in ('paper:7.10', 'paper:7.11', 'paper:7.16', 'paper:7.18', 'paper:7.9'):
            self.assertNotIn('paper:7.8', paper[label]['uses'], label)
        self.assertTrue({'paper:7.8', 'paper:7.9'} <= set(paper['paper:1.4']['uses']))
        self.assertTrue({'paper:1.3', 'paper:1.4'} <= set(paper['paper:1.1']['uses']))
        self.assertIn('paper:7.16', paper['paper:7.18']['uses'])
        for row in paper.values():
            self.assertTrue(any(not target.startswith('decl:') for target in row['uses']), row['label'])


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
