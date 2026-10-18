"""Regression tests for the compiled-environment to native-hgraph boundary."""
import importlib.util
from pathlib import Path
import tempfile
import re
import shutil
import unittest

from hgraph.graph import Graph, node_id

spec = importlib.util.spec_from_file_location(
    'blueprint_import', Path(__file__).resolve().parents[1] / 'scripts/build-blueprint.py')
blueprint = importlib.util.module_from_spec(spec)
spec.loader.exec_module(blueprint)


def fixture():
    rows = [
        {'name': 'pending', 'source_name': 'pending', 'dependencies': [],
         'direct_sorry': True, 'synthetic_sorry': False, 'is_axiom': False,
         'axioms': ['sorryAx']},
        {'name': '_generated.helper', 'dependencies': ['pending'],
         'direct_sorry': False, 'synthetic_sorry': False, 'is_axiom': False,
         'axioms': ['sorryAx']},
        {'name': 'result', 'source_name': 'result', 'dependencies': ['_generated.helper'],
         'direct_sorry': False, 'synthetic_sorry': False, 'is_axiom': False,
         'axioms': ['sorryAx']},
    ]
    sources = {r['name']: {'row': r, 'fqname': r['name'], 'label': r['name'],
                           'lean_id': node_id('lean', r['name'])}
               for r in (rows[0], rows[2])}
    return rows, sources, {'pending': {'status': 'pending-proof'}}


class BlueprintBoundaryTests(unittest.TestCase):
    def test_native_memo_tab_reads_the_root_file_in_the_export_workspace(self):
        from unittest.mock import patch
        import yaml
        from hgraph.site import _project_site_options

        config = (blueprint.ROOT / 'hgraph/config.yaml').read_text()
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'hgraph').mkdir()
            (root / 'hgraph/config.yaml').write_text(config)
            memo = root / 'MEMO.md'
            memo.write_text('# Root memo\n\nFirst revision.\n')
            with patch.object(blueprint, 'ROOT', root), \
                 patch.object(blueprint, 'STATE', root / '.lake/blueprint'), \
                 patch.object(blueprint, 'prepare_web_blueprint', return_value=root / 'blueprint'):
                project = blueprint.stage_workspace() / 'Kervaire126'
            site = yaml.safe_load((project / 'hgraph/config.yaml').read_text())['site']
            self.assertEqual([tab['content'] for tab in site['tabs']], ['MEMO.md'])
            self.assertEqual((project / 'MEMO.md').resolve(), memo)
            tabs = _project_site_options(site, base=project)['customTabs']
            self.assertEqual([tab['id'] for tab in tabs], ['memo'])
            self.assertIn('First revision.', tabs[0]['html'])
            memo.write_text('# Root memo\n\nSecond revision.\n')
            updated = _project_site_options(site, base=project)['customTabs']
            self.assertIn('Second revision.', updated[0]['html'])
            self.assertNotIn('First revision.', updated[0]['html'])


    def test_computation_moves_preserve_source_review_ids(self):
        name = 'KIP126.Computation.Standard.d2_h6'
        old = blueprint.label('KIP126.Computation.Standard', name)
        self.assertEqual(old, blueprint.label('KIP126.AdamsCalculations.Standard', name))
        self.assertEqual(old, blueprint.label('KIP126.E2Computation.Standard', name))
        self.assertNotEqual(old, blueprint.label('KIP126.ProofTools.Standard', name))

    def test_generated_helper_cannot_hide_a_pending_dependency(self):
        rows, sources, obligations = fixture()
        dependencies = blueprint.project_dependencies(rows, sources)
        self.assertEqual(dependencies, {'pending': set(), 'result': {'pending'}})
        self.assertEqual(blueprint.validate_kernel(rows, sources, dependencies, obligations),
                         {'pending', 'result'})
        with self.assertRaisesRegex(ValueError, 'closure disagrees'):
            blueprint.validate_kernel(rows, sources, {'pending': set(), 'result': set()}, obligations)

    def test_unregistered_or_invisible_holes_are_rejected(self):
        rows, sources, obligations = fixture()
        dependencies = blueprint.project_dependencies(rows, sources)
        with self.assertRaisesRegex(ValueError, 'Obligation mismatch'):
            blueprint.validate_kernel(rows, sources, dependencies, {})
        with self.assertRaisesRegex(ValueError, 'Unrepresented direct holes'):
            blueprint.validate_kernel(rows, {'result': sources['result']}, {'result': set()}, obligations)

    def test_both_native_populations_must_have_the_correct_closure(self):
        _rows, sources, _obligations = fixture()
        with tempfile.TemporaryDirectory() as directory:
            graph = Graph.open(directory)
            for source in sources.values():
                for nid, kind in ((node_id('bp', source['label']), 'tex'),
                                  (source['lean_id'], 'lean')):
                    graph.add_node(source['fqname'], id=nid, type=kind,
                                   lean_status='sorry' if source['row']['direct_sorry'] else 'lean_ok')
            graph.add_edge(node_id('bp', 'result'), node_id('bp', 'pending'), 'uses')
            with self.assertRaisesRegex(ValueError, 'Native hgraph closure disagrees'):
                blueprint.validate_graph(graph, sources, {'pending', 'result'})
            graph.add_edge(sources['result']['lean_id'], sources['pending']['lean_id'], 'uses')
            blueprint.validate_graph(graph, sources, {'pending', 'result'})

    def test_compiled_private_homonyms_remain_separate_native_nodes(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            original_root = blueprint.ROOT
            try:
                blueprint.ROOT = root
                rows = []
                for suffix in ('A', 'B'):
                    module = 'KIP126.SpectralSequence.' + suffix
                    path = root / ('KIP126/SpectralSequence/' + suffix + '.lean')
                    path.parent.mkdir(parents=True, exist_ok=True)
                    path.write_text('module\nnamespace Shared\n'
                                    'def helper : Nat := 1\nend Shared\n')
                    rows.append({'module': module, 'source_name': 'Shared.helper',
                                 'name': '_private.' + module + '.0.Shared.helper',
                                 'dependencies': [], 'direct_sorry': False, 'line': 3})
                sources = blueprint.index_sources(rows)
                dependencies = blueprint.project_dependencies(rows, sources)
                blueprint.generate_blueprint(sources, dependencies)
                (root / 'blueprint/content.tex').write_text(
                    '\\chapter{SpectralSequence}\n\\input{generated/SpectralSequence.tex}\n')
                graph = Graph.open(root)
                blueprint.sync_kernel_graph(graph, sources, dependencies)
                nodes = [graph.resolve('decl:' + r['name']) for r in rows]
                self.assertNotEqual(*nodes)
                target = node_id('bp', next(iter(sources.values()))['label'])
                graph.add_comment(target, 'Keep this source review.', author='reviewer')
                graph.modify_node(target, set_meta={'tags': ['human-authored']})
                report = blueprint.sync_kernel_graph(graph, sources, dependencies)
                self.assertEqual(report['node_changes'] + report['edge_changes'], 0)
                self.assertEqual(graph.comments(target)[0].content, 'Keep this source review.')
                self.assertIn('human-authored', graph.get_node(target).meta['tags'])
            finally:
                blueprint.ROOT = original_root


    def test_main_remark_sync_uses_compiled_public_identity_and_status(self):
        from hgraph.sync import parse_blueprint
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            original_root = blueprint.ROOT
            try:
                blueprint.ROOT = root
                module = 'KIP126.Main.Remarks'
                name = 'KIP126.Main.local_proof'
                path = root / 'KIP126/Main/Remarks.lean'
                path.parent.mkdir(parents=True)
                path.write_text('module\nnamespace KIP126.Main\n'
                                'public theorem local_proof : True := by trivial\n'
                                'end KIP126.Main\n')
                sources = blueprint.index_sources([{'module': module,
                    'source_name': 'KIP126.Main.local_proof', 'name': name,
                    'dependencies': [], 'direct_sorry': False, 'line': 3}])
                # Unknown compiled evidence must remain unknown in the native
                # remark too; the lack of lexical sorry cannot make it green.
                sources[name]['lean_status'] = 'empty'
                deps = {name: set()}
                blueprint.generate_blueprint(sources, deps)
                document = ('\\chapter{Main}\n\\begin{remark}[A consequence]\n'
                    '\\label{sem:Main:remark-7.4}\n'
                    '\\lean{KIP126.Main.local_proof}\n'
                    '\\uses{' + sources[name]['label'] + '}\n'
                    'A precise consequence.\\end{remark}\n')
                (root / 'blueprint/content.tex').write_text(document)
                (root / 'blueprint/generated/implementation.tex').write_text('\\input{Main.tex}\n')
                rows, _ = parse_blueprint(document)
                rows[0]['lean'] = blueprint.semantic.resolve_main_remark(rows[0], sources, {name: 'Main'})
                projection = blueprint.semantic.make_projection(sources, deps, {}, rows)
                graph = Graph.open(root)
                blueprint.sync_kernel_graph(graph, sources, deps, projection)
                target = node_id('bp', rows[0]['label'])
                self.assertEqual(graph.get_node(target).meta['lean_status'], 'empty')
                self.assertTrue(graph.has_node(node_id('lean', name)))
            finally:
                blueprint.ROOT = original_root


class DraftPublicationTests(unittest.TestCase):
    def test_build_report_refresh_updates_json_without_recreating_retired_pages(self):
        import gzip
        import json
        spec = importlib.util.spec_from_file_location('publisher_build_evidence',
            Path(__file__).resolve().parents[1] / 'scripts/publish-blueprint.py')
        publisher = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(publisher)
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            publisher.ROOT, publisher.STATE = root, root / 'state'
            publisher.STATE.mkdir()
            live = root / '_site'
            (live / 'Kervaire126').mkdir(parents=True)
            evidence = {'publication_mode':'curated-mathematical-blueprint',
                        'full_project_build':{'status':'unknown'},
                        'checks':{'native_closure_matches_selected_compiled_evidence':True},
                        'source_declarations':4159, 'direct_obligations':299}
            (live / 'validation.json').write_text(json.dumps(evidence))
            before = {}
            for name in ('data.json', 'project.json'):
                payload = {'entries':[{'label':'paper:2.12', 'lean_status':'lean_ok',
                                       'state':'formalized_open', 'deps':['pending'],
                                       'statement':'All original hypotheses remain.'}],
                           'edges':[{'source':'paper:2.12', 'target':'pending', 'type':'uses'}],
                           'customTabs':[{'id':'memo', 'html':'Original memo'}],
                           'map':{'chapters':['SpectralSequence', 'Main'], 'edges':[[0,1]]}}
                path = live / 'Kervaire126' / name
                path.write_text(json.dumps(payload, indent=3))
                path.with_suffix('.json.gz').write_bytes(gzip.compress(path.read_bytes(), mtime=0))
                before[path] = path.read_bytes()
                before[path.with_suffix('.json.gz')] = path.with_suffix('.json.gz').read_bytes()
            report = {'status':'failed', 'required_for_publication':False,
                      'blocking_module':'Tests.Main.Interface'}
            publisher.full_build_report = lambda: report
            publisher.refresh_build_report()
            updated = json.loads((live / 'validation.json').read_text())
            self.assertEqual(updated['full_project_build'], report)
            self.assertTrue(updated.pop('build_report_refresh')['all_mathematical_payloads_and_bindings_unchanged'])
            updated['full_project_build'] = evidence['full_project_build']
            self.assertEqual(updated, evidence)
            for path, raw in before.items():
                self.assertEqual(path.read_bytes(), raw)
            self.assertEqual(gzip.decompress((live / 'validation.json.gz').read_bytes()),
                             (live / 'validation.json').read_bytes())
            self.assertFalse((live / 'verification.html').exists())
            self.assertFalse((live / 'implementation').exists())
            self.assertFalse((publisher.STATE / 'verification.html').exists())

    def test_restored_verified_source_does_not_inherit_stale_ui_open_state(self):
        spec = importlib.util.spec_from_file_location('publisher_restoration',
            Path(__file__).resolve().parents[1] / 'scripts/publish-blueprint.py')
        publisher = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(publisher)
        sources = {'base': {'lean_status': 'empty', 'row': {'direct_sorry': False}},
                   'result': {'row': {'direct_sorry': False}}}
        deps = {'base': set(), 'result': {'base'}}
        self.assertEqual(publisher.source_open_nodes(sources, deps), {'base', 'result'})
        sources['base']['lean_status'] = 'lean_ok'
        self.assertEqual(publisher.source_open_nodes(sources, deps), set())

    def test_new_public_alias_can_be_discovered_and_remain_unknown_on_failed_build(self):
        import json
        spec = importlib.util.spec_from_file_location('publisher_alias_discovery',
            Path(__file__).resolve().parents[1] / 'scripts/publish-blueprint.py')
        publisher = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(publisher)
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            previous = publisher.ROOT
            try:
                publisher.ROOT = root
                source = root / 'KIP126/ProofTools/Alias.lean'
                source.parent.mkdir(parents=True)
                source.write_text('module\nnamespace Shared\nsection\n'
                                  '-- public alias decoy := unavailable\n'
                                  'public alias result :=\n  unavailable\n'
                                  'end\nend Shared\n')
                private = source.with_name('Private.lean')
                private.write_text('module\nnamespace Shared\nalias result := unavailable\nend Shared\n')
                (root / 'metadata').mkdir()
                (root / 'metadata/proof-tools-api.json').write_text(json.dumps({
                    'schema_version': 4, 'declarations': [
                        {'name': 'Shared.result', 'type_fingerprint': '123',
                         'universes': [], 'axioms': []}]}))
                self.assertEqual(publisher.public_source_paths({'Shared.result'}), {source})
                unknown = publisher.unknown_support({source})
                self.assertEqual(set(unknown), {'Shared.result'})
                self.assertEqual(unknown['Shared.result']['lean_status'], 'empty')
                self.assertEqual(unknown['Shared.result']['body'], 'public alias result :=\n  unavailable')
                self.assertEqual(unknown['Shared.result']['row']['line'], 5)
                self.assertFalse(unknown['Shared.result']['row']['direct_sorry'])
            finally:
                publisher.ROOT = previous

    def test_unknown_support_uses_source_without_metadata_or_false_public_identities(self):
        spec = importlib.util.spec_from_file_location('publisher_source_discovery',
            Path(__file__).resolve().parents[1] / 'scripts/publish-blueprint.py')
        publisher = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(publisher)
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            previous = publisher.ROOT
            try:
                publisher.ROOT = root
                source = root / 'KIP126/ProofTools/Draft.lean'
                source.parent.mkdir(parents=True)
                source.write_text('module\nnamespace Outer\nnamespace Inner\n'
                                  '/- public alias fake := unavailable -/\n'
                                  'public def message : String := "public alias fake := unavailable"\n'
                                  'alias localResult := unavailable\n'
                                  'public alias _root_.Exported.result := unavailable\n'
                                  'public theorem pending : True := by sorry\n'
                                  'end Inner\nend Outer\n')
                unknown = publisher.unknown_support({source})
                self.assertEqual(set(unknown), {
                    'Outer.Inner.message', 'KIP126.ProofTools.Draft:Outer.Inner.localResult',
                    'Exported.result', 'Outer.Inner.pending'})
                self.assertTrue(all(row['lean_status'] == 'empty' for row in unknown.values()))
                self.assertTrue(unknown['Outer.Inner.pending']['row']['direct_sorry'])
                self.assertEqual(unknown['Exported.result']['row']['line'], 7)
                self.assertIn('"public alias fake := unavailable"', unknown['Outer.Inner.message']['body'])
            finally:
                publisher.ROOT = previous

    def test_build_report_does_not_gate_publication_and_tracks_latest_result(self):
        spec = importlib.util.spec_from_file_location('publisher_build_report',
            Path(__file__).resolve().parents[1] / 'scripts/publish-blueprint.py')
        publisher = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(publisher)
        with tempfile.TemporaryDirectory() as directory:
            original_state, original_root = publisher.STATE, publisher.ROOT
            try:
                publisher.ROOT = Path(directory)
                publisher.STATE = Path(directory)
                log = publisher.STATE / 'current-project-build.log'
                log.write_text('error: KIP126/ProofTools/Example.lean:3:1: unsolved goals\nerror: build failed\n')
                report = publisher.full_build_report()
                self.assertEqual(report['status'],'failed')
                self.assertFalse(report['required_for_publication'])
                self.assertEqual(report['blocking_module'],'KIP126.ProofTools.Example')
                log.write_text('Build completed successfully (3090 jobs).\n')
                report = publisher.full_build_report()
                self.assertEqual(report['status'],'passed')
                self.assertFalse(report['required_for_publication'])
                self.assertIsNone(report['blocking_module'])
            finally:
                publisher.STATE, publisher.ROOT = original_state, original_root

    def test_unverified_lean_target_never_turns_green_in_native_sync(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            original_root = blueprint.ROOT
            try:
                blueprint.ROOT = root
                path = root / 'KIP126/SpectralSequence/Draft.lean'
                path.parent.mkdir(parents=True)
                path.write_text('module\npublic def pending : Nat := 1\n')
                rows = [{'module':'KIP126.SpectralSequence.Draft','source_name':'pending',
                         'name':'pending','dependencies':[],'direct_sorry':False,'line':2}]
                sources = blueprint.index_sources(rows)
                sources['pending']['lean_status'] = 'empty'
                deps = {'pending':set()}
                blueprint.generate_blueprint(sources, deps)
                (root / 'blueprint/content.tex').write_text('\\chapter{Draft}\n\\input{generated/SpectralSequence.tex}\n')
                graph = Graph.open(root)
                blueprint.sync_kernel_graph(graph, sources, deps)
                from hgraph.analysis import Analysis
                states = Analysis(graph)
                for nid in (node_id('lean','pending'), node_id('bp',sources['pending']['label'])):
                    self.assertEqual(graph.get_node(nid).meta['lean_status'], 'empty')
                    self.assertFalse(states.closed[nid])
            finally:
                blueprint.ROOT = original_root

    def test_changed_source_file_invalidates_cached_green_status(self):
        import hashlib
        from hgraph.dashboard import _clip
        spec = importlib.util.spec_from_file_location('draft_publisher',
            Path(__file__).resolve().parents[1] / 'scripts/publish-blueprint.py')
        publisher = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(publisher)
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            original_root = publisher.ROOT
            try:
                publisher.ROOT = root
                path = root / 'KIP126/SpectralSequence/Draft.lean'
                path.parent.mkdir(parents=True)
                body = 'public def value : Nat := 1'
                path.write_text('module\n' + body + '\n')
                graph = Graph.open(root)
                nid = node_id('lean','value'); bp = node_id('bp','decl:source')
                graph.add_node('value',id=nid,type='lean',content=body,
                    statement=body,context='module',lean_status='lean_ok')
                graph.add_node('value',id=bp,type='tex',source_line=2)
                data = {'entries':[{'id':bp,'label':'decl:source','kind':'definition','deps':[],
                    'lean_status':'lean_ok','lean':[{'name':'value','code':_clip(body),
                    'file':str(path.relative_to(root)),'statement':body,'context':'module','status':'lean_ok'}]}]}
                evidence = {'inputs':{str(path.relative_to(root)):hashlib.sha256(path.read_bytes()).hexdigest()}}
                sources, _ = publisher.cached_sources(data,evidence,graph)
                self.assertEqual(sources['value']['lean_status'],'lean_ok')
                path.write_text('module\npublic def value : Nat := broken\n')
                sources, _ = publisher.cached_sources(data,evidence,graph)
                self.assertEqual(sources['value']['lean_status'],'empty')
                self.assertEqual(sources['value']['body'],body)
            finally:
                publisher.ROOT = original_root


class AimPaperBoundaryTests(unittest.TestCase):
    def test_web_copy_preserves_every_nonpaper_tex_statement(self):
        from blueprint_paper import prepare_web_blueprint
        from hgraph.sync import parse_blueprint, read_blueprint
        root = Path(__file__).resolve().parents[1]
        with tempfile.TemporaryDirectory() as directory:
            web = prepare_web_blueprint(root, Path(directory) / 'web')
            for path in (root / 'blueprint').rglob('*.tex'):
                if path.parent.name == 'paper' and '% AimPaper: ' in path.read_text():
                    continue
                self.assertEqual(path.read_bytes(),
                                 (web / path.relative_to(root / 'blueprint')).read_bytes(),
                                 str(path))
            authored, _ = parse_blueprint(read_blueprint(root / 'blueprint/content.tex'))
            rendered, _ = parse_blueprint(read_blueprint(web / 'content.tex'))
            self.assertEqual([r['label'] for r in authored], [r['label'] for r in rendered])

    def test_two_line_corollary_binds_the_complete_proof_and_keeps_its_target_definition(self):
        from hgraph.sync import parse_blueprint, read_blueprint
        root = Path(__file__).resolve().parents[1]
        _, corollary = self.paper_source(root, 'paper:1.5')
        self.assertEqual(corollary['lean'], ['KIP126.Main.adams_two_line_classification'])
        self.assertFalse(corollary['sketch'])
        rows, _ = parse_blueprint(read_blueprint(root / 'blueprint/semantic/Main.tex'))
        target = next(row for row in rows if row['label'] == 'sem:Main:two-line-classification-goal')
        self.assertEqual(target['content_type'], 'definition')
        self.assertEqual(set(target['lean']), {'KIP126.Main.AdamsTwoLineListed',
                                              'KIP126.Main.AdamsTwoLineClassification'})
        self.assertIn('does not prove', target['body'])
        partial = next(row for row in rows if row['label'] == 'sem:Main:two-line-known-squares')
        self.assertEqual(partial['lean'], ['KIP126.Main.adams_two_line_known_squares'])

    def paper_source(self, root, label):
        from hgraph.sync import parse_blueprint, read_blueprint
        matches = [(path, row) for path in (root / 'blueprint/paper').glob('*.tex')
                   for row in parse_blueprint(read_blueprint(path))[0]
                   if row['label'] == label]
        self.assertEqual(len(matches), 1, f'Expected one authored source for {label}')
        return matches[0]

    def paper_fixture(self, root):
        original = Path(__file__).resolve().parents[1]
        shutil.copytree(original / 'blueprint/paper', root / 'blueprint/paper')
        (root / 'AimPaper').mkdir()
        for name in ('main.tex', 'main.bib'):
            shutil.copyfile(original / 'AimPaper' / name, root / 'AimPaper' / name)
        labels = {}
        for path in (root / 'blueprint/paper').glob('*.tex'):
            for name, label in re.findall(r'\\item \\texttt\{([^}]+)\}[:：]\s*\\ref\{(decl:[^}]+)\}', path.read_text()):
                name = name.replace(r'\_', '_')
                labels[label] = {'lean_name': name, 'fqname': name}
        from hgraph.sync import parse_blueprint
        for path in (root / 'blueprint/paper').glob('*.tex'):
            rows, _ = parse_blueprint(path.read_text())
            for row in rows:
                refs = list(dict.fromkeys(label for label in row['uses'] if label.startswith('decl:')))
                if len(refs) != len(row['lean']):
                    raise ValueError('Fixture binding/reference mismatch')
                for name, label in zip(row['lean'], refs):
                    labels.setdefault(label, {'lean_name': name, 'fqname': name})
        return labels

    def test_changed_source_and_unrelated_formalization_are_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            labels = self.paper_fixture(root)
            records, stats = blueprint.load_paper(root, labels)
            self.assertEqual(stats['statements'], 57)
            self.assertEqual(stats['displayed_nodes'], 56)
            self.assertEqual(stats['mathematical_dependencies_reviewed'], 57)
            self.assertEqual(stats['mathematical_dependency_edges'], 175)
            repeated = next(r for r in records if r['number'] == '7.1')
            self.assertEqual(repeated['canonical_label'], 'paper:1.4')
            self.assertEqual(stats['cited_entries'], 56)
            partial = next(r for r in records if r['number'] == '2.1')
            self.assertEqual(len(partial['lean']), 1)
            self.assertTrue(partial['sketch'])
            self.assertEqual(stats['bound_statements'], 42)
            self.assertNotIn('% Blueprint note:', partial['body'])
            self.assertNotIn('% Correspondence:', partial['body'])
            path, _ = self.paper_source(root, 'paper:2.1')
            content = path.read_text()
            path.write_text(content.replace('For a map', 'For every arbitrary map', 1))
            with self.assertRaisesRegex(ValueError, 'differs from its source'):
                blueprint.load_paper(root, labels)
            path.write_text(content.replace('\\label{paper:2.1}',
                '\\label{paper:2.1}\\lean{KIP126.Main.h6_sq_permanent}'))
            with self.assertRaisesRegex(ValueError, 'does not uniquely match'):
                blueprint.load_paper(root, labels)

    def test_partial_mapping_requires_scope_marker_and_actual_sources(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            labels = self.paper_fixture(root)
            path, _ = self.paper_source(root, 'paper:2.1')
            path.write_text(path.read_text().replace('\\sketch\n', '', 1))
            with self.assertRaisesRegex(ValueError, 'needs native sketch'):
                blueprint.load_paper(root, labels)

    def test_private_binding_uses_its_explicit_source_instead_of_namespace_guess(self):
        sources = {'decl:A': {'fqname':'Shared.helper','lean_name':'_private.A.0.Shared.helper'},
                   'decl:B': {'fqname':'Shared.helper','lean_name':'_private.B.0.Shared.helper'}}
        statement = {'body':'A mathematical statement without implementation links.',
                     'lean':['Shared.helper'], 'uses':['decl:B']}
        self.assertEqual(blueprint.resolve_paper_bindings(statement, sources),
                         ['_private.B.0.Shared.helper'])
        statement['uses'].append('decl:A')
        with self.assertRaisesRegex(ValueError, 'does not uniquely match'):
            blueprint.resolve_paper_bindings(statement, sources)

    def test_hidden_status_and_scope_notes_do_not_render(self):
        from blueprint_paper import correspondence_status, display_body
        from hgraph.sync import parse_blueprint
        text = ('\\begin{theorem}\n\\label{paper:1.1}\n'
                'For every $x$, $x=x$.\n'
                '% Correspondence: partial.\n'
                '% Blueprint note: A scope restriction.\n'
                '\\lean{actual}\n\\uses{decl:actual}\n\\sketch\n\\end{theorem}')
        self.assertEqual(correspondence_status(text, '1.1'), 'partial.')
        rows, _ = parse_blueprint(text)
        rendered = display_body(rows[0]['body'], '1.1')
        self.assertIn('For every $x$, $x=x$', rendered)
        self.assertNotIn('Correspondence', rendered)
        self.assertNotIn('scope restriction', rendered)
        self.assertTrue(rows[0]['sketch'])
        self.assertEqual(blueprint.resolve_paper_bindings(rows[0], {
            'decl:actual': {'lean_name':'actual', 'fqname':'actual'}}), ['actual'])

    def test_missing_duplicate_and_empty_correspondence_statuses_are_rejected(self):
        from blueprint_paper import correspondence_status
        for text in ('A statement.', '% Correspondence:   \n'):
            with self.subTest(text=text), self.assertRaisesRegex(ValueError, 'Missing correspondence'):
                correspondence_status(text, '1.1')
        for text in ('% Correspondence: partial.\n% Correspondence: public.\n',
                     '% Correspondence: partial.\n\\textbf{Correspondence: partial.}',
                     '\\textbf{Correspondence: partial.}\\textbf{Correspondence: public.}'):
            with self.subTest(text=text), self.assertRaisesRegex(ValueError, 'exactly one'):
                correspondence_status(text, '1.1')

    def test_explicit_dependency_bindings_reject_unlisted_and_wrong_sources(self):
        sources = {'decl:A': {'fqname':'A', 'lean_name':'A'},
                   'decl:B': {'fqname':'B', 'lean_name':'B'}}
        for statement, error in (
                ({'body':'The statement.', 'lean':['A'], 'uses':['decl:B']}, 'does not uniquely match'),
                ({'body':'The statement.', 'lean':['A'], 'uses':['decl:missing']}, 'Unknown Lean correspondence'),
                ({'body':'The statement.', 'lean':['A'], 'uses':['decl:A', 'decl:B']}, 'Every listed correspondence'),
                ({'body':r'\ref{decl:B}', 'lean':['A'], 'uses':['decl:A']}, 'inherit every bound source')):
            with self.subTest(statement=statement), self.assertRaisesRegex(ValueError, error):
                blueprint.resolve_paper_bindings(statement, sources)

    def test_bound_partial_inherits_open_dependencies_without_claiming_closure(self):
        from hgraph.analysis import Analysis
        with tempfile.TemporaryDirectory() as directory:
            graph = Graph.open(directory)
            target = node_id('lean', 'actual')
            source = node_id('bp', 'decl:actual')
            pending = graph.add_node('upstream', type='lean', lean_status='sorry')
            paper = node_id('bp', 'paper:2.1')
            graph.add_node('actual', id=target, type='lean', lean_status='lean_ok')
            graph.add_node('actual source', id=source, type='tex', lean_status='lean_ok')
            graph.add_node('paper', id=paper, type='tex', lean_status='lean_ok', sketch=True)
            graph.add_edge(target, pending, 'uses')
            graph.add_edge(source, pending, 'uses')
            graph.add_edge(paper, source, 'uses')
            graph.add_edge(paper, target, 'formalizes')
            records = [{'label':'paper:2.1','number':'2.1','lean':['actual'],
                        'mapping_labels':['decl:actual'],'sketch':True}]
            states = blueprint.validate_paper_graph(graph, records, Analysis(graph))
            self.assertEqual(states, {'formalized_open':1})
            graph.modify_node(paper, set_meta={'sketch':False})
            with self.assertRaisesRegex(ValueError, 'scope marker differs'):
                blueprint.validate_paper_graph(graph, records, Analysis(graph))

    def test_unknown_citation_and_broken_public_correspondence_are_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            labels = self.paper_fixture(root)
            with self.assertRaisesRegex(ValueError, 'Unknown Lean correspondence'):
                blueprint.load_paper(root, {})
            path = root / 'AimPaper/main.tex'
            path.write_text(path.read_text() + '\\cite{NonexistentBibliographyKey}')
            with self.assertRaisesRegex(ValueError, 'bibliography missing citations'):
                blueprint.load_paper(root, labels)

    def test_chapter_and_detail_rendering_both_use_compatible_math(self):
        from blueprint_paper import (display_body,
                                     prepare_web_blueprint, reference_targets)
        from hgraph.sync import read_blueprint, parse_blueprint
        root = Path(__file__).resolve().parents[1]
        original, _ = parse_blueprint(read_blueprint(root / 'blueprint/content.tex'))
        refs = reference_targets(root, original)
        diagram_sources = [row for row in original
                           if row['label'].startswith('paper:') and r'\xymatrix' in row['body']]
        self.assertTrue(diagram_sources)
        source_path, source_diagram = self.paper_source(root, 'paper:2.12')
        self.assertIn(r'\xymatrix', source_diagram['body'])
        authored = {path: path.read_bytes() for path in (root / 'blueprint/paper').glob('*.tex')}
        with tempfile.TemporaryDirectory() as directory:
            destination = prepare_web_blueprint(root, Path(directory) / 'web')
            statements, _ = parse_blueprint(read_blueprint(destination / 'content.tex'))
            paper = [row for row in statements if row['label'].startswith('paper:')]
            self.assertEqual(len(paper), 56)
            permanence = next(row for row in paper if row['label'] == 'paper:1.4')
            self.assertIn('paper:7.1', permanence['labels'])
            self.assertIn('thm:126survives', permanence['labels'])
            self.assertFalse(any(row['label'] == 'paper:7.1' for row in paper))
            self.assertEqual(permanence['title'], 'Permanence of $h_6^2$')
            self.assertIn(r'(From \cite{LWX126}, Theorem 1.4, Theorem 7.1.)', permanence['body'])
            self.assertNotIn('[Theorem', permanence['body'])
            original_permanence = next(row for row in original if row['label'] == 'paper:1.4')
            self.assertNotIn('[Theorem', display_body(original_permanence['body'], '1.4', refs))
            by_label = {row['label']: row for row in paper}
            for source in diagram_sources:
                with self.subTest(label=source['label']):
                    number = source['label'].removeprefix('paper:')
                    chapter_body = by_label[source['label']]['body']
                    detail_body = display_body(source['body'], number, refs)
                    self.assertNotIn(r'\xymatrix', chapter_body)
                    self.assertNotIn(r'\xymatrix', detail_body)
                    footer = (r'\par\href{paper/diagrams/' + number
                              + '.html}{Original diagrams and hypotheses}')
                    # Whole-chapter conversion appends the fallback link after
                    # the theorem; detail conversion appends it inside the body.
                    diagram_path, _ = self.paper_source(root, source['label'])
                    rendered_path = destination / diagram_path.relative_to(root / 'blueprint')
                    self.assertIn(footer, rendered_path.read_text())
                    self.assertEqual(' '.join((chapter_body + '\n' + footer).split()),
                                     ' '.join(detail_body.split()))
            self.assertIn('Suppose $m,n,l', by_label['paper:2.12']['body'])
            self.assertNotIn(r'\xymatrix',
                             (destination / source_path.relative_to(root / 'blueprint')).read_text())
        for path, content in authored.items():
            self.assertEqual(path.read_bytes(), content, f'Rendering changed authored source: {path}')

    def test_external_bx_criterion_stays_upstream_of_main_choice_transport(self):
        from hgraph.sync import parse_blueprint, read_blueprint
        root = Path(__file__).resolve().parents[1]
        rows, _ = parse_blueprint(read_blueprint(root / 'blueprint/content.tex'))
        entries = {row['label']: row for row in rows}
        external = entries['paper:7.3']
        transport = entries['sem:Main:any-choice-criterion']
        self.assertTrue(external['chapter'].startswith('Literature'))
        self.assertEqual(set(external['lean']), {
            'KIP126.Literature.Standard.bx_finite',
            'KIP126.Literature.Standard.bx_untruncated'})
        self.assertTrue(external['sketch'])
        self.assertIn(r'\ref{sem:Main:any-choice-criterion}', external['body'])
        self.assertNotIn('sem:Main:any-choice-criterion', external['uses'])
        self.assertTrue(transport['chapter'].startswith('Main'))
        self.assertEqual(transport['lean'], ['KIP126.Main.any_choice_criterion'])

    def test_web_bibliography_resolves_doi_urls_without_changing_sources(self):
        from blueprint_paper import prepare_web_blueprint
        from hgraph.dashboard import discover_bib
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / 'blueprint'
            source.mkdir()
            (source / 'content.tex').write_text('')
            bibliography = source / 'references.bib'
            original = '''@article{full,
  title = {Full DOI URL},
  DOI = {https://doi.org/10.1007/s00222-024-01298-6},
}
@article{legacy,
  title = {Legacy DOI resolver},
  doi = "http://dx.doi.org/10.48550/arXiv.2105.07628",
}
@article{bare,
  title = {Bare DOI},
  doi = {10.1007/example},
}
@article{explicit,
  title = {Explicit URL},
  doi = {https://doi.org/10.1007/ignored},
  url = {https://example.org/paper},
}
'''
            bibliography.write_text(original)
            destination = prepare_web_blueprint(root, root / 'web')
            urls = {row['key']: row['url']
                    for row in discover_bib(destination / 'content.tex')}
            self.assertEqual(urls, {
                'full': 'https://doi.org/10.1007/s00222-024-01298-6',
                'legacy': 'https://doi.org/10.48550/arXiv.2105.07628',
                'bare': 'https://doi.org/10.1007/example',
                'explicit': 'https://example.org/paper'})
            self.assertEqual(bibliography.read_text(), original)

    def test_paper_statement_numbers_and_primes_survive_browser_layout(self):
        from blueprint_paper import display_body
        text = r"\begin{enumerate} \setcounter{enumi}{2}\item first \item second \end{enumerate}"
        result = display_body(text, '7.8')
        self.assertIn(r'\item[(3)]', result)
        self.assertIn(r'\item[(4)]', result)
        prime = r"\begin{enumerate}[label=(\arabic*')]\setcounter{enumi}{3}\item hypothesis\end{enumerate}"
        self.assertIn(r"\item[(4')]", display_body(prime, '7.10'))

    def test_diagram_and_reference_fallback_retain_original_conditions(self):
        from blueprint_paper import display_body
        original = r"Assume $x=0$. $$\xymatrix{X \ar[r]^f & Y}$$ Then $y=0$ (\ref{original})."
        rendered = display_body(original, '2.12', {'original': ('#/Kervaire126#paper:1.4', '1.4')})
        self.assertIn('Assume $x=0$', rendered)
        self.assertIn('Then $y=0$', rendered)
        self.assertIn('paper/diagrams/2.12.html', rendered)
        self.assertIn(r'\href{#/Kervaire126#paper:1.4}{1.4}', rendered)
        self.assertNotIn(r'\xymatrix', rendered)


if __name__ == '__main__':
    unittest.main()
