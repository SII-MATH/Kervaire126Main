#!/usr/bin/env python3
"""Publish authored paper mappings independently of a whole-project build.

Reuse the last verified declaration snapshot. Compile only new source modules
needed by the paper, retaining explicit unverified states if those fail.
Full repository verification remains available through build-blueprint.py.
"""
import argparse
from collections import Counter, defaultdict, deque
from copy import deepcopy
from datetime import datetime, timezone
import hashlib
import gzip
import importlib.util
import json
from pathlib import Path
import re
import sys
import tempfile

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / 'scripts'))
spec = importlib.util.spec_from_file_location('blueprint_builder', ROOT / 'scripts/build-blueprint.py')
b = importlib.util.module_from_spec(spec)
spec.loader.exec_module(b)
from hgraph.analysis import Analysis
from hgraph.dashboard import _clip
from hgraph.graph import Graph, node_id
from hgraph.sync import parse_lean

STATE = b.STATE
BASELINE = STATE / 'paper-binding-baseline'


def full_build_report():
    logs = [p for p in (STATE / 'current-project-build.log', STATE / 'build.log') if p.exists()]
    if not logs:
        return {'status': 'unknown', 'required_for_publication': False}
    path = max(logs, key=lambda p: p.stat().st_mtime)
    text = path.read_text()
    status = 'passed' if 'Build completed successfully' in text else 'failed' if 'error: build failed' in text else 'unknown'
    failed = re.findall(r'error:\s+(KIP126/[^\s:]+)\.lean:', text)
    return {'status': status, 'required_for_publication': False,
            'blocking_module': failed[0].replace('/', '.') if status == 'failed' and failed else None,
            'log': str(path.relative_to(ROOT)), 'log_sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
            'scope': 'Latest recorded build run; subsequent source edits are not implicitly verified.'}


def verification_html(evidence):
    if evidence.get('semantic_blueprint'):
        b.semantic.write_verification(STATE, evidence)
        return (STATE / 'verification.html').read_text()
    stats, target = evidence['aimpaper'], evidence['targeted_verification']
    status = evidence['full_project_build']['status']
    body = '<h2>Paper mappings and publication verification</h2><p>Publication and whole-project verification are tracked separately. A failed whole-project build does not prevent publishing reviewed correspondences.</p>'
    body += f'<p>{stats["statements"]} paper statements; {stats["bound_statements"]} bound statements, including {stats["partial_bound_statements"]} partial correspondences marked as sketches. Geometric endpoints have their own chapter.</p>'
    body += f'<p>{evidence["baseline"]["source_declarations"]} declarations reuse a verified compiled snapshot. Independent support-module verification: {"passed" if target["target_build"] else "failed; affected nodes remain unverified"}. Unverified source nodes: {len(evidence["unverified_source_labels"])}.</p>'
    body += '<p>Latest recorded whole-project build: ' + {'passed':'passed', 'failed':'failed', 'unknown':'in progress or no complete result recorded'}[status] + '. This report does not gate publication. Existing proof obligations and unverified source states are recorded separately.</p>'
    body += f'<p>There are {evidence["direct_obligations"]} unique Lean proof or construction obligations. Paper and source entries can refer to the same obligation; displayed entries do not create additional obligations.</p>'
    return body + '<p>Local completion and transitive dependency closure are checked separately. Partial correspondences retain their sketch markers and explicit scope; local status does not assert the full generality of the original paper.</p>'


def refresh_build_report():
    """Refresh the secondary report, preserving mathematics and other tabs.

    Older exports may still embed a verification tab. Update that tab when
    present; an export without it keeps data/project files byte-for-byte intact.
    """
    live = ROOT / '_site'
    paths = ['validation.json', 'Kervaire126/data.json', 'Kervaire126/project.json']
    if (live / 'verification.html').exists():
        paths.append('verification.html')
    original = {name: (live / name).read_bytes() for name in paths}
    evidence = json.loads(original['validation.json'])
    if evidence.get('publication_mode') not in ('paper-mappings-with-scoped-verification', 'curated-mathematical-blueprint'):
        raise ValueError('Publish the authored paper mappings first')
    evidence['full_project_build'] = full_build_report()
    evidence['build_report_refresh'] = {
        'updated_at_utc': datetime.now(timezone.utc).isoformat(),
        'publisher_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'all_mathematical_payloads_and_bindings_unchanged': True}
    body = verification_html(evidence)
    payloads = {'validation.json': evidence}
    for name in ('Kervaire126/data.json', 'Kervaire126/project.json'):
        before = json.loads(original[name])
        after = deepcopy(before)
        tabs = [tab for tab in after.get('customTabs', []) if tab['id'] == 'verification']
        if len(tabs) > 1:
            raise ValueError('Expected at most one native verification tab')
        if not tabs:
            continue
        tabs[0]['html'] = body
        restored = deepcopy(after)
        next(tab for tab in restored['customTabs'] if tab['id'] == 'verification')['html'] = next(
            tab for tab in before['customTabs'] if tab['id'] == 'verification')['html']
        if restored != before:
            raise ValueError('Build report refresh changed mathematical payloads')
        payloads[name] = after
    documents = {name: json.dumps(payload, ensure_ascii=False) for name, payload in payloads.items()}
    documents['verification.html'] = b.blueprint_map.verification_document(body)
    with tempfile.TemporaryDirectory(dir=STATE, prefix='build-report-') as directory:
        replacements = []
        for index, (name, document) in enumerate(documents.items()):
            temporary = Path(directory) / str(index)
            temporary.write_text(document)
            compressed = temporary.with_suffix('.gz')
            compressed.write_bytes(gzip.compress(temporary.read_bytes(), mtime=0))
            replacements.extend([(temporary, live / name), (compressed, live / (name + '.gz'))])
        if any((live / name).read_bytes() != content for name, content in original.items()):
            raise ValueError('Published snapshot changed while updating build report')
        for source, destination in replacements:
            source.replace(destination)
    (STATE / 'verification.html').write_text(body)
    print('Updated full-build report; all declaration/proof/binding data preserved.')


def hashes(paths):
    return {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(paths)}


def source_open_nodes(sources, dependencies):
    """Derive open states from verified source evidence, never mutable old UI state."""
    opened = {name for name in sources if b.semantic.local_status([name], sources) not in b.semantic.DONE}
    reverse = defaultdict(set)
    for name, deps in dependencies.items():
        for dependency in deps:
            reverse[dependency].add(name)
    pending = deque(opened)
    while pending:
        for name in reverse[pending.popleft()]:
            if name not in opened:
                opened.add(name)
                pending.append(name)
    return opened


def source_declarations(text):
    """Read source locations, including aliases, without metadata provenance.

    Native parsing already tracks namespaces, sections and declaration bounds.
    Give it an equal-width lexical stand-in for ``alias`` so it can do the same
    for those commands; restore every displayed character from the real source.
    This only discovers source commands, never compiled identities or proof state.
    """
    code = b.scan_lean(text).code
    alias_pattern = re.compile(
        r'^[ \t]*(?:@\[[^\]\n]*\][ \t]*)?'
        r'(?:(?:public|private|protected|noncomputable|unsafe)[ \t]+)*(alias)\b', re.M)
    aliases = list(alias_pattern.finditer(code))
    shadow = list(text)
    for match in aliases:
        shadow[match.start(1):match.end(1)] = 'lemma'
    shadow = ''.join(shadow)
    declarations, cursor = [], 0
    module_default_private = bool(re.search(r'^\s*module\b', code, re.M))
    for parsed in parse_lean(shadow):
        declaration = dict(parsed)
        offset = shadow.find(parsed['body'], cursor)
        if offset < 0:
            raise ValueError('Native declaration cannot be located in its source')
        end = offset + len(parsed['body'])
        cursor = end
        body = text[offset:end]
        declaration['body'] = body
        declaration['line'] = text.count('\n', 0, offset) + 1
        local_code = code[offset:end]
        declaration['public'] = (bool(re.search(r'\bpublic\b', local_code.splitlines()[0]))
                                 or (not module_default_private and not parsed['private']))
        declaration['private'] = not declaration['public']
        if any(offset <= match.start(1) < end for match in aliases):
            declaration['kind'] = 'theorem'
            declaration['statement'] = body
        declarations.append(declaration)
    return declarations


def public_source_paths(names):
    """Locate locked public names in current source, not obsolete lock fields."""
    locked = {declaration['name'] for path in (ROOT / 'metadata').glob('*-api.json')
              for declaration in json.loads(path.read_text()).get('declarations', [])}
    wanted = set(names) & locked
    if not wanted:
        return set()
    return {path for path in (ROOT / 'KIP126').rglob('*.lean')
            if any(d['public'] and d['fqname'] in wanted
                   for d in source_declarations(path.read_text()))}


def module_inputs(modules):
    pending, seen, paths = list(modules), set(), set()
    while pending:
        module = pending.pop()
        if module in seen or not module.startswith('KIP126.'):
            continue
        seen.add(module)
        path = ROOT / (module.replace('.', '/') + '.lean')
        paths.add(path)
        code = b.scan_lean(path.read_text()).code
        for match in re.finditer(r'^\s*(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?([^\n]+)', code, re.M):
            pending.extend(match[1].split())
    paths.update(ROOT / name for name in ('lean-toolchain', 'lake-manifest.json', 'lakefile.lean'))
    return hashes(paths)


def cached_sources(data, evidence, graph):
    """A cached green node must match the actual verified Lean payload."""
    result, dependencies, file_hashes = {}, {}, {}
    labels = {r['id']: r for r in data['entries'] if r['label'].startswith('decl:')}
    for row in labels.values():
        if len(row['lean']) != 1:
            raise ValueError('Expected one cached Lean identity per source declaration')
        lean = row['lean'][0]
        nid = node_id('lean', lean['name'])
        node = graph.get_node(nid)
        if (_clip(node.content) != lean['code'] or node.meta.get('statement') != lean['statement']
                or node.meta.get('context') != lean['context']
                or node.meta.get('lean_status') != lean['status']):
            raise ValueError('Cached Lean payload differs from its verified snapshot: ' + lean['name'])
        name = lean['name']
        source_node = graph.get_node(row['id'])
        fqname = re.sub(r'^_private\..*?\.\d+\.', '', name)
        line = source_node.meta.get('source_line') or 1
        deps = {labels[d['id']]['lean'][0]['name'] for d in row['deps'] if d['type'] == 'uses'}
        path = ROOT / lean['file']
        if lean['file'] not in file_hashes:
            file_hashes[lean['file']] = hashes([path])[lean['file']] if path.exists() else None
        same_file = file_hashes[lean['file']] == evidence['inputs'].get(lean['file'])
        result[name] = {'fqname': fqname, 'kind': 'theorem' if row['kind'] == 'theorem' else 'def',
            'body': node.content, 'statement': lean['statement'], 'context': lean['context'],
            'doc': lean.get('docstring') or '', 'file': lean['file'], 'owner': lean['file'].split('/')[1],
            'lean_name': name, 'lean_id': nid, 'label': row['label'],
            'lean_status': row['lean_status'] if same_file else 'empty',
            'row': {'name': name, 'source_name': fqname, 'line': line,
                    'direct_sorry': row['lean_status'] == 'sorry', 'dependencies': sorted(deps)},
            'verification': 'compiled-snapshot' if same_file else 'unverified-source-change',
            'source_sha256': file_hashes[lean['file']]}
        dependencies[name] = deps
    return result, dependencies


def new_support(sources, required):
    existing = {s['label'] for s in sources.values()}
    missing = required - existing
    paths = set()
    for path in (ROOT / 'KIP126').rglob('*.lean'):
        module = str(path.relative_to(ROOT).with_suffix('')).replace('/', '.')
        for declaration in source_declarations(path.read_text()):
            if b.label(module, declaration['fqname']) in missing:
                paths.add(path)
    return paths


def capture_support(paths):
    modules = sorted(str(p.relative_to(ROOT).with_suffix('')).replace('/', '.') for p in paths)
    before = module_inputs(modules)
    checkpoint = STATE / 'paper-target-checkpoint.json'
    output = STATE / 'targets-kernel.json'
    saved = json.loads(checkpoint.read_text()) if checkpoint.exists() else {}
    if saved.get('inputs') == before and saved.get('modules') == modules and output.exists():
        if saved.get('capture_sha256') == hashlib.sha256(output.read_bytes()).hexdigest():
            return json.loads(output.read_text()), saved
    try:
        b.run_logged(['lake', 'build', *modules], 'paper-target-build.log')
        template = (ROOT / 'scripts/BlueprintCapture.lean').read_text().split('import Lean', 1)[1]
        condition = ' || '.join('mod.toString == ' + json.dumps(m) for m in modules)
        template = template.replace('let axioms ← collectAxioms name',
            'let axioms ← if ' + condition + ' then collectAxioms name else pure #[]')
        template = template.replace('".lake/blueprint/kernel.json"', '".lake/blueprint/targets-kernel.json"')
        capture = STATE / 'TargetCapture.lean'
        capture.write_text('module\n' + ''.join('import all ' + m + '\n' for m in modules) + 'import Lean\n' + template)
        b.run_logged(['lake', 'env', 'lean', str(capture.relative_to(ROOT))], 'paper-target-capture.log')
        if module_inputs(modules) != before:
            raise ValueError('Support source inputs changed during capture')
        record = {'modules': modules, 'inputs': before, 'target_build': True,
                  'capture_sha256': hashlib.sha256(output.read_bytes()).hexdigest(),
                  'captured_at_utc': datetime.now(timezone.utc).isoformat()}
        checkpoint.write_text(json.dumps(record, ensure_ascii=False, indent=2))
        return json.loads(output.read_text()), record
    except (RuntimeError, ValueError) as error:
        # Publication still proceeds: a failure never becomes a green node.
        return [], {'modules': modules, 'inputs': before, 'target_build': False, 'error': str(error)}


def unknown_support(paths):
    result = {}
    for path in paths:
        module = str(path.relative_to(ROOT).with_suffix('')).replace('/', '.')
        text = path.read_text()
        for d in source_declarations(text):
            # Uncompiled private identities are scoped explicitly; they are not
            # asserted to be compiler kernel names or published public exports.
            name = d['fqname'] if not d['private'] else module + ':' + d['fqname']
            result[name] = {**d, 'file': str(path.relative_to(ROOT)), 'owner': module.split('.')[1],
                'lean_name': name, 'lean_id': node_id('lean', name), 'label': b.label(module, d['fqname']),
                'lean_status': 'empty', 'verification': 'unverified-support-module',
                'row': {'name': name, 'source_name': d['fqname'], 'line': d['line'],
                        'direct_sorry': d['sorry'], 'dependencies': []}}
    return result


def mathematical_source_paths():
    """Compile mathematical producers separately from repository audit consumers.

    Audit failures remain in the full-build report. An audit file containing a
    named mathematical declaration cannot silently be excluded from capture.
    """
    paths = set()
    for path in (ROOT / 'KIP126').rglob('*.lean'):
        if path.name == 'InternalAudit.lean':
            if source_declarations(path.read_text()):
                raise ValueError('Audit contains named mathematical declarations: ' + str(path))
        else:
            paths.add(path)
    modules = [str(path.relative_to(ROOT).with_suffix('')).replace('/', '.') for path in paths]
    closure = module_inputs(modules)
    if any(Path(name).name == 'InternalAudit.lean' or name.startswith(('Tests/', 'Checks/'))
           for name in closure):
        raise ValueError('Mathematical source capture imports audit consumers')
    return paths


def publish(*, refresh_source_evidence=False):
    b.verify_native_runtime()
    b.run_logged([sys.executable, '-m', 'unittest', 'discover', '-s', 'Tests', '-p', 'test_blueprint*.py'], 'paper-tests.log')
    b.run_logged(['python3', 'scripts/check-source-inventory.py'], 'paper-inventory.log')
    if not BASELINE.exists():
        prior = json.loads((ROOT / '_site/validation.json').read_text())
        if not all(prior['checks'].values()):
            raise ValueError('Initialize from an existing verified declaration snapshot')
        BASELINE.mkdir()
        for name in ('validation.json', 'Kervaire126/data.json'):
            destination = BASELINE / Path(name).name
            destination.write_bytes((ROOT / '_site' / name).read_bytes())
    graph = Graph.open(ROOT)
    snapshot = STATE / 'verified-source-snapshot.json'
    if snapshot.exists():
        if hashlib.sha256(snapshot.read_bytes()).hexdigest() != snapshot.with_suffix('.sha256').read_text():
            raise ValueError('Verified source snapshot checksum mismatch')
        saved = json.loads(snapshot.read_text())
        original, sources = saved['evidence'], saved['sources']
        dependencies = {n: set(ds) for n, ds in saved['dependencies'].items()}
        current = hashes({ROOT / s['file'] for s in sources.values()})
        for source in sources.values():
            same = current[source['file']] == original['inputs'][source['file']]
            source['verification'] = 'compiled-snapshot' if same else 'unverified-source-change'
            source['source_sha256'] = current[source['file']]
            if not same:
                source['lean_status'] = 'empty'
    else:
        data = json.loads((BASELINE / 'data.json').read_text())
        original = json.loads((BASELINE / 'validation.json').read_text())
        sources, dependencies = cached_sources(data, original, graph)
    required = {label for path in (ROOT / 'blueprint/paper').glob('*.tex')
                for label in re.findall(r'\\ref\{(decl:[^}]+)\}', path.read_text())}
    # New public semantic bindings receive the same independently compiled
    # support-module treatment as new paper correspondences.
    semantic_statements, _ = b.parse_blueprint(b.read_blueprint(ROOT / 'blueprint/content.tex'))
    # Main remarks identify private proofs by explicit stable declaration IDs;
    # their source spellings are not public kernel names to rediscover.
    required.update(label for row in semantic_statements
                    if row['label'].startswith('sem:Main:remark-')
                    for label in row['uses'] if label.startswith('decl:'))
    needed_names = {name for row in semantic_statements if row['label'].startswith('sem:')
                    and not row['label'].startswith('sem:Main:remark-')
                    for name in row['lean']} - sources.keys()
    if needed_names:
        for path in (ROOT / 'KIP126').rglob('*.lean'):
            module = str(path.relative_to(ROOT).with_suffix('')).replace('/', '.')
            for declaration in source_declarations(path.read_text()):
                if declaration['fqname'] in needed_names:
                    required.add(b.label(module, declaration['fqname']))
    paths = new_support(sources, required)
    paths.update(public_source_paths(needed_names))
    if refresh_source_evidence:
        paths.update(mathematical_source_paths())
    b.phase(f'Publishing paper mappings using {len(sources)} cached declarations and {len(paths)} support module(s)…')
    rows, target = capture_support(paths) if paths else ([], {'modules': [], 'inputs': {}, 'target_build': True})
    new = b.index_sources(rows, paths) if target['target_build'] else unknown_support(paths)
    if refresh_source_evidence:
        if not target['target_build']:
            raise ValueError('Complete mathematical source capture failed: ' + target.get('error', 'unknown'))
        old_labels = {source['label'] for source in sources.values()}
        if not old_labels <= {source['label'] for source in new.values()}:
            raise ValueError('Current mathematical source capture lost a baseline declaration')
        b.validate_api_coverage(new)
    if target['target_build']:
        actual = [r for r in rows if r['module'] in target['modules']]
        registered = {r['name'] for r in json.loads((ROOT / 'metadata/proof-obligations.json').read_text())['obligations']}
        if any(r['is_axiom'] or r['synthetic_sorry'] or (r['direct_sorry'] and r['name'] not in registered) for r in actual):
            raise ValueError('Support capture introduced an axiom or unregistered hole')
    for s in new.values():
        s.setdefault('verification', 'targeted-compiled')
        s['source_sha256'] = target['inputs'][s['file']]
    # A recompiled private identity can change while its stable source label
    # stays the same. Reconcile that identity instead of duplicating the source.
    new_labels = {source['label']: name for name, source in new.items()}
    replaced = {name: new_labels[source['label']] for name, source in sources.items()
                if source['label'] in new_labels and name != new_labels[source['label']]}
    for name in replaced:
        sources.pop(name)
        dependencies.pop(name)
    dependencies = {name: {replaced.get(dep, dep) for dep in deps} for name, deps in dependencies.items()}
    sources.update(new)
    projected = b.project_dependencies(rows, sources)
    dependencies.update({name: projected[name] for name in new})
    baseline_open = source_open_nodes(sources, dependencies)
    records, stats = b.load_paper(ROOT, {s['label']: s for s in sources.values()})
    obligations = {r['name']: r for r in json.loads((ROOT / 'metadata/proof-obligations.json').read_text())['obligations']}
    if {name for name, s in sources.items() if s['row']['direct_sorry']} != set(obligations):
        raise ValueError('The actual registered proof obligations changed; refresh their compiled evidence')
    selected = {ROOT / s['file'] for s in sources.values()}
    represented_inputs = {s['file']: s['source_sha256'] for s in sources.values()}
    authored = b.site_inputs()
    b.generate_blueprint(sources, dependencies, obligations, records)
    projection = b.semantic.prepare(ROOT, sources, dependencies, obligations, records)
    b.phase('Synchronizing native bindings, source links and actual dependency states…')
    report = b.sync_kernel_graph(graph, sources, dependencies, projection)
    b.annotate_graph(graph, sources, dependencies, obligations)
    for name, s in sources.items():
        unverified = s.get('lean_status') == 'empty'
        for nid in (s['lean_id'], node_id('bp', s['label'])):
            n = graph.get_node(nid)
            tags = set(n.meta.get('tags') or []) - {'unverified'}
            if unverified:
                tags.add('unverified')
                note = '\n\\par This source has not yet been verified and cannot establish proof completion.\n'
                if nid == node_id('bp', s['label']):
                    graph.modify_node(nid, content=n.content + note if note not in n.content else n.content)
            graph.modify_node(nid, set_meta={'tags': sorted(tags), 'verification': s['verification']})
    analysis = b.validate_graph(graph, sources, baseline_open)
    stats['native_states'] = b.validate_paper_graph(graph, records, analysis, projection)
    semantic_stats = b.semantic.validate(graph, projection, analysis)
    documented = [node_id('bp', label) for label in projection['entries']]
    source_states = Counter(analysis.states[node_id('bp', s['label'])] for s in sources.values())
    states = Counter(analysis.states[nid] for nid in documented)
    local = Counter(analysis.nodes[nid].meta.get('lean_status') or 'empty' for nid in documented)
    unverified = [s['label'] for s in sources.values() if s.get('lean_status') == 'empty']
    evidence = {'generated_at_utc': datetime.now(timezone.utc).isoformat(),
        'publication_mode': 'curated-mathematical-blueprint', 'working_tree_snapshot': True,
        'semantic_blueprint': semantic_stats,
        'source_commit': original['source_commit'],
        'hgraph_repository': b.HGRAPH_REPOSITORY, 'hgraph_revision': b.PIN,
        'hgraph_runtime_sha256': b.RUNTIME_SHA256,
        'inputs': represented_inputs, 'input_fingerprint': b.fingerprint(represented_inputs),
        'site_inputs': authored, 'site_input_fingerprint': b.fingerprint(authored),
        'source_declarations': len(sources), 'compiled_declarations': len(rows) if refresh_source_evidence else original['compiled_declarations'] + sum(r['module'] in target['modules'] for r in rows),
        'direct_obligations': len(obligations), 'projected_dependency_edges': sum(map(len, dependencies.values())),
        'aimpaper': stats, 'states': dict(source_states), 'native_states_including_paper': dict(states),
        'native_local_statuses': dict(local), 'unverified_source_labels': unverified,
        'native_summary_ready_now': sum(not analysis.local[nid] and all(analysis.local[d] for d in analysis.deps[nid]) for nid in documented),
        'source_summary_ready_now': sum(not analysis.local[node_id('bp', s['label'])]
            and all(analysis.local[d] for d in analysis.deps[node_id('bp', s['label'])]) for s in sources.values()),
        'baseline': {'generated_at_utc': original['generated_at_utc'], 'input_fingerprint': original['input_fingerprint'],
                     'source_declarations': original['source_declarations'], 'checks': original['checks']},
        'targeted_verification': target,
        'refreshed_all_mathematical_source_evidence': refresh_source_evidence,
        'full_project_build': full_build_report(),
        'scope': ('Every mathematical source was independently compiled and its complete declaration evidence recaptured; '
                  'repository audit consumers remain in the separate full-build report. '
                  'This is not a claim that the current whole repository builds.' if refresh_source_evidence else
                  'Cached declaration evidence plus independently checked support modules; not a claim that the current whole repository builds.'),
        'checks': {'source_inventory': True, 'blueprint_boundary_tests': True,
                   'pinned_native_code_and_frontend_verified': True, 'cached_lean_payloads_match_baseline': True,
                   'aimpaper_statements_verbatim_and_exhaustive': True,
                   'aimpaper_all_citation_keys_resolved': True,
                   'paper_bindings_match_actual_lean_and_partial_scopes_are_marked': True,
                   'native_closure_matches_selected_compiled_evidence': True,
                   'unverified_nodes_cannot_be_marked_complete': True}}
    body = verification_html(evidence)
    (STATE / 'verification.html').write_text(body)
    (STATE / 'mapping-publication.json').write_text(json.dumps(evidence, ensure_ascii=False, indent=2))
    (STATE / 'mapping-sync.json').write_text(json.dumps(report, ensure_ascii=False, indent=2))
    b.phase('Exporting the native frontend; full-project verification remains separate…')
    b.export_site(evidence, records, ROOT / '_site',
                  lambda: hashes(selected) == represented_inputs and b.site_inputs() == authored,
                  (sources, dependencies, obligations, analysis))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--refresh-build-report', action='store_true')
    parser.add_argument('--refresh-source-evidence', action='store_true',
                        help='Compile and capture every mathematical source, retaining the separate full-build audit report')
    args = parser.parse_args()
    if args.refresh_build_report and args.refresh_source_evidence:
        parser.error('Choose either a build-report refresh or a source-evidence refresh')
    refresh_build_report() if args.refresh_build_report else publish(refresh_source_evidence=args.refresh_source_evidence)
