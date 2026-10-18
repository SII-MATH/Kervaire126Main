#!/usr/bin/env python3
"""Import the current Lean environment into native hgraph and export its site.

No Lean source, interface lock, obligation registry or hgraph implementation is
rewritten. Blueprint/Lean nodes, uses/formalizes edges, tags and workflow states
use hgraph's own schema. Compiler-generated helpers are traversed, not ignored.
"""
from __future__ import annotations

import argparse
from collections import Counter, defaultdict, deque
import hashlib
import html
import gzip
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
from datetime import datetime, timezone

sys.path.insert(0, str(Path(__file__).resolve().parent))
from blueprint_paper import load_paper, display_body, export_paper, validate_paper_graph, reference_targets, prepare_web_blueprint, resolve_paper_bindings
import blueprint_semantic as semantic
import blueprint_map
from blueprint_annotations import sync_authoring_notes

from hgraph.analysis import Analysis
from hgraph.lean_source import scan_lean
from hgraph.graph import Graph, node_id
from hgraph.site import write_from_manifest
from hgraph.sync import (parse_lean, parse_blueprint, read_blueprint,
                        _upsert, _tex_lean_status, _status_warnings,
                        _label_warnings, _unlabeled_statement_warnings,
                        LEAN_KINDS)

ROOT = Path(__file__).resolve().parent.parent
STATE = ROOT / '.lake/blueprint'
MODULES = ('SpectralSequence', 'AdamsSynthetic', 'Literature',
           'E2Computation', 'ProofTools', 'AdamsCalculations', 'Main')
HGRAPH_REPOSITORY = 'https://github.com/SII-MATH/hgraph'
PIN = '6dce6022de98ffda2cde18cc7441526c4577efa7'
RUNTIME_SHA256 = '0f75d03ee9f345276c173dc34d632d2bc9d4f4b4fc5672791fbaa52898238ada'
IMPORTER = 'kip126-lean-kernel'


def phase(message):
    print(message, flush=True)


def inputs():
    paths = {ROOT / p for p in ('lean-toolchain', 'lakefile.lean',
             'lake-manifest.json', 'metadata/proof-obligations.json',
             'KIP126.lean', 'scripts/BlueprintCapture.lean')}
    for directory in ('KIP126', 'Tests', 'Checks'):
        paths.update((ROOT / directory).rglob('*.lean'))
    paths.update((ROOT / 'metadata').glob('*-api.json'))
    return {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in sorted(paths)}


def fingerprint(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True).encode()).hexdigest()


def site_inputs():
    paths = [ROOT / p for p in ('scripts/build-blueprint.py', 'scripts/publish-blueprint.py', 'scripts/blueprint_paper.py', 'scripts/blueprint_semantic.py', 'scripts/blueprint_annotations.py', 'scripts/serve-blueprint.py', 'requirements-blueprint.txt',
             'Tests/test_blueprint.py', 'Tests/test_blueprint_semantic.py', 'Tests/test_blueprint_annotations.py', 'Tests/check_blueprint_formulae.py', 'hgraph/config.yaml', 'site/config.yaml', 'site/overview.html')]
    paths.extend(p for p in (ROOT / 'blueprint').rglob('*')
                 if p.is_file() and 'generated' not in p.parts)
    paths.extend([ROOT / 'MEMO.md', ROOT / 'scripts/blueprint_map.py', ROOT / 'Tests/test_blueprint_map.py',
                  ROOT / 'Tests/check_blueprint_map.py'])
    paths.extend(ROOT / 'AimPaper' / p for p in ('main.tex', '112.tex', 'main.bib', 'algtop.sty', '2412.10879.pdf'))
    return {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in sorted(paths)}


def verify_native_runtime():
    import hgraph
    directory = Path(hgraph.__file__).parent
    files = {str(p.relative_to(directory)): hashlib.sha256(p.read_bytes()).hexdigest()
             for p in sorted(directory.rglob('*')) if p.is_file() and '__pycache__' not in p.parts}
    if fingerprint(files) != RUNTIME_SHA256:
        raise ValueError('Installed hgraph code/assets differ from the pinned hgraph revision')


def run_logged(command, name):
    path = STATE / name
    with path.open('w') as out:
        result = subprocess.run(command, cwd=ROOT, stdout=out, stderr=subprocess.STDOUT)
    if result.returncode:
        print(path.read_text()[-12000:], file=sys.stderr)
        raise RuntimeError(f'{command[0]} failed; see {path}')


def tex(text):
    chars = {'\\': r'\textbackslash{}', '{': r'\{', '}': r'\}',
             '_': r'\_', '%': r'\%', '#': r'\#', '&': r'\&',
             '$': r'\$', '^': r'\textasciicircum{}', '~': r'\textasciitilde{}'}
    return ''.join(chars.get(c, c) for c in text)


def label(module, name):
    # A private declaration's kernel prefix can change as a file is edited.
    # Source module + user name stays stable, preserving native review IDs.
    # The approved computation split changes physical ownership, while source
    # review IDs and article correspondences retain their original identity.
    for owner in ('E2Computation', 'AdamsCalculations'):
        prefix = 'KIP126.' + owner
        if module == prefix or module.startswith(prefix + '.'):
            module = 'KIP126.Computation' + module[len(prefix):]
            break
    return 'decl:' + hashlib.sha256(f'{module}:{name}'.encode()).hexdigest()[:16]


def index_sources(rows, paths=None):
    by_key = defaultdict(list)
    by_location = defaultdict(list)
    for row in rows:
        by_key[(row['module'], row['source_name'])].append(row)
        by_location[(row['module'], row.get('line'))].append(row)
    sources = {}
    for path in sorted(paths if paths is not None else (ROOT / 'KIP126').rglob('*.lean')):
        relative = str(path.relative_to(ROOT))
        module = str(path.relative_to(ROOT).with_suffix('')).replace('/', '.')
        text = path.read_text()
        declarations = parse_lean(text)
        lines = text.splitlines()
        code_lines = scan_lean(text).code.splitlines()
        # `alias` is a source command with a real compiled theorem/definition;
        # upstream's lexical declaration list does not currently include it.
        # Resolve it by compiled source range and name, never by guessing RHS.
        for index, code_line in enumerate(code_lines):
            if not re.match(r'^\s*(?:(?:public|private|protected)\s+)*alias\b', code_line):
                continue
            match = re.match(r'^\s*(?:(?:public|private|protected)\s+)*alias\s+([^\s:=]+)\s*:=', lines[index])
            if not match:
                raise ValueError(f'Unsupported alias syntax: {relative}:{index + 1}')
            short_name = match[1]
            candidates = [r for r in by_location[(module, index + 1)]
                          if r['source_name'] == short_name
                          or r['source_name'].endswith('.' + short_name)]
            if len(candidates) != 1:
                raise ValueError(f'Alias does not have one compiled identity: {relative}:{index + 1}')
            row = candidates[0]
            end = index + 1
            while end < len(lines) and (not lines[end].strip() or lines[end][0].isspace()):
                end += 1
            body = '\n'.join(lines[index:end]).rstrip()
            declarations.append({'fqname': row['source_name'],
                'kind': row['declaration_kind'], 'body': body, 'statement': body,
                'context': '\n'.join(lines[:index]), 'doc': '',
                'sorry': row['direct_sorry'], 'private': row['name'].startswith('_private.')})
        for declaration in declarations:
            matches = by_key[(module, declaration['fqname'])]
            if len(matches) != 1:
                raise ValueError(f'Expected one compiled declaration: {relative}: '
                                 f'{declaration["fqname"]}; got {len(matches)}')
            row = matches[0]
            if declaration['sorry'] != row['direct_sorry']:
                raise ValueError(f'Lexical/kernel local status mismatch: {row["name"]}')
            sources[row['name']] = {
                **declaration, 'row': row, 'file': relative,
                'owner': module.split('.')[1],
                'label': label(module, row['source_name']),
                'lean_id': node_id('lean', declaration['fqname']),
            }
    # A module-private name can occur in multiple files. Kernel names, unlike
    # lexical namespace names, are unique. The readable title and source body
    # remain unchanged; stable Blueprint labels carry comments across edits.
    for name, source in sources.items():
        source['lean_name'] = name
        source['lean_id'] = node_id('lean', name)
    return sources


def validate_api_coverage(sources):
    names = set(sources)
    expected = set()
    for path in (ROOT / 'metadata').glob('*-api.json'):
        expected.update(d['name'] for d in json.loads(path.read_text()).get('declarations', []))
    missing = expected - names
    if missing:
        raise ValueError(f'Locked public interfaces missing from source index: {sorted(missing)}')
    return len(expected)


def project_dependencies(rows, sources):
    by_name = {row['name']: row for row in rows}
    result = {}
    for name, source in sources.items():
        pending = list(source['row']['dependencies'])
        seen, found = {name}, set()
        while pending:
            dependency = pending.pop()
            if dependency in seen:
                continue
            seen.add(dependency)
            if dependency in sources:
                found.add(dependency)
            elif dependency in by_name:
                pending.extend(by_name[dependency]['dependencies'])
        result[name] = found
    return result


def validate_kernel(rows, sources, dependencies, obligations):
    direct = {row['name'] for row in rows if row['direct_sorry']}
    if not direct <= sources.keys():
        raise ValueError(f'Unrepresented direct holes: {direct - sources.keys()}')
    if any(row['is_axiom'] or row['synthetic_sorry'] for row in rows):
        raise ValueError('Project axiom or synthetic sorry in compiled capture')
    actual = direct
    if actual != set(obligations):
        raise ValueError(f'Obligation mismatch: missing={set(obligations) - actual}; '
                         f'unregistered={actual - set(obligations)}')
    reverse = defaultdict(set)
    for name, deps in dependencies.items():
        for dependency in deps:
            reverse[dependency].add(name)
    open_nodes, pending = set(direct), deque(direct)
    while pending:
        for dependent in reverse[pending.popleft()]:
            if dependent not in open_nodes:
                open_nodes.add(dependent)
                pending.append(dependent)
    for name, source in sources.items():
        if (name in open_nodes) != ('sorryAx' in source['row']['axioms']):
            raise ValueError(f'Projected dependency closure disagrees with Lean: {name}')
    return open_nodes


def generate_blueprint(sources, dependencies, obligations=None, paper_records=()):
    generated = ROOT / 'blueprint/generated'
    generated.mkdir(parents=True, exist_ok=True)
    paper_links = defaultdict(list)
    for record in paper_records:
        for target in record['mapping_labels']:
            paper_links[target].append(record)
    for owner in MODULES:
        entries = sorted((s for s in sources.values() if s['owner'] == owner),
                         key=lambda s: (s['file'], s['row']['line'] or 0, s['fqname']))
        chunks = ['% Generated by scripts/build-blueprint.py; edit authored chapters instead.\n']
        previous = None
        for source in entries:
            if source['file'] != previous:
                chunks.append('\\section{' + tex(source['file'].removeprefix('KIP126/')) + '}\n')
                previous = source['file']
            kind = 'theorem' if source['kind'] in ('theorem', 'lemma') else 'definition'
            title = tex(source['fqname'].removeprefix('KIP126.'))
            chunks += ['\\begin{' + kind + '}[' + title + ']\n',
                       '\\label{' + source['label'] + '}\n',
                       '\\lean{' + source['lean_name'] + '}\n']
            deps = sorted(sources[d]['label'] for d in dependencies[source['row']['name']])
            if deps:
                chunks.append('\\uses{' + ','.join(deps) + '}\n')
            if source.get('lean_status', 'sorry' if source['row']['direct_sorry'] else 'lean_ok') in ('lean_ok', 'mathlib_ok'):
                chunks.append('\\leanok\n')
            # Keep the imported stage honest: this is a source index with its
            # original docs, not a newly authored informal mathematical proof.
            doc = ' '.join(source['doc'].split())
            if doc:
                chunks.append(tex(doc) + '\n\n')
            obligation = (obligations or {}).get(source['row']['name'])
            if obligation:
                kind_label = {'pending-construction': 'construction pending', 'pending-proof': 'proof pending'}[obligation['status']]
                chunks.append('Existing obligation: ' + kind_label + ' (' + obligation['status'] + ').\n\n')
            chunks.append('See the associated Lean declaration for the complete statement and proof.\n\n')
            for record in paper_links[source['label']]:
                chunks.append('AimPaper counterpart: ' + tex(record['title']) + ', \\ref{'
                              + record['label'] + '} (' + tex(record['mapping_status']) + ').\n')
            source_url = 'source/' + source['file'] + '.html#L' + str(source['row']['line'] or 1)
            chunks.append('\\href{' + source_url + '}{Source: ' + tex(source['file'])
                          + ':' + str(source['row']['line'] or 1) + '}\n')
            chunks.append('\\end{' + kind + '}\n\n')
        (generated / f'{owner}.tex').write_text(''.join(chunks))


def sync_kernel_graph(graph, sources, dependencies, projection=None):
    """Native parsers, schema and reconciliation, with kernel identities.

    The upstream lexical sync cannot distinguish module-private homonyms.
    This source adapter supplies compiled identities to native Lean nodes and
    uses the upstream Blueprint/status parsers and native Graph operations.
    It neither modifies hgraph nor manufactures substitute Lean source.
    """
    changes = 0
    interfaces = semantic.public_interfaces(ROOT)
    status = {}
    lean_ids = {}
    seen = set()
    for source in sources.values():
        name = source['lean_name']
        nid = source['lean_id']
        status[name] = source.get('lean_status', 'sorry' if source['row']['direct_sorry'] else 'lean_ok')
        lean_ids[name] = nid
        changes += _upsert(graph, nid, title=source['fqname'], type='lean',
            content=source['body'], owned={
                'generated': 'lean', 'author': 'sync', 'decl': name,
                'content_type': LEAN_KINDS.get(source['kind'], source['kind']),
                'lean_status': status[name], 'file': source['file'],
                'statement': source['statement'], 'docstring': source['doc'] or None,
                'context': source['context'] or None,
                'private': True if name not in interfaces else None})
        seen.add(nid)
    document = read_blueprint(ROOT / 'blueprint/content.tex')
    if projection is not None:
        document += '\n' + read_blueprint(ROOT / 'blueprint/generated/implementation.tex')
    statements, proofs = parse_blueprint(document)
    if proofs:
        raise ValueError('Generated declaration index unexpectedly contains authored proof blocks')
    warnings = _unlabeled_statement_warnings(document) + _label_warnings(statements)
    ids = {alias: node_id('bp', s['label']) for s in statements for alias in s['labels']}
    desired_edges = {}
    paper_refs = reference_targets(ROOT, statements)
    source_labels = {source['label']: source for source in sources.values()}
    for order, statement in enumerate(statements):
        correspondence = []
        if statement['label'].startswith('paper:'):
            correspondence = list(statement['uses'])
            statement = {**statement, 'lean': resolve_paper_bindings(statement, source_labels)}
        if projection is not None and statement['label'] in projection['uses']:
            statement = {**statement,
                         'lean': projection['entries'][statement['label']]['lean'],
                         'uses': sorted(projection['uses'][statement['label']])}
        local_status, mathlib_names = _tex_lean_status(statement, status)
        # Native lexical sync treats any resolved target without `sorry` as
        # complete, even an explicitly unverified `empty` target. Preserve the
        # conservative draft status instead of turning it green.
        if any(status.get(name) == 'empty' for name in statement['lean']):
            local_status = 'sorry' if any(status.get(name) == 'sorry' for name in statement['lean']) else 'empty'
        semantic_entry = projection['entries'].get(statement['label']) if projection else None
        if semantic_entry is not None:
            local_status = semantic_entry['local_status']
        warnings.extend(_status_warnings(statement, status))
        nid = ids[statement['label']]
        seen.add(nid)
        is_paper = statement['label'].startswith('paper:')
        content = display_body(statement['body'], statement['label'].removeprefix('paper:'), paper_refs) if is_paper else statement['body']
        archived = projection is not None and statement['label'].startswith('decl:')
        changes += _upsert(graph, nid, title=statement['title'], type='implementation' if archived else 'tex',
            content=content, owned={
                'content_type': statement['content_type'], 'generated': 'blueprint',
                'author': 'sync', 'label': statement['label'], 'chapter': statement['chapter'],
                'order': order, 'lean_status': local_status,
                'source_local_status': semantic_entry['source_local_status'] if semantic_entry else None,
                'internal_obligations': [sources[name]['label'] for name in
                    semantic_entry['internal_producers']] if semantic_entry else None,
                'mathlib_name': mathlib_names or None, 'ref': statement.get('ref') or None,
                'level': statement.get('level') or None,
                'sketch': True if statement.get('sketch') else None})
        for name in statement['lean']:
            if name not in lean_ids:
                raise ValueError(f'Unresolved compiled Lean identity: {name}')
            desired_edges[nid, lean_ids[name]] = 'formalizes'
        for dependency in statement['uses']:
            if dependency not in ids:
                raise ValueError(f'Unresolved Blueprint dependency: {dependency}')
            desired_edges[nid, ids[dependency]] = 'uses'
        if is_paper:
            # A native soft relation expresses correspondence without claiming
            # equivalence or adding an unreviewed mathematical prerequisite.
            for target in correspondence:
                if target not in ids:
                    raise ValueError(f'Unresolved paper correspondence: {target}')
                desired_edges.setdefault((nid, ids[target]), 'related_to')
    if warnings:
        raise ValueError(f'Native Blueprint warnings: {warnings[:10]}')
    # Formal-scope reports belong to native comments, never statement bodies.
    sync_authoring_notes(graph, ROOT)
    existing = {(e.source, e.target): e for e in graph.edges()
                if e.attrs.get('generated') == 'blueprint'}
    edge_changes = 0
    for pair, kind in desired_edges.items():
        old = existing.get(pair)
        if old is None:
            graph.add_edge(*pair, kind, generated='blueprint')
            edge_changes += 1
        elif old.type != kind:
            graph.add_edge(*pair, kind, replace=True, **old.attrs)
            edge_changes += 1
    for pair in existing.keys() - desired_edges.keys():
        edge = existing[pair]
        attachment_dir = graph.base / 'edges' / edge.id
        if attachment_dir.exists() and any(attachment_dir.iterdir()):
            raise ValueError(f'Retired dependency has authored attachments: {edge.id}')
        graph.delete_edge(edge.id)
        edge_changes += 1
    stale = 0
    for node in graph.nodes():
        if node.meta.get('generated') in ('lean', 'blueprint') and node.id not in seen:
            if not node.meta.get('stale'):
                graph.modify_node(node.id, type='implementation' if projection is not None and node.type == 'tex' else node.type,
                                  set_meta={'stale': True})
                stale += 1
    return {'blueprint': len(statements), 'lean': len(sources),
            'node_changes': changes, 'edge_changes': edge_changes,
            'stale': stale, 'warnings': warnings}


def annotate_graph(graph, sources, dependencies, obligations):
    """Authored fields/attachments stay native and survive the next sync.

    The native Blueprint parser already supplies Blueprint uses edges. Add the same kernel
    dependencies to its Lean population so decl: queries have correct closure,
    too. Only edges marked with this importer are reconciled here.
    """
    nodes = {n.id: n for n in graph.nodes()}
    interfaces = semantic.public_interfaces(ROOT)
    desired = set()
    for name, source in sources.items():
        row = source['row']
        blueprint_id = node_id('bp', source['label'])
        obligation = obligations.get(name)
        for nid in (blueprint_id, source['lean_id']):
            node = nodes[nid]
            auto_tags = {'module:' + source['owner'],
                         'visibility:public' if name in interfaces else 'visibility:private'}
            if obligation:
                auto_tags.add(obligation['status'])
            tags = set(node.meta.get('tags') or [])
            tags = {t for t in tags if not t.startswith(('module:', 'visibility:'))
                    and t not in ('pending-proof', 'pending-construction')}
            updates = {'tags': sorted(tags | auto_tags), 'kernel_name': row['name'],
                       'source_line': row['line'], 'source_file': source['file']}
            if obligation:
                updates['obligation_kind'] = obligation['status']
            # Do not overwrite a human-authored workflow state.
            if node.meta.get('status') in (None, 'pending-proof', 'pending-construction'):
                updates['status'] = obligation['status'] if obligation else None
            graph.modify_node(nid, set_meta=updates,
                              unset=[] if obligation else ['obligation_kind'])
        desired.update((source['lean_id'], sources[d]['lean_id']) for d in dependencies[name])
    existing = {(e.source, e.target): e for e in graph.edges()
                if e.attrs.get('importer') == IMPORTER}
    for pair in desired - existing.keys():
        # A foreign authored edge on this pair must be reviewed, never replaced.
        graph.add_edge(*pair, 'uses', importer=IMPORTER, origin='Lean compiled type and body')
    for pair in existing.keys() - desired:
        edge = existing[pair]
        attachment_dir = graph.base / 'edges' / edge.id
        if attachment_dir.exists() and any(attachment_dir.iterdir()):
            raise ValueError(f'Retired dependency has authored attachments: {edge.id}')
        graph.delete_edge(edge.id)


def validate_graph(graph, sources, open_nodes):
    analysis = Analysis(graph)
    for name, source in sources.items():
        expected_closed = name not in open_nodes
        for nid in (node_id('bp', source['label']), source['lean_id']):
            if analysis.closed[nid] != expected_closed:
                raise ValueError(f'Native hgraph closure disagrees with Lean: {name}')
    return analysis


def stage_workspace():
    workspace = STATE / 'workspace'
    project = workspace / 'Kervaire126'
    project.mkdir(parents=True, exist_ok=True)
    links = {workspace / 'config.yaml': ROOT / 'site/config.yaml',
             workspace / 'site': ROOT / 'site'}
    web_blueprint = prepare_web_blueprint(ROOT, STATE / 'web-blueprint')
    links.update({project / name: ROOT / name for name in ('KIP126', 'hgraph', '.lake', 'MEMO.md')})
    links[project / 'blueprint'] = web_blueprint
    for target, source in links.items():
        if target.is_symlink() and target.resolve() != source.resolve():
            target.unlink()
        if not target.is_symlink():
            target.symlink_to(source, target_is_directory=source.is_dir())
    return workspace


def export_sources(out):
    for path in sorted((ROOT / 'KIP126').rglob('*.lean')):
        relative = path.relative_to(ROOT)
        destination = out / 'source' / (str(relative) + '.html')
        destination.parent.mkdir(parents=True, exist_ok=True)
        title = html.escape(str(relative))
        lines = '\n'.join(f'<span id="L{i}"><a href="#L{i}">{i:4}</a> {html.escape(line)}</span>'
                          for i, line in enumerate(path.read_text().splitlines(), 1))
        destination.write_text('<!doctype html><meta charset="utf-8"><title>' + title
            + '</title><style>body{margin:24px;background:#fbfaf7;color:#222}'
              'pre{line-height:1.6}pre>span{display:block}pre>span:target{background:#fff0a8}'
              'a{color:#888;text-decoration:none}</style><h1>' + title + '</h1><pre>' + lines + '</pre>')


def write_evidence(sources, dependencies, rows, analysis, before, authored_inputs, paper_stats):
    totals = Counter()
    chapter_rows = []
    for owner in MODULES:
        items = [s for s in sources.values() if s['owner'] == owner]
        counts = Counter(analysis.states[node_id('bp', s['label'])] for s in items)
        totals.update(counts)
        chapter_rows.append({'module': owner, 'declarations': len(items), **dict(counts)})
    documented = [nid for nid, node in analysis.nodes.items()
                  if node.meta.get('generated') == 'blueprint' and node.type == 'tex' and not node.meta.get('stale')]
    native_totals = Counter(analysis.states[nid] for nid in documented)
    evidence = {
        'generated_at_utc': datetime.now(timezone.utc).isoformat(),
        'source_commit': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
        'working_tree_snapshot': True,
        'hgraph_repository': HGRAPH_REPOSITORY, 'hgraph_revision': PIN, 'input_fingerprint': fingerprint(before), 'inputs': before,
        'hgraph_runtime_sha256': RUNTIME_SHA256,
        'site_input_fingerprint': fingerprint(authored_inputs), 'site_inputs': authored_inputs,
        'aimpaper': paper_stats,
        'compiled_declarations': len(rows), 'source_declarations': len(sources),
        'projected_dependency_edges': sum(map(len, dependencies.values())),
        'direct_obligations': sum(r['direct_sorry'] for r in rows),
        'states': dict(totals), 'chapters': chapter_rows,
        'native_states_including_paper': dict(native_totals),
        'native_local_statuses': dict(Counter(analysis.nodes[nid].meta.get('lean_status') or 'empty' for nid in documented)),
        'native_summary_ready_now': sum(not analysis.local[nid]
            and all(analysis.local[d] for d in analysis.deps[nid]) for nid in documented),
        'source_summary_ready_now': sum(sources[name]['row']['direct_sorry']
            and all(not sources[d]['row']['direct_sorry'] for d in dependencies[name])
            for name in sources),
        'ready_semantics': 'The native Summary Ready now uses local status of direct prerequisites. '
                           'Native CLI Analysis ready requires their full closure.',
        'checks': {'source_inventory': True, 'lake_build': True, 'blueprint_boundary_tests': True,
                   'pinned_native_code_and_frontend_verified': True,
                   'source_to_kernel_unique': True, 'all_locked_public_interfaces_visible': True,
                   'all_direct_holes_registered_and_visible': True,
                   'lexical_local_status_matches_kernel': True,
                   'native_closure_matches_kernel_for_every_source_declaration': True,
                   'unchanged_inputs_during_capture': True,
                   'aimpaper_statements_verbatim_and_exhaustive': True,
                   'aimpaper_all_citation_keys_resolved': True,
                   'paper_bindings_match_actual_lean_and_partial_scopes_are_marked': True},
        'scope': 'Current source declarations; generated project helpers traversed. '
                 'External Lean/mathlib constants are trusted at their locked versions. '
                 'This imports formal dependency evidence, not a new informal proof or mathematical review.',
    }
    (STATE / 'validation.json').write_text(json.dumps(evidence, ensure_ascii=False, indent=2) + '\n')
    return evidence


def export_site(evidence, paper_records, out, still_current):
    workspace = stage_workspace()
    out = out.resolve()
    out.parent.mkdir(parents=True, exist_ok=True)
    staging = Path(tempfile.mkdtemp(prefix='.' + out.name + '-', dir=out.parent))
    try:
        write_from_manifest(workspace / 'config.yaml', out_path=staging / 'index.html')
        export_sources(staging)
        export_paper(ROOT, staging, paper_records)
        evidence['blueprint_map'] = blueprint_map.export_map(ROOT, staging)
        (staging / 'validation.json').write_text(json.dumps(evidence, ensure_ascii=False, indent=2) + '\n')
        (staging / 'inputs.json').write_text(json.dumps(evidence['inputs'], ensure_ascii=False, indent=2) + '\n')
        # A complete native declaration/dependency index is large. Compress at
        # export time; the native frontend and its JSON schema remain unchanged.
        for path in sorted(staging.rglob('*')):
            if path.is_file() and path.suffix in ('.json', '.html', '.js', '.css', '.svg'):
                if path.stat().st_size >= 1024:
                    path.with_name(path.name + '.gz').write_bytes(gzip.compress(path.read_bytes(), mtime=0))
        # Publish only after all files and fingerprints pass; never expose a
        # partial export or destroy a previously verified preview on failure.
        if not still_current():
            raise ValueError('Published inputs changed during site export; rerun before serving')
        previous = STATE / 'previous-site'
        if out.exists():
            if not (out / 'validation.json').exists():
                raise ValueError(f'Refusing to replace an unrecognized output directory: {out}')
            if previous.exists():
                if not (previous / 'validation.json').exists():
                    raise ValueError(f'Unrecognized backup directory: {previous}')
                shutil.rmtree(previous)
            out.rename(previous)
        try:
            staging.rename(out)
        except Exception:
            if previous.exists() and not out.exists():
                previous.rename(out)
            raise
    finally:
        if staging.exists():
            shutil.rmtree(staging)
    phase(f'Built {out}; states: {evidence["states"]}')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', type=Path, default=ROOT / '_site')
    args = parser.parse_args()
    STATE.mkdir(parents=True, exist_ok=True)
    verify_native_runtime()
    before = inputs()
    authored_inputs = site_inputs()
    phase('1/7 Checking source inventory and building the complete Lean project…')
    run_logged([sys.executable, '-m', 'unittest', 'discover', '-s', 'Tests', '-p', 'test_blueprint*.py'], 'tests.log')
    run_logged(['python3', 'scripts/check-source-inventory.py'], 'inventory.log')
    run_logged(['lake', 'build'], 'build.log')
    phase('2/7 Capturing compiled declarations, private helpers and axiom dependencies…')
    capture = STATE / 'kernel.json'
    checkpoint = STATE / 'capture-inputs.json'
    saved = json.loads(checkpoint.read_text()) if checkpoint.exists() else {}
    if (capture.exists() and saved.get('inputs') == before
            and saved.get('capture_sha256') == hashlib.sha256(capture.read_bytes()).hexdigest()):
        phase('Reusing the verified compiled capture for identical inputs.')
    else:
        run_logged(['lake', 'env', 'lean', 'scripts/BlueprintCapture.lean'], 'capture.log')
        if inputs() != before:
            raise ValueError('Build inputs changed during capture; rerun')
        checkpoint.write_text(json.dumps({'inputs': before,
            'capture_sha256': hashlib.sha256(capture.read_bytes()).hexdigest()}, sort_keys=True))
    if inputs() != before:
        raise ValueError('Build inputs changed during capture; rerun for a consistent snapshot')
    rows = json.loads((STATE / 'kernel.json').read_text())
    sources = index_sources(rows)
    validate_api_coverage(sources)
    dependencies = project_dependencies(rows, sources)
    obligations = {r['name']: r for r in json.loads((ROOT / 'metadata/proof-obligations.json').read_text())['obligations']}
    open_nodes = validate_kernel(rows, sources, dependencies, obligations)
    phase(f'3/7 Generating seven mathematical chapters and the geometry reference chapter ({len(sources)} source declarations)…')
    paper_records, paper_stats = load_paper(ROOT, {s['label']: s for s in sources.values()})
    generate_blueprint(sources, dependencies, obligations, paper_records)
    projection = semantic.prepare(ROOT, sources, dependencies, obligations, paper_records)
    phase('4/7 Synchronizing native hgraph nodes and Blueprint dependencies…')
    graph = Graph.open(ROOT)
    report = sync_kernel_graph(graph, sources, dependencies, projection)
    (STATE / 'sync.json').write_text(json.dumps(report, ensure_ascii=False, indent=2) + '\n')
    if report['warnings']:
        raise ValueError(f'Native sync warnings (not suppressed): {report["warnings"][:10]}')
    phase('5/7 Importing native tags, workflow states and compiled Lean dependency edges…')
    annotate_graph(graph, sources, dependencies, obligations)
    phase('6/7 Checking native dependency closure against Lean for every declaration…')
    analysis = validate_graph(graph, sources, open_nodes)
    paper_stats['native_states'] = validate_paper_graph(graph, paper_records, analysis, projection)
    semantic_stats = semantic.validate(graph, projection, analysis)
    if inputs() != before or site_inputs() != authored_inputs:
        raise ValueError('Build inputs changed during graph generation; rerun')
    evidence = write_evidence(sources, dependencies, rows, analysis, before, authored_inputs, paper_stats)
    evidence['publication_mode'] = 'curated-mathematical-blueprint'
    evidence['semantic_blueprint'] = semantic_stats
    phase('7/7 Exporting the pinned native frontend and current source snapshot…')
    export_site(evidence, paper_records, args.out,
                lambda: inputs() == before and site_inputs() == authored_inputs)
    semantic.save_source_snapshot(STATE, sources, dependencies, evidence)


if __name__ == '__main__':
    main()
