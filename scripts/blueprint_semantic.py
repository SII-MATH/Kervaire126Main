"""Curated mathematical Blueprint over an independently retained source graph.

All states and dependencies come from actual compiled declarations.  A hidden
producer is represented by a native, Lean-bound frontier entry. Producers may
share an entry only if every mathematical consumer AND every producer has the
same strict dependency on them. This preserves closure and frontier readiness.
No proof responsibility, interface or native frontend is changed.
"""
from collections import Counter, defaultdict
import hashlib
import html
import json
import re

from hgraph.graph import node_id
from hgraph.sync import parse_blueprint, read_blueprint
from blueprint_paper import active_tex, resolve_paper_bindings

DONE = {'lean_ok', 'mathlib_ok'}
MODULES = ('SpectralSequence', 'AdamsSynthetic', 'Literature',
           'E2Computation', 'ProofTools', 'AdamsCalculations', 'Main')


def validate_chapter_dependencies(projection, statements):
    """Require the displayed chapter order to be topological, with witnesses.

    A fine dependency DAG can acquire cycles when entries are collapsed into
    chapters. Check the actual displayed partition as well as the fine graph.
    """
    chapters = list(dict.fromkeys(row['chapter'] for row in statements))
    positions = {chapter: index for index, chapter in enumerate(chapters)}
    labels = {row['label']: row['chapter'] for row in statements}
    if not projection['entries'].keys() <= labels.keys():
        raise ValueError('Projected entries missing from primary chapters')
    edges, witnesses = set(), []
    for source, targets in projection['uses'].items():
        for target in targets:
            consumer, prerequisite = labels[source], labels[target]
            if consumer == prerequisite:
                continue
            edges.add((consumer, prerequisite))
            if positions[prerequisite] >= positions[consumer]:
                witnesses.append(f'{source} ({consumer}) -> {target} ({prerequisite})')
    if witnesses:
        raise ValueError('Chapter dependency points forward: ' + '; '.join(sorted(witnesses)[:20]))
    return {'chapters': chapters, 'dependency_edges': [list(edge) for edge in sorted(edges)],
            'topological_order_verified': True}


def ancestor_sets(dependencies):
    """Strict transitive source ancestry; compiled source dependencies are a DAG."""
    result, active = {}, set()
    def visit(name):
        if name in result:
            return result[name]
        if name in active:
            raise ValueError('Cyclic compiled source dependency: ' + name)
        active.add(name)
        found = set()
        for dependency in dependencies[name]:
            if dependency == name:
                continue
            if dependency not in dependencies:
                raise ValueError('Missing compiled source dependency: ' + dependency)
            found.add(dependency)
            found.update(visit(dependency))
        active.remove(name)
        result[name] = found
        return found
    for name in dependencies:
        visit(name)
    return result


def local_status(names, sources):
    statuses = {sources[n].get('lean_status',
                'sorry' if sources[n]['row']['direct_sorry'] else 'lean_ok') for n in names}
    return ('sorry' if 'sorry' in statuses else 'empty' if not statuses or 'empty' in statuses
            else 'lean_ok')


def make_projection(sources, dependencies, obligations, statements):
    """Pure projection. Statements have label/title/lean(actual kernel names).

    Result: entries keyed by label (lean, ancestors, local_status,
    expected_closed, frontier), uses keyed by label, and frontier member lists.
    Every visible dependency is justified by ALL target bindings occurring in
    the consumer's strict actual ancestry. Frontier grouping includes producer
    incidence, so no internal pending prerequisite is erased by grouping.
    """
    ancestry = ancestor_sets(dependencies)
    entries = {}
    for statement in statements:
        label = statement['label']
        names = set(statement['lean'])
        if not names <= sources.keys():
            raise ValueError('Unknown semantic Lean binding: ' + str(names - sources.keys()))
        if label in entries:
            raise ValueError('Duplicate mathematical label: ' + label)
        ancestors = set().union(*(ancestry[n] for n in names)) - names if names else set()
        entries[label] = {**statement, 'lean': sorted(names), 'ancestors': ancestors,
                          'local_status': local_status(names, sources), 'frontier': False}
    # Include unknown producers as unknowns; they are never invented sorries.
    producers = sorted(n for n in sources if local_status([n], sources) not in DONE)
    consumers = [(label, entry['ancestors']) for label, entry in sorted(entries.items())]
    consumers += [('producer:' + n, ancestry[n] - {n}) for n in producers]
    groups = defaultdict(list)
    for name in producers:
        source = sources[name]
        kind = obligations.get(name, {}).get('status', 'unverified')
        incidence = tuple(index for index, (_label, ancestors) in enumerate(consumers) if name in ancestors)
        groups[source['owner'], kind, incidence].append(name)
    frontiers = {}
    for (owner, kind, _incidence), names in sorted(groups.items()):
        stable = '\n'.join(sorted(sources[n]['label'] for n in names))
        label = 'frontier:' + owner + ':' + hashlib.sha256(stable.encode()).hexdigest()[:12]
        # An authored exact producer group can itself serve as the frontier.
        equivalent = [key for key, entry in entries.items() if set(entry['lean']) == set(names)]
        if equivalent:
            frontiers[equivalent[0]] = names
            continue
        files = sorted({sources[n]['file'].split('/')[-1].removesuffix('.lean') for n in names})
        title = {'pending-construction': 'Constructions', 'pending-proof': 'Proofs',
                 'unverified': 'Verification'}[kind] + ': ' + ', '.join(files[:3])
        if len(files) > 3:
            title += ' and related objects'
        ancestors = set().union(*(ancestry[n] for n in names)) - set(names)
        entries[label] = {'label': label, 'title': title, 'lean': names,
                          'owner': owner, 'obligation_kind': kind,
                          'ancestors': ancestors, 'frontier': True,
                          'local_status': local_status(names, sources)}
        frontiers[label] = names
    uses = {label: set() for label in entries}
    for label, entry in entries.items():
        actual = entry['ancestors']
        for target, candidate in entries.items():
            names = set(candidate['lean'])
            if label != target and names and names <= actual:
                uses[label].add(target)
        # All actual pending ancestors must have a visible, exact carrier.
        represented = set().union(*(set(frontiers[target]) for target in uses[label]
                                    if target in frontiers)) if uses[label] else set()
        if represented != actual.intersection(producers):
            raise ValueError('Frontier projection lost or invented a producer: ' + label)
        entry['expected_closed'] = bool(entry['lean']) and all(
            local_status([n], sources) in DONE and not ancestry[n].intersection(producers)
            for n in entry['lean'])
    # Strict ancestry of ALL bindings implies a DAG. Reduce redundant edges
    # while preserving reachability; keep the native graph readable.
    visited, order, visiting = set(), [], set()
    def walk(label):
        if label in visiting:
            raise ValueError('Cyclic semantic projection: ' + label)
        if label in visited:
            return
        visiting.add(label)
        for target in sorted(uses[label]):
            walk(target)
        visiting.remove(label)
        visited.add(label)
        order.append(label)
    for label in sorted(entries):
        walk(label)
    reachable = {}
    for label in order:
        descendants = set()
        for target in uses[label]:
            descendants.update(reachable[target])
        direct = uses[label] - descendants
        reachable[label] = set(uses[label]) | descendants
        uses[label] = direct
    closed = {}
    for label in order:
        closed[label] = entries[label]['local_status'] in DONE and all(closed[t] for t in uses[label])
        if closed[label] != entries[label]['expected_closed']:
            raise ValueError('Semantic projection changed actual compiled closure: ' + label)
    return {'entries': entries, 'uses': uses, 'frontiers': frontiers,
            'producer_names': producers, 'source_ancestors': ancestry}


def read_frontier_authoring(root, projection, sources):
    """Read mathematical prose without changing the compiled frontier quotient.

    Kernel names remain authoritative. A source spelling is accepted only when
    it identifies exactly one kernel declaration, including private producers.
    Coverage and bindings are checked before any presentation is substituted.
    """
    aliases = defaultdict(set)
    for name, source in sources.items():
        for spelling in (name, source.get('fqname'), source.get('lean_name')):
            if spelling:
                aliases[spelling].add(name)
    expected = {label: row for label, row in projection['entries'].items()
                if row.get('frontier')}
    authored = {}
    for owner in MODULES:
        path = root / 'blueprint/frontier' / (owner + '.tex')
        if not path.exists():
            continue
        # Parse only active statements: note comments must never create a
        # binding or an apparent completion flag. Attachments read the source.
        rows, proofs = parse_blueprint(active_tex(path.read_text()))
        if proofs:
            raise ValueError('Unexpected informal frontier proof block: ' + str(path))
        for row in rows:
            label = row['label']
            if label in authored:
                raise ValueError('Duplicate frontier mathematical label: ' + label)
            if label not in expected:
                raise ValueError('Unexpected frontier mathematical label: ' + label)
            if expected[label]['owner'] != owner:
                raise ValueError('Frontier mathematical owner mismatch: ' + label)
            if row.get('labels', [label]) != [label]:
                raise ValueError('Frontier entry must retain its unique label: ' + label)
            if row['leanok'] or row['mathlibok']:
                raise ValueError('Frontier status must be derived from compiled evidence: ' + label)
            if row['uses']:
                raise ValueError('Frontier dependencies must be derived from compiled evidence: ' + label)
            bindings = []
            for spelling in row['lean']:
                matches = {spelling} if spelling in sources else aliases.get(spelling, set())
                if len(matches) != 1:
                    raise ValueError('Unknown or ambiguous frontier Lean binding: ' + spelling)
                bindings.append(next(iter(matches)))
            if len(bindings) != len(set(bindings)) or set(bindings) != set(expected[label]['lean']):
                raise ValueError('Frontier mathematical bindings differ from compiled group: ' + label)
            if not row['title'] or not re.sub(r'(?m)%[^\n]*', '', row['body']).strip():
                raise ValueError('Frontier entry requires a mathematical title and statement: ' + label)
            authored[label] = row
    missing = expected.keys() - authored.keys()
    if missing:
        raise ValueError('Missing frontier mathematical entries: ' + ', '.join(sorted(missing)))
    return authored


def resolve_main_remark(statement, sources):
    """Bind Main remarks to explicit, scoped implementation declarations.

    Public semantic entries keep their API-only rule. Remarks may expose a
    private Main proof in the blueprint without changing the Lean interface.
    """
    label = statement['label']
    if (not re.fullmatch(r'sem:Main:remark-\d+(?:\.\d+)*', label)
            or statement['content_type'] != 'remark'):
        raise ValueError('Invalid Main remark binding: ' + label)
    if statement['leanok'] or statement['mathlibok']:
        raise ValueError('Curated status must be derived from compiled evidence')
    if any(not label.startswith('decl:') for label in statement['uses']):
        raise ValueError('Main remark dependencies must come from compiled bindings')
    names = resolve_paper_bindings(statement, {s['label']: s for s in sources.values()})
    if not names or any(sources[name]['owner'] != 'Main' for name in names):
        raise ValueError('Main remark must bind its own implementation proofs: ' + label)
    return names


def prepare(root, sources, dependencies, obligations, paper_records):
    generated = root / 'blueprint/generated'
    generated.mkdir(parents=True, exist_ok=True)
    # Avoid reading the previous projection as authored mathematical input.
    for owner in MODULES:
        (generated / ('frontier-' + owner + '.tex')).write_text('')
    authored, proofs = parse_blueprint(read_blueprint(root / 'blueprint/content.tex'))
    if proofs:
        raise ValueError('Unexpected informal proof block in curated document')
    papers = {r['label']: r for r in paper_records}
    api = {d['name'] for path in (root / 'metadata').glob('*-api.json')
           for d in json.loads(path.read_text()).get('declarations', [])}
    for row in authored:
        if row['label'] in papers:
            row['lean'] = papers[row['label']]['lean']
        elif row['label'].startswith('sem:Main:remark-'):
            row['lean'] = resolve_main_remark(row, sources)
        elif row['label'].startswith('sem:'):
            if not row['lean'] or not set(row['lean']) <= api:
                raise ValueError('Curated entry must bind actual public interfaces: ' + row['label'])
            if row['leanok'] or row['mathlibok']:
                raise ValueError('Curated status must be derived from compiled evidence')
        else:
            raise ValueError('Unexpected primary Blueprint label: ' + row['label'])
    projection = make_projection(sources, dependencies, obligations, authored)
    frontier_authoring = read_frontier_authoring(root, projection, sources)
    for label, statement in frontier_authoring.items():
        # Presentation only: membership, status, ancestors and closure retain
        # their values from the independent source projection above.
        projection['entries'][label]['title'] = statement['title']
        projection['entries'][label]['body'] = statement['body']
    section_titles = {
        'SpectralSequence': 'Further spectral constructions',
        'AdamsSynthetic': 'Adams towers and synthetic comparison',
        'Literature': 'Further homotopy and detection results',
        'E2Computation': 'Coordinates and algebraic relations on the E2 page',
        'ProofTools': 'Leibniz and Mahowald formulas',
        'AdamsCalculations': 'Differentials and survival in the Adams spectral sequence',
        'Main': 'Further Kervaire invariant calculations',
    }
    for owner in MODULES:
        rows = [r for r in projection['entries'].values() if r.get('frontier') and r['owner'] == owner]
        chunks = []
        if rows:
            chunks.append('\\section{' + section_titles[owner] + '}\n')
        for row in sorted(rows, key=lambda r: (r['obligation_kind'], r['title'], r['label'])):
            statement = frontier_authoring[row['label']]
            kind = statement['content_type']
            chunks += ['\\begin{' + kind + '}[' + row['title'] + ']\n',
                       '\\label{' + row['label'] + '}\n',
                       '\\level{' + (statement['level'] or 'fine') + '}\n',
                       '\\lean{' + ','.join(row['lean']) + '}\n']
            if statement['sketch']:
                chunks.append('\\sketch\n')
            chunks += [row['body'] + '\n', '\\end{' + kind + '}\n\n']
        (generated / ('frontier-' + owner + '.tex')).write_text(''.join(chunks))
    # The implementation graph is synchronized natively but is not part of
    # the primary document, its statement count or its eight chapters.
    (generated / 'implementation.tex').write_text(''.join(
        '\\chapter{' + owner + ' implementation}\n\\input{' + owner + '.tex}\n' for owner in MODULES))
    primary, _ = parse_blueprint(read_blueprint(root / 'blueprint/content.tex'))
    projection['chapter_dependencies'] = validate_chapter_dependencies(projection, primary)
    return projection


def validate(graph, projection, analysis):
    """Validate CLI/full graph AND the frontend's entries-only graph."""
    from hgraph.layout import _Model
    entries = []
    hard_edges = defaultdict(set)
    formalizes = defaultdict(set)
    for edge in graph.edges():
        if edge.hard:
            hard_edges[edge.source].add(edge.target)
        if edge.type == 'formalizes':
            formalizes[edge.source].add(edge.target)
    for label, row in projection['entries'].items():
        nid = node_id('bp', label)
        node = graph.get_node(nid)
        actual = hard_edges[nid]
        expected = {node_id('bp', target) for target in projection['uses'][label]}
        actual_bindings = formalizes[nid]
        expected_bindings = {node_id('lean', name) for name in row['lean']}
        if actual != expected or actual_bindings != expected_bindings or node.meta.get('lean_status') != row['local_status']:
            raise ValueError('Native semantic bindings/status/edges changed: ' + label)
        if analysis.closed[nid] != row['expected_closed']:
            raise ValueError('Native semantic closure differs from compiled evidence: ' + label)
        entries.append({'id': nid, 'lean_status': row['local_status'],
                        'deps': [{'id': target, 'type': 'uses'} for target in expected]})
    model = _Model({'entries': entries})
    for index, label in enumerate(projection['entries']):
        if model.closed[index] != projection['entries'][label]['expected_closed']:
            raise ValueError('Frontend semantic closure differs from compiled evidence: ' + label)
    return {'mathematical_entries': sum(not r['frontier'] for r in projection['entries'].values()),
            'frontier_entries': sum(r['frontier'] for r in projection['entries'].values()),
            'statements': len(entries), 'unique_unfinished_producers': len(projection['producer_names']),
            'dependency_edges': sum(map(len, projection['uses'].values())),
            'chapter_dependencies': projection.get('chapter_dependencies'),
            'states': dict(Counter(analysis.states[node_id('bp', label)] for label in projection['entries'])),
            'all_primary_and_frontend_closures_match_compiled_evidence': True}


def write_verification(state, evidence):
    stats = evidence['semantic_blueprint']
    paper = evidence['aimpaper']
    body = '<h2>Blueprint verification</h2><p>The primary blueprint is organized by mathematical content across seven formalization modules and an eighth geometry chapter. The chapter order is checked against every displayed dependency.</p>'
    body += (f'<p><strong>{stats["statements"]} blueprint entries</strong>: '
             f'{stats["mathematical_entries"]} mathematical and paper entries, '
             f'{stats["frontier_entries"]} additional construction and proof frontier groups. '
             f'The complete implementation index retains {evidence["source_declarations"]} source declarations.</p>')
    body += (f'<p><strong>{evidence["direct_obligations"]} unique registered Lean obligations</strong> remain in the existing registry. '
             'Grouping changes presentation only. It adds no axioms, assumptions or proof responsibilities.</p>')
    body += '<p>Every visible dependency is supported by actual compiled type or proof ancestry. Frontier groups combine unfinished producers only when every mathematical consumer and every unfinished producer depends on each member in exactly the same way. Both the native full graph and the native frontend graph have been checked against the compiled dependency closure for every primary entry.</p>'
    body += f'<p>AimPaper: {paper["statements"]} original statements, {paper["bound_statements"]} bound counterparts, including {paper["partial_bound_statements"]} partial correspondences. Partial correspondences retain sketch and explicit scope limitations. The three geometric endpoints remain unformalized in Chapter 8.</p>'
    body += '<table><tr><th>Dependency state</th><th>Entries</th></tr>'
    for name in ('closed', 'formalized_open', 'ready', 'blocked'):
        body += '<tr><td>' + name + '</td><td>' + str(stats['states'].get(name, 0)) + '</td></tr>'
    body += '</table><p>The top formalized percentage describes local completion. Fully closed also requires all transitive prerequisites. Native Summary Ready now uses local states of direct prerequisites; verification and CLI ready require their complete closure.</p>'
    status = evidence.get('full_project_build', {}).get('status') or ('passed' if evidence['checks'].get('lake_build') else 'unknown')
    body += '<p>Latest complete repository build: <strong>' + html.escape(status) + '</strong>. Publication is independent of a complete build; unknown source evidence is never marked complete.</p>'
    body += '<p>This is a working-tree snapshot. Interface locks, source inventory and full build checks remain in place. Native hgraph code and frontend match the pinned distribution.</p>'
    body += '<p><a href="implementation/index.html" target="_blank">Open the complete implementation index</a> · <a href="validation.json" target="_blank">Verification evidence</a></p>'
    (state / 'verification.html').write_text(body)
    (state / 'implementation-index.html').write_text('<h2>Implementation index</h2><p>The mathematical blueprint groups public definitions and results. All source declarations, private implementation details, exact Lean bodies, compiled dependencies and original proof obligations remain available in a separate searchable archive.</p><p><a href="implementation/index.html" target="_blank">Open the complete implementation index</a></p>')


def save_source_snapshot(state, sources, dependencies, evidence):
    snapshot = {'sources': sources, 'dependencies': {n: sorted(ds) for n, ds in dependencies.items()},
                'evidence': evidence}
    path = state / 'verified-source-snapshot.json'
    temporary = path.with_suffix('.tmp')
    temporary.write_text(json.dumps(snapshot, ensure_ascii=False))
    temporary.replace(path)
    path.with_suffix('.sha256').write_text(hashlib.sha256(path.read_bytes()).hexdigest())


def export_implementation(out, sources, dependencies, obligations, analysis):
    """Searchable full implementation archive, separate from statement counts."""
    target = out / 'implementation'
    target.mkdir(exist_ok=True)
    rows = []
    for name, source in sorted(sources.items(), key=lambda p: (p[1]['owner'], p[1]['file'], p[1]['row']['line'] or 0)):
        rows.append({'label': source['label'], 'name': name, 'title': source['fqname'],
                     'module': source['owner'], 'file': source['file'], 'line': source['row']['line'] or 1,
                     'status': local_status([name], sources), 'state': analysis.states[source['lean_id']],
                     'obligation': obligations.get(name, {}).get('status'),
                     'dependencies': sorted(sources[n]['label'] for n in dependencies[name]),
                     'code': source['body'], 'statement': source['statement']})
    (target / 'data.json').write_text(json.dumps(rows, ensure_ascii=False))
    # No dependency or body is injected as HTML; code uses textContent.
    page = '''<!doctype html><html lang="en"><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>Kervaire 126 — Implementation index</title><style>
body{font:15px/1.6 system-ui;margin:0;background:#f7f8fb;color:#202738}main{max-width:1120px;margin:auto;padding:28px}a{color:#4938d1}input{padding:12px;width:95%;border:1px solid #ccd2df;border-radius:8px}details{background:white;border:1px solid #e1e5ee;border-radius:8px;margin:9px 0;padding:12px}summary{cursor:pointer;overflow-wrap:anywhere}pre{white-space:pre-wrap;overflow-wrap:anywhere;background:#f5f6fa;padding:12px}small{color:#647088}.sorry{color:#b94b24}.empty{color:#697383}.lean_ok{color:#13743e}#count{margin:12px 0}</style>
<main><a href="../#/Kervaire126">← Mathematical blueprint</a><h1>Implementation index</h1>
<p>All source declarations and their actual compiled dependencies. These implementation records are separate from the mathematical statement count. Unfinished declarations retain their original responsibility.</p>
<input id="search" aria-label="Search implementation" placeholder="Search names, modules, files, proof or construction status…"><div id="count"></div><div id="rows"></div></main>
<script>
fetch('data.json').then(r=>r.json()).then(data=>{const byLabel=new Map(data.map(r=>[r.label,r]));const box=document.querySelector('#rows');const search=document.querySelector('#search');
function render(){box.replaceChildren();const q=search.value.toLowerCase();const selected=data.filter(r=>JSON.stringify([r.title,r.module,r.file,r.state,r.obligation]).toLowerCase().includes(q));document.querySelector('#count').textContent=selected.length+' / '+data.length+' source declarations';
for(const r of selected){const d=document.createElement('details');d.id=r.label;const s=document.createElement('summary');s.textContent=r.title+' · '+r.state+(r.obligation?' · '+r.obligation:'');s.className=r.status;d.append(s);d.addEventListener('toggle',()=>{if(!d.open||d.childNodes.length>1)return;const a=document.createElement('a');a.href='../source/'+r.file+'.html#L'+r.line;a.textContent=r.file+':'+r.line;d.append(a);const p=document.createElement('pre');p.textContent=r.code;d.append(p);const deps=document.createElement('p');deps.textContent='Compiled dependencies: ';for(const key of r.dependencies){const a=document.createElement('a');a.href='#'+key;a.textContent=(byLabel.get(key)||{}).title||key;deps.append(a,document.createTextNode(' · '));}d.append(deps);});box.append(d);}jump();}
function jump(){if(!location.hash)return;const d=document.getElementById(decodeURIComponent(location.hash.slice(1)));if(d){d.open=true;d.scrollIntoView();}}search.addEventListener('input',render);window.addEventListener('hashchange',jump);render();});
</script></html>'''
    (target / 'index.html').write_text(page)
