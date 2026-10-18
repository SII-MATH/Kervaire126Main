"""Curated mathematical Blueprint over an independently retained source graph.

Proof states come from actual compiled declarations; reviewed mathematical
dependencies augment the retained compiled projection. In-scope public producers
have Lean-bound frontier entries. Other producers stay in the
internal source graph and contribute to the dependent mathematical status.
No proof responsibility, interface or native frontend is changed.
"""
from collections import Counter, defaultdict
import hashlib
import json
import re

from hgraph.graph import node_id
from hgraph.sync import parse_blueprint, read_blueprint
from blueprint_paper import active_tex, resolve_paper_bindings

DONE = {'lean_ok', 'mathlib_ok'}
MODULES = ('SpectralSequence', 'AdamsSynthetic', 'Literature',
           'E2Computation', 'ProofTools', 'AdamsCalculations', 'Main', 'Geometry')


def public_interfaces(root):
    """The eight locks partition the public interfaces by actual module owner."""
    result = {}
    for path in (root / 'metadata').glob('*-api.json'):
        lock = json.loads(path.read_text())
        if lock.get('module') not in MODULES:
            continue  # Only mathematical module locks determine ownership.
        for name in lock.get('exports', [row['name'] for row in lock['declarations']]):
            if name in result:
                raise ValueError('Public interface has multiple module owners: ' + name)
            result[name] = lock['module']
    return result


def validate_binding_owners(statements, sources, interfaces):
    """Bind each chapter only to declarations defined in its own Lean module.

    Namespaces and statement labels do not determine
    ownership. Sources come from the compiled declaration/source-file index.
    Upstream objects may be referenced in prose and in compiled dependencies.
    """
    checked = Counter()
    for statement in statements:
        names = statement['lean']
        if not names:
            continue
        chapter = statement.get('chapter', '')
        match = re.match(r'^([A-Za-z][A-Za-z0-9]*)\b', chapter)
        owner = match[1] if match else None
        if owner not in MODULES:
            raise ValueError('Lean-bound chapter must name its mathematical module: '
                             + statement['label'] + ': ' + chapter)
        for name in names:
            if name not in sources:
                raise ValueError('Unknown chapter Lean binding: ' + name)
            source = sources[name]
            parts = source['file'].split('/')
            actual = parts[1].removesuffix('.lean') if len(parts) > 1 and parts[0] == 'KIP126' else None
            if actual not in MODULES or actual != source['owner']:
                raise ValueError('Invalid source module ownership: ' + name)
            if actual != owner:
                raise ValueError(f'Cross-module Blueprint binding: {statement["label"]} '
                                 f'in {owner} binds {name} defined in {source["file"]} '
                                 f'({actual}); reference the upstream mathematical entry instead')
            if name not in interfaces:
                raise ValueError('Non-public Blueprint binding: ' + statement['label'] + ': ' + name)
            if interfaces[name] != owner:
                raise ValueError('Public interface lock/source owner mismatch: ' + name)
            checked[owner] += 1
    return {'same_module_verified': True, 'public_interfaces_verified': True,
            'bindings_by_module': dict(checked)}


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


def main_proof_scope(root, sources, dependencies, obligations, public_names):
    """Restrict presentation while retaining all compiled responsibilities."""
    path = root / 'blueprint/scope.json'
    if not path.exists():
        return {'omitted_producers': [], 'restricted_obligations': []}
    policy = json.loads(path.read_text())
    if policy != {'route': 'Main', 'restricted_module': 'AdamsSynthetic'}:
        raise ValueError('Unsupported Blueprint presentation scope')
    lock = json.loads((root / 'metadata/main-api.json').read_text())
    roots = {row['name'] for row in lock['declarations']}
    if not roots or not roots <= sources.keys():
        raise ValueError('Main presentation roots lack compiled source evidence')
    ancestry = ancestor_sets(dependencies)
    required = roots | set().union(*(ancestry[name] for name in roots))
    restricted = {name for name in obligations
                  if sources[name]['owner'] == 'AdamsSynthetic' and name not in required}
    omitted = {name for name in public_names if name in sources and
               local_status([name], sources) not in DONE and
               (name in restricted or ancestry[name].intersection(restricted))}
    if omitted.intersection(required):
        raise ValueError('Presentation scope omitted a Main prerequisite')
    return {**policy, 'roots': sorted(roots), 'omitted_producers': sorted(omitted),
            'restricted_obligations': sorted(restricted),
            'main_adams_synthetic_obligations': sorted(
                name for name in obligations if sources[name]['owner'] == 'AdamsSynthetic'
                and name in required)}


def make_projection(sources, dependencies, obligations, statements, public_names=None,
                    omitted_producers=(), authored_frontier_labels=()):
    """Pure projection. Statements have label/title/lean(actual kernel names).

    Result: entries keyed by label (lean, ancestors, local_status,
    expected_closed, frontier), uses keyed by label, and frontier member lists.
    Every visible dependency is justified by ALL target bindings occurring in
    the consumer's strict actual ancestry. Undisplayed prerequisites remain in the
    complete source graph and affect mathematical status without a binding.
    """
    ancestry = ancestor_sets(dependencies)
    producers = sorted(n for n in sources if local_status([n], sources) not in DONE)
    private_producers = set(producers) - set(public_names) if public_names is not None else set()
    omitted_producers = set(omitted_producers)
    if not omitted_producers <= set(producers):
        raise ValueError('Presentation scope names a non-producer')
    public_producers = set(producers) - private_producers - omitted_producers

    def status(names):
        # The source archive retains exact declaration-local completion. At the
        # mathematical boundary, unfinished work must not disappear merely
        # because its producer has no independent presentation binding.
        internal = (private_producers | omitted_producers).intersection(
            set(names) | set().union(*(ancestry[n] for n in names)))
        return local_status(set(names) | internal, sources), sorted(internal)

    entries = {}
    for statement in statements:
        label = statement['label']
        names = set(statement['lean'])
        if not names <= sources.keys():
            raise ValueError('Unknown semantic Lean binding: ' + str(names - sources.keys()))
        if label in entries:
            raise ValueError('Duplicate mathematical label: ' + label)
        ancestors = set().union(*(ancestry[n] for n in names)) - names if names else set()
        effective_status, internal = status(names)
        entries[label] = {**statement, 'lean': sorted(names), 'ancestors': ancestors,
                          'local_status': effective_status,
                          'source_local_status': local_status(names, sources),
                          'internal_producers': internal,
                          'internal_obligation_labels': [sources[n]['label'] for n in internal],
                          'frontier': False}
    # Include unknown producers as unknowns; they are never invented sorries.
    consumers = [(label, entry['ancestors']) for label, entry in sorted(entries.items())]
    consumers += [('producer:' + n, ancestry[n] - {n}) for n in producers]
    groups = defaultdict(list)
    for name in sorted(public_producers):
        source = sources[name]
        kind = obligations.get(name, {}).get('status', 'unverified')
        incidence = tuple(index for index, (_label, ancestors) in enumerate(consumers) if name in ancestors)
        groups[source['owner'], kind, incidence].append(name)
    authored = sorted(entries.items())
    carrier_bindings = {frozenset(entry['lean']) for _label, entry in authored}
    authored_frontier_labels = set(authored_frontier_labels)
    def frontier_label(owner, names):
        stable = '\n'.join(sorted(sources[n]['label'] for n in names))
        return 'frontier:' + owner + ':' + hashlib.sha256(stable.encode()).hexdigest()[:12]
    frontier_groups = []
    for (owner, kind, _incidence), names in sorted(groups.items()):
        by_binding = defaultdict(list)
        for name in names:
            bindings = tuple(label for label, entry in authored if name in entry['lean'])
            by_binding[bindings].append(name)
        # Reuse distinct authored results only when every part already has an
        # exact carrier and the old group has no authored frontier to preserve.
        # Existing frontier bindings are still checked against the full group.
        parts = list(by_binding.values())
        if (frontier_label(owner, names) in authored_frontier_labels
                or not all(frozenset(part) in carrier_bindings for part in parts)):
            parts = [names]
        frontier_groups.extend((owner, kind, part) for part in parts)
    frontiers = {}
    for owner, kind, names in frontier_groups:
        label = frontier_label(owner, names)
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
        effective_status, internal = status(names)
        entries[label] = {'label': label, 'title': title, 'lean': names,
                          'owner': owner, 'obligation_kind': kind,
                          'ancestors': ancestors, 'frontier': True,
                          'source_local_status': local_status(names, sources),
                          'internal_producers': internal,
                          'internal_obligation_labels': [sources[n]['label'] for n in internal],
                          'local_status': effective_status}
        frontiers[label] = names
    uses = {label: set() for label in entries}
    for label, entry in entries.items():
        actual = entry['ancestors']
        for target, candidate in entries.items():
            names = set(candidate['lean'])
            if label != target and names and names <= actual:
                uses[label].add(target)
        # Public pending ancestors have an exact public carrier. Private pending
        # ancestors remain in the implementation graph and in effective status.
        represented = set().union(*(set(frontiers[target]) for target in uses[label]
                                    if target in frontiers)) if uses[label] else set()
        if represented != actual.intersection(public_producers):
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
            'producer_names': producers, 'private_producer_names': sorted(private_producers),
            'omitted_producer_names': sorted(omitted_producers),
            'source_ancestors': ancestry}


def read_frontier_authoring(root, projection, sources):
    """Read mathematical prose without changing the compiled frontier quotient.

    Kernel names remain authoritative. A source spelling is accepted only when
    it identifies exactly one public kernel declaration.
    Coverage and bindings are checked before any presentation is substituted.
    """
    aliases = defaultdict(set)
    interfaces = public_interfaces(root)
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
                name = next(iter(matches))
                if interfaces.get(name) != owner:
                    raise ValueError('Non-public or wrong-module frontier Lean binding: ' + spelling)
                bindings.append(name)
            if len(bindings) != len(set(bindings)) or set(bindings) != set(expected[label]['lean']):
                raise ValueError('Frontier mathematical bindings differ from compiled group: ' + label)
            if not row['title'] or not re.sub(r'(?m)%[^\n]*', '', row['body']).strip():
                raise ValueError('Frontier entry requires a mathematical title and statement: ' + label)
            authored[label] = row
    missing = expected.keys() - authored.keys()
    if missing:
        raise ValueError('Missing frontier mathematical entries: ' + ', '.join(sorted(missing)))
    return authored


def add_paper_dependencies(projection, paper_records):
    """Add reviewed mathematical edges without reducing them by Lean ancestry.

    During migration the old compiled projection remains a conservative fallback.
    Its independent closure oracle is retained verbatim, rather than making
    mathematical uses pass an ALL-bindings test or hiding unfinished producers.
    """
    if not paper_records:
        return
    aliases = {r['label']: r.get('canonical_label', r['label']) for r in paper_records}
    compiled = {label: set(targets) for label, targets in projection['uses'].items()}
    authored = {}
    for record in paper_records:
        label = aliases[record['label']]
        if label not in projection['entries']:
            raise ValueError('Canonical paper node is not displayed: ' + label)
        if label != record['label']:
            continue
        targets = {aliases.get(target, target) for target in record['mathematical_uses']}
        if label in targets:
            raise ValueError('Self-dependent mathematical paper statement: ' + label)
        if not targets <= projection['entries'].keys():
            raise ValueError('Unknown mathematical paper dependency: '
                             + str(targets - projection['entries'].keys()))
        authored[label] = targets
        projection['uses'][label].update(targets)
    # Explicit mathematical prerequisites must not disappear just because a
    # transitive route or a compiler-selected implementation also exists.
    closed, active = {}, []
    def visit(label):
        if label in active:
            raise ValueError('Cyclic mathematical dependency: '
                             + ' -> '.join(active[active.index(label):] + [label]))
        if label in closed:
            return closed[label]
        active.append(label)
        prerequisites = [visit(target) for target in sorted(projection['uses'][label])]
        active.pop()
        row = projection['entries'][label]
        closed[label] = row['local_status'] in DONE and all(prerequisites)
        if closed[label] and not row['expected_closed']:
            raise ValueError('Mathematical dependency migration hid compiled work: ' + label)
        row['expected_display_closed'] = closed[label]
        return closed[label]
    for label in projection['entries']:
        visit(label)
    projection['compiled_uses'] = compiled
    projection['authored_uses'] = authored
    projection['paper_aliases'] = aliases


def resolve_main_remark(statement, sources, interfaces):
    """Resolve explicit source identities, subject to the same public-only rule."""
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
    if any(interfaces.get(name) != 'Main' for name in names):
        raise ValueError('Non-public Blueprint binding: ' + label)
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
    api = public_interfaces(root)
    for row in authored:
        if row['label'] in papers:
            row['lean'] = papers[row['label']]['lean']
        elif row['label'].startswith('sem:Main:remark-'):
            row['lean'] = resolve_main_remark(row, sources, api)
        elif row['label'].startswith('sem:'):
            if not row['lean'] or not set(row['lean']) <= api.keys():
                raise ValueError('Curated entry must bind actual public interfaces: ' + row['label'])
            if row['leanok'] or row['mathlibok']:
                raise ValueError('Curated status must be derived from compiled evidence')
        else:
            raise ValueError('Unexpected primary Blueprint label: ' + row['label'])
    validate_binding_owners(authored, sources, api)
    scope = main_proof_scope(root, sources, dependencies, obligations, api)
    frontier_labels = {row['label']
        for path in (root / 'blueprint/frontier').glob('*.tex')
        for row in parse_blueprint(active_tex(path.read_text()))[0]}
    projection = make_projection(sources, dependencies, obligations, authored, public_names=api,
                                 omitted_producers=scope['omitted_producers'],
                                 authored_frontier_labels=frontier_labels)
    projection['display_scope'] = scope
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
        'Geometry': 'Geometric consequences',
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
    projection['binding_owners'] = validate_binding_owners([
        {**row, 'lean': projection['entries'][row['label']]['lean']} for row in primary
    ], sources, api)
    add_paper_dependencies(projection, paper_records)
    projection['chapter_dependencies'] = validate_chapter_dependencies(projection, primary)
    return projection


def validate(graph, projection, analysis):
    """Validate CLI/full graph AND the frontend's entries-only graph."""
    from hgraph.layout import _Model
    entries, compiled_entries = [], []
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
        if (node.meta.get('source_local_status') != row['source_local_status'] or
                node.meta.get('internal_obligations') != row['internal_obligation_labels']):
            # Private audit identities do not introduce formalizes edges.
            raise ValueError('Native internal-obligation evidence changed: ' + label)
        display_closed = row.get('expected_display_closed', row['expected_closed'])
        if analysis.closed[nid] != display_closed:
            raise ValueError('Native semantic closure differs from mathematical evidence: ' + label)
        entries.append({'id': nid, 'lean_status': row['local_status'],
                        'deps': [{'id': target, 'type': 'uses'} for target in expected]})
        compiled_entries.append({'id': nid, 'lean_status': row['local_status'],
            'deps': [{'id': node_id('bp', target), 'type': 'uses'} for target in
                     projection.get('compiled_uses', projection['uses'])[label]]})
    model = _Model({'entries': entries})
    compiled_model = _Model({'entries': compiled_entries})
    for index, label in enumerate(projection['entries']):
        row = projection['entries'][label]
        if compiled_model.closed[index] != row['expected_closed']:
            raise ValueError('Independent compiled projection differs from source closure: ' + label)
        if model.closed[index] != row.get('expected_display_closed', row['expected_closed']):
            raise ValueError('Frontend semantic closure differs from mathematical evidence: ' + label)
    return {'mathematical_entries': sum(not r['frontier'] for r in projection['entries'].values()),
            'frontier_entries': sum(r['frontier'] for r in projection['entries'].values()),
            'statements': len(entries), 'unique_unfinished_producers': len(projection['producer_names']),
            'private_implementation_producers': len(projection['private_producer_names']),
            'omitted_presentation_producers': len(projection.get('omitted_producer_names', [])),
            'display_scope': projection.get('display_scope'),
            'entries_with_internal_obligations': sum(bool(r['internal_producers'])
                                                    for r in projection['entries'].values()),
            'dependency_edges': sum(map(len, projection['uses'].values())),
            'authored_paper_dependency_edges': sum(map(len, projection.get('authored_uses', {}).values())),
            'compiled_fallback_dependency_edges': sum(map(len, projection.get('compiled_uses', projection['uses']).values())),
            'dependency_migration': 'Reviewed AimPaper uses plus the retained compiled fallback; '
                                    'mathematical edges are independent of Lean bindings.',
            'paper_aliases': {alias: target for alias, target in projection.get('paper_aliases', {}).items()
                             if alias != target},
            'chapter_dependencies': projection.get('chapter_dependencies'),
            'binding_owners': projection.get('binding_owners'),
            'states': dict(Counter(analysis.states[node_id('bp', label)] for label in projection['entries'])),
            'compiled_projection_closure_matches_source_evidence': True,
            'all_primary_and_frontend_closures_match_compiled_evidence': all(
                model.closed[i] == projection['entries'][label]['expected_closed']
                for i, label in enumerate(projection['entries'])),
            'display_closure_includes_all_compiled_and_mathematical_prerequisites': True}


def save_source_snapshot(state, sources, dependencies, evidence):
    snapshot = {'sources': sources, 'dependencies': {n: sorted(ds) for n, ds in dependencies.items()},
                'evidence': evidence}
    path = state / 'verified-source-snapshot.json'
    temporary = path.with_suffix('.tmp')
    temporary.write_text(json.dumps(snapshot, ensure_ascii=False))
    temporary.replace(path)
    path.with_suffix('.sha256').write_text(hashlib.sha256(path.read_bytes()).hexdigest())
