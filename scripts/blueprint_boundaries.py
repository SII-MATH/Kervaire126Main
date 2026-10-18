"""The only repository additions to native hgraph: public/module ownership
and chapter dependency order. No dependency inference or state rewriting.
"""
from collections import Counter
import json
import re

from hgraph.sync import parse_lean, parse_blueprint, read_blueprint, _assoc_proofs

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
    ownership. Sources are located in the actual Lean files.
    Upstream objects may be referenced through native mathematical dependencies.
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


def validate_chapter_dependencies(statements, proofs=()):
    """Require the displayed chapter order to be topological, with witnesses.

    Resolve native label aliases and statement/proof uses; impose no additional
    same-chapter dependency policy.
    """
    chapters = list(dict.fromkeys(row['chapter'] for row in statements))
    positions = {chapter: index for index, chapter in enumerate(chapters)}
    labels = {row['label']: row['chapter'] for row in statements}
    aliases = {alias: row['label'] for row in statements for alias in row['labels']}
    proof_uses = _assoc_proofs(statements, proofs)
    uses = {row['label']: set(row['uses']) | proof_uses.get(row['label'], set())
            for row in statements}
    edges, witnesses = set(), []
    for source, targets in uses.items():
        for target in targets:
            target = aliases.get(target)
            if target is None:
                continue  # Native sync reports unresolved references as warnings.
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


def source_owners(root, interfaces):
    """Locate public bindings in actual sources, solely for ownership checks.

    Alias commands are recognized for this boundary check; the original Lean
    text is passed unchanged to native sync, which owns binding/status handling.
    """
    result = {}
    for path in (root / 'KIP126').rglob('*.lean'):
        relative = path.relative_to(root)
        owner = relative.parts[1].removesuffix('.lean')
        text = path.read_text()
        shadow = re.sub(r'(?m)^(\s*(?:(?:public|private|protected|noncomputable|unsafe)\s+)*)alias\b',
                        r'\1lemma', text)
        for declaration in parse_lean(shadow):
            name = declaration['fqname']
            if name not in interfaces:
                continue
            if name in result:
                raise ValueError('Public binding has multiple definition sources: ' + name)
            result[name] = {'file': str(relative), 'owner': owner}
    return result


def check(root):
    statements, proofs = parse_blueprint(read_blueprint(root / 'blueprint/content.tex'))
    interfaces = public_interfaces(root)
    sources = source_owners(root, interfaces)
    return {'bindings': validate_binding_owners(statements, sources, interfaces),
            'chapters': validate_chapter_dependencies(statements, proofs)}
