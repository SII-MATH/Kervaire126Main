"""A chapter map derived exclusively from the exported native hgraph payload."""
from collections import Counter
import json
from pathlib import Path
from urllib.parse import quote


def project_map_data(project):
    """Keep every statement, its exact local status and every displayed uses edge.

    Map arrows run from prerequisite to consumer. They reverse only the native
    adjacency convention; they never infer or reduce mathematical dependencies.
    """
    entries = project['entries']
    indexed = {entry['id']: entry for entry in entries}
    if len(indexed) != len(entries) or len({r['label'] for r in entries}) != len(entries):
        raise ValueError('Duplicate native map statement identity')
    chapters, nodes, seen = [], [], set()
    for ci, chapter in enumerate(project['chapters'], 1):
        group = {'id': 'chapter-' + str(ci), 'title': chapter['title'], 'sections': []}
        section = None
        for block in chapter['blocks']:
            if block['t'] == 'head':
                if block.get('level') == 2:
                    section = {'id': f'section-{ci}-{len(group["sections"]) + 1}',
                               'title': block['title'], 'nodes': []}
                    group['sections'].append(section)
                continue
            if block['t'] != 'stmt':
                continue
            identity = block['id']
            if identity not in indexed or identity in seen:
                raise ValueError('Unknown or repeated map chapter statement: ' + identity)
            entry = indexed[identity]
            if block['label'] != entry['label']:
                raise ValueError('Map chapter and entry identities disagree: ' + identity)
            if section is None:
                section = {'id': f'section-{ci}-1', 'title': chapter['title'], 'nodes': []}
                group['sections'].append(section)
            node = {'id': identity, 'label': entry['label'], 'title': entry['title'],
                    'display_title': f'{block.get("abbr", entry["kind"].title())} '
                                     f'{block.get("num", "")}: {entry["title"]}',
                    'body': entry['body'], 'chapter': chapter['title'],
                    'section': section['title'], 'kind': entry['kind'],
                    'status': entry['lean_status'], 'order': len(nodes),
                    'ref': entry.get('ref') or '', 'sketch': bool(entry.get('sketch')),
                    'url': '../#/Kervaire126#' + quote(entry['label'], safe=':')}
            section['nodes'].append(node)
            nodes.append(node)
            seen.add(identity)
        group['sections'] = [section for section in group['sections'] if section['nodes']]
        chapters.append(group)
    if seen != indexed.keys():
        raise ValueError('Native statements missing from map chapters')
    pairs = set()
    for consumer in entries:
        for dependency in consumer['deps']:
            if dependency.get('type') != 'uses':
                continue
            prerequisite = dependency['id']
            if prerequisite not in indexed:
                raise ValueError('Map dependency is outside the published statement graph: ' + prerequisite)
            if prerequisite == consumer['id']:
                raise ValueError('Self-dependent map statement: ' + prerequisite)
            pairs.add((prerequisite, consumer['id']))
    edges = [{'from': prerequisite, 'to': consumer} for prerequisite, consumer in sorted(pairs)]
    return {'title': project['title'], 'project_route': '../#/Kervaire126',
            'theme': project.get('theme'),
            'chapters': chapters, 'nodes': nodes, 'edges': edges, 'important_labels': [],
            'macros': project.get('macros', {}), 'refs': project.get('refs', {}),
            'bib': project.get('bib', []),
            'stats': {'nodes': len(nodes), 'edges': len(edges), 'chapters': len(chapters),
                      'important': 0, 'statuses': dict(Counter(n['status'] for n in nodes))}}


def export_map(root, out):
    """Build the map after native export, so all views use the same snapshot."""
    out = Path(out)
    project = json.loads((out / 'Kervaire126/data.json').read_text())
    data = project_map_data(project)
    assets = out / 'assets'
    js = sorted(assets.glob('katexLoader-*.js'))
    css = sorted(assets.glob('katexLoader-*.css'))
    if len(js) != 1 or len(css) != 1:
        raise ValueError('Expected the pinned native KaTeX renderer and styles')
    data['katex'] = {'js': '../assets/' + js[0].name, 'css': '../assets/' + css[0].name}
    destination = out / 'blueprint-map'
    if not (destination / 'renderer.html').is_file():
        raise ValueError('The pinned hgraph native map renderer is missing')
    (destination / 'data.json').write_text(json.dumps(data, ensure_ascii=False, separators=(',', ':')))
    return data['stats']


def verification_document(body):
    """Retain review evidence as a secondary document, outside main navigation."""
    return ('<!doctype html><html lang="en"><meta charset="utf-8">'
            '<meta name="viewport" content="width=device-width,initial-scale=1">'
            '<title>Blueprint verification — Kervaire 126</title>'
            '<style>body{max-width:900px;margin:36px auto;padding:0 20px;'
            'font:16px/1.65 system-ui;color:#202738;background:#fafbfc}'
            'a{color:#4938d1}table{border-collapse:collapse}td,th{padding:6px 12px;'
            'border:1px solid #dce0e7;text-align:left}</style>'
            '<p><a href="./#/Kervaire126">← Blueprint</a></p><main>' + body + '</main></html>')
