"""Read-only presentation of the existing interface and obligation baselines.

This is a derived custom page, not a mathematical chapter or a trust snapshot.
"""
from __future__ import annotations

import json
from pathlib import Path
import shutil
from urllib.parse import quote

from hgraph.sync import parse_lean
from blueprint_boundaries import MODULES


def interface_navigation(active):
    """Shared subnavigation within the single native Interfaces tab."""
    links = [('baselines', '../interfaces/index.html', 'Baselines'),
             ('proposals', '../interfaces/index.html?section=proposals', 'Proposals')]
    return '<nav class="interface-navigation" aria-label="Interfaces sections">' + ''.join(
        '<a data-interface-section="' + key + '" href="' + href + '"' + (' aria-current="page"' if key == active else '') + '>'
        + label + '</a>' for key, href, label in links) + '</nav>'


def source_statements(root):
    result = {}
    for path in sorted((root / 'KIP126').rglob('*.lean')):
        text = path.read_text()
        for declaration in parse_lean(text):
            start = text.find(declaration['body'])
            result[declaration['fqname']] = {
                'file': path.relative_to(root).as_posix(),
                'line': text.count('\n', 0, start) + 1 if start >= 0 else None,
                'statement': declaration['statement'],
                'kind': declaration['kind'],
                'sorry': declaration['sorry'],
                'context': declaration['context'],
            }
    return result


def read_interfaces(root):
    """Project canonical JSON and native source statements without accepting changes."""
    root = Path(root)
    sources = source_statements(root)
    registry = json.loads((root / 'interface/baselines/proof-obligations.json').read_text())
    pending = {row['name']: row for row in registry['obligations']}
    modules, records, downloads = [], [], []
    for path in sorted((root / 'interface/baselines').glob('*-api.json')):
        lock = json.loads(path.read_text())
        owner = lock['module']
        if owner not in MODULES:
            continue
        baseline = path.relative_to(root).as_posix()
        downloads.append(baseline)
        modules.append({'name': owner, 'entry_module': lock['entry_module'],
                        'declarations': len(lock['declarations']),
                        'generated': len(lock['generated_declarations']),
                        'exports': len(lock['exports']),
                        'obligations': sum(row['module'].split('.')[1] == owner
                                           for row in pending.values()),
                        'baseline': baseline, 'schema_version': lock['schema_version']})
        for group, kind in (('declarations', 'declaration'), ('generated_declarations', 'generated')):
            for declaration in lock[group]:
                name = declaration['name']
                source = sources.get(name)
                # Compiler-generated fields/equations may have only a parent source.
                parent = name
                while source is None and '.' in parent and kind == 'generated':
                    parent = parent.rsplit('.', 1)[0]
                    source = sources.get(parent)
                records.append({**declaration, 'owner': owner, 'kind': kind,
                                'baseline': baseline, 'source': source,
                                'source_is_parent': source is not None and parent != name,
                                'obligation': pending.get(name)})
    for row in registry['obligations']:
        file = row['module'].replace('.', '/') + '.lean'
        source = sources.get(row['name'])
        if source is None and (root / file).is_file():
            source = {'file': file, 'line': None, 'statement': '', 'context': ''}
        records.append({**row, 'owner': row['module'].split('.')[1], 'kind': 'obligation',
                        'baseline': 'interface/baselines/proof-obligations.json', 'source': source,
                        'source_is_parent': False, 'obligation': row})
    modules.sort(key=lambda row: MODULES.index(row['name']))
    downloads += ['interface/baselines/proof-obligations.json', 'interface/baselines/mathematical-naming-restoration.json']
    audit = {key: value for key, value in registry.items()
             if key not in ('schema_version', 'summary', 'obligations')}
    naming = json.loads((root / 'interface/baselines/mathematical-naming-restoration.json').read_text())
    for row in records:
        source = row['source']
        if source:
            source['href'] = '../source/' + quote(source['file'], safe='/') + '.html'
            if source['line']:
                source['href'] += '#L' + str(source['line'])
    return {'modules': modules, 'records': records, 'downloads': downloads,
            'audit_boundaries': audit, 'naming': naming,
            'scope': 'Recorded baselines and unelaborated source statements. '
                     'This page does not certify a Lean build or compiled dependency closure.'}


def stage_interfaces(root, project):
    destination = Path(project) / 'site/interfaces.html'
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text('<iframe class="interface-frame" title="Interfaces" '
                           'src="interfaces/index.html" loading="lazy"></iframe>')


def export_interfaces(root, out):
    root, out = Path(root), Path(out)
    data = read_interfaces(root)
    destination = out / 'interfaces'
    destination.mkdir(parents=True, exist_ok=True)
    for name in ('interfaces.html', 'interfaces.css', 'interfaces.js'):
        target = destination / ('baselines.html' if name.endswith('.html') else name)
        if name.endswith('.html'):
            target.write_text((root / 'site' / name).read_text().replace(
                '<!-- INTERFACE_NAV -->', interface_navigation('baselines')))
        else:
            shutil.copyfile(root / 'site' / name, target)
    for name in ('interface-workspace.html', 'interface-workspace.css', 'interface-workspace.js', 'interface-navigation.js'):
        shutil.copyfile(root / 'site' / name, destination / ('index.html' if name.endswith('.html') else name))
    (destination / 'data.json').write_text(json.dumps(data, ensure_ascii=False) + '\n')
    for relative in data['downloads']:
        target = destination / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(root / relative, target)
    # Export the existing explanation, not a separately maintained guide.
    from blueprint_proposals import markdown
    guide = markdown((root / 'docs/metadata-baselines.md').read_text(),
                     'docs/metadata-baselines.md', root)
    guide = guide.replace('href="reports/docs/corrections.md"', 'href="docs/corrections.md"')
    (destination / 'docs').mkdir(exist_ok=True)
    shutil.copyfile(root / 'docs/corrections.md', destination / 'docs/corrections.md')
    (destination / 'guide.html').write_text('<!doctype html><html lang="zh-CN"><meta charset="utf-8">'
        '<meta name="viewport" content="width=device-width,initial-scale=1"><title>Interface baseline guide</title>'
        '<link rel="stylesheet" href="../proposals/proposals.css">'
        '<main class="proposal-page proposal-body">' + guide + '</main></html>')
    return {'modules': len(data['modules']), 'records': len(data['records'])}
