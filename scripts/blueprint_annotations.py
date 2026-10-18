"""Publish authoring notes as native attachments, outside mathematical bodies."""
from datetime import datetime, timezone
from pathlib import Path
import re

from hgraph.dashboard import discover_bib
from hgraph.graph import node_id, _write_doc

ORIGIN = 'blueprint-authoring-notes'
ENV = re.compile(r'\\begin\{(theorem|lemma|definition|corollary|proposition|fact|remark)\}'
                 r'.*?\\end\{\1\}', re.S)
NOTE = re.compile(r'^\s*%\s*(Blueprint note|Correspondence):\s*(.*)$', re.M)


def authoring_notes(root):
    """Read only explicitly marked notes; preserve chapter-wide provenance."""
    root = Path(root)
    result = {}
    for directory in ('semantic', 'paper', 'frontier'):
        for path in sorted((root / 'blueprint' / directory).glob('*.tex')):
            text = path.read_text()
            blocks = list(ENV.finditer(text))
            if not blocks:
                continue
            chapter = root / 'blueprint/chapters' / path.name
            common = NOTE.findall(text[:blocks[0].start()])
            if chapter.exists():
                common += NOTE.findall(chapter.read_text().split(r'\input', 1)[0])
            for block in blocks:
                labels = re.findall(r'\\label\{((?:sem:|paper:|frontier:)[^}]+)\}', block[0])
                if len(labels) != 1 or labels[0] in result:
                    raise ValueError('Ambiguous annotation target in ' + str(path))
                notes = list(dict.fromkeys(common + NOTE.findall(block[0])))
                if notes:
                    result[labels[0]] = {'path': str(path.relative_to(root)), 'notes': notes}
    return result


def markdown_note(kind, text, bibliography):
    """Use Markdown links in native comments; retain mathematical TeX."""
    def citation(match):
        links = []
        for key in match[1].split(','):
            key = key.strip()
            source = bibliography.get(key)
            if source is None:
                raise ValueError('Unknown annotation bibliography key: ' + key)
            url = source.get('url')
            links.append('[' + key + '](' + url + ')' if url else '`' + key + '`')
        return ', '.join(links)
    text = re.sub(r'\\cite\{([^}]+)\}', citation, text)
    text = re.sub(r'\\texttt\{([^}]+)\}', lambda m: '`' + m[1] + '`', text)
    text = re.sub(r'\\(?:emph|textbf)\{([^}]+)\}', lambda m: m[1], text)
    text = re.sub(r'\\par\b\s*', '', text)
    return ('**Formal scope:** ' if kind == 'Correspondence' else '') + text


def sync_authoring_notes(graph, root):
    """Reconcile our own attachment only; leave every human comment untouched."""
    bibliography = {r['key']: r for r in discover_bib(Path(root) / 'blueprint/content.tex')}
    changed = 0
    for label, record in authoring_notes(root).items():
        target = node_id('bp', label)
        if not graph.has_node(target):
            raise ValueError('Missing native annotation target: ' + label)
        content = '\n\n'.join(markdown_note(kind, text, bibliography)
                              for kind, text in record['notes'])
        matches = [note for note in graph.comments(target) if note.meta.get('origin') == ORIGIN]
        if len(matches) > 1:
            raise ValueError('Duplicate managed Blueprint annotations: ' + label)
        metadata = {'origin': ORIGIN, 'blueprint_label': label,
                    'authored_source': record['path'], 'title': 'Formal scope and provenance'}
        if not matches:
            graph.add_attachment(target, 'comment', content, author='blueprint-authoring', **metadata)
            changed += 1
        else:
            old = matches[0]
            if old.content != content or any(old.meta.get(k) != v for k, v in metadata.items()):
                updated = {**old.meta, **metadata, 'updated': datetime.now(timezone.utc).isoformat()}
                _write_doc(graph.base / 'nodes' / target / (old.id + '.md'), updated, content)
                changed += 1
    return changed
