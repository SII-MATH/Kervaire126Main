"""Present structured AimPaper corrections through a native hgraph HTML content tab.

corrections.yaml is the only authored correction record. Typed fields supply
source and revised-node references, explanations and qualified progress.
Presentation never changes a binding or infers that a proof is complete.
"""
import html
import hashlib
import json
from pathlib import Path
import re
from urllib.parse import quote

import yaml

from hgraph.site import _md_to_html
from hgraph.sync import _brace_span
from blueprint_paper import active_tex, source_statements


TEXT_FIELDS = ('problem', 'counterexample', 'progress', 'history')
TONES = {'proposed', 'revised', 'partial'}


class CorrectionsLoader(yaml.SafeLoader):
    """Reject duplicate keys rather than silently replacing recorded evidence."""


def _unique_mapping(loader, node):
    result = {}
    for key_node, value_node in node.value:
        key = loader.construct_object(key_node)
        if not isinstance(key, str) or key in result:
            raise ValueError('Duplicate or invalid correction key: ' + str(key))
        result[key] = loader.construct_object(value_node)
    return result


CorrectionsLoader.add_constructor('tag:yaml.org,2002:map', _unique_mapping)


def read_corrections(path):
    data = yaml.load(Path(path).read_text(), Loader=CorrectionsLoader)

    def mapping(value, required, optional, where):
        if (not isinstance(value, dict) or not set(required) <= value.keys()
                or value.keys() - set(required) - set(optional)):
            raise ValueError('Missing or unknown correction fields: ' + where)

    def text(value, where):
        if not isinstance(value, str) or not value.strip():
            raise ValueError('Expected nonempty correction text: ' + where)

    def labels(value, where, nonempty=False):
        if (not isinstance(value, list) or (nonempty and not value)
                or any(not isinstance(v, str) or not v.strip() for v in value)
                or len(value) != len(set(value))):
            raise ValueError('Expected unique correction references: ' + where)

    mapping(data, ('version', 'scope', 'corrections'), (), 'document')
    if type(data['version']) is not int or data['version'] != 1:
        raise ValueError('Unsupported corrections version')
    text(data['scope'], 'scope')
    records = data['corrections']
    if not isinstance(records, list) or not records:
        raise ValueError('Expected correction records')
    identities = set()
    for record in records:
        mapping(record, ('id', 'title', 'reference', 'status', 'original', 'revision',
                         'problem', 'progress', 'links'), ('counterexample', 'history'), 'record')
        for key in ('id', 'title', 'reference', 'problem', 'progress'):
            text(record[key], key)
        if not re.fullmatch(r'[a-z][a-z0-9-]*', record['id']) or record['id'] in identities:
            raise ValueError('Invalid or duplicate correction identity: ' + record['id'])
        identities.add(record['id'])
        for key in ('counterexample', 'history'):
            if key in record and not isinstance(record[key], str):
                raise ValueError('Expected correction text: ' + key)
        status = record['status']
        mapping(status, ('kind', 'label'), (), record['id'] + '.status')
        if not isinstance(status['kind'], str) or status['kind'] not in TONES:
            raise ValueError('Invalid correction status: ' + record['id'])
        text(status['label'], 'status.label')
        original = record['original']
        mapping(original, ('statements', 'source_line'), ('include_proof_claim',), 'original')
        labels(original['statements'], 'original.statements', nonempty=True)
        if any(not re.fullmatch(r'\d+\.\d+', n) for n in original['statements']):
            raise ValueError('Invalid AimPaper statement number')
        if type(original['source_line']) is not int or original['source_line'] < 1:
            raise ValueError('Invalid original source line')
        if type(original.get('include_proof_claim', False)) is not bool:
            raise ValueError('Invalid original proof-claim flag')
        revision = record['revision']
        mapping(revision, ('nodes',), ('definitions', 'note'), 'revision')
        labels(revision['nodes'], 'revision.nodes')
        labels(revision.get('definitions', []), 'revision.definitions')
        if 'note' in revision:
            text(revision['note'], 'revision.note')
        if not revision['nodes'] and not revision.get('note'):
            raise ValueError('A correction without a revised node must state its gap')
        links = record['links']
        if not isinstance(links, list) or not links:
            raise ValueError('Expected Blueprint reading links')
        for link in links:
            mapping(link, ('node', 'title'), (), 'links')
            text(link['node'], 'links.node'); text(link['title'], 'links.title')
    return records


def markdown(text):
    """Use the pinned native Markdown/math convention and repair root links."""
    rendered = _md_to_html(text.strip())

    def link(match):
        url, label = html.unescape(match[1]), match[2]
        if url.startswith('local-history/'):
            return '<span class="memo-local-ref">' + label + ' <small>本地审查记录</small></span>'
        if url.startswith('interface-proposals/'):
            from blueprint_proposals import read_reports
            report = next((r for r in read_reports(Path(__file__).resolve().parents[1]) if r['path'] == url), None)
            if report:
                url = 'proposals/index.html#' + quote(report['meta']['issue_id'], safe='')
            else:
                return '<span class="memo-local-ref">' + label + ' <small>未随本次导出提供</small></span>'
        if url == 'AimPaper/main.tex':
            url = 'paper/main.tex.html'
        source = re.fullmatch(r'(KIP126/[^:#]+\.lean)(?::(\d+))?', url)
        if source:
            url = 'source/' + source[1] + '.html' + ('#L' + source[2] if source[2] else '')
        return '<a href="' + html.escape(url, quote=True) + '">' + label + '</a>'

    return re.sub(r'<a href="([^"]+)">(.*?)</a>', link, rendered)


def original_statements(root):
    """Read original statements from AimPaper itself, checking provenance."""
    root = Path(root)
    source = (root / 'AimPaper/main.tex').read_text()
    actual = {(r['kind'], r['start_line'], r['end_line']): r for r in source_statements(source)}
    statements, references = {}, {}
    for path in sorted((root / 'blueprint/paper').rglob('*.tex')):
        for match in re.finditer(r'^% AimPaper: (\d+\.\d+) (\w+) (\d+) (\d+)$', path.read_text(), re.M):
            number, kind, start, end = match.groups()
            row = actual[(kind, int(start), int(end))]
            statements[number] = {**row, 'number': number, 'kind': kind}
            for label in re.findall(r'\\label\{([^}]+)\}', row['raw']):
                references[label] = ('#/Kervaire126#paper:' + number, number)
    for match in re.finditer(r'\\label\{([^}]+)\}', active_tex(source)):
        references.setdefault(match[1], ('paper/main.tex.html#L' + str(source.count('\n', 0, match.start()) + 1), 'original diagram' if match[1].startswith('fig:') else 'original source'))
    references["eq:dr'"] = ('paper/main.tex.html#L1984', '6.21')
    return statements, references


def original_html(raw, references):
    """Convert only prose/list markup; retain every source math expression.

    This is deliberately strict: an unsupported prose control is an error,
    rather than an excuse to silently omit part of the printed statement.
    """
    raw = re.sub(r'\\label\{[^}]+\}', '', active_tex(raw))
    raw = re.sub(r'\\par(?:\{\})?(?![A-Za-z])', '\n\n', raw)
    while match := re.search(r'\\(?:textit|emph|textbf)\{', raw):
        inner, end = _brace_span(raw, raw.index('{', match.start()))
        raw = raw[:match.start()] + inner + raw[end:]
    raw = re.sub(r'^\s*\[[^\]]+\]', '', raw)
    raw = re.sub(r'\\begin\{equation\*?\}', '$$', raw)
    raw = re.sub(r'\\end\{equation\*?\}', '$$', raw)
    math = []

    def protect(match):
        token = 'MEMOMATH' + str(len(math)) + 'TOKEN'
        math.append(html.escape(match[0]))
        return token

    raw = re.sub(r'\$\$[\s\S]*?\$\$|\$[^$]*?\$|\\\[[\s\S]*?\\\]|\\\([\s\S]*?\\\)', protect, raw)

    def prose(text):
        text = text.strip().replace('~', ' ')
        if not text:
            return ''
        links = []

        def reference(match):
            if match[1] not in references:
                raise ValueError('Unknown reference in Memo original: ' + match[1])
            url, title = references[match[1]]
            token = 'MEMOREF' + str(len(links)) + 'TOKEN'
            links.append('<a href="' + html.escape(url, quote=True) + '">' + html.escape(title) + '</a>')
            return token

        text = re.sub(r'\\ref\{([^}]+)\}', reference, text)
        text = re.sub(r'\\cite\{([^}]+)\}', r'[\1]', text)
        if re.search(r'\\[A-Za-z]+', text):
            raise ValueError('Unsupported original prose control: ' + text)
        paragraphs = []
        for paragraph in re.split(r'\n\s*\n', text):
            paragraph = html.escape(re.sub(r'\s+', ' ', paragraph).strip())
            for i, value in enumerate(math):
                paragraph = paragraph.replace('MEMOMATH' + str(i) + 'TOKEN', value)
            for i, value in enumerate(links):
                paragraph = paragraph.replace('MEMOREF' + str(i) + 'TOKEN', value)
            if paragraph:
                paragraphs.append('<p>' + paragraph + '</p>')
        return ''.join(paragraphs)

    out, in_list, in_item = [], False, False
    for part in re.split(r'(\\begin\{enumerate\}|\\end\{enumerate\}|\\item\b)', raw):
        if part == r'\begin{enumerate}':
            if in_list:
                raise ValueError('Unexpected nested enumeration in Memo source')
            out.append('<ol>'); in_list = True
        elif part == r'\item':
            if not in_list:
                raise ValueError('Original item outside enumeration')
            if in_item:
                out.append('</li>')
            out.append('<li>'); in_item = True
        elif part == r'\end{enumerate}':
            if in_item:
                out.append('</li>')
            out.append('</ol>'); in_list = in_item = False
        else:
            out.append(prose(part))
    if in_list:
        raise ValueError('Unclosed source enumeration')
    return ''.join(out)


def blueprint_statement_html(entry, references):
    """Display the actual exported node body, without a second authored version."""
    label = entry['label']
    digest = hashlib.sha256(entry['body'].encode()).hexdigest()
    return ('<section class="memo-blueprint-statement" data-blueprint-label="' + html.escape(label, quote=True)
            + '" data-body-sha256="' + digest + '"><h4><a href="#/Kervaire126#' + quote(label, safe=':') + '">'
            + html.escape(entry['title']) + ' ↗</a></h4><div class="memo-verbatim" lang="en">'
            + original_html(entry['body'], references) + '</div></section>')


def render_memo(root, project=None):
    root = Path(root)
    records = read_corrections(root / 'corrections.yaml')
    originals, references = original_statements(root) if records else ({}, {})
    entries = {e['label']: e for e in project['entries']} if project is not None else None
    if entries:
        references = {**references, **{label: ('#/Kervaire126#' + label, e['title']) for label, e in entries.items()}}
    cards = []
    for i, record in enumerate(records, 1):
        esc = lambda value: html.escape(str(value), quote=True)
        fields = record
        revisions = record['revision']['nodes']
        revision = markdown(record['revision'].get('note', ''))
        if revisions and entries is None:
            revision += '<p>节点正文将在原生导出完成后引入。</p>'
        elif revisions:
            context = record['revision'].get('definitions', [])
            if context:
                revision += ('<details class="memo-history"><summary>Definitions</summary><div class="memo-detail-body">'
                             + ''.join(blueprint_statement_html(entries[label], references) for label in context) + '</div></details>')
            revision += ''.join(blueprint_statement_html(entries[label], references) for label in revisions)
        original = ''
        for number in record['original']['statements']:
            row = originals[number]
            original += ('<h4>' + esc(row['kind'].title() + ' ' + number) + '</h4>'
                         '<div class="memo-verbatim" lang="en">' + original_html(row['raw'], references) + '</div>')
        if record['original'].get('include_proof_claim'):
            source = (root / 'AimPaper/main.tex').read_text()
            start = source.index("From Adams's Hopf invariant one differentials")
            end = source.index('$$', source.index('$$', start) + 2) + 2
            original += ('<h4>原文证明中的第三页候选陈述</h4><div class="memo-verbatim" lang="en">'
                         + original_html(source[start:end], references) + '</div>')
        links = ''.join(
            '<a class="memo-node" href="#/Kervaire126#' + quote(label, safe=':')
            + '"><span>' + esc(title) + '</span><span aria-hidden="true">↗</span></a>'
            for label, title in ((link['node'], link['title']) for link in record['links']))
        details = ''
        if fields.get('counterexample', '').strip():
            details += ('<details class="memo-evidence"><summary><span><b>反例与证据</b>'
                        '</span><span class="memo-expand" '
                        'aria-hidden="true">＋</span></summary><div class="memo-detail-body">'
                        + markdown(fields['counterexample']) + '</div></details>')
        if fields.get('history', '').strip():
            details += ('<details class="memo-history"><summary><span><b>论证与修订过程</b>'
                        '</span>'
                        '<span class="memo-expand" aria-hidden="true">＋</span></summary>'
                        '<div class="memo-detail-body">' + markdown(fields['history']) + '</div></details>')
        cards.append(f'''<article class="memo-case memo-{esc(record['status']['kind'])}" id="memo-{esc(record['id'])}">
  <header class="memo-case-header"><div class="memo-case-number">{i:02d}</div><div class="memo-case-heading">
    <div class="memo-reference">{esc(record['reference'])}</div><h2>{esc(record['title'])}</h2>
  </div><span class="memo-status"><i aria-hidden="true"></i>{esc(record['status']['label'])}</span></header>
  <div class="memo-comparison">
    <section class="memo-original"><h3>原文完整陈述</h3>{original}
      <a class="memo-source" href="paper/main.tex.html#L{int(record['original']['source_line'])}">核对原始出处 <span aria-hidden="true">↗</span></a></section>
    <details class="memo-problem"><summary><b>问题与修改理由</b><span class="memo-expand" aria-hidden="true">＋</span></summary><div class="memo-detail-body">{markdown(fields['problem'])}</div></details>
    {details}
    <section class="memo-revision"><h3>修正后完整陈述</h3>{revision}</section>
  </div>
  <section class="memo-boundary"><h3>进展与未完成边界</h3>{markdown(fields['progress'])}</section>
  <footer class="memo-case-footer"><span class="memo-footer-label">对应 Blueprint</span><div class="memo-node-list">{links}</div></footer>
</article>''')
    template = (root / 'site/memo.html').read_text()
    return template.replace('<!-- MEMO_COUNT -->', str(len(records))).replace('<!-- MEMO_CASES -->', '\n'.join(cards))


def stage_memo(root, project):
    destination = Path(project) / 'site/memo.html'
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text(render_memo(root))


def export_memo(root, out):
    """Check that reading links resolve in this export; preserve the root record."""
    root, out = Path(root), Path(out)
    project = json.loads((out / 'Kervaire126/data.json').read_text())
    labels = {label for entry in project['entries']
              for label in [entry['label'], *entry.get('labels', [])]}
    records = read_corrections(root / 'corrections.yaml')
    requested = {link['node'] for record in records for link in record['links']}
    requested.update(label for record in records for label in record['revision']['nodes'] + record['revision'].get('definitions', []))
    if missing := requested - labels:
        raise ValueError('Memo links are missing from the exported Blueprint: ' + ', '.join(sorted(missing)))
    content = render_memo(root, project)
    for name in ('data.json', 'project.json'):
        path = out / 'Kervaire126' / name
        payload = json.loads(path.read_text())
        tabs = [t for t in payload['customTabs'] if t['id'] == 'memo']
        if len(tabs) != 1:
            raise ValueError('Expected exactly one native Memo tab')
        tabs[0]['html'] = content
        path.write_text(json.dumps(payload, ensure_ascii=False, separators=(',', ':')))
    # Remove obsolete generated downloads when refreshing a previous export.
    for name in ('MEMO.md', 'MEMO.md.gz'):
        (out / 'memo' / name).unlink(missing_ok=True)
    return {'records': len(records), 'blueprint_links': len(requested),
            'content_source': 'corrections.yaml', 'schema_version': 1, 'revised_statement_source': 'Kervaire126/data.json entries[].body',
            'scope': 'Reading links only; no formal bindings or proof-status changes.'}
