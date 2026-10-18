"""AimPaper provenance checks and rendering compatibility for native hgraph.

The authored statements, hidden correspondence metadata, labels and Lean links
live in blueprint/paper/*.tex. Explicit uses bind declarations independently of
the mathematical prose. Historical metadata only seeded that authoring.
"""
from collections import Counter
import hashlib
import html
from pathlib import Path
import re
import shutil

from hgraph.dashboard import discover_bib
from hgraph.sync import parse_blueprint, _brace_span

CORE = r'theorem|lemma|definition|corollary|proposition|fact'
START = '% BEGIN AIMPAPER STATEMENT\n'
END = '\n% END AIMPAPER STATEMENT'
STATUS = {
    'public-existing': '已有公共对应（范围限制见说明）',
    'public-new': '已有公共对应（范围限制见说明）',
    'partial': '部分对应', 'incomplete': '相关步骤待补齐',
    'missing': '尚无公共对应', 'outside': '当前目标范围外',
}


def active_tex(text):
    # Preserve offsets/line numbers, including TeX's odd/even slash escaping.
    return re.sub(r'(\\*)%[^\n]*', lambda m: m[0] if len(m[1]) % 2
                  else m[1] + ' ' * (len(m[0]) - len(m[1])), text)


def source_statements(text):
    active = active_tex(text)
    return [{'kind': m[1], 'start_line': text.count('\n', 0, m.start()) + 1,
             'end_line': text.count('\n', 0, m.end()) + 1,
             'raw': text[m.start(2):m.end(2)].strip()}
            for m in re.finditer(r'\\begin\{(' + CORE + r')\}(.*?)\\end\{\1\}', active, re.S)]


def citation_keys(text):
    return {key.strip() for m in re.finditer(r'\\cite\w*\*?(?:\[[^\]]*\])?\{([^}]+)\}', active_tex(text))
            for key in m[1].split(',')}


def resolve_paper_bindings(statement, source_labels):
    """Resolve stable authored names through explicit declaration dependencies.

    Private homonyms in different modules remain separate. No textual name
    search or global namespace guess can silently bind the wrong declaration;
    mathematical prose need not contain implementation links.
    """
    refs = {label for label in statement['uses'] if label.startswith('decl:')}
    if not refs <= source_labels.keys():
        raise ValueError('Unknown Lean correspondence: ' + str(refs - source_labels.keys()))
    visible_refs = set(re.findall(r'\\ref\{(decl:[^}]+)\}', active_tex(statement['body'])))
    if not visible_refs <= refs:
        raise ValueError('Paper dependencies must inherit every bound source')
    names, targets = [], set()
    for name in statement['lean']:
        matches = [(label, source_labels[label]) for label in refs
                   if name in (source_labels[label].get('lean_name'), source_labels[label].get('fqname'))]
        if len(matches) != 1:
            raise ValueError('Lean binding does not uniquely match its explicit source: ' + name)
        target, source = matches[0]
        names.append(source['lean_name'])
        targets.add(target)
    if targets != refs or len(names) != len(set(names)):
        raise ValueError('Every listed correspondence needs one native Lean binding')
    return names


def correspondence_status(block, number):
    """Read exactly one hidden status, accepting legacy rendered status text.

    Comments preserve audit metadata while keeping the mathematical statement
    clean. A duplicate or empty status must not silently override another one.
    """
    hidden = re.findall(r'^[ \t]*%[ \t]*Correspondence:[ \t]*([^\n]*)', block, re.M)
    legacy = re.findall(r'\\textbf\{(?:对应状态：|Correspondence: )([^}]+)\}', active_tex(block))
    statuses = [status.strip() for status in hidden + legacy]
    if not statuses or not statuses[0]:
        raise ValueError(f'Missing correspondence explanation: {number}')
    if len(statuses) != 1:
        raise ValueError(f'Expected exactly one correspondence status: {number}')
    return statuses[0]


def load_paper(root, source_labels):
    """Reject missing/altered statements, broken correspondences and false green.

    Native Lean bindings describe the existing project representation.
    Incomplete/general-scope bridges carry the native sketch marker. Their scope
    notes and correspondence status are hidden authoring metadata, rather than
    explanatory text rendered inside the mathematical statement.
    """
    original = (root / 'AimPaper/main.tex').read_text()
    expected = {(r['kind'], r['start_line'], r['end_line']): r for r in source_statements(original)}
    result = []
    seen = set()
    for path in sorted((root / 'blueprint/paper').glob('*.tex')):
        text = path.read_text()
        blocks = re.split(r'(?=^% AimPaper: )', text, flags=re.M)[1:]
        for block in blocks:
            m = re.match(r'% AimPaper: (\d+\.\d+) (\w+) (\d+) (\d+)\n', block)
            if not m or START not in block or END not in block:
                raise ValueError(f'Malformed AimPaper provenance: {path}')
            number, kind, start, end = m.groups()
            key = kind, int(start), int(end)
            raw = block.split(START, 1)[1].split(END, 1)[0]
            if key not in expected or key in seen or raw != expected[key]['raw']:
                raise ValueError(f'AimPaper statement differs from its source: {number}')
            seen.add(key)
            statements, proofs = parse_blueprint(active_tex(block))
            if len(statements) != 1 or proofs or statements[0]['label'] != 'paper:' + number:
                raise ValueError(f'AimPaper must have one native statement: {number}')
            statement = statements[0]
            refs = {label for label in statement['uses'] if label.startswith('decl:')}
            if not refs <= source_labels.keys():
                raise ValueError(f'Unknown Lean correspondence in AimPaper {number}: {refs - source_labels.keys()}')
            if statement['leanok'] or statement['mathlibok']:
                raise ValueError(f'AimPaper must derive status from real Lean declarations: {number}')
            names = resolve_paper_bindings(statement, source_labels)
            if set(statement['uses']) != refs:
                raise ValueError(f'Paper dependencies must inherit every bound source: {number}')
            status = correspondence_status(block, number)
            if (status in ('部分对应', '相关步骤待补齐') or status.lower().startswith(('partial', 'incomplete', 'related steps remain'))) and not statement['sketch']:
                raise ValueError(f'Partial correspondence needs native sketch and scope notes: {number}')
            result.append({**statement, 'authored_lean': statement['lean'], 'lean': names, 'number': number, 'kind': kind, 'start_line': int(start),
                           'end_line': int(end), 'raw': raw, 'mapping_labels': sorted(refs),
                           'mapping_status': status, 'owner': path.stem})
    if seen != expected.keys() or len({r['number'] for r in result}) != len(expected):
        raise ValueError('AimPaper statement coverage is not exhaustive and unique')
    bib = discover_bib(root / 'blueprint/content.tex')
    keys = [r['key'] for r in bib]
    cited = citation_keys(original)
    if len(keys) != len(set(keys)) or not cited <= set(keys):
        raise ValueError(f'AimPaper bibliography missing citations: {cited - set(keys)}')
    if any(not r['title'] for r in bib if r['key'] in cited):
        raise ValueError('AimPaper bibliography has an untitled cited entry')
    if (root / 'AimPaper/algtop.sty').exists() and (root / 'blueprint/paper/algtop.sty').read_bytes() != (root / 'AimPaper/algtop.sty').read_bytes():
        raise ValueError('Native paper macros differ from AimPaper/algtop.sty; update explicitly')
    if (root / 'blueprint/paper/references.bib').read_bytes() != (root / 'AimPaper/main.bib').read_bytes():
        raise ValueError('Native bibliography differs from AimPaper/main.bib; update explicitly')
    return sorted(result, key=lambda r: tuple(map(int, r['number'].split('.')))), {
        'statements': len(result), 'by_kind': dict(Counter(r['kind'] for r in result)),
        'mapping_status': dict(Counter(r['mapping_status'] for r in result)),
        'with_source_links': sum(bool(r['mapping_labels']) for r in result),
        'bound_statements': sum(bool(r['lean']) for r in result),
        'partial_bound_statements': sum(bool(r['lean']) and r['sketch'] for r in result),
        'bibliography_entries': len(bib), 'cited_entries': len(cited),
        'source_sha256': hashlib.sha256(original.encode()).hexdigest(),
    }


def reference_targets(root, statements):
    refs = {alias: ('#/Kervaire126#' + row['label'], row['label'].removeprefix('paper:'))
            for row in statements if row['label'].startswith('paper:') for alias in row['labels']}
    path = root / 'AimPaper/main.tex'
    if path.exists():
        source = path.read_text()
        for match in re.finditer(r'\\label\{([^}]+)\}', active_tex(source)):
            refs.setdefault(match[1], ('paper/main.tex.html#L'
                + str(source.count('\n', 0, match.start()) + 1), 'original source'))
    return refs


def web_bibliography(text):
    """Normalize DOI fields in the rendering copy for native hgraph's parser.

    The pinned parser prepends https://doi.org/ to a DOI field verbatim.
    Authored bibliographies, explicit URL fields and bare DOIs stay intact.
    """
    def normalize(match):
        field = match[2]
        value = field[1:-1].strip()
        doi = re.sub(r'^https?://(?:dx\.)?doi\.org/', '', value, flags=re.I)
        return match[0] if doi == value else match[1] + field[0] + doi + field[-1]
    return re.sub(r'(?i)(\bdoi\s*=\s*)(\{[^{}]*\}|"[^"]*")', normalize, text)


def prepare_web_blueprint(root, destination):
    # Native chapter rendering reads the TeX document; graph detail rendering
    # reads node bodies. Supply both with the same compatibility conversion.
    # The source of truth stays authored native TeX, including exact raw text.
    from hgraph.sync import read_blueprint
    statements, _proofs = parse_blueprint(read_blueprint(root / 'blueprint/content.tex'))
    refs = reference_targets(root, statements)
    if destination.exists():
        shutil.rmtree(destination)
    destination.mkdir(parents=True, exist_ok=True)
    for path in sorted((root / 'blueprint').rglob('*')):
        if not path.is_file() or path.suffix not in ('.tex', '.sty', '.bib'):
            continue
        relative = path.relative_to(root / 'blueprint')
        target = destination / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        if path.parent.name == 'paper' and path.suffix == '.tex' and '% AimPaper: ' in path.read_text():
            blocks = re.split(r'(?=^% AimPaper: )', path.read_text(), flags=re.M)
            for index in range(1, len(blocks)):
                number = re.match(r'% AimPaper: (\d+\.\d+)', blocks[index])[1]
                blocks[index] = display_body(blocks[index], number, refs)
            target.write_text(implementation_links(''.join(blocks)))
        elif path.suffix == '.bib':
            target.write_text(web_bibliography(path.read_text()))
        else:
            # Use buffered reads/writes to preserve the exact source bytes;
            # a previous shared-filesystem copy contained a NUL-filled prefix.
            target.write_bytes(path.read_bytes())
    return destination


def implementation_links(body):
    """Stable source labels now open the separate implementation archive."""
    return re.sub(r'\\ref\{(decl:[^}]+)\}',
        lambda m: r'\href{implementation/index.html#' + m[1] + '}{implementation}', body)


def display_enumeration(body):
    stack = []
    pattern = re.compile(r"\\begin\{enumerate\}(?:\[[^\]]*\])?|\\end\{enumerate\}|"
                         r"\\setcounter\{(enumi+)\}\{(\d+)\}|\\item\b(?:\[[^\]]*\])?")
    def token(match):
        text = match[0]
        if text.startswith(r'\begin'):
            stack.append([0, "'" if "arabic*'" in text else ''])
            return r'\begin{enumerate}'
        if text.startswith(r'\end'):
            if not stack:
                raise ValueError('Unbalanced AimPaper enumeration')
            stack.pop()
            return text
        if text.startswith(r'\setcounter'):
            if not stack:
                raise ValueError('Counter outside AimPaper enumeration')
            stack[-1][0] = int(match[2])
            return ''
        if stack:
            stack[-1][0] += 1
            return r'\item[(' + str(stack[-1][0]) + stack[-1][1] + ')]'
        return text
    result = pattern.sub(token, body)
    if stack:
        raise ValueError('Unbalanced AimPaper enumeration')
    return result


def display_body(body, number, reference_targets=None):
    """Use native links for unsupported XY diagrams; keep original TeX intact."""
    body = display_enumeration(active_tex(body))
    spans = []
    for match in re.finditer(r'\\xymatrix\s*\{', body):
        _inner, end = _brace_span(body, body.index('{', match.start()))
        spans.append((match.start(), end))
    for start, end in reversed(spans):
        index = next(i for i, span in enumerate(spans, 1) if span[0] == start)
        body = body[:start] + r'\text{see the original commutative diagram}' + body[end:]
    if spans:
        body += '\n\\par\\href{paper/diagrams/' + number + '.html}{Original diagrams and hypotheses}\n'
    # TeX layout/counter commands are not mathematical content. Retain them in
    # the authored source, omit them from the native browser's text renderer.
    if reference_targets:
        def reference(match):
            label = match[1]
            target = reference_targets.get(label)
            return ('\\href{' + target[0] + '}{' + target[1] + '}') if target else match[0]
        body = re.sub(r'\\ref\{([^}]+)\}', reference, body)
    # Native citations link correctly but omit their optional locator. Keep that
    # locator visible next to the native citation instead of silently losing it.
    body = re.sub(r'\\cite(\[[^\]]+\])\{([^}]+)\}', r'\\cite{\2} (\1)', body)
    body = re.sub(r'\\setcounter\{[^}]*\}\{[^}]*\}', '', body)
    body = re.sub(r'\\vspace\*?\{[^}]*\}', '', body)
    return body


def validate_paper_graph(graph, records, analysis, projection=None):
    from hgraph.graph import node_id
    by_source = {}
    for edge in graph.edges():
        by_source.setdefault(edge.source, []).append(edge)
    for record in records:
        nid = node_id('bp', record['label'])
        node = graph.get_node(nid)
        mappings = {node_id('bp', target) for target in (projection['uses'][record['label']]
                    if projection else record['mapping_labels'])}
        hard = {e.target for e in by_source.get(nid, []) if e.hard}
        if record['lean']:
            targets = [node_id('lean', name) for name in record['lean']]
            statuses = [graph.get_node(target).meta.get('lean_status') or 'empty' for target in targets]
            expected_local = 'sorry' if 'sorry' in statuses else 'empty' if 'empty' in statuses else 'lean_ok'
            formal = {e.target for e in by_source.get(nid, []) if e.type == 'formalizes'}
            if (analysis.closed[nid] != all(analysis.closed[target] for target in targets)
                    or node.meta.get('lean_status') != expected_local
                    or hard != mappings or formal != set(targets)):
                raise ValueError('Paper binding lost actual local status/closure: ' + record['number'])
        elif node.meta.get('lean_status') != 'empty' or hard:
            raise ValueError('Unmapped paper node acquired proof status: ' + record['number'])
        if bool(node.meta.get('sketch')) != record['sketch']:
            raise ValueError('Paper mapping scope marker differs: ' + record['number'])
        tags = set(node.meta.get('tags') or [])
        tags.add('source:AimPaper')
        graph.modify_node(nid, set_meta={'tags': sorted(tags)})
    return dict(Counter(analysis.states[node_id('bp', r['label'])] for r in records))


def write_index(root, records, stats):
    def link(label, title):
        return '<a href="#/Kervaire126#' + html.escape(label, quote=True) + '">' + html.escape(title) + '</a>'
    body = '<h2>AimPaper concordance</h2><p>Lin–Wang–Xu, <em>On the Last Kervaire Invariant Problem</em>.</p>'
    body += '<p>All original numbers are retained. The first seven chapters follow the mathematical modules; Chapter 8 contains the unformalized geometric endpoint. Each statement begins with its article citation and original locator. Bound counterparts inherit their actual local state and complete dependency closure. Native sketch marks partial correspondences; read the explicit scope limitations.</p>'
    body += '<p>Global conventions: spectra are 2-completed, connective and of finite type, with strongly convergent HF-Adams spectral sequences. Local hypotheses, notation and preceding definitions remain part of each source statement.</p>'
    body += '<p><a href="paper/main.tex.html#L254" target="_blank">Full article and context</a> · <a href="paper/2412.10879.pdf" target="_blank">Original PDF</a> · <a href="paper/main.bib" target="_blank">Original BibTeX</a></p>'
    body += f'<p>{stats["statements"]} original definitions and results; {stats["bibliography_entries"]} bibliography entries, of which {stats["cited_entries"]} are cited in the article. Remarks, notation, questions and proof text remain available in the original source. These reference entries add no Lean proof obligations.</p>'
    body += '<table><thead><tr><th>Paper item</th><th>Chapter</th><th>Correspondence</th><th>Lean counterparts</th></tr></thead><tbody>'
    for r in records:
        body += '<tr><td>' + link(r['label'], r['kind'].title() + ' ' + r['number']) + '</td><td>' + r['owner'] + '</td><td>' + html.escape(r['mapping_status']) + '</td><td>' + str(len(r['mapping_labels'])) + '</td></tr>'
    body += '</tbody></table>'
    (root / '.lake/blueprint/paper-index.html').write_text(body)


def export_paper(root, out, records):
    target = out / 'paper'
    target.mkdir(parents=True, exist_ok=True)
    for filename in ('main.bib', '2412.10879.pdf'):
        shutil.copyfile(root / 'AimPaper' / filename, target / filename)
    source = (root / 'AimPaper/main.tex').read_text()
    lines = '\n'.join(f'<span id="L{i}"><a href="#L{i}">{i:4}</a> {html.escape(line)}</span>'
                      for i, line in enumerate(source.splitlines(), 1))
    (target / 'main.tex.html').write_text('<!doctype html><meta charset="utf-8"><title>AimPaper source</title><style>pre>span{display:block}pre>span:target{background:#fff0a8}pre{line-height:1.6;white-space:pre-wrap}</style><h1>AimPaper/main.tex</h1><pre>' + lines + '</pre>')
    # Every original XY diagram is compiled directly from the paper, without
    # transcribing arrows or converting it into a weaker mathematical claim.
    import subprocess
    diagram_dir = target / 'diagrams'
    diagram_dir.mkdir(exist_ok=True)
    work = root / '.lake/blueprint/paper-diagrams'
    work.mkdir(parents=True, exist_ok=True)
    for r in records:
        diagrams = []
        for match in re.finditer(r'\\xymatrix\s*\{', r['raw']):
            _body, end = _brace_span(r['raw'], r['raw'].index('{', match.start()))
            diagrams.append(r['raw'][match.start():end])
        if not diagrams:
            continue
        page = '<!doctype html><meta charset="utf-8"><title>AimPaper ' + r['number'] + ' diagrams</title><h1>AimPaper ' + r['number'] + ' original commutative diagrams</h1>'
        for i, diagram in enumerate(diagrams, 1):
            stem = r['number'] + '-' + str(i)
            document = (r'\documentclass{article}\usepackage{algtop}\usepackage[all,cmtip]{xy}'
                        r'\usepackage{mathtools}\pagestyle{empty}\begin{document}$$' + diagram + r'$$\end{document}')
            input_path = work / (stem + '.tex')
            input_path.write_text(document)
            svg = work / (stem + '.svg')
            stamp = work / (stem + '.sha256')
            signature = hashlib.sha256((document + (root / 'AimPaper/algtop.sty').read_text()).encode()).hexdigest()
            if not svg.exists() or not stamp.exists() or stamp.read_text() != signature:
                for command in (['latex', '-interaction=nonstopmode', '-halt-on-error', '-output-directory=' + str(work), str(input_path)],
                                ['dvisvgm', '--no-fonts', '--exact', '--bbox=min', '-o', str(svg), str(work / (stem + '.dvi'))]):
                    process = subprocess.run(command, cwd=root / 'AimPaper', capture_output=True, text=True)
                    if process.returncode:
                        raise ValueError('AimPaper diagram rendering failed: ' + process.stdout[-3000:] + process.stderr[-1000:])
                stamp.write_text(signature)
            shutil.copyfile(svg, diagram_dir / (stem + '.svg'))
            page += '<p><img alt="AimPaper ' + r['number'] + ' original commutative diagrams" src="' + stem + '.svg"></p>'
        page += '<p><a href="../main.tex.html#L' + str(r['start_line']) + '">Full source, hypotheses and context</a> · <a href="../2412.10879.pdf">Original paper PDF</a></p>'
        (diagram_dir / (r['number'] + '.html')).write_text(page)
