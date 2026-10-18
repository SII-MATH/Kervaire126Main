"""Paper source links and rendering compatibility for native hgraph.

These presentation helpers do not validate or change bindings, dependencies or
proof states. All such semantics belong to native hgraph.
"""
import hashlib
import html
from pathlib import Path
import re
import shutil
import xml.etree.ElementTree as ET

from hgraph.sync import parse_blueprint, _brace_span

CORE = r'theorem|lemma|definition|corollary|proposition|fact'
START = '% BEGIN AIMPAPER STATEMENT\n'
END = '\n% END AIMPAPER STATEMENT'


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


def load_paper(root):
    """Read original paper material for source links and diagram rendering only."""
    source = (root / 'AimPaper/main.tex').read_text()
    originals = {(r['kind'], r['start_line'], r['end_line']): r
                 for r in source_statements(source)}
    records = []
    for path in sorted((root / 'blueprint/paper').rglob('*.tex')):
        for number, kind, start, end in re.findall(
                r'^% AimPaper: (\d+\.\d+) (\w+) (\d+) (\d+)$', path.read_text(), re.M):
            original = originals.get((kind, int(start), int(end)))
            if original is not None:
                records.append({**original, 'number': number})
    return records


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
        if 'generated' in path.relative_to(root / 'blueprint').parts:
            continue
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
            target.write_text(''.join(blocks))
        elif path.suffix == '.bib':
            target.write_text(web_bibliography(path.read_text()))
        else:
            # Use buffered reads/writes to preserve the exact source bytes;
            # a previous shared-filesystem copy contained a NUL-filled prefix.
            target.write_bytes(path.read_bytes())
    return destination



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
    """Place styled native SVG links at each diagram's original reading position."""
    body = display_enumeration(active_tex(body))
    if number == '1.4':
        # The merged permanence node cites both original occurrences in its
        # source prefix. The original optional heading would link to itself.
        # Omit it only in the rendering copy; provenance stays verbatim.
        body = body.replace(r'[Theorem~\ref{thm:126survives}]', '', 1)
    spans = []
    for match in re.finditer(r'\\xymatrix\s*\{', body):
        _inner, end = _brace_span(body, body.index('{', match.start()))
        # A link belongs in prose, outside the formula renderer. Only unwrap a
        # display containing this diagram alone; never discard adjoining math.
        opening = re.search(r'(\$\$|\\\[)\s*$', body[:match.start()])
        closing = re.match(r'\s*([.,;:]?)\s*' + (r'\$\$' if opening and opening[1] == '$$' else r'\\\]'), body[end:])
        if not opening or not closing:
            raise ValueError('Expected a standalone display for AimPaper diagram ' + number)
        spans.append((opening.start(), end + closing.end(), closing[1]))
    for index, (start, end, punctuation) in reversed(list(enumerate(spans, 1))):
        link = (r'\href{paper/diagrams/' + number + '-' + str(index)
                + '.svg}{Commutative diagram ' + number + ' (' + str(index) + ')' + punctuation + '}')
        body = body[:start] + '\n\n' + link + '\n\n' + body[end:]
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


def inline_diagram_styles(diagrams):
    """Use the native link and stylesheet APIs without patching pinned hgraph.

    SVG coordinates are TeX points at 10pt. Scale to the surrounding font size;
    cap wide diagrams at the reading column while preserving their aspect ratio.
    Link text stays available to assistive technology and without the stylesheet.
    """
    rules = []
    for stem, svg in diagrams:
        box = [float(v) for v in ET.fromstring(svg.read_text()).attrib['viewBox'].split()]
        width, height = box[2:]
        if width <= 0 or height <= 0:
            raise ValueError('Invalid diagram dimensions: ' + stem)
        rules.append('a.tex-link[href="paper/diagrams/' + stem + '.svg"] {'
                     ' display:block; box-sizing:content-box;'
                     f' width:{width / 10:.6f}em; aspect-ratio:{width:.6f}/{height:.6f};'
                     ' max-width:calc(100% - 1.5em); margin:1.2em auto; padding:.5em;'
                     ' background:white url("' + stem + '.svg") center / contain no-repeat;'
                     ' background-origin:content-box; background-clip:padding-box;'
                     ' border-radius:.25em; text-indent:200%; white-space:nowrap; overflow:hidden;'
                     ' }')
    return '\n'.join(rules) + '\n'


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
    rendered_diagrams = []
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
            rendered_diagrams.append((stem, svg))
            page += '<p><img alt="AimPaper ' + r['number'] + ' original commutative diagrams" src="' + stem + '.svg"></p>'
        page += '<p><a href="../main.tex.html#L' + str(r['start_line']) + '">Full source, hypotheses and context</a> · <a href="../2412.10879.pdf">Original paper PDF</a></p>'
        (diagram_dir / (r['number'] + '.html')).write_text(page)
    # Project presentation only: preserve the pinned native JS/CSS assets.
    (diagram_dir / 'inline.css').write_text(inline_diagram_styles(rendered_diagrams))
    index = out / 'index.html'
    text = index.read_text()
    tag = '<link rel="stylesheet" href="paper/diagrams/inline.css" data-paper-diagrams>'
    if tag not in text:
        index.write_text(text.replace('</head>', tag + '\n</head>', 1))
