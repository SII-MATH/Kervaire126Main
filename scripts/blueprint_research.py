"""Export canonical research reports without assigning Lean verification states."""
from __future__ import annotations

from datetime import date
import html
from pathlib import Path
import re
import shutil
from urllib.parse import quote, unquote, urlsplit

import yaml

import blueprint_proposals as proposals

SOURCE = 'research/results/*/report.md'
EVIDENCE_SUFFIXES = frozenset(('.md', '.txt', '.json', '.lean', '.log', '.py'))
MAX_EVIDENCE_BYTES = 1_000_000
STATUSES = {
    'reviewed-informal': '已独立复核（非形式化）',
    'conditional': '条件性结果',
    'draft': '研究草稿',
}
FORMALIZATION = {
    'not-formalized': '尚未形式化',
    'partially-formalized': '部分形式化',
    'formalized': '已形式化（报告声明）',
}
NOVELTY = {
    'not-assessed': '新颖性未核查',
    'not-established': '已核查，原创性未确认',
    'known': '文献已有',
    'new': '新结果（报告声明）',
}


class ReportLoader(yaml.SafeLoader):
    pass


def unique_mapping(loader, node):
    result = {}
    for key_node, value_node in node.value:
        key = loader.construct_object(key_node)
        if not isinstance(key, str) or key in result:
            raise ValueError('Duplicate or invalid research key: ' + str(key))
        result[key] = loader.construct_object(value_node)
    return result


ReportLoader.add_constructor('tag:yaml.org,2002:map', unique_mapping)


def _checked_file(root, relative):
    """Check lexical paths before resolving so symlink ancestors cannot disappear."""
    relative = Path(relative)
    if relative.is_absolute() or '..' in relative.parts:
        return None
    candidate = Path(root).resolve()
    for part in relative.parts:
        candidate = candidate / part
        if candidate.is_symlink():
            return None
    return candidate if candidate.is_file() else None


def read_reports(root):
    root = Path(root).resolve()
    reports, seen = [], set()
    for path in sorted(root.glob(SOURCE)):
        relative = path.relative_to(root)
        if _checked_file(root, relative) is None:
            raise ValueError(f'{path}: report must be a regular file without symlinks')
        raw = path.read_text(encoding='utf-8')
        parts = re.split(r'^---\s*$', raw, maxsplit=2, flags=re.M)
        if len(parts) != 3 or parts[0].strip():
            raise ValueError(f'{path}: expected YAML front matter')
        try:
            meta = yaml.load(parts[1], Loader=ReportLoader)
        except (yaml.YAMLError, ValueError) as error:
            raise ValueError(f'{path}: {error}') from error
        if not isinstance(meta, dict):
            raise ValueError(f'{path}: expected research metadata')
        for key in ('result_id', 'title', 'summary', 'topic', 'status', 'evidence_level',
                    'formalization_status', 'novelty_status', 'baseline_commit', 'updated'):
            if not isinstance(meta.get(key), str) or not meta[key].strip():
                raise ValueError(f'{path}: expected nonempty string {key}')
        identity = meta['result_id']
        if not re.fullmatch(r'[A-Za-z0-9][A-Za-z0-9_.-]*', identity) or identity in seen:
            raise ValueError(f'{path}: invalid or duplicate result_id {identity}')
        seen.add(identity)
        if path.parent.name != identity:
            raise ValueError(f'{path}: result_id must match its directory name')
        for key, values in (('status', STATUSES), ('formalization_status', FORMALIZATION),
                            ('novelty_status', NOVELTY)):
            if meta[key] not in values:
                raise ValueError(f'{path}: unknown {key} {meta[key]}')
        try:
            updated = date.fromisoformat(meta['updated'])
        except ValueError as error:
            raise ValueError(f'{path}: updated must be a quoted ISO date') from error
        if updated.isoformat() != meta['updated']:
            raise ValueError(f'{path}: updated must be a quoted ISO date')
        for key in ('authors', 'reviewers'):
            values = meta.get(key)
            if not isinstance(values, list) or any(
                    not isinstance(value, str) or not value.strip() for value in values):
                raise ValueError(f'{path}: expected {key} list of nonempty strings')
        if not meta['authors']:
            raise ValueError(f'{path}: authors must not be empty')
        if meta['status'] == 'reviewed-informal' and not meta['reviewers']:
            raise ValueError(f'{path}: reviewed-informal requires reviewers')
        if not parts[2].strip():
            raise ValueError(f'{path}: empty report body')
        reports.append({'meta': meta, 'body': parts[2].strip(), 'raw': raw,
                        'path': relative.as_posix()})
    return sorted(reports, key=lambda report: (report['meta']['topic'],
                  -date.fromisoformat(report['meta']['updated']).toordinal(),
                  report['meta']['result_id']))


def _evidence_file(root, report_path, url):
    parsed = urlsplit(url)
    if parsed.scheme or parsed.netloc or parsed.query or not parsed.path:
        return None
    relative = Path(unquote(parsed.path))
    if relative.is_absolute() or '..' in relative.parts or '\x00' in str(relative):
        return None
    candidate = _checked_file(root, Path(report_path).parent / relative)
    if (candidate and candidate.suffix in EVIDENCE_SUFFIXES
            and candidate.stat().st_size <= MAX_EVIDENCE_BYTES):
        return candidate
    return None


def _canonical_report_link(parsed, report_path, root, reports):
    if parsed.scheme or parsed.netloc or parsed.query:
        return None
    known = {report['path']: report['meta']['result_id'] for report in reports}
    if not parsed.path:
        identity = unquote(parsed.fragment)
        return identity if identity in known.values() else None
    relative = Path(unquote(parsed.path))
    if relative.is_absolute() or '\x00' in str(relative):
        return None
    root = Path(root).resolve()
    candidate = root / Path(report_path).parent
    # Cross-report links may use .. only when they end at a validated report.
    for part in relative.parts:
        candidate = candidate.parent if part == '..' else candidate / part
        if not candidate.is_relative_to(root) or candidate.is_symlink():
            return None
    return known.get(candidate.relative_to(root).as_posix())


def reading_link(url, label, report_path, root, *, reports=None):
    url = html.unescape(url)
    local = (f'<span class="proposal-local" title="{html.escape(url, quote=True)}">'
             f'{label} <small>\u672c\u5730\u8bc1\u636e</small></span>')
    try:
        parsed = urlsplit(url)
        canonical = _canonical_report_link(parsed, report_path, root,
                                            read_reports(root) if reports is None else reports)
        evidence = _evidence_file(root, report_path, url)
    except ValueError:
        return local
    if canonical:
        return f'<a href="#{canonical}">{label}</a>'
    if evidence:
        relative = evidence.relative_to(Path(root).resolve()).as_posix()
        href = 'reports/' + quote(relative, safe='/')
        return f'<a href="{href}" download>{label} &#8599;</a>'
    if parsed.scheme in ('http', 'https') and parsed.netloc:
        return proposals.reading_link(url, label, report_path, root)
    if url.startswith('#/Kervaire126#'):
        return proposals.reading_link(url, label, report_path, root)
    source = re.fullmatch(r'(?:\.\./)*(KIP126/[^:#]+\.lean)(?::(\d+))?', url)
    if source and _checked_file(root, source[1]):
        return proposals.reading_link(url, label, report_path, root)
    return local


def markdown(text, report_path, root, *, reports=None):
    reports = read_reports(root) if reports is None else reports
    return proposals.markdown(text, report_path, root, link_renderer=lambda url, label, path, base:
                              reading_link(url, label, path, base, reports=reports))


def _render_reports(root, reports):
    esc = html.escape
    cards = []
    for report in reports:
        meta = report['meta']
        identity, status = meta['result_id'], meta['status']
        cards.append(f'''<article class="research-card" id="{esc(identity, quote=True)}"
 data-topic="{esc(meta['topic'], quote=True)}" data-status="{esc(status, quote=True)}">
 <div class="proposal-meta"><span>{esc({'theta5': 'θ₅', 'theta6': 'θ₆'}.get(meta['topic'], meta['topic']))}</span><span class="proposal-status {status}">{STATUSES[status]}</span></div>
 <h2>{esc(meta['title'])}</h2><p class="proposal-id">{esc(identity)}</p>
 <p class="research-summary">{esc(meta['summary'])}</p>
 <dl><dt>证据等级</dt><dd>{esc(meta['evidence_level'])}</dd>
 <dt>Lean 形式化</dt><dd>{FORMALIZATION[meta['formalization_status']]}</dd>
 <dt>文献新颖性</dt><dd>{NOVELTY[meta['novelty_status']]}</dd></dl>
 <details class="proposal-report"><summary>展开完整报告</summary>
 <div class="proposal-body">{markdown(report['body'], report['path'], root, reports=reports)}</div></details>
 <details class="research-source"><summary>来源与复核记录</summary><pre>{esc(yaml.safe_dump(meta, allow_unicode=True, sort_keys=False))}</pre></details>
 <footer><a class="research-permalink" href="#{identity}">固定链接</a>
 <a href="reports/{quote(report['path'], safe='/')}" download>下载完整报告</a></footer>
 </article>''')
    template = (Path(root) / 'site/research.html').read_text(encoding='utf-8')
    return template.replace('<!-- RESEARCH_CARDS -->', '\n'.join(cards)).replace(
        '<!-- RESEARCH_COUNT -->', str(len(cards)))


def render_reports(root):
    return _render_reports(root, read_reports(root))


def stage_research(root, project):
    destination = Path(project) / 'site/research.html'
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text('<iframe class="research-frame" title="Research" '
                           'src="research/index.html" loading="lazy"></iframe>', encoding='utf-8')


def export_research(root, out):
    root, out = Path(root).resolve(), Path(out)
    reports = read_reports(root)
    content = _render_reports(root, reports)
    try:
        loader = next(iter(sorted((out / 'assets').glob('katexLoader-*.js'))))
        style = next(iter(sorted((out / 'assets').glob('katexLoader-*.css'))))
    except StopIteration as error:
        raise ValueError('Research export requires local hgraph KaTeX assets') from error
    content = content.replace('<!-- RESEARCH_MATH -->',
        f'<link rel="stylesheet" href="../assets/{style.name}">'
        f'<script type="module">import renderMath from "../assets/{loader.name}";'
        'window.renderProposalMath = element => renderMath(element, {throwOnError:false,'
        'delimiters:[{left:"$$",right:"$$",display:true},{left:"$",right:"$",display:false},'
        '{left:"\\\\[",right:"\\\\]",display:true},{left:"\\\\(",right:"\\\\)",display:false}]});'
        'document.addEventListener("toggle",event=>{if(event.target.matches(".proposal-report[open]"))'
        'window.renderProposalMath(event.target)},true);'
        'document.querySelectorAll(".proposal-report[open]").forEach(window.renderProposalMath);</script>')
    destination = out / 'research'
    destination.mkdir(parents=True, exist_ok=True)
    (destination / 'index.html').write_text(content, encoding='utf-8')
    for name in ('research.css', 'research.js', 'proposals.css'):
        shutil.copyfile(root / 'site' / name, destination / name)
    for report in reports:
        target = destination / 'reports' / report['path']
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(root / report['path'], target)
        directory = (root / report['path']).parent
        for source in sorted(directory.rglob('*')):
            evidence = _evidence_file(root, report['path'], source.relative_to(directory).as_posix())
            if evidence and evidence != root / report['path']:
                target = destination / 'reports' / evidence.relative_to(root)
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(evidence, target)
    return {'reports': len(reports), 'source': SOURCE,
            'scope': 'Research presentation only; formalization and novelty are reported metadata, not verified proof states.'}
