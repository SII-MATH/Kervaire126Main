"""Read agent interface reports and export a review tab without changing proof states."""
from __future__ import annotations

import html
from pathlib import Path
import re
import shutil
from urllib.parse import quote, unquote, urlsplit

import yaml
from hgraph.site import _md_to_html

MODULES = ('SpectralSequence', 'AdamsSynthetic', 'Literature', 'E2Computation',
           'ProofTools', 'AdamsCalculations', 'Main', 'Geometry', 'Computation')
STATUSES = {
    'draft': ('draft', '草稿'),
    'pending-human-review': ('pending', '未获人审批准'),
    'partially-approved': ('partial', '部分批准'),
    'first-clause-approved-second-clause-under-review': ('partial', '首段已批准 · 后段待审'),
    'approved-interface-change': ('approved', '已批准接口修改'),
    'approved-implemented-and-validated-before-publication': ('approved', '已批准并实施验证'),
    'rejected': ('rejected', '不采纳'),
    'withdrawn': ('withdrawn', '已撤回'),
}


class ReportLoader(yaml.SafeLoader):
    pass


def unique_mapping(loader, node):
    result = {}
    for key_node, value_node in node.value:
        key = loader.construct_object(key_node)
        if not isinstance(key, str) or key in result:
            raise ValueError('Duplicate or invalid proposal key: ' + str(key))
        result[key] = loader.construct_object(value_node)
    return result


ReportLoader.add_constructor('tag:yaml.org,2002:map', unique_mapping)


def read_reports(root):
    """The tracked report is canonical; local-history is never a build input."""
    root = Path(root)
    reports, seen = [], set()
    for path in sorted((root / 'interface-proposals').glob('*/*/report.md')):
        raw = path.read_text()
        parts = re.split(r'^---\s*$', raw, maxsplit=2, flags=re.M)
        if len(parts) != 3 or parts[0].strip():
            raise ValueError(f'{path}: expected YAML front matter')
        meta = yaml.load(parts[1], Loader=ReportLoader)
        if not isinstance(meta, dict):
            raise ValueError(f'{path}: expected proposal metadata')
        for key in ('issue_id', 'title', 'summary', 'responsibility_module', 'reporter_agent',
                    'evidence_level', 'status', 'baseline_commit'):
            if not isinstance(meta.get(key), str) or not meta[key].strip():
                raise ValueError(f'{path}: missing nonempty {key}')
        identity = meta['issue_id']
        if not re.fullmatch(r'[A-Za-z0-9][A-Za-z0-9_.-]*', identity) or identity in seen:
            raise ValueError(f'{path}: invalid or duplicate issue_id {identity}')
        seen.add(identity)
        if meta['responsibility_module'] not in MODULES or meta['status'] not in STATUSES:
            raise ValueError(f'{path}: unknown module or status')
        if not isinstance(meta.get('targets'), list) or not meta['targets'] or any(
                not isinstance(t, str) or not t.strip() for t in meta['targets']):
            raise ValueError(f'{path}: expected nonempty targets')
        independent = meta.get('independent_of_discoverer_and_implementer')
        if type(independent) is not bool or (not independent and meta['status'] != 'draft'):
            raise ValueError(f'{path}: independent reporter required except for explicitly marked research drafts')
        if 'human_decision' not in meta:
            raise ValueError(f'{path}: human_decision must be explicit (null if unapproved)')
        decision = meta['human_decision']
        if decision is not None and (not isinstance(decision, str) or not decision.strip()):
            raise ValueError(f'{path}: invalid human_decision')
        if STATUSES[meta['status']][0] in ('approved', 'partial', 'rejected') and not decision:
            raise ValueError(f'{path}: decision status requires a human_decision record')
        if not parts[2].strip():
            raise ValueError(f'{path}: empty report body')
        reports.append({'meta': meta, 'body': parts[2].strip(), 'raw': raw,
                        'path': path.relative_to(root).as_posix()})
    priority = {'pending': 0, 'partial': 1, 'draft': 2, 'approved': 3, 'rejected': 4, 'withdrawn': 5}
    def order(report):
        date = re.search(r'\d{8}', report['path'])
        return (priority[STATUSES[report['meta']['status']][0]],
                -int(date[0]) if date else 0, report['path'])
    return sorted(reports, key=order)


def reading_link(url, label, report_path, root):
    """Only export links which actually work; mark archived evidence as local."""
    url = html.unescape(url)
    parsed = urlsplit(url)
    if parsed.scheme in ('http', 'https') and parsed.netloc:
        return f'<a href="{html.escape(url, quote=True)}" target="_blank" rel="noopener noreferrer">{label} ↗</a>'
    if url.startswith('#/Kervaire126#'):
        locator = unquote(url.split('#', 2)[2])
        return f'<a href="#" data-blueprint="{html.escape(locator, quote=True)}">{label} ↗</a>'
    source = re.fullmatch(r'(?:\.\./)*(KIP126/[^:#]+\.lean)(?::(\d+))?', url)
    if source and (Path(root) / source[1]).is_file():
        href = '../source/' + source[1] + '.html' + ('#L' + source[2] if source[2] else '')
        return f'<a href="{html.escape(href, quote=True)}" target="_blank">{label} ↗</a>'
    # Evidence is exported only when the agent intentionally places a small file
    # beside the canonical report, never by following paths into local-history.
    if not parsed.scheme and not parsed.netloc and not parsed.query and parsed.path:
        base = Path(root) / report_path
        candidate = (base.parent / unquote(parsed.path)).resolve()
        if base.parent.resolve() in candidate.parents and candidate.is_file() and not candidate.is_symlink():
            relative = candidate.relative_to(Path(root).resolve()).as_posix()
            if candidate.stat().st_size <= 1_000_000 and candidate.suffix in ('.md', '.txt', '.json', '.lean', '.log'):
                href = 'reports/' + quote(relative, safe='/')
                return f'<a href="{href}" target="_blank">{label} ↗</a>'
    return f'<span class="proposal-local" title="{html.escape(url, quote=True)}">{label} <small>本地证据</small></span>'


def markdown(text, report_path, root):
    """Native prose convention, plus literal code fences and readable tables.

    Raw HTML is escaped by the native renderer. Links are allowlisted after
    rendering, including in tables; code blocks are never treated as prose.
    """
    def prose(value):
        rendered = _md_to_html(value)
        return re.sub(r'<a href="([^"]*)">(.*?)</a>',
                      lambda m: reading_link(m[1], m[2], report_path, root), rendered)

    out, pending, code, fence = [], [], [], None

    def flush():
        if pending:
            # Keep Markdown tables readable without adding a new dependency.
            chunks = '\n'.join(pending)
            pieces = re.split(r'((?:^\|[^\n]*\|\s*\n?){2,})', chunks, flags=re.M)
            for piece in pieces:
                rows = piece.strip().splitlines()
                if len(rows) > 1 and re.fullmatch(r'[\s|:\-]+', rows[1]):
                    cells = lambda row: re.split(r'(?<!\\)\|', row.strip().strip('|'))
                    out.append('<div class="proposal-table"><table><thead><tr>' + ''.join(
                        '<th>' + prose(c.strip()) + '</th>' for c in cells(rows[0])) + '</tr></thead><tbody>')
                    for row in rows[2:]:
                        out.append('<tr>' + ''.join('<td>' + prose(c.strip()) + '</td>' for c in cells(row)) + '</tr>')
                    out.append('</tbody></table></div>')
                elif piece.strip():
                    out.append(prose(piece))
            pending.clear()

    for line in text.splitlines():
        marker = re.match(r'^\s*(`{3,}|~{3,})(.*)$', line)
        if fence:
            if marker and marker[1][0] == fence[0] and len(marker[1]) >= len(fence) and not marker[2].strip():
                out.append('<pre><code>' + html.escape('\n'.join(code)) + '</code></pre>')
                code, fence = [], None
            else:
                code.append(line)
        elif marker:
            flush()
            fence = marker[1]
        else:
            pending.append(line)
    if fence:
        out.append('<pre><code>' + html.escape('\n'.join(code)) + '</code></pre>')
    flush()
    return '\n'.join(out)


def render_reports(root):
    reports = read_reports(root)
    cards = []
    esc = html.escape
    for report in reports:
        m = report['meta']
        group, label = STATUSES[m['status']]
        if not m['independent_of_discoverer_and_implementer']:
            label = '研究草稿 · 待独立复核'
        decision = m['human_decision'] or '未记录人类批准；不表示当前必须等待决定。具体行动范围见报告。'
        cards.append(f'''<article class="proposal-card" id="{esc(m['issue_id'], quote=True)}"
 data-module="{esc(m['responsibility_module'], quote=True)}" data-status="{group}">
 <div class="proposal-meta"><span>{esc(m['responsibility_module'])}</span><span class="proposal-status {group}">{label}</span></div>
 <h2>{esc(m['title'])}</h2><p class="proposal-id">{esc(m['issue_id'])}</p>
 <p>{esc(m['summary'])}</p>
 <div class="proposal-targets">{''.join('<code>' + esc(t) + '</code>' for t in m['targets'])}</div>
 <dl><dt>证据等级</dt><dd>{esc(m['evidence_level'])}</dd><dt>人审记录</dt><dd>{esc(decision)}</dd></dl>
 <details class="proposal-report"><summary>展开报告 · 完整前提、证据与方案</summary>
 <div class="proposal-body">{markdown(report['body'], report['path'], root)}</div></details>
 <details><summary>来源与原始状态</summary><pre>{esc(yaml.safe_dump(m, allow_unicode=True, sort_keys=False))}</pre></details>
 <footer><button type="button" data-feedback="{esc(m['issue_id'], quote=True)}">填写审阅反馈</button>
 <a href="reports/{quote(report['path'], safe='/')}" download>下载完整报告 ↓</a></footer>
 </article>''')
    template = (Path(root) / 'site/proposals.html').read_text()
    return template.replace('<!-- PROPOSAL_CARDS -->', '\n'.join(cards)).replace(
        '<!-- PROPOSAL_COUNT -->', str(len(cards)))


def stage_proposals(root, project):
    destination = Path(project) / 'site/proposals.html'
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text('<iframe class="proposal-frame" title="接口提案审阅区" '
                           'src="proposals/index.html" loading="lazy"></iframe>')


def export_proposals(root, out):
    root, out = Path(root), Path(out)
    destination = out / 'proposals'
    destination.mkdir(parents=True, exist_ok=True)
    # Reuse KaTeX shipped with pinned hgraph; no CDN, dependency or toolchain change.
    content = render_reports(root)
    loader = next((out / 'assets').glob('katexLoader-*.js'))
    style = next((out / 'assets').glob('katexLoader-*.css'))
    content = content.replace('<!-- PROPOSAL_MATH -->',
        f'<link rel="stylesheet" href="../assets/{style.name}">'
        f'<script type="module">import renderMath from "../assets/{loader.name}";'
        'window.renderProposalMath = element => renderMath(element, {throwOnError:false,'
        'delimiters:[{left:"$$",right:"$$",display:true},{left:"$",right:"$",display:false},'
        '{left:"\\\\[",right:"\\\\]",display:true},{left:"\\\\(",right:"\\\\)",display:false}]});'
        'document.addEventListener("toggle",event=>{if(event.target.matches(".proposal-report[open]"))'
        'window.renderProposalMath(event.target)},true);</script>')
    (destination / 'index.html').write_text(content)
    for name in ('proposals.css', 'proposals.js'):
        shutil.copyfile(root / 'site' / name, destination / name)
    reports = read_reports(root)
    for report in reports:
        path = destination / 'reports' / report['path']
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(report['raw'])
        for source in (root / report['path']).parent.rglob('*'):
            if (source.is_file() and not source.is_symlink() and source.resolve().is_relative_to((root / report['path']).parent.resolve())
                    and source.suffix in ('.md', '.txt', '.json', '.lean', '.log') and source.stat().st_size <= 1_000_000):
                target = destination / 'reports' / source.relative_to(root)
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(source, target)
    shutil.copyfile(root / 'interface-proposals/TEMPLATE.md', destination / 'TEMPLATE.md')
    guide = markdown((root / 'docs/interface-proposals.md').read_text(), 'docs/interface-proposals.md', root)
    (destination / 'guide.html').write_text('<!doctype html><html lang="zh-CN"><meta charset="utf-8">'
        '<meta name="viewport" content="width=device-width,initial-scale=1"><title>接口提案投递指南</title>'
        '<link rel="stylesheet" href="proposals.css"><main class="proposal-page proposal-body">' + guide + '</main></html>')
    return {'reports': len(reports), 'source': 'interface-proposals/*/*/report.md',
            'scope': 'Review presentation only; no interface, proof-state or approval changes.'}
