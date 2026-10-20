"""Render the meeting task record as a native hgraph custom tab."""
from collections import Counter
import html
from pathlib import Path
import re
import shutil
from urllib.parse import quote, urlsplit

import yaml

STATUSES = {
    'completed': '已完成',
    'in_progress': '进行中',
    'to_confirm': '待确认',
    'to_discuss': '待上会讨论',
    'to_verify': '待核实',
    'merged': '已合并',
}
FOLLOW_UP = {'in_progress', 'to_confirm', 'to_discuss', 'to_verify'}
RECORD = 'meeting/2026-10-13.yaml'


def read_meeting(root):
    record = yaml.safe_load((Path(root) / RECORD).read_text())
    tasks = record['tasks']
    identities = [task['id'] for task in tasks]
    if (len(identities) != len(set(identities)) or
            any(not re.fullmatch(r'T\d{2}', identity) for identity in identities)):
        raise ValueError('Invalid or duplicate meeting task ID')
    by_id = {task['id']: task for task in tasks}
    for task in tasks:
        if task['status'] not in STATUSES:
            raise ValueError('Unknown meeting task status: ' + task['id'])
        target = task.get('merged_into')
        if task['status'] == 'merged':
            if (target not in by_id or target == task['id'] or
                    by_id[target]['status'] == 'merged'):
                raise ValueError('Invalid meeting merge target: ' + task['id'])
        elif target is not None:
            raise ValueError('Merge target on an active meeting task: ' + task['id'])
    for url in record['sources'].values():
        if urlsplit(url).scheme != 'https' or not urlsplit(url).netloc:
            raise ValueError('Expected an HTTPS meeting source')
    return record


def summary(record):
    counts = Counter(task['status'] for task in record['tasks'])
    return {'completed': counts['completed'],
            'follow_up': sum(counts[status] for status in FOLLOW_UP),
            'to_discuss': counts['to_discuss'], 'merged': counts['merged']}


def render_details(task, root):
    if not task.get('details'):
        return ''
    sections = []
    for section in task['details']:
        references = []
        for reference in section.get('links', []):
            url = reference['url']
            if urlsplit(url).scheme != 'https' or not urlsplit(url).netloc:
                raise ValueError('Expected an HTTPS meeting detail source')
            references.append('<li><a href="' + html.escape(url, quote=True) +
                              '" target="_blank" rel="noopener noreferrer">' +
                              html.escape(reference['title']) + ' ↗</a></li>')
        for reference in section.get('code', []):
            relative = Path(reference['file'])
            if relative.is_absolute() or '..' in relative.parts or relative.suffix != '.lean':
                raise ValueError('Invalid meeting code reference')
            declaration = reference['declaration']
            pattern = re.compile(r'^\s*(?:public\s+)?(?:noncomputable\s+)?'
                                 r'(?:def|abbrev|theorem|structure)\s+' +
                                 re.escape(declaration) + r'(?=\s|[(:]|$)')
            lines = (Path(root) / relative).read_text().splitlines()
            line = next((i for i, text in enumerate(lines, 1) if pattern.match(text)), None)
            if line is None:
                raise ValueError(f'Missing meeting code reference: {relative}: {declaration}')
            href = '../source/' + quote(relative.as_posix(), safe='/') + f'.html#L{line}'
            label = html.escape(relative.name + ' · ' + declaration)
            references.append(f'<li><a href="{href}" target="_blank" rel="noopener noreferrer">{label} ↗</a></li>')
        snippet = ('<pre><code>' + html.escape(section['snippet']) + '</code></pre>'
                   if section.get('snippet') else '')
        links = '<ul class="code-references">' + ''.join(references) + '</ul>' if references else ''
        sections.append('<section><h3>' + html.escape(section['title']) + '</h3><p>' +
                        html.escape(section['body']) + '</p>' + snippet + links + '</section>')
    label = task.get('details_label', '查看完成说明与代码依据')
    return ('<details class="task-details"><summary>' + html.escape(label) + '</summary>' +
            ''.join(sections) + '</details>')


def render_meeting(record, root=None):
    root = Path(root) if root is not None else Path(__file__).resolve().parent.parent
    escape = html.escape
    counts = summary(record)
    metrics = ''.join(
        f'<button type="button" class="metric metric-{key}" data-filter="{key}" '
        f'aria-pressed="false"><strong>{counts[key]}</strong><span>{label}</span></button>'
        for key, label in [('completed', '已完成'), ('follow_up', '仍需跟进'),
                           ('to_discuss', '待上会讨论'), ('merged', '合并记录')])
    rows = []
    for task in record['tasks']:
        identity, status = task['id'], task['status']
        note = f'<p class="task-note">{escape(task["note"])}</p>' if task.get('note') else ''
        details = render_details(task, root)
        target = task.get('merged_into')
        merge = (f'<a class="merge-link" href="#{target}" data-target="{target}">并入 {target} ↗</a>'
                 if target else '')
        search = ' '.join([identity, task['title'], STATUSES[status], task.get('owner', ''),
                           task.get('note', ''), target or ''])
        search += ' ' + ' '.join(section['title'] + ' ' + section['body'] + ' ' +
                                section.get('snippet', '')
                                for section in task.get('details', []))
        rows.append(
            f'<tr id="{identity}" tabindex="-1" data-status="{status}" '
            f'data-search="{escape(search, quote=True)}">'
            f'<th scope="row"><a href="#{identity}" data-target="{identity}">{identity}</a></th>'
            f'<td class="task-title"><strong>{escape(task["title"])}</strong>{note}{details}</td>'
            f'<td><span class="status status-{status}">{STATUSES[status]}</span>{merge}</td>'
            f'<td class="owner">{escape(task.get("owner", "—"))}</td></tr>')
    options = '<option value="all">全部状态</option><option value="follow_up">仍需跟进</option>'
    options += ''.join(f'<option value="{key}">{label}</option>' for key, label in STATUSES.items())
    links = ' '.join(
        f'<a href="{escape(record["sources"][key], quote=True)}" target="_blank" rel="noopener noreferrer">{label} ↗</a>'
        for key, label in [('card', '群内原卡片'), ('checklist', '原会议清单'),
                           ('recording', '会议录屏'), ('transcript', '逐字稿')])
    merges = '；'.join(f'{task["id"]} 并入 {task["merged_into"]}'
                      for task in record['tasks'] if task['status'] == 'merged')
    footer = escape(merges + '。合并记录不重复计作跟进事项。待上会讨论计入仍需跟进。')
    return f'''<!doctype html>
<html lang="zh-CN"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>Meeting · Kervaire 126</title><link rel="stylesheet" href="meeting.css">
<script src="../hgraph-custom-page.js" defer></script><script src="meeting.js" defer></script>
</head><body><main class="meeting-page">
<header><p class="eyebrow">MEETING / {escape(record['date'])}</p>
<h1>{escape(record['title'])}</h1>
<p class="intro">原始 {len(record['tasks'])} 项逐项保留，合并事项统一跟进。</p>
<div class="header-footer"><span>更新于 {escape(record['updated'])}</span><nav aria-label="会议依据">{links}</nav></div>
</header>
<section class="metrics" aria-label="会议进度">{metrics}</section>
<section aria-labelledby="tasks-heading">
<div class="section-heading"><h2 id="tasks-heading">全部事项</h2>
<button type="button" id="reset-filters">显示全部 {len(record['tasks'])} 项</button></div>
<form id="meeting-filters" role="search">
<label class="search">搜索事项<input id="task-search" type="search" placeholder="编号、事项或负责人" autocomplete="off"></label>
<label>状态<select id="task-status">{options}</select></label></form>
<p id="result-count" aria-live="polite">共 {len(record['tasks'])} 项</p>
<div class="task-table"><table><thead><tr><th scope="col">编号</th><th scope="col">事项</th>
<th scope="col">状态</th><th scope="col">负责人</th></tr></thead><tbody>{''.join(rows)}</tbody></table></div>
<p id="no-results" hidden>没有匹配的事项。<button type="button" data-reset>清除筛选</button></p>
</section><footer>{footer}</footer>
</main></body></html>'''


def stage_meeting(root, project):
    destination = Path(project) / 'site/meeting.html'
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text('<iframe class="meeting-frame" title="Meeting" '
                           'src="meeting/index.html" loading="lazy"></iframe>')


def export_meeting(root, out):
    root = Path(root)
    record = read_meeting(root)
    destination = Path(out) / 'meeting'
    destination.mkdir(parents=True, exist_ok=True)
    (destination / 'index.html').write_text(render_meeting(record, root))
    for name in ('meeting.css', 'meeting.js'):
        shutil.copyfile(root / 'site' / name, destination / name)
