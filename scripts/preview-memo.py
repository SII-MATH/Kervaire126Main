#!/usr/bin/env python3
"""Refresh only Memo in an isolated local copy of an existing Blueprint export.

All mathematical payloads and proof states stay at the verified base snapshot.
This preview does not claim a new compilation or publish to the remote site.
"""
import argparse
import gzip
import hashlib
import json
from pathlib import Path
import re
import shutil
import tempfile

import blueprint_memo

ROOT = Path(__file__).resolve().parents[1]


def prepare_preview(root, base, out):
    root, base, out = Path(root), Path(base).resolve(), Path(out).resolve()
    if base == out or base in out.parents:
        raise ValueError('Memo preview must be separate from the base export')
    validation_bytes = (base / 'validation.json').read_bytes()
    validation = json.loads(validation_bytes)
    if not validation.get('checks') or not all(validation['checks'].values()):
        raise ValueError('Memo preview needs a verified base export')
    if out.exists() and not (out / 'memo-preview.json').exists():
        raise ValueError('Refusing to replace a directory not created by this preview command')
    out.parent.mkdir(parents=True, exist_ok=True)
    temporary = Path(tempfile.mkdtemp(prefix='.memo-preview-', dir=out.parent))
    try:
        shutil.copytree(base, temporary, dirs_exist_ok=True)
        project = json.loads((temporary / 'Kervaire126/data.json').read_text())
        content = blueprint_memo.render_memo(root, project)
        changed = []
        for name in ('project.json', 'data.json'):
            path = temporary / 'Kervaire126' / name
            payload = json.loads(path.read_text())
            tabs = [tab for tab in payload['customTabs'] if tab['id'] == 'memo']
            if len(tabs) != 1:
                raise ValueError('Expected exactly one native Memo tab')
            tabs[0]['html'] = content
            path.write_text(json.dumps(payload, ensure_ascii=False, separators=(',', ':')))
            changed.append(path)
        index = temporary / 'index.html'
        text, count = re.subn(r'(<style data-hgraph-stylesheet>)[\s\S]*?(</style>)',
                             lambda m: m[1] + '\n' + (root / 'site/memo.css').read_text() + '\n' + m[2], index.read_text())
        if count != 1:
            raise ValueError('Expected native custom stylesheet slot')
        index.write_text(text)
        changed.append(index)
        report = {'scope': 'Local Memo presentation only; mathematical data, bindings and proof states are copied unchanged from the base export.',
                  'base_export': str(base), 'base_validation_sha256': hashlib.sha256(validation_bytes).hexdigest(),
                  'memo_inputs': {name: hashlib.sha256((root / name).read_bytes()).hexdigest() for name in
                                 ('corrections.yaml', 'AimPaper/main.tex', 'scripts/blueprint_memo.py', 'site/memo.html', 'site/memo.css')}}
        validation['local_memo_preview'] = report
        validation['memo'] = blueprint_memo.export_memo(root, temporary)
        (temporary / 'validation.json').write_text(json.dumps(validation, ensure_ascii=False, indent=2))
        changed.append(temporary / 'validation.json')
        (temporary / 'memo-preview.json').write_text(json.dumps(report, ensure_ascii=False, indent=2))
        for path in changed:
            path.with_name(path.name + '.gz').write_bytes(gzip.compress(path.read_bytes(), mtime=0))
        if out.exists():
            shutil.rmtree(out)
        temporary.rename(out)
        return report
    finally:
        if temporary.exists():
            shutil.rmtree(temporary)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=ROOT / '_site')
    parser.add_argument('--out', type=Path, default=ROOT / '.lake/blueprint/memo-statements-preview')
    args = parser.parse_args()
    prepare_preview(ROOT, args.base, args.out)
    print('Memo preview prepared at', args.out)
