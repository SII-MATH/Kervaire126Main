#!/usr/bin/env python3
"""Export with native hgraph sync and site generation.

The only repository graph checks are public/module binding ownership and chapter
order. Lean compilation and its trust audits are separate from website export.
"""
from __future__ import annotations

import argparse
import gzip
import html
import json
from pathlib import Path
import shutil
import sys
import tempfile

sys.path.insert(0, str(Path(__file__).resolve().parent))
import blueprint_boundaries
import blueprint_memo
import blueprint_proposals
import blueprint_interfaces
from blueprint_annotations import sync_authoring_notes
from blueprint_paper import export_paper, load_paper, prepare_web_blueprint
from hgraph.graph import Graph
from hgraph.site import write_from_manifest
from hgraph.sync import sync

ROOT = Path(__file__).resolve().parent.parent
STATE = ROOT / '.lake/blueprint'


def stage_workspace():
    workspace = STATE / 'workspace'
    project = workspace / 'Kervaire126'
    project.mkdir(parents=True, exist_ok=True)
    links = {workspace / 'config.yaml': ROOT / 'site/config.yaml',
             workspace / 'site': ROOT / 'site',
             project / 'blueprint': prepare_web_blueprint(ROOT, STATE / 'web-blueprint')}
    links.update({project / name: ROOT / name for name in ('KIP126', 'hgraph', 'corrections.yaml')})
    for target, source in links.items():
        if target.is_symlink() and target.resolve() != source.resolve():
            target.unlink()
        if not target.exists():
            target.symlink_to(source, target_is_directory=source.is_dir())
    blueprint_memo.stage_memo(ROOT, project)
    blueprint_interfaces.stage_interfaces(ROOT, project)
    return workspace


def sync_project(project):
    """Pass original Lean and authored TeX annotations to the native synchronizer."""
    graph = Graph.open(ROOT)
    report = sync(graph, blueprint=str(project / 'blueprint/content.tex'),
                  lean_paths=[ROOT / 'KIP126'], root=ROOT)
    sync_authoring_notes(graph, ROOT)
    return report


def export_sources(out):
    for path in sorted((ROOT / 'KIP126').rglob('*.lean')):
        relative = path.relative_to(ROOT)
        destination = out / 'source' / (str(relative) + '.html')
        destination.parent.mkdir(parents=True, exist_ok=True)
        title = html.escape(str(relative))
        lines = '\n'.join(f'<span id="L{i}"><a href="#L{i}">{i:4}</a> {html.escape(line)}</span>'
                          for i, line in enumerate(path.read_text().splitlines(), 1))
        destination.write_text('<!doctype html><meta charset="utf-8"><title>' + title
            + '</title><style>body{margin:24px;background:#fbfaf7;color:#222}'
              'pre{line-height:1.6}pre>span{display:block}pre>span:target{background:#fff0a8}'
              'a{color:#888;text-decoration:none}</style><h1>' + title + '</h1><pre>' + lines + '</pre>')


def export_site(workspace, out, report, boundary_checks):
    out = out.resolve()
    out.parent.mkdir(parents=True, exist_ok=True)
    staging = Path(tempfile.mkdtemp(prefix='.' + out.name + '-', dir=out.parent))
    try:
        write_from_manifest(workspace / 'config.yaml', out_path=staging / 'index.html')
        export_sources(staging)
        export_paper(ROOT, staging, load_paper(ROOT))
        blueprint_memo.export_memo(ROOT, staging)
        blueprint_proposals.export_proposals(ROOT, staging)
        blueprint_interfaces.export_interfaces(ROOT, staging)
        (staging / 'native-sync.json').write_text(json.dumps(report, ensure_ascii=False, indent=2) + '\n')
        (staging / 'publication.json').write_text(json.dumps({
            'mode': 'native-hgraph', 'boundaries': boundary_checks,
            'proof_states': 'Native hgraph source-local states and authored uses only; '
                            'website export does not verify Lean compilation or compiled dependency closure.'},
            ensure_ascii=False, indent=2) + '\n')
        for path in sorted(staging.rglob('*')):
            if path.is_file() and path.suffix in ('.json', '.html', '.js', '.css', '.svg') and path.stat().st_size >= 1024:
                path.with_name(path.name + '.gz').write_bytes(gzip.compress(path.read_bytes(), mtime=0))
        previous = STATE / 'previous-site'
        if out.exists():
            if previous.exists():
                shutil.rmtree(previous)
            out.rename(previous)
        try:
            staging.rename(out)
        except Exception:
            if previous.exists() and not out.exists():
                previous.rename(out)
            raise
    finally:
        if staging.exists():
            shutil.rmtree(staging)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', type=Path, default=ROOT / '_site')
    args = parser.parse_args()
    STATE.mkdir(parents=True, exist_ok=True)
    checks = blueprint_boundaries.check(ROOT)
    workspace = stage_workspace()
    report = sync_project(workspace / 'Kervaire126')
    print(f'Native hgraph: {report["blueprint"]} mathematical entries, '
          f'{report["lean"]} Lean declarations, {len(report["warnings"])} warning(s).', flush=True)
    export_site(workspace, args.out, report, checks)
    print('Built', args.out, flush=True)


if __name__ == '__main__':
    main()
