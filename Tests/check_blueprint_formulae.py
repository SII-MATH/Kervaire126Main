#!/usr/bin/env python3
"""Render every published Blueprint formula with the actual native KaTeX bundle.

Unlike checking `.katex-error`, strict rendering also catches unknown commands
that the native non-throwing renderer displays as red text without an error node.
"""
import argparse
import json
import os
from pathlib import Path
import re
from urllib.parse import urljoin
from playwright.sync_api import sync_playwright
from hgraph.graph import node_id
from hgraph.sync import parse_blueprint, read_blueprint

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--url', default=os.environ.get('VSCODE_PROXY_URI', '').replace('{{port}}', '18726'))
    parser.add_argument('--chromium', default='/root/.cache/ms-playwright/chromium-1228/chrome-linux64/chrome')
    args = parser.parse_args()
    if not args.url:
        parser.error('Provide --url or VSCODE_PROXY_URI')
    base = args.url.rstrip('/') + '/'
    data = json.loads((ROOT / '_site/Kervaire126/data.json').read_text())
    authored, _ = parse_blueprint(read_blueprint(ROOT / 'blueprint/content.tex'))
    expected_papers = sum(row['label'].startswith('paper:') for row in authored)
    loader = next((ROOT / '_site/assets').glob('katexLoader-*.js')).name
    errors, runtime, http = [], [], []
    checked = 0
    statements_checked = 0
    with sync_playwright() as p:
        browser = p.chromium.launch(headless=True, executable_path=args.chromium, args=['--no-sandbox'])
        page = browser.new_page(viewport={'width':1440,'height':1000})
        page.set_default_timeout(60000)
        page.on('pageerror', lambda e: runtime.append(str(e)))
        page.on('response', lambda r: http.append((r.status,r.url)) if r.status>=400 and not r.url.endswith('/favicon.ico') else None)
        for chapter in data['chapters']:
            papers = [b for b in chapter['blocks'] if b.get('t') == 'stmt' and b.get('label')]
            if not papers:
                continue
            page.goto(base + '#/Kervaire126#' + papers[-1]['label'], wait_until='domcontentloaded')
            page.reload(wait_until='domcontentloaded')
            page.locator('#stmt-' + node_id('bp', papers[-1]['label']) + ' .sbody').wait_for()
            for row in papers:
                selector = '#stmt-' + node_id('bp', row['label'])
                body = page.locator(selector + ' .sbody')
                body.wait_for()
                # Wait for asynchronous native KaTeX to finish for math-bearing bodies.
                if re.search(r'\$|\\\[|\\\(', row['body']):
                    page.locator(selector + ' .katex, ' + selector + ' .katex-error').first.wait_for(state='attached')
                report = body.evaluate(r'''async (el, config) => {
                    const render = (await import(config.loader)).default;
                    const formulas = [...el.querySelectorAll('.katex-mathml annotation[encoding="application/x-tex"]')]
                        .map(n => n.textContent);
                    const failures = [...el.querySelectorAll('.katex-error')].map(n => n.getAttribute('title') || n.textContent);
                    for (const formula of formulas) {
                        const probe = document.createElement('div');
                        probe.textContent = '\\[' + formula + '\\]';
                        render(probe, {
                            delimiters: [{left:'\\[', right:'\\]', display:true}],
                            macros: {...config.macros}, throwOnError:true,
                            errorCallback: (message, error) => failures.push(error?.message || message),
                        });
                    }
                    // Unknown controls can still appear in existing red output,
                    // so check that too rather than relying only on error nodes.
                    for (const node of el.querySelectorAll('.katex .mord')) {
                        if (/^\\[A-Za-z]+/.test(node.textContent || '')
                            && getComputedStyle(node).color === 'rgb(204, 0, 0)')
                            failures.push('Visible unknown command: ' + node.textContent);
                    }
                    return {formulas:formulas.length, failures};
                }''', {'loader':urljoin(base, 'assets/' + loader), 'macros':data['macros']})
                statements_checked += 1
                checked += report['formulas']
                errors.extend({'statement':row['label'], 'error':error} for error in report['failures'])
                if row['label']=='paper:2.1':
                    page.locator(selector).screenshot(path=str(ROOT / '.lake/blueprint/formula-definition-2.1.png'))
        browser.close()
    result = {'blueprint_statements':statements_checked,
              'paper_statements':sum(r['label'].startswith('paper:') for r in data['entries']), 'formulae_checked':checked,
              'strict_render_errors':errors, 'runtime_errors':runtime,'http_failures':http}
    (ROOT / '.lake/blueprint/formula-browser-validation.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
    print(json.dumps(result,ensure_ascii=False))
    if statements_checked != len(data['entries']) or result['paper_statements'] != expected_papers or checked < 100 or errors or runtime or http:
        raise SystemExit(1)


if __name__=='__main__':
    main()
