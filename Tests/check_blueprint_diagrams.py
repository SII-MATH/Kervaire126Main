#!/usr/bin/env python3
"""Check original diagram visibility and responsive layout in the native reader."""
import argparse
import json
from pathlib import Path
from urllib.parse import urlsplit
from playwright.sync_api import sync_playwright
from hgraph.graph import node_id
from hgraph.sync import read_blueprint, parse_blueprint
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
from blueprint_paper import paper_figures


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--url', default='http://127.0.0.1:18726/')
    parser.add_argument('--site', type=Path, default=ROOT / '_site')
    parser.add_argument('--chromium', default='/root/.cache/ms-playwright/chromium-1228/chrome-linux64/chrome')
    args = parser.parse_args()
    diagrams = sorted((args.site / 'paper/diagrams').glob('*.svg'))
    assert len(diagrams) == 10, 'Expected seven commutative diagrams and three standalone figures'
    rows, _ = parse_blueprint(read_blueprint(ROOT / 'blueprint/content.tex'))
    figure_owners = {f['stem']: next(row['label'] for row in rows
                                   if r'\ref{' + f['label'] + '}' in row['body'])
                     for f in paper_figures(ROOT)}
    failures, checked = [], []
    with sync_playwright() as p:
        browser = p.chromium.launch(headless=True, executable_path=args.chromium, args=['--no-sandbox'])
        for width in (1440, 390):
            for svg in diagrams:
                page = browser.new_page(viewport={'width': width, 'height': 1000})
                page.set_default_timeout(60000)
                page.on('pageerror', lambda error: failures.append(str(error)))
                label = figure_owners.get(svg.stem, 'paper:' + svg.stem.rsplit('-', 1)[0])
                page.goto(args.url.rstrip('/') + '/#/Kervaire126#' + label, wait_until='domcontentloaded')
                statement = page.locator('#stmt-' + node_id('bp', label))
                selector = '#stmt-' + node_id('bp', label) + ' .sbody a.tex-link[href="paper/diagrams/' + svg.name + '"]'
                link = page.locator(selector)
                link.wait_for(state='visible')
                link.evaluate("el => el.scrollIntoView({block:'center'})")
                report = page.wait_for_function('''selector => {
                    const el = document.querySelector(selector);
                    const body = el?.closest('.sbody');
                    if (!el?.isConnected || !body) return false;
                    const style = getComputedStyle(el);
                    const box = el.getBoundingClientRect();
                    const column = body.getBoundingClientRect();
                    if (!box.width || !box.height) return false;
                    return {width:box.width, height:box.height, column:column.width,
                        background:style.backgroundImage, display:style.display,
                        href:el.href};
                }''', arg=selector).json_value()
                # Native reading-position updates may replace a statement while
                # the image loads. Keep the synchronous DOM measurement separate.
                report['loaded'] = page.evaluate('''async href => {
                    const image = new Image();
                    image.src = href;
                    await image.decode();
                    return image.naturalWidth > 0;
                }''', report['href'])
                assert report['loaded'] and svg.name in report['background'], report
                assert report['display'] == 'block' and report['height'] >= 60, report
                assert report['width'] <= report['column'] + 1, report
                if svg.stem.startswith('figure-'):
                    assert report['height'] < 500, 'Standalone figure retained a paper footer or blank page'
                assert urlsplit(page.url).path == urlsplit(args.url).path, page.url
                assert '#/Kervaire126' in page.url and len(page.context.pages) == 1, page.url
                assert 'see the original commutative diagram' not in statement.inner_text()
                checked.append({'viewport': width, 'diagram': svg.name, **report})
                if label == 'paper:2.16':
                    statement.screenshot(path=str(ROOT / '.lake/blueprint' / f'inline-diagram-{width}.png'))
                page.close()
        browser.close()
    assert not failures, failures
    result = {'checked': checked, 'runtime_errors': failures}
    (ROOT / '.lake/blueprint/diagram-browser-validation.json').write_text(json.dumps(result, indent=2))
    print(f'Passed: {len(checked)} diagram checks across desktop and mobile widths.')


if __name__ == '__main__':
    main()
