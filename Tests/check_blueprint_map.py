"""Exercise the published map through the actual pinned hgraph frontend."""
import argparse
from collections import Counter
import json
from pathlib import Path

from playwright.sync_api import sync_playwright, expect

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--url', default='http://127.0.0.1:18726/')
    parser.add_argument('--chromium', default='/root/.cache/ms-playwright/chromium-1228/chrome-linux64/chrome')
    args = parser.parse_args()
    base = args.url.rstrip('/') + '/'
    project = json.loads((ROOT / '_site/Kervaire126/data.json').read_text())
    data = {'nodes': project['entries'], 'chapters': project['chapters'],
            'edges': [edge for row in project['entries'] for edge in row['deps'] if edge['type'] == 'uses'],
            'stats': {'nodes': len(project['entries']),
                      'statuses': dict(Counter(row['lean_status'] for row in project['entries']))}}
    by_label = {node['label']: node for node in data['nodes']}
    errors, http, checks = [], [], []
    with sync_playwright() as p:
        browser = p.chromium.launch(headless=True, executable_path=args.chromium, args=['--no-sandbox'])
        page = browser.new_page(viewport={'width': 1440, 'height': 1000})
        page.set_default_timeout(30000)
        page.on('pageerror', lambda e: errors.append(str(e)))
        page.on('response', lambda r: http.append([r.status, r.url]) if r.status >= 400 else None)
        page.goto(base + '#/Kervaire126', wait_until='networkidle')

        def open_map():
            nav = page.locator('#blueprint-navigation')
            expand = page.get_by_role('button', name='Expand navigation panel')
            if expand.count():
                expand.click()
            nav.get_by_role('button', name='Blueprint map').click()
            frame = page.frame_locator('iframe[title="Blueprint map"]')
            frame.locator('.node-card').last.wait_for()
            assert frame.locator('.node-card').count() == data['stats']['nodes']
            return frame

        nav_text = page.locator('#blueprint-navigation').inner_text()
        assert 'Verification' not in nav_text and 'Implementation index' not in nav_text
        frame = open_map()
        checks.append('navigation and complete node population')
        zoom = frame.locator('#map-zoom-level').inner_text()
        frame.locator('#map-zoom-in').click()
        assert frame.locator('#map-zoom-level').inner_text() != zoom
        frame.locator('#map-fit').click()
        checks.append('zoom and fit')

        focus = by_label['paper:7.8']
        card = frame.locator('[data-node="' + focus['id'] + '"]')
        card.scroll_into_view_if_needed()
        card.click()
        assert frame.locator('.node-card.selected').count() == 1
        frame.locator('#map-depth').select_option('1')
        first_layer = frame.locator('.node-card.layer-active').count()
        assert first_layer > 0
        frame.locator('#map-depth').select_option('all')
        assert frame.locator('.node-card.layer-active').count() >= first_layer
        card.click()
        checks.append('dependency focus and depth')

        frame.locator('#map-search').fill('sem:Main:last-differential')
        assert frame.locator('.node-card:not(.dim)').count() == 1
        frame.locator('#map-search').fill('')
        frame.locator('#map-status').select_option('empty')
        assert frame.locator('.node-card:not(.dim)').count() == data['stats']['statuses'].get('empty', 0)
        frame.locator('#map-status').select_option('all')
        frame.locator('#map-chapter').select_option(data['chapters'][-1]['title'])
        expected = sum(block.get('t') == 'stmt' for block in data['chapters'][-1]['blocks'])
        expect(frame.locator('.node-card:not(.dim)')).to_have_count(expected)
        frame.locator('#map-chapter').select_option('all')
        checks.append('search, status and chapter filters')

        frame.locator('#map-viewport').evaluate('(e)=>{e.scrollTop=0;}')
        page.mouse.move(185, 650)
        page.mouse.down()
        page.mouse.move(185, 350, steps=5)
        page.mouse.up()
        assert frame.locator('#map-viewport').evaluate('(e)=>e.scrollTop') > 0
        checks.append('canvas drag')

        node = by_label['sem:Main:last-differential']
        card = frame.locator('[data-node="' + node['id'] + '"]')
        card.scroll_into_view_if_needed()
        card.locator('.node-preview-toggle').click()
        frame.locator('#detail-body .katex').first.wait_for()
        assert frame.locator('#detail-body .katex-error').count() == 0
        page.screenshot(path=str(ROOT / '.lake/blueprint/map-published-desktop.png'))
        frame.locator('#detail-body .detail-source-ref a').click()
        page.wait_for_function("decodeURIComponent(location.hash).endsWith('#sem:Main:last-differential')")
        page.locator('#stmt-' + node['id'] + ' .sbody').wait_for()
        page.locator('iframe[title="Blueprint map"]').wait_for(state='detached')
        checks.append('math preview and parent blueprint navigation')

        # Navigation scrolls smoothly; measure the reading position after that
        # animation settles, rather than halfway through the requested jump.
        page.evaluate('''() => new Promise((resolve, reject) => {
            let last=scrollY, stable=0, frames=0;
            function tick() {
                stable=Math.abs(scrollY-last)<0.5 ? stable+1 : 0;
                last=scrollY;
                if (stable>=6) return resolve();
                if (++frames>180) return reject(new Error('Reader scroll did not settle'));
                requestAnimationFrame(tick);
            }
            requestAnimationFrame(tick);
        })''')
        before = page.evaluate('''() => {
            window.__mapCloseSentinel = 'preserve-document';
            window.__mapPreviousStatement = document.querySelector('.stmt.sel');
            return {hash:location.hash,scrollY:scrollY,query:document.querySelector('.navq').value};
        }''')
        frame = open_map()
        frame.locator('#map-close').click()
        page.locator('iframe[title="Blueprint map"]').wait_for(state='detached')
        after = page.evaluate('''() => ({hash:location.hash,scrollY:scrollY,
            query:document.querySelector('.navq').value,
            sentinel:window.__mapCloseSentinel,
            sameStatement:window.__mapPreviousStatement===document.querySelector('.stmt.sel')})''')
        assert after['sentinel'] == 'preserve-document' and after['sameStatement']
        assert after['hash'] == before['hash'] and after['query'] == before['query']
        assert abs(after['scrollY'] - before['scrollY']) <= 1, (before, after)
        checks.append('native close preserves document, selection, query and scroll without reload')
        frame = open_map()
        page.set_viewport_size({'width': 390, 'height': 844})
        page.screenshot(path=str(ROOT / '.lake/blueprint/map-published-mobile.png'))
        checks.append('mobile map viewport')
        browser.close()
    report = {'nodes': len(data['nodes']), 'edges': len(data['edges']),
              'checks': checks, 'runtime_errors': errors, 'http_errors': http}
    (ROOT / '.lake/blueprint/map-browser-validation.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report))
    if errors or http:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
