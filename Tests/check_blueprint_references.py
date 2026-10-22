#!/usr/bin/env python3
"""Exercise native equation and notation navigation in the actual reader."""
import argparse
import json
from pathlib import Path

from hgraph.graph import node_id
from playwright.sync_api import sync_playwright

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--url', default='http://127.0.0.1:18726/')
    parser.add_argument('--chromium', default='/root/.cache/ms-playwright/chromium-1228/chrome-linux64/chrome')
    args = parser.parse_args()
    data = json.loads((ROOT / '_site/Kervaire126/data.json').read_text())
    cases = {
        'eq:eae450fe': 'paper:5.4', 'eq:334248d2': 'paper:5.4',
        'eq:b98be76a': 'paper:5.9', 'eq:a020bad3': 'paper:5.4',
        'eq:9d45feac': 'paper:2.12', 'eq:36e72616': 'paper:2.12',
        "eq:dr'": 'paper:6.20', 'not:deltaandrho': 'paper:4.2',
    }
    checked, errors = [], []
    with sync_playwright() as p:
        browser = p.chromium.launch(headless=True, executable_path=args.chromium, args=['--no-sandbox'])
        page = browser.new_page(viewport={'width': 1440, 'height': 1000})
        page.set_default_timeout(20000)
        page.on('pageerror', lambda error: errors.append(str(error)))
        for label, source in cases.items():
            page.goto(args.url.rstrip('/') + '/#/Kervaire126#' + source)
            statement = page.locator('#stmt-' + node_id('bp', source))
            statement.wait_for(state='visible')
            ref = data['refs'][label]
            attribute = 'data-id' if ref['id'] else 'data-loc'
            value = ref['id'] or f"{ref['ch']}:{ref['anchor']}"
            if label in ('eq:9d45feac', 'eq:36e72616'):
                proof = statement.locator('xpath=following-sibling::details[1]')
                if proof.get_attribute('open') is None:
                    proof.locator('summary').click()
                container = proof
            else:
                container = statement
            link = container.locator(f'a.ref[{attribute}="{value}"]').first
            link.wait_for(state='visible')
            assert link.get_attribute('target') != '_blank'
            assert link.get_attribute('href') is None
            link.click()
            target = page.locator('[id="' + ref['anchor'] + '"]').first
            # Native equation anchors are empty spans before the display.
            target.wait_for(state='attached')
            page.wait_for_function('''anchor => {
                const box = document.getElementById(anchor)?.getBoundingClientRect();
                return box && box.top >= 0 && box.top < innerHeight;
            }''', arg=ref['anchor'])
            assert len(page.context.pages) == 1
            checked.append(label)
        assert not errors, errors
        page.goto(args.url.rstrip('/') + '/#/Kervaire126#paper:5.9')
        page.mouse.move(0, 0)
        statement = page.locator('#stmt-' + node_id('bp', 'paper:5.9'))
        statement.locator('a[href*="figure-66241bf6"]').wait_for(state='visible')
        statement.screenshot(path=str(ROOT / '.lake/blueprint/crossing-inline-figure.png'))
        browser.close()
    (ROOT / '.lake/blueprint/reference-browser-validation.json').write_text(
        json.dumps({'checked': checked, 'runtime_errors': errors}, indent=2) + '\n')
    print(f'Passed: {len(checked)} native references; no new tabs or source fallback.')


if __name__ == '__main__':
    main()
