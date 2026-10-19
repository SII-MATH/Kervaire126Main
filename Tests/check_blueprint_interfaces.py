"""Exercise Interfaces through the real native hgraph dashboard."""
import argparse
import json
from pathlib import Path
import sys

from playwright.sync_api import sync_playwright, expect

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--url', default='http://127.0.0.1:18727/')
    parser.add_argument('--chromium', default='/root/.cache/ms-playwright/chromium-1228/chrome-linux64/chrome')
    args = parser.parse_args()
    registry = json.loads((ROOT / 'interface/baselines/proof-obligations.json').read_text())
    proof_tools_obligations = [r for r in registry['obligations']
                              if r['module'].startswith('KIP126.ProofTools.')]
    assert {r['name'] for r in proof_tools_obligations} == {
        'KIP126.ProofTools.Paper.finiteCrossing_iff_syntheticCrossing'}
    assert registry['summary']['by_module']['ProofTools'] == len(proof_tools_obligations) == 1
    errors, failed, data_requests = [], [], []
    with sync_playwright() as p:
        browser = p.chromium.launch(headless=True, executable_path=args.chromium, args=['--no-sandbox'])
        page = browser.new_page(viewport={'width':1440, 'height':1000})
        page.on('request', lambda request: data_requests.append(request.url) if request.url.endswith('/interfaces/data.json') else None)
        page.on('pageerror', lambda e: errors.append(str(e)))
        page.on('response', lambda r: failed.append([r.status, r.url]) if r.status >= 400 and not r.url.endswith('/favicon.ico') else None)
        page.goto(args.url.rstrip('/') + '/#/Kervaire126', wait_until='networkidle')
        expand = page.get_by_role('button', name='Expand navigation panel')
        if expand.count():
            expand.click()
        navigation = page.locator('#blueprint-navigation')
        expect(navigation.get_by_role('button', name='Interface proposals')).to_have_count(0)
        navigation.get_by_role('button', name='Interfaces').click()
        workspace = page.frame_locator('iframe[title="Interfaces"]')
        frame = workspace.frame_locator('iframe[title="Baselines"]')
        expect(frame.locator('.module-card')).to_have_count(8)
        cards = frame.locator('.interface-card')
        expect(cards).to_have_count(40)
        expect(frame.locator('#interface-prev')).to_be_disabled()
        # Status totals partition only the named public API, never generated exports.
        payload = page.request.get(args.url.rstrip('/') + '/interfaces/data.json').json()
        published_tools = [r['obligation'] for r in payload['records']
                           if r['kind'] == 'obligation' and r['owner'] == 'ProofTools']
        assert published_tools == proof_tools_obligations
        public = [r for r in payload['records'] if r['kind'] == 'declaration']
        def state(row):
            source = row.get('source') or {}
            if row.get('obligation') or source.get('sorry') is True:
                return 'pending'
            if row['source_is_parent'] or not source.get('kind') or not isinstance(source.get('sorry'), bool):
                return 'unknown'
            if source['kind'] in ('theorem', 'lemma'):
                return 'local' if 'sorryAx' in row['axioms'] else 'proved'
            return 'defined'
        totals = {value: sum(state(row) == value for row in public)
                  for value in ('proved', 'local', 'pending', 'defined', 'unknown')}
        assert sum(totals.values()) == len(public)
        for value, count in totals.items():
            if not count and value == 'unknown':
                continue
            button = frame.locator(f'#interface-summary [data-status="{value}"]')
            expect(button.locator('strong')).to_have_text(f'{count:,}')
            button.click()
            expect(frame.locator('#interface-status')).to_have_value(value)
            expect(frame.locator('#interface-results')).to_contain_text(f'{count} matching entries')
        # The final geometric theorem is locally complete but still permits upstream gaps.
        geometry = frame.locator('.module-card').filter(has=frame.locator('[data-module="Geometry"]'))
        geometry.locator('[data-status="local"]').click()
        expect(cards).to_have_count(2)
        expect(cards.first).to_contain_text('Local proof complete')
        expect(cards.first).to_contain_text('Baseline permits dependency gaps')
        expect(geometry.locator('.status-bar')).to_have_attribute('aria-label',
            'Proofs complete: 0; Local proofs complete: 2; Direct obligations: 0; Definitions & objects: 0; Source unavailable: 0')
        proof_tools = frame.locator('.module-card').filter(has=frame.locator('[data-module="ProofTools"]'))
        proof_tools.locator('.obligation-link').click()
        expect(frame.locator('#interface-kind')).to_have_value('obligation')
        expect(cards).to_have_count(len(proof_tools_obligations))
        expect(cards.first).to_contain_text(proof_tools_obligations[0]['name'])
        frame.get_by_role('button', name='Reset', exact=True).click()
        expect(cards).to_have_count(40)
        first = cards.first.locator('h2').inner_text()
        frame.locator('#interface-next').click()
        expect(frame.locator('#interface-page-number')).to_contain_text('Page 2 of')
        assert cards.first.locator('h2').inner_text() != first
        frame.locator('#interface-search').fill('KIP126.Main.h6_sq_permanent')
        expect(cards).to_have_count(1)
        expect(cards).to_contain_text('NonzeroSurvival')
        cards.first.locator('summary').click()
        expect(cards).to_contain_text('sorryAx')
        expect(cards).to_contain_text('namespace KIP126.Main')
        source = cards.first.get_by_role('link', name='Read Lean source')
        response = page.request.get(source.get_attribute('href') if source.get_attribute('href').startswith('http') else
                                    args.url.rstrip('/') + '/source/KIP126/Main/H6SquarePermanent.lean.html')
        assert response.ok
        review = cards.first.get_by_role('link', name='Find interface proposals')
        expect(review).to_have_attribute('href', '../interfaces/index.html?section=proposals&module=Main&search=KIP126.Main.h6_sq_permanent')
        with page.expect_download() as downloaded:
            cards.first.get_by_role('link', name='Download baseline').click()
        assert Path(downloaded.value.path()).read_bytes() == (ROOT / 'interface/baselines/main-api.json').read_bytes()
        navigation.get_by_role('button', name='Overview').click()
        navigation.get_by_role('button', name='Interfaces').click()
        expect(frame.locator('#interface-search')).to_have_value('KIP126.Main.h6_sq_permanent')
        assert len(data_requests) == 1, data_requests
        frame.get_by_role('button', name='Reset', exact=True).click()
        frame.locator('#interface-kind').select_option('generated')
        frame.locator('#interface-module').select_option('Geometry')
        expect(cards).to_have_count(0)
        expect(frame.locator('#interface-empty')).to_be_visible()
        frame.get_by_role('button', name='Reset', exact=True).click()
        frame.locator('#interface-kind').select_option('obligation')
        frame.locator('#interface-module').select_option('ProofTools')
        expect(cards).to_have_count(len(proof_tools_obligations))
        expect(cards.first).to_contain_text(proof_tools_obligations[0]['name'])
        expect(cards.first).to_contain_text('Registered obligation')
        frame.locator('#interface-dependency').select_option('no-sorry')
        expect(cards).to_have_count(0)  # obligations do not carry a compiled axiom list
        frame.get_by_role('button', name='Reset', exact=True).click()
        frame.locator('#interface-module').select_option('Geometry')
        frame.locator('#interface-dependency').select_option('sorry')
        expect(cards).to_have_count(2)
        frame.locator('#interface-dependency').select_option('no-sorry')
        expect(cards).to_have_count(0)
        frame.get_by_role('button', name='Reset', exact=True).click()
        frame.get_by_role('heading', name='Interfaces', exact=True).scroll_into_view_if_needed()
        page.screenshot(path=str(ROOT / '.lake/blueprint/interfaces-desktop.png'), full_page=True)
        page.set_viewport_size({'width':390,'height':844})
        frame.locator('#interface-search').fill('KIP126.Main.h6_sq_permanent')
        expect(cards).to_have_count(1)
        iframe = page.frames[-1]
        assert iframe.evaluate('document.documentElement.scrollWidth <= innerWidth + 1')
        frame.locator('#interface-summary [data-status="pending"]').click()
        expect(frame.locator('#interface-status')).to_have_value('pending')
        assert iframe.evaluate('document.documentElement.scrollWidth <= innerWidth + 1')
        frame.get_by_role('button', name='Reset', exact=True).click()
        frame.locator('#interface-search').fill('KIP126.Main.h6_sq_permanent')
        page.screenshot(path=str(ROOT / '.lake/blueprint/interfaces-mobile.png'), full_page=True)
        workspace.get_by_role('tab', name='Proposals', exact=True).click()
        proposals = workspace.frame_locator('iframe[title="Proposals"]')
        expect(proposals.get_by_role('heading', name='Interface proposals')).to_be_visible()
        workspace.get_by_role('tab', name='Baselines', exact=True).click()
        expect(frame.locator('#interface-search')).to_have_value('KIP126.Main.h6_sq_permanent')
        expect(frame.locator('.module-card')).to_have_count(8)
        assert len(data_requests) == 1, data_requests
        assert not errors, errors
        assert not failed, failed
        browser.close()
    print('Interfaces: native tab, filters, pagination, source context, downloads and mobile checks passed.')


if __name__ == '__main__':
    main()
