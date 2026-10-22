"""Exercise published research through the native hgraph dashboard."""

import argparse
from pathlib import Path
import sys
from urllib.parse import urlsplit

from playwright.sync_api import expect, sync_playwright

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
from blueprint_research import read_reports


def watch_page(page, errors, failed):
    page.on('pageerror', lambda error: errors.append(str(error)))
    page.on('response', lambda response: failed.append(
        [response.status, response.url]
    ) if response.status >= 400 and not response.url.endswith('/favicon.ico') else None)


def visible_ids(frame):
    return frame.locator('.research-card:not([hidden])').evaluate_all(
        '(cards) => cards.map(card => card.id).sort()'
    )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--url', default='http://127.0.0.1:18726/')
    parser.add_argument('--chromium', default='/root/.cache/ms-playwright/chromium-1228/chrome-linux64/chrome')
    args = parser.parse_args()
    reports = read_reports(ROOT)
    expected_ids = sorted(report['meta']['result_id'] for report in reports)
    reviewed_ids = ['20261022-theta5-products', '20261022-theta6-moore']
    assert set(reviewed_ids) <= set(expected_ids), 'Missing reviewed research reports'
    reviewed = [next(report for report in reports if report['meta']['result_id'] == identity)
                for identity in reviewed_ids]
    selected = reviewed[0]
    selected_id = selected['meta']['result_id']
    errors, failed = [], []
    snapshots = ROOT / '.lake/blueprint'
    snapshots.mkdir(parents=True, exist_ok=True)

    with sync_playwright() as playwright:
        browser = playwright.chromium.launch(
            headless=True, executable_path=args.chromium, args=['--no-sandbox']
        )
        context = browser.new_context(
            viewport={'width': 1440, 'height': 1000}, accept_downloads=True
        )
        page = context.new_page()
        watch_page(page, errors, failed)
        page.goto(args.url.rstrip('/') + '/#/Kervaire126', wait_until='networkidle')
        expand = page.get_by_role('button', name='Expand navigation panel')
        if expand.count():
            expand.click()
        navigation = page.locator('#blueprint-navigation')
        navigation.get_by_role('button', name='Research').click()
        frame = page.frame_locator('iframe[title="Research"]')
        cards = frame.locator('.research-card')
        visible = frame.locator('.research-card:not([hidden])')
        expect(cards).to_have_count(len(reports))
        expect(frame.locator('#research-results')).to_contain_text(f'{len(reports)} / {len(reports)}')
        assert visible_ids(frame) == expected_ids

        frame.locator('#research-search').fill(selected_id)
        expect(visible).to_have_count(1)
        assert visible_ids(frame) == [selected_id]
        frame.locator('#research-search').fill('__no_matching_research__')
        expect(visible).to_have_count(0)
        expect(frame.locator('#research-empty')).to_be_visible()
        reset = frame.get_by_role('button', name='\u91cd\u7f6e', exact=True)
        reset.click()
        expect(visible).to_have_count(len(reports))
        expect(frame.locator('#research-empty')).not_to_be_visible()

        for field in ('topic', 'status'):
            control = frame.locator(f'#research-{field}')
            values = sorted({report['meta'][field] for report in reports})
            for value in values:
                control.select_option(value)
                expected = sorted(report['meta']['result_id'] for report in reports
                                  if report['meta'][field] == value)
                expect(visible).to_have_count(len(expected))
                assert visible_ids(frame) == expected
                reset.click()

        # Render both full reports, including the long displayed equations.
        for report in reviewed:
            card = frame.locator(f'[id="{report["meta"]["result_id"]}"]')
            details = card.locator('details.proposal-report')
            details.locator('summary').click()
            expect(details).to_have_attribute('open', '')
            body = card.locator('.proposal-body')
            expect(body).to_be_visible()
            expect(body.locator('.katex').first).to_be_visible()
            expect(body.locator('.katex-error')).to_have_count(0)
            assert not body.evaluate(r'''element => [...element.querySelectorAll('.katex .mord')]
                .some(node => /^\\[A-Za-z]+/.test(node.textContent || '')
                    && getComputedStyle(node).color === 'rgb(204, 0, 0)')''')
            with page.expect_download() as downloaded:
                card.locator(f'a[download][href="reports/{report["path"]}"]').click()
            download = downloaded.value
            assert download.failure() is None
            source = ROOT / report['path']
            assert Path(download.path()).read_bytes() == source.read_bytes()

        card = frame.locator(f'[id="{selected_id}"]')
        evidence = card.locator('a[download][href*="/evidence/"]').first
        expect(evidence).to_be_visible()
        with page.expect_download() as downloaded:
            evidence.click()
        assert downloaded.value.failure() is None
        assert Path(downloaded.value.path()).stat().st_size > 0

        # Canonical report references open the destination in the same Research view.
        for report in reviewed:
            source_id = report['meta']['result_id']
            target_id = next(identity for identity in reviewed_ids if identity != source_id)
            source_card = frame.locator(f'[id="{source_id}"]')
            target_card = frame.locator(f'[id="{target_id}"]')
            target_card.locator('details.proposal-report').evaluate(
                'element => { element.open = false; }'
            )
            source_card.locator(f'.proposal-body a[href="#{target_id}"]').first.click()
            expect(target_card.locator('details.proposal-report')).to_have_attribute('open', '')
            assert target_card.evaluate('element => element.ownerDocument.defaultView.location.hash') == '#' + target_id

        frame.locator('.research-header').scroll_into_view_if_needed()
        page.screenshot(path=str(snapshots / 'research-desktop.png'), full_page=True)
        card.locator('.proposal-body .katex-display').first.scroll_into_view_if_needed()
        page.screenshot(path=str(snapshots / 'research-formula-desktop.png'), full_page=True)

        # Research keeps its filters and expanded reports when another native view is opened.
        frame.locator('#research-search').fill(selected_id)
        frame.locator('#research-topic').select_option(selected['meta']['topic'])
        frame.locator('#research-status').select_option(selected['meta']['status'])
        permalink = card.locator('a.research-permalink')
        permalink.click()
        permalink_url = permalink.evaluate('link => link.href')
        assert urlsplit(permalink_url).fragment == selected_id
        assert card.evaluate('element => element.ownerDocument.defaultView.location.hash') == '#' + selected_id
        navigation.get_by_role('button', name='Interfaces').click()
        navigation.get_by_role('button', name='Research').click()
        expect(frame.locator('#research-search')).to_have_value(selected_id)
        expect(frame.locator('#research-topic')).to_have_value(selected['meta']['topic'])
        expect(frame.locator('#research-status')).to_have_value(selected['meta']['status'])
        expect(card.locator('details.proposal-report')).to_have_attribute('open', '')
        assert visible_ids(frame) == [selected_id]

        direct = context.new_page()
        watch_page(direct, errors, failed)
        direct.goto(permalink_url, wait_until='networkidle')
        direct_card = direct.locator(f'[id="{selected_id}"]')
        expect(direct_card.locator('details.proposal-report')).to_have_attribute('open', '')
        expect(direct_card.locator('.proposal-body .katex').first).to_be_visible()
        direct.reload(wait_until='networkidle')
        expect(direct_card.locator('details.proposal-report')).to_have_attribute('open', '')
        direct.close()

        page.set_viewport_size({'width': 390, 'height': 844})
        reset.click()
        expect(visible).to_have_count(len(reports))
        assert page.evaluate('document.documentElement.scrollWidth <= innerWidth + 1')
        assert cards.first.evaluate('element => { const doc = element.ownerDocument; '
                                    'return doc.documentElement.scrollWidth <= doc.defaultView.innerWidth + 1; }')
        assert frame.locator('.research-filters').evaluate(
            'element => element.scrollWidth <= element.clientWidth + 1'
        )
        frame.locator('.research-header').scroll_into_view_if_needed()
        page.screenshot(path=str(snapshots / 'research-mobile.png'), full_page=True)
        card.locator('.proposal-body .katex-display').first.scroll_into_view_if_needed()
        page.screenshot(path=str(snapshots / 'research-formula-mobile.png'), full_page=True)
        assert not errors, errors
        assert not failed, failed
        browser.close()

    print('Research dashboard: native navigation, filters, formulae, downloads, permalinks and mobile checks passed.')


if __name__ == '__main__':
    main()
