"""Exercise interface review through the actual native hgraph dashboard."""
import argparse
from pathlib import Path
import sys

from playwright.sync_api import sync_playwright, expect

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
from blueprint_proposals import read_reports


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--url', default='http://127.0.0.1:18726/')
    parser.add_argument('--chromium', default='/root/.cache/ms-playwright/chromium-1228/chrome-linux64/chrome')
    args = parser.parse_args()
    errors, failed = [], []
    reports = read_reports(ROOT)
    with sync_playwright() as p:
        browser = p.chromium.launch(headless=True, executable_path=args.chromium, args=['--no-sandbox'])
        page = browser.new_page(viewport={'width': 1440, 'height': 1000})
        page.on('pageerror', lambda e: errors.append(str(e)))
        page.on('response', lambda r: failed.append([r.status, r.url]) if r.status >= 400 and not r.url.endswith('/favicon.ico') else None)
        page.goto(args.url.rstrip('/') + '/#/Kervaire126', wait_until='networkidle')
        expand = page.get_by_role('button', name='Expand navigation panel')
        if expand.count():
            expand.click()
        page.locator('#blueprint-navigation').get_by_role('button', name='Interfaces').click()
        workspace = page.frame_locator('iframe[title="Interfaces"]')
        workspace.get_by_role('tab', name='Proposals', exact=True).click()
        frame = workspace.frame_locator('iframe[title="Proposals"]')
        expect(frame.locator('.proposal-card')).to_have_count(len(reports))
        expect(frame.locator('#proposal-results')).to_contain_text(f'{len(reports)} / {len(reports)}')
        page.screenshot(path=str(ROOT / '.lake/blueprint/proposals-desktop.png'), full_page=True)

        frame.locator('#proposal-search').fill('generalizedLeibniz')
        visible = frame.locator('.proposal-card:not([hidden])')
        assert 0 < visible.count() < len(reports)
        frame.locator('#proposal-module').select_option('Main')
        # The Main dependency audit now explicitly records independence from GL.
        expect(visible).to_have_count(1)
        expect(visible.first).to_have_attribute('id', 'Main-20261018-gray-toda-anyy')
        frame.locator('#proposal-search').fill('__no_matching_proposal__')
        expect(visible).to_have_count(0)
        expect(frame.locator('#proposal-empty')).to_be_visible()
        frame.get_by_role('button', name='重置', exact=True).click()
        expect(visible).to_have_count(len(reports))

        frame.locator('#proposal-status').select_option('approved')
        expect(visible).to_have_count(sum(r['meta']['status'].startswith('approved-') for r in reports))
        frame.get_by_role('button', name='重置', exact=True).click()
        gl = frame.locator('#ProofTools-20261018-GL-fixed-object-counterexample')
        gl.locator('summary').first.click()
        expect(gl.locator('.proposal-body pre').first).to_be_visible()
        expect(gl.locator('.proposal-body')).to_contain_text('没有生成 Lean 命题')
        # Downloads resolve within this export, including after a prefixed URL.
        with page.expect_download() as downloaded:
            gl.get_by_role('link', name='下载完整报告').click()
        assert downloaded.value.suggested_filename == 'report.md'

        gl.get_by_role('button', name='填写审阅反馈').click()
        expect(frame.locator('#proposal-review')).to_be_visible()
        frame.locator('#proposal-feedback').fill('请补充固定对象的完整前提；本条意见不批准修改接口。')
        workspace.get_by_role('tab', name='Baselines', exact=True).click()
        workspace.get_by_role('tab', name='Proposals', exact=True).click()
        expect(frame.locator('#proposal-feedback')).to_have_value('请补充固定对象的完整前提；本条意见不批准修改接口。')
        with page.expect_download() as downloaded:
            frame.get_by_role('button', name='下载反馈', exact=True).click()
        assert downloaded.value.suggested_filename.endswith('-review.txt')
        page.keyboard.press('Escape')
        expect(frame.locator('#proposal-review')).not_to_be_visible()
        # Draft feedback leaves the actual approval boundary unchanged.
        expect(gl.locator('.proposal-status')).to_have_text('已批准接口修改')
        expect(frame.locator('#ProofTools-20261018-gl-crossing-lambda-lift .proposal-status')).to_have_text('未获人审批准')
        page.set_viewport_size({'width': 390, 'height': 844})
        frame.locator('#proposal-search').fill('ProofTools-20261018-GL-fixed-object-counterexample')
        expect(visible).to_have_count(1)
        iframe = page.frames[-1]
        assert iframe.evaluate('document.documentElement.scrollWidth <= innerWidth + 1')
        page.screenshot(path=str(ROOT / '.lake/blueprint/proposals-mobile.png'), full_page=True)
        assert not errors, errors
        assert not failed, failed
        browser.close()
    print('Proposal dashboard: search, filters, evidence, downloads, feedback and mobile checks passed.')


if __name__ == '__main__':
    main()
