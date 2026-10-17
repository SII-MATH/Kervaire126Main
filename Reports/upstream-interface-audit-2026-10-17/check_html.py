from pathlib import Path
import json
from playwright.sync_api import sync_playwright

folder = Path(__file__).resolve().parent
with sync_playwright() as p:
    browser = p.chromium.launch(headless=True, executable_path='/root/.cache/ms-playwright/chromium-1228/chrome-linux64/chrome', args=['--no-sandbox'])
    page = browser.new_page(viewport={'width': 1440, 'height': 1000}, device_scale_factor=1)
    errors = []
    page.on('pageerror', lambda error: errors.append(str(error)))
    page.goto((folder/'index.html').as_uri(), wait_until='load')
    page.wait_for_selector('details.interface')
    expected = json.loads((folder/'audit-data.json').read_text())
    assert str(expected['summary']['used']['total']['total']) in page.locator('#count').inner_text()
    page.locator('details.interface').first.click()
    page.wait_for_selector('.details-body pre')
    assert page.locator('.details-body pre').first.inner_text()
    page.locator('#group').select_option('unused')
    assert str(expected['summary']['unused']['total']['total']) in page.locator('#count').inner_text()
    page.locator('#search').fill('generalizedMahowald')
    assert page.locator('details.interface').count() >= 1
    page.locator('#search').fill('')
    page.locator('#group').select_option('all')
    page.locator('#status').select_option('clean')
    assert str(expected['summary']['all']['total']['strict_clean']) in page.locator('#count').inner_text()
    page.locator('#scope').select_option('generated')
    assert page.locator('details.interface').count() > 0
    page.locator('#scope').select_option('named')
    page.locator('#status').select_option('all')
    page.locator('#group').select_option('used')
    page = browser.new_page(viewport={'width': 1440, 'height': 1000})
    page.goto((folder/'index.html').as_uri(), wait_until='load')
    page.wait_for_selector('details.interface')
    page.locator('#search').blur()
    page.evaluate("document.documentElement.style.scrollBehavior='auto'; window.scrollTo(0, 0)")
    page.wait_for_timeout(200)
    page.screenshot(path=str(folder/'preview-desktop.png'), full_page=False)
    page.set_viewport_size({'width': 390, 'height': 844})
    page.evaluate("document.documentElement.style.scrollBehavior='auto'; window.scrollTo(0, 0)")
    page.wait_for_timeout(200)
    page.screenshot(path=str(folder/'preview-mobile.png'), full_page=False)
    assert page.evaluate('document.documentElement.scrollWidth <= window.innerWidth')
    assert not errors, errors
    browser.close()
print('HTML passed: both groups, expanding types, search, status and generated filters, mobile overflow, no JS errors.')
