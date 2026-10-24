# site/ のページをヘッドレスのブラウザで開き、コンソールのエラーを表示してスクリーンショットを保存する(手元の確認用)
#   python tools/screenshot.py site/credit_simulation_v6.html out.png [プリセット名]
import sys
from pathlib import Path
from playwright.sync_api import sync_playwright

page_path, out = Path(sys.argv[1]).resolve(), sys.argv[2]
preset = sys.argv[3] if len(sys.argv) > 3 else None
with sync_playwright() as pw:
    b = pw.chromium.launch()
    pg = b.new_page(viewport={'width': 1200, 'height': 900})
    errs = []
    pg.on('console', lambda m: errs.append(f'{m.type}: {m.text}') if m.type in ('error', 'warning') else None)
    pg.on('pageerror', lambda e: errs.append(f'pageerror: {e}'))
    pg.goto(page_path.as_uri())
    pg.wait_for_timeout(1500)
    if preset:
        pg.select_option('#preset', preset)
        pg.wait_for_timeout(2500)
    print('verdict:', pg.inner_text('#verdict'))
    pg.screenshot(path=out, full_page=True)
    print('\n'.join(errs) if errs else 'no console errors')
    b.close()
