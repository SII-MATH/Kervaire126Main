"""Fetch official archive in bounded independent ranges; verify full MD5."""
import concurrent.futures
import hashlib
import json
from pathlib import Path
import time
import requests

ROOT = Path(__file__).parent
URL = 'https://zenodo.org/records/14875701/files/kervaire_database.rar?download=1'
SIZE = 82746451
MD5 = '91ea5d8ef613828b9ef66f6d9f879166'
PARTS = ROOT / 'archive-parts'
PARTS.mkdir(exist_ok=True)
CHUNK = 4 * 1024 * 1024

def fetch(start):
    end = min(start + CHUNK, SIZE) - 1
    dest = PARTS / str(start)
    if dest.exists() and dest.stat().st_size == end - start + 1:
        return
    for attempt in range(3):
        try:
            with requests.get(URL, headers={'Range': f'bytes={start}-{end}'},
                              timeout=(20, 60), stream=True) as response:
                response.raise_for_status()
                assert response.status_code == 206
                assert response.headers['Content-Range'] == f'bytes {start}-{end}/{SIZE}'
                temp = dest.with_suffix('.partial')
                with temp.open('wb') as output:
                    for block in response.iter_content(262144):
                        output.write(block)
                assert temp.stat().st_size == end - start + 1
                temp.replace(dest)
                print(json.dumps({'start': start, 'bytes': dest.stat().st_size}), flush=True)
                return
        except Exception:
            if attempt == 2:
                raise
            time.sleep(1)

starts = list(range(0, SIZE, CHUNK))
with concurrent.futures.ThreadPoolExecutor(max_workers=8) as pool:
    list(pool.map(fetch, starts))
target = ROOT / 'kervaire_database_complete.rar'
with target.open('wb') as out:
    for start in starts:
        out.write((PARTS / str(start)).read_bytes())
assert target.stat().st_size == SIZE
assert hashlib.md5(target.read_bytes()).hexdigest() == MD5
print(json.dumps({'verified_md5': MD5, 'bytes': SIZE, 'file': str(target)}), flush=True)
