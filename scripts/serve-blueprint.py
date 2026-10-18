#!/usr/bin/env python3
"""Serve the native static hgraph export, with precompressed JSON/assets.

The default loopback bind is suitable for the workspace's authenticated proxy.
No application API, repository write access or frontend modifications are added.
"""
import argparse
from functools import partial
from http.server import SimpleHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from urllib.parse import urlsplit

ROOT = Path(__file__).resolve().parent.parent


class Handler(SimpleHTTPRequestHandler):
    def end_headers(self):
        self.send_header('Cache-Control', 'no-cache')
        self.send_header('Vary', 'Accept-Encoding')
        self.send_header('X-Content-Type-Options', 'nosniff')
        super().end_headers()

    def send_head(self):
        encoding = self.headers.get('Accept-Encoding', '')
        accepts_gzip = any(part.strip().split(';')[0] == 'gzip'
                           and not any(p.strip() in ('q=0', 'q=0.0', 'q=0.00', 'q=0.000')
                                       for p in part.split(';')[1:])
                           for part in encoding.split(','))
        path = Path(self.translate_path(self.path))
        if path.is_dir() and urlsplit(self.path).path.endswith('/'):
            path = path / 'index.html'
        compressed = path.with_name(path.name + '.gz')
        if accepts_gzip and path.is_file() and compressed.is_file():
            stream = compressed.open('rb')
            self.send_response(200)
            self.send_header('Content-Type', self.guess_type(str(path)))
            self.send_header('Content-Encoding', 'gzip')
            self.send_header('Content-Length', str(compressed.stat().st_size))
            self.end_headers()
            return stream
        return super().send_head()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--port', type=int, default=18726)
    parser.add_argument('--bind', default='127.0.0.1')
    parser.add_argument('--directory', type=Path, default=ROOT / '_site')
    args = parser.parse_args()
    if not (args.directory / 'validation.json').is_file():
        raise SystemExit('Generate a verified site with scripts/build-blueprint.py first.')
    handler = partial(Handler, directory=str(args.directory.resolve()))
    with ThreadingHTTPServer((args.bind, args.port), handler) as server:
        print(f'Blueprint preview: http://{args.bind}:{args.port}/#/Kervaire126', flush=True)
        server.serve_forever()


if __name__ == '__main__':
    main()
