#!/usr/bin/env python3
"""Publish the authored Blueprint with native hgraph, independently of Lean CI."""
from pathlib import Path
import runpy

if __name__ == '__main__':
    runpy.run_path(str(Path(__file__).with_name('build-blueprint.py')), run_name='__main__')
