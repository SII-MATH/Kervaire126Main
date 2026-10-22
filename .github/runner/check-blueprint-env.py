#!/usr/bin/env python3
"""Verify the preinstalled, fixed Blueprint exporter before using its slot."""
import importlib.metadata
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

PIN = 'c33cf070fb664360e8822fd2834b39d15ebd8d8e'


def main():
    directory = Path(os.environ['BLUEPRINT_TOOLS'])
    record = json.loads((directory / 'toolchain.json').read_text())
    if record['hgraph_commit'] != PIN or importlib.metadata.version('hgraph') != '0.1.0+sii.5':
        raise SystemExit('Preinstalled hgraph differs from the repository pin; provision the pinned environment')
    if importlib.metadata.version('PyYAML') != '6.0.1':
        raise SystemExit('Preinstalled PyYAML differs from the fixed export environment')
    if Path(sys.prefix).resolve() != (directory / 'venv').resolve():
        raise SystemExit('Exporter must use the dedicated preinstalled environment')
    for tool in ('latex', 'dvisvgm', 'dot'):
        if not shutil.which(tool):
            raise SystemExit('Missing preinstalled diagram tool: ' + tool)
    subprocess.run(['latex', '--version'], check=True, stdout=subprocess.DEVNULL)
    subprocess.run(['dvisvgm', '--version'], check=True, stdout=subprocess.DEVNULL)
    print('Fixed hgraph, PyYAML and diagram tools are ready; no per-job installation')


if __name__ == '__main__':
    main()
