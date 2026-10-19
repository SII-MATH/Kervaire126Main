#!/usr/bin/env python3
"""Create or validate canonical agent interface reports."""
import argparse
from pathlib import Path
import re
import subprocess

import yaml
from blueprint_proposals import MODULES, read_reports

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest='command', required=True)
    commands.add_parser('validate')
    new = commands.add_parser('new')
    new.add_argument('--module', required=True, choices=MODULES[:-1])
    new.add_argument('--id', required=True)
    new.add_argument('--title', required=True)
    new.add_argument('--reporter', required=True)
    args = parser.parse_args()
    if args.command == 'validate':
        print(f'Validated {len(read_reports(ROOT))} interface reports.')
        return
    if not re.fullmatch(r'[A-Za-z0-9][A-Za-z0-9_-]*', args.id):
        parser.error('--id must contain only letters, digits, underscores and hyphens')
    identity = args.module + '-' + args.id
    if any(r['meta']['issue_id'] == identity for r in read_reports(ROOT)):
        parser.error('Proposal identity already exists')
    destination = ROOT / 'interface/proposals' / args.module / args.id / 'report.md'
    template = (ROOT / 'interface/proposals/TEMPLATE.md').read_text().split('---', 2)
    metadata = yaml.safe_load(template[1])
    metadata.update(issue_id=identity, title=args.title, responsibility_module=args.module,
                    reporter_agent=args.reporter,
                    baseline_commit=subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip())
    destination.parent.mkdir(parents=True, exist_ok=True)
    # Exclusive creation makes repeated submissions safe even during concurrent work.
    with destination.open('x') as stream:
        stream.write('---\n' + yaml.safe_dump(metadata, allow_unicode=True, sort_keys=False) + '---' + template[2])
    print(destination.relative_to(ROOT))
    print('Created a draft. Complete the evidence and targets before requesting review.')


if __name__ == '__main__':
    main()
