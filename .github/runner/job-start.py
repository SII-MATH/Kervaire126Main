#!/usr/bin/env python3
"""Install a root-owned copy on the host; reject untrusted jobs before checkout."""
import json
import os
from pathlib import Path

REPOSITORY = 'SII-MATH/Kervaire126Main'


def allowed(env, event):
    if env.get('GITHUB_REPOSITORY') != REPOSITORY:
        return False
    workflow = env.get('GITHUB_WORKFLOW_REF', '')
    if not workflow.startswith(REPOSITORY + '/.github/workflows/ci.yml@'):
        return False
    name = env.get('GITHUB_EVENT_NAME')
    if name == 'pull_request':
        pr = event.get('pull_request') or {}
        return ((pr.get('head') or {}).get('repo') or {}).get('full_name') == REPOSITORY
    if name == 'push':
        return event.get('ref') in {'refs/heads/main', 'refs/heads/develop'}
    if name == 'merge_group':
        return (event.get('merge_group') or {}).get('base_ref') == 'refs/heads/main'
    return name == 'workflow_dispatch'


if __name__ == '__main__':
    event = json.loads(Path(os.environ['GITHUB_EVENT_PATH']).read_text())
    if not allowed(os.environ, event):
        raise SystemExit('Host policy rejected this job: only repository CI and same-repository PRs are allowed')
    print('Host policy accepted repository CI job')
