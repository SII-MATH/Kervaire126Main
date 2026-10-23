#!/usr/bin/env python3
"""Root-owned admission for the independent, main-only Blueprint runner."""
import json
import os
from pathlib import Path

REPOSITORY = 'SII-MATH/Kervaire126Main'


def allowed(env, event):
    return (env.get('GITHUB_REPOSITORY') == REPOSITORY and
            env.get('GITHUB_WORKFLOW_REF') == REPOSITORY + '/.github/workflows/pages.yml@refs/heads/main' and
            env.get('GITHUB_EVENT_NAME') in {'push', 'workflow_dispatch'} and
            env.get('GITHUB_REF') == 'refs/heads/main' and
            (env.get('GITHUB_EVENT_NAME') != 'push' or event.get('ref') == 'refs/heads/main'))


if __name__ == '__main__':
    event = json.loads(Path(os.environ['GITHUB_EVENT_PATH']).read_text())
    if not allowed(os.environ, event):
        raise SystemExit('Host policy rejected job: only main Blueprint exports use this slot')
    print('Host policy accepted main Blueprint export')
