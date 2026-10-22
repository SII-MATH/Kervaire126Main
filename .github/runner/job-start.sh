#!/usr/bin/env bash
# The runner accepts shell hooks; keep policy in a separately root-owned file.
set -euo pipefail
exec /usr/bin/python3 /usr/local/lib/kip126-ci/job-start.py
