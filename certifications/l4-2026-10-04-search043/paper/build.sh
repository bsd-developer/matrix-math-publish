#!/usr/bin/env bash
set -euo pipefail
PAPER_DIR="$(cd "$(dirname "$0")" && pwd)"
exec "$PAPER_DIR/../../../papers/build.sh" "$PAPER_DIR/${1:-paper.md}"
