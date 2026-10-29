#!/usr/bin/env bash
# One acceptance gate for CI, pre-commit, and pre-push. Never skip LexLean/PDFs.
set -euo pipefail
ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"
LEXLEAN_COMPILER="${1:-lexlean}"
LOCK_DIR="$(mktemp -d)"
trap 'rm -rf "$LOCK_DIR"' EXIT
cp rule30-lexlean/lexlean.lock "$LOCK_DIR/core.lock"
cp rule30-paper/lexlean.lock "$LOCK_DIR/paper.lock"
make check-tooling
make check-research
make bridge
make lexlean LEXLEAN="$LEXLEAN_COMPILER"
# Verification must reproduce the committed locks, not silently repair them.
cmp "$LOCK_DIR/core.lock" rule30-lexlean/lexlean.lock
cmp "$LOCK_DIR/paper.lock" rule30-paper/lexlean.lock
make release-artifacts
