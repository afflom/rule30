#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
LEXLEAN_BIN="${1:-${LEXLEAN_BIN:-lexlean}}"

for project in rule30-lexlean rule30-paper; do
  (
    cd "$ROOT_DIR/$project"
    mkdir -p .lexlean
    # A failed attempt must not leave a previous success available for packaging.
    printf '{"success":false}\n' > .lexlean/latest-verified.json
    result="$(mktemp .lexlean/verification.XXXXXX)"
    trap 'rm -f "$result"' EXIT
    "$LEXLEAN_BIN" lock
    if ! "$LEXLEAN_BIN" verify --diagnostic-format json > "$result"; then
      cat "$result" >&2
      exit 1
    fi
    python3 - "$result" <<'PY'
import json
import sys

with open(sys.argv[1]) as stream:
    result = json.load(stream)
if result.get("success") is not True or not result.get("attestation_id"):
    raise SystemExit("LexLean did not produce a verified attestation")
print("verified " + result["attestation_id"])
PY
    mv "$result" .lexlean/latest-verified.json
  )
done
