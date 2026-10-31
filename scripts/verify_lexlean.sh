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
    # A verification whose exact tracked inputs were already accepted is reused:
    # LexLean is deterministic and the lock pins the compiler's semantics. The
    # gate supplies the cache directory and the input digest; without them every
    # run verifies.
    key_var="RULE30_LEXLEAN_KEY_${project//-/_}"
    cache_slot=""
    if [[ -n "${RULE30_LEXLEAN_CACHE:-}" && -n "${!key_var:-}" ]]; then
      cache_slot="$RULE30_LEXLEAN_CACHE/$project/${!key_var}"
    fi
    if [[ -n "$cache_slot" && -f "$cache_slot/latest-verified.json" ]]; then
      identity="$(python3 -c 'import json,sys; r=json.load(open(sys.argv[1])); print(r["attestation_id"] if r.get("success") is True else "")' "$cache_slot/latest-verified.json")"
      if [[ -n "$identity" && -f "$cache_slot/verified/$identity/attestation.json" ]]; then
        mkdir -p .lexlean/verified
        rm -rf ".lexlean/verified/$identity"
        cp -a "$cache_slot/verified/$identity" ".lexlean/verified/$identity"
        cp "$cache_slot/latest-verified.json" "$result"
        echo "reused verification $identity for $project"
        mv "$result" .lexlean/latest-verified.json
        exit 0
      fi
    fi
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
    if [[ -n "$cache_slot" ]]; then
      identity="$(python3 -c 'import json,sys; print(json.load(open(sys.argv[1]))["attestation_id"])' .lexlean/latest-verified.json)"
      if [[ -d ".lexlean/verified/$identity" ]]; then
        fresh="$cache_slot.new.$$"
        rm -rf "$fresh"
        mkdir -p "$fresh/verified"
        cp -a ".lexlean/verified/$identity" "$fresh/verified/$identity"
        cp .lexlean/latest-verified.json "$fresh/latest-verified.json"
        rm -rf "$cache_slot"
        mkdir -p "$(dirname "$cache_slot")"
        mv "$fresh" "$cache_slot"
      fi
    fi
  )
done
