#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
DIST_DIR="${ROOT_DIR}/dist"
LEXLEAN_BIN="${LEXLEAN_BIN:-lexlean}"
PACKAGE_ONLY="${PACKAGE_ONLY:-0}"

case "${1:-}" in
  --package-only) PACKAGE_ONLY=1 ;;
  "") ;;
  *) echo "Usage: $0 [--package-only]" >&2; exit 2 ;;
esac

if [[ "$PACKAGE_ONLY" == "0" ]]; then
  if ! command -v "$LEXLEAN_BIN" >/dev/null 2>&1; then
    echo "LexLean compiler not found: $LEXLEAN_BIN (use --package-only for verified bundles)" >&2
    exit 1
  fi
  make -C "$ROOT_DIR" core lexlean bridge LEXLEAN="$LEXLEAN_BIN"
fi

select_verified() {
  python3 - "$ROOT_DIR/$1" <<'PY'
import json
import re
import sys
import tomllib
from pathlib import Path

project = Path(sys.argv[1])
latest = project / ".lexlean/latest-verified.json"
if latest.exists():
    result = json.loads(latest.read_text())
    identity = result.get("attestation_id", "")
    if result.get("success") is not True or not re.fullmatch(r"[0-9a-f]{64}", identity):
        raise SystemExit(f"Invalid verification result: {latest}")
    directory = project / ".lexlean/verified" / identity
else:
    candidates = sorted((project / "verified-latest").glob("*/attestation.json"))
    if len(candidates) != 1:
        raise SystemExit(f"Expected one release bundle in {project}; run make lexlean to select a verification")
    directory = candidates[0].parent
    identity = directory.name
attestation = json.loads((directory / "attestation.json").read_text())
if attestation.get("status") != "verified" or attestation.get("attestation_id") != identity:
    raise SystemExit(f"Invalid verified bundle: {directory}")
lock = tomllib.loads((project / "lexlean.lock").read_text())
if attestation.get("lexlean", {}).get("compiler_semantics") != lock.get("compiler_semantics"):
    raise SystemExit(f"Compiler fingerprint mismatch in {project}; run make lexlean before packaging")
print(directory)
PY
}

CORE_SOURCE="$(select_verified rule30-lexlean)"
PAPER_SOURCE="$(select_verified rule30-paper)"
CORE_ATTEST="$(basename "$CORE_SOURCE")"
PAPER_ATTEST="$(basename "$PAPER_SOURCE")"

# TeX writes auxiliary files and timestamps. Compile copies so packaging never changes
# tracked PDFs, immutable attestations, or the caller's working tree.
STAGING_DIR="$(mktemp -d)"
trap 'rm -rf "$STAGING_DIR"' EXIT
mkdir -p "$STAGING_DIR/core/$CORE_ATTEST" "$STAGING_DIR/paper/$PAPER_ATTEST"
cp -R "$CORE_SOURCE/." "$STAGING_DIR/core/$CORE_ATTEST/"
cp -R "$PAPER_SOURCE/." "$STAGING_DIR/paper/$PAPER_ATTEST/"

compile_tex() {
  local workdir="$1"
  local texfile="$2"
  if command -v pdflatex >/dev/null 2>&1; then
    (cd "$workdir" && pdflatex -halt-on-error -interaction=nonstopmode "$texfile" >/dev/null && pdflatex -halt-on-error -interaction=nonstopmode "$texfile" >/dev/null)
  elif command -v docker >/dev/null 2>&1 && docker image inspect lexlean-tex:latest >/dev/null 2>&1; then
    docker run --rm --user "$(id -u):$(id -g)" -v "${workdir}:/work" -w /work lexlean-tex:latest pdflatex -halt-on-error -interaction=nonstopmode "$texfile" >/dev/null
    docker run --rm --user "$(id -u):$(id -g)" -v "${workdir}:/work" -w /work lexlean-tex:latest pdflatex -halt-on-error -interaction=nonstopmode "$texfile" >/dev/null
  elif [[ -s "$workdir/${texfile%.tex}.pdf" ]]; then
    echo "TeX unavailable; using the verified bundle's existing ${texfile%.tex}.pdf" >&2
  else
    echo "TeX is required to render $workdir/$texfile" >&2
    exit 1
  fi
}

CORE_DIR="$STAGING_DIR/core/$CORE_ATTEST"
PAPER_DIR="$STAGING_DIR/paper/$PAPER_ATTEST"
echo "==> Packaging verified Core ($CORE_ATTEST) and Paper ($PAPER_ATTEST)..."
compile_tex "$CORE_DIR/modules/Rule30UOR" Core.tex
compile_tex "$PAPER_DIR/modules/Rule30Paper" Paper.tex
find "$STAGING_DIR" -type f \( -name '*.aux' -o -name '*.log' -o -name '*.out' \) -delete

rm -rf "$DIST_DIR"
mkdir -p "$DIST_DIR"
cp "$CORE_DIR/modules/Rule30UOR/Core.pdf" "$DIST_DIR/Rule30-Core.pdf"
cp "$CORE_DIR/modules/Rule30UOR/Core.pdf" "$DIST_DIR/Core.pdf"
cp "$PAPER_DIR/modules/Rule30Paper/Paper.pdf" "$DIST_DIR/Rule30-Paper.pdf"
cp "$PAPER_DIR/modules/Rule30Paper/Paper.pdf" "$DIST_DIR/Paper.pdf"
cp "$CORE_DIR/modules/Rule30UOR/Core.lean" "$DIST_DIR/Core.lean"
cp "$CORE_DIR/modules/Rule30UOR/Core.tex" "$DIST_DIR/Core.tex"
cp "$PAPER_DIR/modules/Rule30Paper/Paper.lean" "$DIST_DIR/Paper.lean"
cp "$PAPER_DIR/modules/Rule30Paper/Paper.tex" "$DIST_DIR/Paper.tex"
cp "$CORE_DIR/attestation.json" "$DIST_DIR/core-attestation-${CORE_ATTEST:0:12}.json"
cp "$PAPER_DIR/attestation.json" "$DIST_DIR/paper-attestation-${PAPER_ATTEST:0:12}.json"
cp "$ROOT_DIR/rule30-lexlean/lexlean.lock" "$DIST_DIR/core-lexlean.lock"
cp "$ROOT_DIR/rule30-paper/lexlean.lock" "$DIST_DIR/paper-lexlean.lock"
tar -C "$STAGING_DIR/core" -czf "$DIST_DIR/lexlean-core-verified-${CORE_ATTEST:0:12}.tar.gz" "$CORE_ATTEST"
tar -C "$STAGING_DIR/paper" -czf "$DIST_DIR/lexlean-paper-verified-${PAPER_ATTEST:0:12}.tar.gz" "$PAPER_ATTEST"
(cd "$DIST_DIR" && sha256sum * > SHA256SUMS)
echo "==> Release artifacts ready in $DIST_DIR"
