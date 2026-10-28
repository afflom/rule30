#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
DIST_DIR="${ROOT_DIR}/dist"
LEXLEAN_BIN="${LEXLEAN_BIN:-/home/alex/Desktop/lexlean-v04/src/target/release/lexlean}"
PACKAGE_ONLY="${PACKAGE_ONLY:-0}"

if [[ "${1:-}" == "--package-only" ]]; then
  PACKAGE_ONLY=1
fi

compile_tex() {
  local workdir="$1"
  local texfile="$2"
  if command -v pdflatex >/dev/null 2>&1; then
    (cd "$workdir" && pdflatex -interaction=nonstopmode "$texfile" >/dev/null && pdflatex -interaction=nonstopmode "$texfile" >/dev/null)
  elif command -v docker >/dev/null 2>&1 && docker image inspect lexlean-tex:latest >/dev/null 2>&1; then
    docker run --rm -v "${workdir}:/work" -w /work lexlean-tex:latest pdflatex -interaction=nonstopmode "$texfile" >/dev/null
    docker run --rm -v "${workdir}:/work" -w /work lexlean-tex:latest pdflatex -interaction=nonstopmode "$texfile" >/dev/null
  else
    echo "Warning: Neither pdflatex nor lexlean-tex:latest Docker image found; using pre-built PDF." >&2
  fi
}

if [[ "$PACKAGE_ONLY" == "0" ]] && [[ -x "$LEXLEAN_BIN" ]]; then
  echo "==> [1/4] Building rule30-core-lean..."
  (cd "${ROOT_DIR}/rule30-core-lean" && lake build LexLeanRuntime && lake env lean -R . -o .lake/build/lib/lean/LexLeanRuntime/Laws.olean -i .lake/build/lib/lean/LexLeanRuntime/Laws.ilean LexLeanRuntime/Laws.lean && lake build)

  echo "==> [2/4] Verifying rule30-lexlean (Core.lex.tex)..."
  (cd "${ROOT_DIR}/rule30-lexlean" && "$LEXLEAN_BIN" lock && "$LEXLEAN_BIN" verify)

  echo "==> [3/4] Verifying rule30-paper (Paper.lex.tex)..."
  (cd "${ROOT_DIR}/rule30-paper" && "$LEXLEAN_BIN" lock && "$LEXLEAN_BIN" verify)

  echo "==> [4/4] Building rule30-bridge..."
  (cd "${ROOT_DIR}/rule30-bridge" && lake build LexLeanRuntime && lake env lean -R . -o .lake/build/lib/lean/LexLeanRuntime/Laws.olean -i .lake/build/lib/lean/LexLeanRuntime/Laws.ilean LexLeanRuntime/Laws.lean && lake build)
fi

CORE_ATTEST_DIR="$(find "${ROOT_DIR}/rule30-lexlean/verified-latest" -mindepth 1 -maxdepth 1 -type d | sort | tail -n 1)"
PAPER_ATTEST_DIR="$(find "${ROOT_DIR}/rule30-paper/verified-latest" -mindepth 1 -maxdepth 1 -type d | sort | tail -n 1)"

CORE_ATTEST="$(basename "$CORE_ATTEST_DIR")"
PAPER_ATTEST="$(basename "$PAPER_ATTEST_DIR")"

echo "==> Ensuring PDFs are compiled for Core (${CORE_ATTEST}) and Paper (${PAPER_ATTEST})..."
compile_tex "${CORE_ATTEST_DIR}/modules/Rule30UOR" "Core.tex"
compile_tex "${PAPER_ATTEST_DIR}/modules/Rule30Paper" "Paper.tex"

cp "${CORE_ATTEST_DIR}/modules/Rule30UOR/Core.pdf" "${ROOT_DIR}/Rule30-Core.pdf"
cp "${CORE_ATTEST_DIR}/modules/Rule30UOR/Core.pdf" "${ROOT_DIR}/rule30-lexlean/Core.pdf"
mkdir -p "${ROOT_DIR}/rule30-lexlean/pdf"
cp "${CORE_ATTEST_DIR}/modules/Rule30UOR/Core.pdf" "${ROOT_DIR}/rule30-lexlean/pdf/Core.pdf"

cp "${PAPER_ATTEST_DIR}/modules/Rule30Paper/Paper.pdf" "${ROOT_DIR}/Rule30-Paper.pdf"
cp "${PAPER_ATTEST_DIR}/modules/Rule30Paper/Paper.pdf" "${ROOT_DIR}/rule30-paper/Paper.pdf"
mkdir -p "${ROOT_DIR}/rule30-paper/pdf"
cp "${PAPER_ATTEST_DIR}/modules/Rule30Paper/Paper.pdf" "${ROOT_DIR}/rule30-paper/pdf/Paper.pdf"

rm -f "${CORE_ATTEST_DIR}/modules/Rule30UOR/"*.{aux,log,out} 2>/dev/null || true
rm -f "${PAPER_ATTEST_DIR}/modules/Rule30Paper/"*.{aux,log,out} 2>/dev/null || true

echo "==> Packaging release artifacts into ${DIST_DIR}..."
rm -rf "$DIST_DIR"
mkdir -p "$DIST_DIR"

# 1. Primary PDF deliverables
cp "${ROOT_DIR}/Rule30-Paper.pdf" "${DIST_DIR}/Rule30-Paper.pdf"
cp "${ROOT_DIR}/Rule30-Paper.pdf" "${DIST_DIR}/Paper.pdf"
cp "${ROOT_DIR}/Rule30-Core.pdf" "${DIST_DIR}/Rule30-Core.pdf"
cp "${ROOT_DIR}/Rule30-Core.pdf" "${DIST_DIR}/Core.pdf"

# 2. LexLean generated Lean & LaTeX modules
cp "${PAPER_ATTEST_DIR}/modules/Rule30Paper/Paper.lean" "${DIST_DIR}/Paper.lean"
cp "${PAPER_ATTEST_DIR}/modules/Rule30Paper/Paper.tex" "${DIST_DIR}/Paper.tex"
cp "${CORE_ATTEST_DIR}/modules/Rule30UOR/Core.lean" "${DIST_DIR}/Core.lean"
cp "${CORE_ATTEST_DIR}/modules/Rule30UOR/Core.tex" "${DIST_DIR}/Core.tex"

# 3. LexLean lockfiles and attestations
cp "${PAPER_ATTEST_DIR}/attestation.json" "${DIST_DIR}/paper-attestation-${PAPER_ATTEST:0:12}.json"
cp "${CORE_ATTEST_DIR}/attestation.json" "${DIST_DIR}/core-attestation-${CORE_ATTEST:0:12}.json"
cp "${ROOT_DIR}/rule30-paper/lexlean.lock" "${DIST_DIR}/paper-lexlean.lock"
cp "${ROOT_DIR}/rule30-lexlean/lexlean.lock" "${DIST_DIR}/core-lexlean.lock"

# 4. Complete LexLean verified bundles (.tar.gz)
tar -C "${ROOT_DIR}/rule30-paper/verified-latest" -czf "${DIST_DIR}/lexlean-paper-verified-${PAPER_ATTEST:0:12}.tar.gz" "$PAPER_ATTEST"
tar -C "${ROOT_DIR}/rule30-lexlean/verified-latest" -czf "${DIST_DIR}/lexlean-core-verified-${CORE_ATTEST:0:12}.tar.gz" "$CORE_ATTEST"

# 5. SHA-256 checksums
(cd "$DIST_DIR" && sha256sum * > SHA256SUMS)

echo "==> Release artifacts ready in ${DIST_DIR}:"
ls -lh "$DIST_DIR"

