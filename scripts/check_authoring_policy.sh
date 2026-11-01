#!/usr/bin/env bash
set -euo pipefail

# LexLean-first authoring policy:
# - Proof-level Lean changes in rule30-core-lean/Rule30UOR or rule30-bridge must
#   be paired with LexLean source edits.
# - Generated artifacts must not be edited without LexLean source edits.

# Python is deprecated (the owner, 2026-11-01: "No more python"): the implementation is LexLean,
# with prism-stdlib, and PrismPM generates and governs it. Python is eliminated incrementally, so a
# commit may only shrink it: it may not add a Python file, and the Python it touches may not grow.
# This check runs before the bypass below and has none of its own.
if git rev-parse --git-dir >/dev/null 2>&1; then
  mapfile -t new_python < <(git diff --cached --no-renames --name-only --diff-filter=A -- '*.py')
  if [[ ${#new_python[@]} -gt 0 ]]; then
    echo "Refused: Python is deprecated in this repository; new Python files: ${new_python[*]}" >&2
    echo "Author the capability in LexLean (prism-stdlib; PrismPM generates the runtime)." >&2
    exit 1
  fi
  read -r py_added py_removed < <(git diff --cached --no-renames --numstat -- '*.py' \
    | awk '$1 != "-" { a += $1; r += $2 } END { print a + 0, r + 0 }')
  if (( py_added > py_removed )); then
    echo "Refused: Python is deprecated; this commit grows it by $((py_added - py_removed)) lines" >&2
    echo "(added ${py_added}, removed ${py_removed}). Python may only shrink: move the logic to LexLean." >&2
    exit 1
  fi
fi

if [[ "${ALLOW_NON_LEXLEAN_AUTHORING:-0}" == "1" ]]; then
  exit 0
fi

if ! git rev-parse --git-dir >/dev/null 2>&1; then
  exit 0
fi

mapfile -d '' -t staged < <(git diff --cached --no-renames --name-only --diff-filter=ACMD -z)
if [[ ${#staged[@]} -eq 0 ]]; then
  exit 0
fi

has_lexlean_source=0
has_host_proof_edit=0
has_generated_artifact_edit=0
has_compiler_pin_edit=0
has_non_lock_artifact_edit=0
lockfiles=()

for p in "${staged[@]}"; do
  if [[ "$p" == ".github/lexlean-revision" ]]; then
    has_compiler_pin_edit=1
  fi
  case "$p" in
    rule30-lexlean/src/*.lex.tex|rule30-lexlean/src/**/*.lex.tex|rule30-paper/src/*.lex.tex|rule30-paper/src/**/*.lex.tex|rule30-api/src/*.lex.tex|rule30-lexlean/glossary/*|rule30-paper/glossary/*)
      has_lexlean_source=1
      ;;
  esac

  # The acceptance gate regenerates and stages these derivatives on every commit.
  # Historical bundle PDFs are retired; their deletion needs no proof-text edit.
  case "$p" in
    Rule30-Core.pdf|Rule30-Paper.pdf|Rule30-Observations.pdf|rule30-lexlean/Core.pdf|rule30-paper/Paper.pdf|rule30-paper/Observations.pdf|rule30-lexlean/pdf/Core.pdf|rule30-lexlean/pdf/Core.tex|rule30-paper/pdf/Paper.pdf|rule30-paper/pdf/Paper.tex|rule30-paper/pdf/Observations.pdf|rule30-paper/pdf/Observations.tex)
      continue ;;
  esac
  case "$p" in
    rule30-lexlean/verified-latest/*.pdf|rule30-paper/verified-latest/*.pdf)
      if ! git cat-file -e ":$p" 2>/dev/null; then continue; fi ;;
  esac

  case "$p" in
    rule30-core-lean/Rule30UOR/*.lean|rule30-core-lean/Rule30UOR/**/*.lean|rule30-bridge/*.lean|rule30-bridge/**/*.lean)
      has_host_proof_edit=1
      ;;
  esac

  case "$p" in
    Rule30-Core.pdf|Rule30-Paper.pdf|rule30-lexlean/Core.pdf|rule30-paper/Paper.pdf|rule30-lexlean/lexlean.lock|rule30-paper/lexlean.lock|rule30-lexlean/pdf/*|rule30-paper/pdf/*|rule30-lexlean/verified-latest/*|rule30-paper/verified-latest/*|dist/*)
      has_generated_artifact_edit=1
      case "$p" in
        rule30-lexlean/lexlean.lock|rule30-paper/lexlean.lock) lockfiles+=("$p") ;;
        *) has_non_lock_artifact_edit=1 ;;
      esac
      ;;
  esac
done

if [[ $has_host_proof_edit -eq 1 && $has_lexlean_source -eq 0 ]]; then
  cat >&2 <<'MSG'
pre-commit: blocked by LexLean authoring policy.

Detected staged proof-surface Lean edits in rule30-core-lean/Rule30UOR or rule30-bridge,
but no staged LexLean source edits under rule30-lexlean/src, rule30-paper/src or rule30-api/src.

Policy: the paper/LexLean sources are the authoring surface; host Lean and bridge are
derived/bridge artifacts.

If this commit is intentionally tooling-only, set ALLOW_NON_LEXLEAN_AUTHORING=1 for this commit.
MSG
  exit 1
fi

# A compiler upgrade may refresh only the compiler-semantics fingerprints in lockfiles.
# Inspect the index, not unstaged worktree content. Any other generated change still
# requires LexLean source edits (or the documented exceptional-maintenance override).
compiler_lock_refresh=0
if [[ $has_compiler_pin_edit -eq 1 && $has_non_lock_artifact_edit -eq 0 && ${#lockfiles[@]} -gt 0 ]]; then
  refresh_ok=1
  revision="$(git show :.github/lexlean-revision | tr -d '[:space:]')"
  [[ "$revision" =~ ^[0-9a-f]{40}$ ]] || refresh_ok=0
  for path in "${lockfiles[@]}"; do
    mapfile -t edits < <(git diff --cached --unified=0 -- "$path" | grep -E '^[+-]' | grep -vE '^(\+\+\+|---)' || true)
    if [[ ${#edits[@]} -ne 2 || "${edits[0]:0:1}" != "-" || "${edits[1]:0:1}" != "+" ]]; then
      refresh_ok=0
      continue
    fi
    for line in "${edits[@]}"; do
      [[ "$line" =~ ^[+-]compiler_semantics\ =\ \"[0-9a-f]{64}\"$ ]] || refresh_ok=0
    done
  done
  if [[ $refresh_ok -eq 1 ]]; then
    compiler_lock_refresh=1
  fi
fi

if [[ $has_generated_artifact_edit -eq 1 && $has_lexlean_source -eq 0 && $compiler_lock_refresh -eq 0 ]]; then
  cat >&2 <<'MSG'
pre-commit: blocked by LexLean authoring policy.

Detected staged generated artifact edits (pdf/lock/verified-latest/dist) without
LexLean source edits.

Compiler-only fingerprint refreshes may accompany a staged .github/lexlean-revision update.
Otherwise regenerate artifacts from LexLean source, or set ALLOW_NON_LEXLEAN_AUTHORING=1
if this is an exceptional maintenance commit.
MSG
  exit 1
fi

exit 0
