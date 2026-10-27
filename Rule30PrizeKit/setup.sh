#!/bin/sh
# Set up the Rule 30 Prize kit: prebuilt Mathlib, the statements, the template submission.
# Run from anywhere: sh Rule30PrizeKit/setup.sh
set -eu
cd "$(dirname "$0")"
command -v lake >/dev/null 2>&1 || {
  echo "lake not found. Install elan: curl https://elan.lean-lang.org/elan-init.sh -sSf | sh"; exit 1; }
lake exe cache get                          # prebuilt Mathlib for its v4.35.0 tag (a few GB)
lake build Rule30PrizeKit Rule30Submission  # the statements, the equivalences, the template
lake env lean --run Check.lean Rule30Submission --claim partial --headline Rule30Submission.no_period_one
echo
echo "Kit ready: $(pwd)"
