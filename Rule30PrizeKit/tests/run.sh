#!/bin/sh
# Negative controls for Check.lean. Run from the kit: sh tests/run.sh
# Each test compiles to its own module in a scratch directory, then the checker runs on it.
set -u
cd "$(dirname "$0")/.."
OUT=$(mktemp -d)
fails=0
check() { # module expected-exit checker-args...
  mod=$1; want=$2; shift 2
  [ -f "$OUT/$mod.olean" ] || lake env lean -R tests -o "$OUT/$mod.olean" "tests/$mod.lean" >"$OUT/$mod.log" 2>&1
  json=$(lake env sh -c "LEAN_PATH=\"$OUT:\$LEAN_PATH\" lean --run Check.lean $mod $*")
  got=$?
  if [ "$got" = "$want" ]; then echo "ok    $mod $* -> exit $got"
  else echo "FAIL  $mod $* -> exit $got, expected $want"; printf "%s\n" "$json"; fails=$((fails + 1)); fi
  printf "%s\n" "$json" > "$OUT/$mod.json"
}
check T01Template 0 --claim partial --headline Rule30Submission.no_period_one --headline Rule30Submission.first_bits
check T01Template 1 --claim auto
check T01Template 1 --claim problem1
check T02Sorry 1 --claim problem1
check T03NewAxiom 1 --claim problem1
check T04NativeDecide 1 --claim partial --headline Rule30Submission.first_bits
check T05SkipKernel 1 --claim problem1
check T06WrongType 1 --claim problem1
check T07Redefine 1 --claim problem1
check T07Redefine 1 --claim partial --headline Rule30Submission.problem1
echo "scratch: $OUT"
[ "$fails" = 0 ] && echo "all checks behaved as expected" || { echo "$fails unexpected"; exit 1; }
