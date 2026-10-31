#!/usr/bin/env python3
"""How long can the seeded center column agree with its own lag-Q shift?

For each lag Q the longest run of consecutive times t with center(t + Q) =
center(t) is recorded at transients T = 2^k. A periodic center of period P
would have an infinite such run at every multiple of P. If the longest run
grows with T (as for a random sequence, about log2 T), no horizon that depends
on Q alone can refute a period; a horizon criterion must depend on the
transient T as well. This is a finite diagnostic, not a proof input.

usage: agreement_runs.py [max_log2_T] [max_lag]
"""

import sys
from collections import Counter


def center_column(n):
    """center(0..n-1) by the integer encoding of the row (bit t is column -? no:
    bit 0 is the right edge; the center of row t is bit t)."""
    row, out = 1, []
    for t in range(n):
        out.append((row >> t) & 1)
        row = row ^ ((row << 1) | (row << 2))
    return out


def main(max_log2=16, max_lag=64):
    n = 2 ** max_log2 + max_lag + 1
    c = center_column(n)
    checkpoints = [2 ** k for k in range(8, max_log2 + 1)]
    print(f"center column to t < {n}; checkpoints {checkpoints}")
    print("lag  " + "  ".join(f"T=2^{k:<2d}" for k in range(8, max_log2 + 1)) + "   (longest agreement run up to T)")
    worst = Counter()
    for Q in range(1, max_lag + 1):
        best, run, row = {}, 0, []
        for t in range(2 ** max_log2):
            run = run + 1 if c[t] == c[t + Q] else 0
            if t + 1 in checkpoints:
                best[t + 1] = max(run, max(best.values(), default=0))
                row.append(best[t + 1])
            # keep the running maximum across checkpoints
            if best and run > max(best.values()):
                best[max(best)] = run
        row = [max(v for T2, v in best.items() if T2 <= T) for T in checkpoints]
        for T, v in zip(checkpoints, row):
            worst[T] = max(worst[T], v)
        if Q <= 8 or Q % 16 == 0:
            print(f"{Q:3d}  " + "  ".join(f"{v:6d}" for v in row))
    print("max  " + "  ".join(f"{worst[T]:6d}" for T in checkpoints) + "   (over all lags)")
    print("log2 T:" + "  ".join(f"{k:6d}" for k in range(8, max_log2 + 1)))


if __name__ == "__main__":
    args = [int(a) for a in sys.argv[1:]]
    main(*args)
