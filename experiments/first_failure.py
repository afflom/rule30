#!/usr/bin/env python3
"""Where does a hypothetical center period first fail, and is that time 2-adically structured?

For each transient T and period P, delay(T, P) is the least d with
center(T + d + P) != center(T + d): the first comparison the horizon
certificate (Rule30UOR.Horizon) would find. If the closing argument is the
scale mismatch between the periodically seeded right half (power-of-two
diagonal periods) and the doubling-time reconstruction of the left edge, the
delay should depend on the 2-adic data of P and T (v2(P), P and T modulo powers
of two) rather than look like the geometric law of independent fair bits
(Pr[delay >= d] = 2^-d). This script prints the empirical delay law by v2(P),
by P modulo 4 and 8, by T modulo 8, for powers of two P alone, and the
chi-square-free summary: mean delay and the tail Pr[delay >= 8] per class
against the fair-bit value 1 and 2^-8.

usage: first_failure.py [T0] [T1] [Pmax]   (defaults 256 4352 256)
"""

import sys
from collections import defaultdict


def center_column(n):
    row, out = 1, []
    for t in range(n):
        out.append((row >> t) & 1)
        row = row ^ ((row << 1) | (row << 2))
    return out


def v2(n):
    k = 0
    while n % 2 == 0:
        n //= 2
        k += 1
    return k


def summarize(label, delays):
    n = len(delays)
    mean = sum(delays) / n
    tail = sum(1 for d in delays if d >= 8) / n
    longest = max(delays)
    print(f"  {label:<14} n={n:7d}  mean={mean:6.3f}  P[d>=8]={tail:.5f}  max={longest:3d}")


def main(T0=256, T1=4352, Pmax=256):
    H = 64
    c = center_column(T1 + Pmax + H + 2)
    delays = {}
    for P in range(1, Pmax + 1):
        for T in range(T0, T1):
            d = 0
            while c[T + d + P] == c[T + d]:
                d += 1
                if d >= H:
                    break
            delays[(T, P)] = d
    print(f"delay(T, P) for T in [{T0}, {T1}), P in [1, {Pmax}]; fair bits: mean 1, P[d>=8] = {2**-8:.5f}")
    print("by v2(P):")
    by = defaultdict(list)
    for (T, P), d in delays.items():
        by[v2(P)].append(d)
    for k in sorted(by):
        summarize(f"v2(P)={k}", by[k])
    print("by P mod 8:")
    by = defaultdict(list)
    for (T, P), d in delays.items():
        by[P % 8].append(d)
    for k in sorted(by):
        summarize(f"P%8={k}", by[k])
    print("by T mod 8:")
    by = defaultdict(list)
    for (T, P), d in delays.items():
        by[T % 8].append(d)
    for k in sorted(by):
        summarize(f"T%8={k}", by[k])
    print("powers of two P, by T mod P (P = 2^k, k = 1..5), and P = 2^k alone:")
    for k in range(1, 6):
        P = 2 ** k
        rows = [delays[(T, P)] for T in range(T0, T1)]
        summarize(f"P={P}", rows)
        by = defaultdict(list)
        for T in range(T0, T1):
            by[T % P].append(delays[(T, P)])
        worst = max(by, key=lambda r: sum(by[r]) / len(by[r]))
        best = min(by, key=lambda r: sum(by[r]) / len(by[r]))
        print(f"      residue means: max at T%{P}={worst} ({sum(by[worst])/len(by[worst]):.3f}), "
              f"min at T%{P}={best} ({sum(by[best])/len(by[best]):.3f})")
    print("delay law overall vs fair bits (Pr[d >= k]):")
    allds = list(delays.values())
    n = len(allds)
    for k in range(1, 13):
        emp = sum(1 for d in allds if d >= k) / n
        print(f"  k={k:2d}  empirical={emp:.6f}  fair={2**-k:.6f}  ratio={emp * 2**k:.3f}")


if __name__ == "__main__":
    main(*[int(a) for a in sys.argv[1:]])
