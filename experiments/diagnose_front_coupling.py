#!/usr/bin/env python3
"""Exact finite diagnostics for the center coupling law and the q-adic front budget.

This is not a proof input. It computes the actual seeded orbit and assumes no
infinite periodic center. Polynomial words use XOR addition; q-division is over
F2[X] with q = 1 + X + X^2, not integer division by seven.

Measured quantities, for every lag 1 <= Q <= max_lag and time t < max_time:
  k_t      depth of the rightmost left defect (lowest set bit of E_t);
           k_t = 0 is a center disagreement, k_t = 1 is an arrival.
  R_t      t + Q - 2 qOrder(E_t), with k_t <= R_t (observer_front_q_rank).
  Phi_t    R_t - k_t, the front slack.
  crossing the coupling law: with the center agreeing at t, the next center
           defect is leftDefect(t,1) XOR ((not center t) AND rightDefect(t,1)).
  E(1)     the row-parity reading of the defect word.
"""

import argparse
from collections import Counter
from functools import cache
import json


def phi(word):
    return word ^ (word << 1) ^ (word << 2) ^ ((word & (word << 1)) << 1)


def divide_q(word):
    quotient = 0
    while word.bit_length() >= 3:
        exponent = word.bit_length() - 3
        quotient ^= 1 << exponent
        word ^= 7 << exponent
    return quotient, word


@cache
def q_order(word):
    if word == 0:
        raise ValueError("The diagnostic evaluates q-order only on nonzero defects")
    result = 0
    while True:
        quotient, remainder = divide_q(word)
        if remainder:
            return result
        result += 1
        word = quotient


def diagnose(max_time, max_lag):
    rows = [1]
    for _ in range(max_time + max_lag + 3):
        rows.append(phi(rows[-1]))
    heads = [word >> time for time, word in enumerate(rows)]
    center = [head & 1 for head in heads]

    def right(time, column):
        return (rows[time] >> (time - column)) & 1 if column <= time else 0

    order_histogram = Counter()
    slack_by_class = {}
    coupling = Counter()
    crossing = Counter()
    parity_table = Counter()
    arrivals = 0
    for lag in range(1, max_lag + 1):
        depths, slacks = [], []
        for time in range(max_time + 1):
            word = heads[time + lag] ^ heads[time]
            assert word != 0
            depth = (word & -word).bit_length() - 1
            order = q_order(word)
            rank = time + lag - 2 * order
            assert depth <= rank
            depths.append(depth)
            slacks.append(rank - depth)
            if time < max_time:
                order_histogram[order] += 1
                parity_table[(bin(word).count("1") & 1, depth > 0)] += 1
        for time in range(max_time):
            depth, next_depth = depths[time], depths[time + 1]
            if depth == 0:
                continue
            left = (heads[time + lag] >> 1) & 1 ^ (heads[time] >> 1) & 1
            right_defect = right(time + lag, 1) ^ right(time, 1)
            gate = (1 - center[time]) & right_defect
            # center_defect_coupling, checked exactly at every agreeing step.
            assert (next_depth == 0) == (left ^ gate == 1)
            coupling["checked"] += 1
            if depth == 1:
                arrivals += 1
                crossing[(center[time], next_depth == 0)] += 1
            motion = ("advance" if next_depth == depth - 1 else
                      "witness" if next_depth == 0 else "jump")
            key = ("black" if center[time] else "white") + "/" + motion
            delta = slacks[time + 1] - slacks[time]
            bucket = slack_by_class.setdefault(key, Counter())
            bucket["negative" if delta < 0 else "zero" if delta == 0 else "positive"] += 1

    total = sum(order_histogram.values())
    return {
        "role": "Finite diagnostic only; no infinite periodic-center premise or proof input.",
        "bounds": {"max_time": max_time, "max_lag": max_lag},
        "q_order_histogram": dict(sorted(order_histogram.items())),
        "q_order_ratio_to_previous": [
            round(order_histogram[r + 1] / order_histogram[r], 3)
            for r in range(max(order_histogram)) if order_histogram[r]
        ],
        "q_order_positive_fraction": round(1 - order_histogram[0] / total, 4),
        "front_slack_delta_by_class": {k: dict(v) for k, v in sorted(slack_by_class.items())},
        "coupling_law_steps_checked": coupling["checked"],
        "crossing_at_arrival_by_center": {
            f"center={c},crossed={x}": n for (c, x), n in sorted(crossing.items())},
        "arrival_density": round(arrivals / (max_lag * max_time), 4),
        "parity_vs_center_agreement": {
            f"E(1)={p},agree={a}": n for (p, a), n in sorted(parity_table.items())},
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-time", type=int, default=1024)
    parser.add_argument("--max-lag", type=int, default=64)
    args = parser.parse_args()
    if args.max_time < 1 or args.max_lag < 1:
        parser.error("bounds must be positive")
    print(json.dumps(diagnose(args.max_time, args.max_lag), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
