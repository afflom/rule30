#!/usr/bin/env python3
"""Exact finite diagnostics for the classified seeded cancellation windows.

This is not a proof input. It assumes only finite center agreement over each
reported window, never an infinite periodic center. Polynomial words use XOR
addition; q-division is over F2[X], not integer division by seven.

Updates are classified by their input center: the black root is the reset,
and times b+1 through b+k-1 are white updates, including the arrival erasure.
Windows can overlap and are not asserted to form a causal successor chain.
"""

import argparse
from collections import Counter
from functools import cache
import json


def phi(word):
    return word ^ (word << 1) ^ (word << 2) ^ ((word & (word << 1)) << 1)


def divide_q(word):
    original = word
    quotient = 0
    while word.bit_length() >= 3:
        exponent = word.bit_length() - 3
        quotient ^= 1 << exponent
        word ^= 7 << exponent
    assert (quotient ^ (quotient << 1) ^ (quotient << 2) ^ word) == original
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


def diagnose(max_base, max_lag, example_count, include_all=False):
    rows = [1]
    for _ in range(max(8, max_base + 2 * max_lag + 3)):
        rows.append(phi(rows[-1]))
    heads = [word >> time for time, word in enumerate(rows)]

    def right(time, column):
        return (rows[time] >> (time - column)) & 1 if column <= time else 0

    def center(time):
        return heads[time] & 1

    def defect(lag, time):
        return heads[time + lag] ^ heads[time]

    def rank(lag, time):
        return time + lag - 2 * q_order(defect(lag, time))

    def source(lag, time):
        later, earlier = heads[time + lag], heads[time]
        carry = (later & (later << 1)) ^ (earlier & (earlier << 1))
        boundary = ((1 - center(time + lag)) & right(time + lag, 1)) ^ (
            (1 - center(time)) & right(time, 1)
        )
        return carry, boundary, carry ^ boundary

    # Cross-check the existing kernel-checked finite certificate.
    assert defect(5, 2) == 216 and defect(5, 3) == 412
    assert divide_q(defect(5, 2))[1] == 0
    assert divide_q(defect(5, 3))[1] == 1

    windows = []
    for lag in range(1, max_lag + 1):
        for base in range(max_base + 1):
            if not (center(base) and center(base + lag)):
                continue
            word = defect(lag, base)
            assert word != 0
            depth = (word & -word).bit_length() - 1
            if not 3 <= depth <= lag:
                continue
            # LeadingAdvance: nearest left defect followed by shared black.
            if not ((heads[base] >> (depth - 1)) & 1 and
                    (heads[base + lag] >> (depth - 1)) & 1):
                continue
            # CenterCleanThrough Q b k, and WhiteCenterGap b (k-1).
            if any(center(base + i) != center(base + i + lag)
                   for i in range(depth + 1)):
                continue
            if any(center(base + i) for i in range(1, depth)):
                continue
            start, finish = base + depth - 2, base + depth - 1
            # HeadImportPath at the forced start, with finish=start+1.
            if right(start, 1) or right(start + lag, 1):
                continue
            if right(start, 2) == right(start + lag, 2):
                continue
            if right(finish, 1) == right(finish + lag, 1):
                continue
            assert start < finish
            assert (((1 - right(start, 1)) & right(start, 2)) ^
                    ((1 - right(start + lag, 1)) & right(start + lag, 2))) == 1
            assert all(right(s, 1) != right(s + lag, 1)
                       for s in range(start + 1, finish + 1))
            # Verify the classification's physical consequences independently.
            assert all(right(base, j) == right(base + lag, j) == 1
                       for j in range(depth - 2))
            assert all(right(base + 1, j) == right(base + 1 + lag, j) == 0
                       for j in range(1, depth - 1))
            for i in range(depth):
                left = defect(lag, base + i)
                assert (left & -left).bit_length() - 1 == depth - i
            for i in range(1, depth - 1):
                front = depth - i
                assert right(base + i, front) != right(base + i + lag, front)
                assert all(right(base + i, j) == right(base + i + lag, j)
                           for j in range(1, front))
                assert right(base + i, front - 1) == right(base + i + lag, front - 1) == 0

            steps = []
            for time in range(base, base + depth):
                carry, boundary, complete_source = source(lag, time)
                old, new = defect(lag, time), defect(lag, time + 1)
                assert (new << 1) == (
                    old ^ (old << 1) ^ (old << 2) ^ (complete_source << 1)
                )
                assert boundary == ((old >> 1) & 1)
                delta = rank(lag, time + 1) - rank(lag, time)
                steps.append({
                    "t": time, "center": center(time),
                    "order": q_order(old), "next_order": q_order(new),
                    "delta_R": delta, "carry_zero": carry == 0,
                    "carry_lowest_bit": (carry & -carry).bit_length() - 1 if carry else None,
                    "carry_mod_q": divide_q(carry)[1], "boundary": boundary,
                    "source_zero": complete_source == 0,
                    "source_mod_q": divide_q(complete_source)[1],
                })
            reset_delta = steps[0]["delta_R"]
            white_delta = sum(s["delta_R"] for s in steps[1:])
            assert reset_delta + white_delta == rank(lag, base + depth) - rank(lag, base)
            windows.append({
                "Q": lag, "b": base, "k": depth,
                "reset_delta": reset_delta, "white_delta": white_delta,
                "interior_white_delta": sum(s["delta_R"] for s in steps[1:-1]),
                "arrival_delta": steps[-1]["delta_R"],
                "total_delta": reset_delta + white_delta, "steps": steps,
            })

    def signs(field):
        return dict(Counter("negative" if w[field] < 0 else
                            "positive" if w[field] > 0 else "zero" for w in windows))

    ordered = sorted(windows, key=lambda w: (w["b"] + w["Q"], w["b"], w["Q"]))
    result = {
        "role": "Finite diagnostic only; no infinite periodic-center premise or proof input.",
        "bounds": {"max_base_time": max_base, "max_lag": max_lag, "depth": "3 <= k <= Q"},
        "phase_convention": "Classify each update by its input center; arrival is a white update.",
        "residue_encoding": "Binary polynomials: 0, 1, 2=X, 3=1+X; not integer residues mod 7.",
        "summary": {
            "count": len(windows), "by_k": dict(Counter(w["k"] for w in windows)),
            "white_delta_signs": signs("white_delta"),
            "reset_delta_signs": signs("reset_delta"),
            "white_steps": sum(len(w["steps"]) - 1 for w in windows),
            "white_zero_carry_steps": sum(s["carry_zero"] for w in windows for s in w["steps"][1:]),
        },
        "examples": ordered[:example_count],
    }
    if include_all:
        result["windows"] = windows
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-base-time", type=int, default=512)
    parser.add_argument("--max-lag", type=int, default=128)
    parser.add_argument("--examples", type=int, default=3)
    parser.add_argument("--all-windows", action="store_true")
    args = parser.parse_args()
    if args.max_base_time < 0 or args.max_lag < 1 or args.examples < 0:
        parser.error("base time and example count must be nonnegative; max lag must be positive")
    result = diagnose(args.max_base_time, args.max_lag, args.examples, args.all_windows)
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
