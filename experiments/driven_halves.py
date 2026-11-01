"""Half-lines of Rule 30 driven from white by an eventually periodic boundary column.

Two candidate routes to Problem 1 would follow from a property of ONE driven half alone:
(L) the left half driven by a periodic boundary has an eventually periodic Pascal cone cone0
    (then the increment law and masked Jen would contradict a center period);
(R) the right half driven by a periodic boundary has an eventually periodic column +1
    (then column -1 would be periodic with the center, against Jen's adjacency theorem).
This script drives each half by random eventually periodic boundaries and reports the eventual
period of cone0 (L) and of column +1 (R), searched up to 160 (L) / 512 (R) on the second half of
the window. Both fail for most boundaries: no single driven half carries the contradiction."""
import random
import sys


def rule(a, b, c):
    return a ^ (b | c)


def period(seq, start, maxp):
    for p in range(1, maxp + 1):
        if all(seq[i] == seq[i + p] for i in range(start, len(seq) - p)):
            return p
    return None


def left_cone0(c, n):
    grid, prev = [], {}
    for t in range(n):
        cur = {0: c[t]}
        for p in range(-t, 0):
            cur[p] = rule(prev.get(p - 1, 0), prev.get(p, 0), prev.get(p + 1, 0))
        grid.append(cur)
        prev = cur
    out = []
    for t in range(n):
        s = 0
        for j in range(t):
            m = t - 1 - j
            for q in range(m + 1):
                if (m & q) == q and grid[j].get(-q, 0) and not grid[j].get(-q - 1, 0):
                    s ^= 1
        out.append(s)
    return out


def right_col1(c, n):
    prev, col = {0: c[0]}, [0]
    for t in range(1, n):
        cur = {0: c[t]}
        for p in range(1, t + 1):
            cur[p] = rule(prev.get(p - 1, 0), prev.get(p, 0), prev.get(p + 1, 0))
        col.append(cur.get(1, 0))
        prev = cur
    return col


def main(trials=8, seed=1):
    rng = random.Random(seed)
    for _ in range(trials):
        p = rng.choice([2, 3, 4, 5, 6, 7, 8, 12])
        word = [rng.randint(0, 1) for _ in range(p)]
        c = ([1] + word * 2000)[:1200]
        lp = period(left_cone0(c[:300], 300), 100, 160)
        rp = period(right_col1(c, 1200), 600, 512)
        print(f"boundary {''.join(map(str, word))}: left cone0 period {lp}, right column +1 period {rp}")


if __name__ == "__main__":
    main(*map(int, sys.argv[1:]))
