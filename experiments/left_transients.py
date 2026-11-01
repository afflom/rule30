"""Exact transients of the left diagonals ldiag d (cell (t, -t + d)) of Rule 30 from one black cell.

For each d, the minimal T with ldiag d (s + p) = ldiag d s for all s >= T, at the diagonal's eventual
minimal period p (searched up to 256, confirmed on the second half of the window). Prints the
diagonals whose transient does not exceed their own index: the claim 'T(d) > d for all d >= 8'
fails at d = 8..17 and 19 (e.g. d = 9 settles at time 5)."""
import sys

def phi(y):
    return y ^ ((y << 1) | (y << 2))

def main(n=3000, dmax=120):
    rows = [1]
    for _ in range(n):
        rows.append(phi(rows[-1]))
    def ldiag(d, t):
        b = 2 * t - d
        return (rows[t] >> b) & 1 if 0 <= b <= 2 * t else 0
    out = []
    for d in range(dmax):
        seq = [ldiag(d, t) for t in range(n)]
        for p in range(1, 257):
            if all(seq[i] == seq[i + p] for i in range(n // 2, n - p)):
                T = n // 2
                while T > 0 and seq[T - 1] == seq[T - 1 + p]:
                    T -= 1
                out.append((d, p, T))
                break
    for d, p, T in out:
        print(f"d={d} period={p} transient={T}{'  <= d' if T <= d and d >= 8 else ''}")
    return out

if __name__ == "__main__":
    main(*map(int, sys.argv[1:]))
