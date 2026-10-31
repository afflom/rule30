# Joint versus single facets for the word 10 (eventual period 2 of the center column).
# real facet  : left half finitely supported      (ZBL: the left half alone, center held to the effective boundary)
# joint facets: both halves finitely supported    (an arbitrary finite configuration; center column must alternate)
import numpy as np
from zbl import Z
Tmax=120
def longest_alternation(X,off,T=Tmax):
    W=X.bit_length()+2*T+4; mid=off+T+2; x=X<<(T+2); best=run=0; prev=None; prevprev=None
    for t in range(T):
        c=(x>>mid)&1
        if prev is not None and c!=prev: run+=1
        else: run=1 if prev is None or c!=prev else 1
        best=max(best,run)
        prev=c
        x=((x<<1)^(x|(x>>1)))
    return best
# joint: every finite configuration supported in [-a, a], center = bit a
res=[]
for a in range(2,9):
    n=2*a+1; best=0
    for X in range(1,1<<n):
        best=max(best,longest_alternation(X,a))
    res.append((n,best))
    print(f"joint facets, support width {n:2d}: longest alternating stretch of the center column {best}",flush=True)
# real facet alone: ZBL starts of width W keep column -1 black at even times for 2W+8-ish steps (death table)
for W in range(3,18,2):
    best=0
    for X in range(1<<(W-1),1<<W):
        t=0;Y=X
        while (Y&1) and t<400: Y=Z(Z(Y)); t+=2
        best=max(best,t)
    print(f"real facet alone (left half, width {W:2d}): constraint survives {best} steps")
