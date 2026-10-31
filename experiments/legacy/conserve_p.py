# Additive invariants of rule 30 over GF(p), p = 3, 5, 7 (forward time), windows k <= 7.
import itertools, sys
import numpy as np
def step(x):
    n=len(x); return [x[(i-1)%n]^(x[i]|x[(i+1)%n]) for i in range(n)]
def windows(x,k):
    n=len(x); return [sum(x[(i+j)%n]<<j for j in range(k)) for i in range(n)]
def rank_mod_p(A,p):
    A=[list(r) for r in A]; r=0; cols=len(A[0])
    for c in range(cols):
        piv=None
        for i in range(r,len(A)):
            if A[i][c]%p: piv=i; break
        if piv is None: continue
        A[r],A[piv]=A[piv],A[r]
        inv=pow(A[r][c],p-2,p)
        A[r]=[(v*inv)%p for v in A[r]]
        for i in range(len(A)):
            if i!=r and A[i][c]%p:
                f=A[i][c]; A[i]=[(a-f*b)%p for a,b in zip(A[i],A[r])]
        r+=1
    return r
for k in range(1,7):
    nv=2**k; rows=set()
    for n in range(k,k+7):
        for xs in itertools.product([0,1],repeat=n):
            x=list(xs); y=step(x); v=[0]*nv
            for w in windows(x,k): v[w]+=1
            for w in windows(y,k): v[w]-=1
            rows.add(tuple(v))
    rows=list(rows)
    out=[]
    for p in (3,5,7):
        out.append((p, nv-rank_mod_p(rows,p)))
    print(f"k={k}: invariant dims {out}  (trivial {2**(k-1)})"); sys.stdout.flush()
