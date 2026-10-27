# Additive invariants of rule 30: f on k-windows with sum_p f(x[p..p+k-1]) conserved on cyclic configurations.
import numpy as np, itertools, sys
def step(x):
    n=len(x); return [x[(i-1)%n]^(x[i]|x[(i+1)%n]) for i in range(n)]
def windows(x,k):
    n=len(x); return [sum(x[(i+j)%n]<<j for j in range(k)) for i in range(n)]
def rank_mod2(rows):
    rows=[int(r) for r in rows]; basis=[]
    for r in rows:
        for b in basis: r=min(r,r^b)
        if r: basis.append(r)
    return len(basis)
for k in range(1,9):
    nv=2**k; eqQ=[]; eqF=[]
    for n in range(k,k+7):
        for xs in itertools.product([0,1],repeat=n):
            x=list(xs); y=step(x)
            v=np.zeros(nv,int)
            for w in windows(x,k): v[w]+=1
            for w in windows(y,k): v[w]-=1
            eqQ.append(v); eqF.append(sum(1<<i for i in range(nv) if v[i]%2))
        if n>=k+6 or len(eqQ)>60000: break
    A=np.array(eqQ,float)
    rQ=np.linalg.matrix_rank(A) ; rF=rank_mod2(eqF)
    # trivial invariants: constants (1) + coboundaries g(w)-g(w shifted): dim = 2^(k-1) (functions of k-1 cells) -> total trivial = 2^(k-1)
    triv=2**(k-1)
    print(f"k={k}: invariants over Q {nv-rQ} (trivial {triv}); over F2 {nv-rF} (trivial {triv})"); sys.stdout.flush()
