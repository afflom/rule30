import numpy as np
from scipy.optimize import linprog
from zbl import Z
D=8
def feats(X):
    b=[(X>>i)&1 for i in range(X.bit_length()+D+1)]; f=[1.0]
    for p in (0,1):
        for d in range(D+1):
            f.append(sum(b[k]*b[k+d] for k in range(p,len(b)-d,2)))
    return f
def data(lo,hi):
    dec=set(); pos=set()
    for X in range(1<<(lo-1) if lo>1 else 1,1<<hi):
        if not X&1: continue
        cur=X
        while True:
            nxt=Z(Z(cur)); pos.add(cur)
            if not nxt&1: break
            dec.add((cur,nxt)); cur=nxt
    F={s:np.array(feats(s)) for s in pos|{b for _,b in dec}}
    return np.array([F[a]-F[b] for a,b in dec]), np.array([F[p] for p in pos])
A,P=data(1,15); At,Pt=data(16,18)
n=A.shape[1]
r=linprog(np.zeros(n),A_ub=np.vstack([-A,-P]),b_ub=np.concatenate([-np.ones(len(A)),np.zeros(len(P))]),bounds=[(None,None)]*n,method="highs")
print(f"translation-invariant quadratic ranking (pair counts at gaps 0..{D}, by parity, + constant), widths<=15: feasible = {r.status==0}")
if r.status==0:
    w=r.x; print("  out-of-sample widths 16-18: failing steps",(At@w<1-1e-6).sum(),"of",len(At),"; negative states",(Pt@w<-1e-6).sum(),"of",len(Pt))
