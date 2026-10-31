# Which elementary rules have an eventually periodic single-seed center column, and which invariants
# separate the rest?  (Data: period <= 2048 within 8192 steps.)
import numpy as np, itertools
T=8192
def center(rule):
    tab=[(rule>>i)&1 for i in range(8)]
    W=2*T+3; mid=T+1; x=np.zeros(W,np.uint8); x[mid]=1; c=np.zeros(T,np.uint8)
    for t in range(T):
        c[t]=x[mid]
        l=np.roll(x,1); r=np.roll(x,-1)
        idx=(l.astype(np.uint8)<<2)|(x<<1)|r
        x=np.array(tab,np.uint8)[idx]
        if tab[0]==1: pass
    return c
def ep(c):
    n=len(c)
    for P in range(1,2049):
        neq=np.nonzero(c[:-P]!=c[P:])[0]; tau=0 if len(neq)==0 else int(neq[-1])+1
        if tau<=n//2: return P
    return None
def anf(rule):
    tab=[(rule>>i)&1 for i in range(8)]; a=tab[:]
    for i in range(3):
        for m in range(8):
            if m>>i&1: a[m]^=a[m^(1<<i)]
    return [m for m in range(8) if a[m]]          # monomials over bits (r=1, c=2, l=4)
def invariants(rule):
    tab=[(rule>>i)&1 for i in range(8)]
    lp=all(tab[m]!=tab[m^4] for m in range(4))
    rp=all(tab[m]!=tab[m^1] for m in range(8) if not m&1)
    mons=anf(rule); deg=max((bin(m).count('1') for m in mons),default=0)
    return dict(weight=sum(tab),leftperm=lp,rightperm=rp,degree=deg,monomials=len(mons),quiescent=tab[0]==0)
res={}
for rule in range(256):
    tab0=(rule&1)
    if tab0: continue                                  # quiescent rules only (white background stays white)
    res[rule]=ep(center(rule))
aper=[r for r,p in res.items() if p is None]
print("quiescent rules with no eventual period <= 2048 in 8192 steps:",aper)
for r in aper: print(r, invariants(r), "ANF monomials:",anf(r))
# rules sharing rule 30's invariants but with periodic center
inv30=invariants(30)
same=[r for r in res if invariants(r)==inv30]
print("rules with exactly rule 30's invariants (weight, permutivity, degree, #monomials):",[(r,res[r]) for r in same])
