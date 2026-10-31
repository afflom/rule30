import sys
from ring import cycles
from zbl import Z
K=int(sys.argv[2]); Lmax=int(sys.argv[1]); Pmax=int(sys.argv[3])
def build(prefix,L,w,P,D):
    X=prefix
    for i in range(L,D): X|=((w>>((i-L)%P))&1)<<i
    return X
def life(X,K):
    for k in range(K+1):
        if not X&1: return 2*k
        X=Z(Z(X))
    return None
for P in range(1,Pmax+1):
    for key,Lc,cyc in cycles(P):
        best=(-1,None); surv=0
        for ph in sorted(set([0,1%Lc])):
            w=cyc[ph]; D=2*K+Lmax+P+8; mask=(1<<D)-1
            for L in range(0,Lmax+1):
                for pre in range(1<<L):
                    X=build(pre,L,w,P,D)
                    r=life(X,K)
                    if r is None: surv+=1; continue
                    if r>best[0]: best=(r,(ph,L,pre))
        bg=format(key,'0%db'%P)[::-1]
        print(f"P={P:2d} background {bg:16s} cycle {Lc:5d}: survivors to time {2*K}: {surv:6d}   longest finite life {best[0]}",flush=True)
