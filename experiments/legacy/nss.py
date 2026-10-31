import numpy as np, itertools, sys
from anf import forced, U
def tables(W):
    N=min(63,2*W+21); Y,m=forced(W,N)
    ds=[d for d in range(W+1 if W%2==0 else W+2, N+1, 2)]
    T=[int(''.join(map(str,((Y>>U(d-1))&U(1)).astype(np.uint8)[::-1])),2) for d in ds]
    return T,m,ds
def in_span(target,vecs):
    basis={}
    for v in vecs:
        while v:
            h=v.bit_length()-1
            if h in basis: v^=basis[h]
            else: basis[h]=v; break
    t=target
    while t:
        h=t.bit_length()-1
        if h not in basis: return False
        t^=basis[h]
    return True
for W in range(int(sys.argv[2]) if len(sys.argv)>2 else 2,int(sys.argv[1])+1,2):
    T,m,ds=tables(W); n=1<<m; ONE=(1<<n)-1
    mono=lambda S: sum(1<<x for x in range(n) if (x&S)==S)        # indicator of e containing S
    res=None
    for k in range(0,m+1):
        Ss=[sum(1<<i for i in c) for r in range(k+1) for c in itertools.combinations(range(m),r)]
        vecs=[mono(S)&t for S in Ss for t in T]
        if in_span(ONE,vecs): res=k; break
    # how many conditions are needed at all (shortest prefix with no common zero)
    common=ONE; need=None
    for i,t in enumerate(T):
        common&=~t
        if common==0: need=i+1; break
    print(f"W={W:2d} (m={m:2d} variables): conditions needed {need} (through depth {ds[need-1]}); "
          f"least multiplier degree k with 1 = sum g_d psi_d, deg g_d <= k: {res}")
