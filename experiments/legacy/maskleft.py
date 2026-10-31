# Driven left half by periodic u: is column -1 eventually periodic on the residues where u = 1?
import numpy as np, itertools
def colm1(u,T):
    y=1; w=[]
    for t in range(T):
        # left half bits 0..t, center bit t; column -1 = bit t-1
        w.append((y>>(t-1))&1 if t>=1 else 0)
        n=((y<<2)^((y<<1)|y)) & ((1<<(t+1))-1)
        y=n|(u(t+1)<<(t+1))
    return np.array(w,dtype=np.uint8)
def ep(seq,maxp=512):
    n=len(seq); tail=seq[n//2:]
    for p in range(1,maxp):
        if len(tail)>3*p and np.array_equal(tail[p:],tail[:-p]): return p
    return None
T=12000
for P in range(1,7):
    for bits in itertools.product([0,1],repeat=P):
        if sum(bits)==0: continue
        # skip non-primitive words
        if any(P%d==0 and bits==bits[:d]*(P//d) for d in range(1,P)): continue
        u=lambda t,b=bits:b[t%len(b)]
        w=colm1(u,T)
        res=[]
        for r in range(P):
            if bits[r]: res.append(ep(w[r::P]))
        print(P,''.join(map(str,bits)),"periods on u=1 residues:",res)
