import numpy as np, sys
U=np.uint64
def Zv(X): return (X>>U(1)) ^ (X | (X<<U(1)))
def forced(W,N):
    """all points of InX with even-depth bits e_2..e_W free, zero beyond W; returns rows (uint64) and m"""
    evens=list(range(2,W+1,2)); m=len(evens); idx=np.arange(1<<m,dtype=np.uint64)
    Y=np.zeros(1<<m,dtype=np.uint64)
    for i,d in enumerate(evens): Y|=((idx>>U(i))&U(1))<<U(d-1)
    for t in range(0,N,2):                       # odd depth d=t+1 is fixed by the constraint at time t
        X=Y.copy()
        for _ in range(t): X=Zv(X)
        Y|=((X&U(1))^U(1))<<U(t)                 # set depth t+1 black iff column -1 would be white
    return Y,m
def anf(tt,m):                                   # Moebius transform over F2
    a=tt.astype(np.uint8).copy()
    for i in range(m):
        a=a.reshape(-1,2,1<<i); a[:,1,:]^=a[:,0,:]; a=a.reshape(-1)
    return a
def show(c,m,names):
    terms=[]
    for mono in np.nonzero(c)[0]:
        vs=[names[i] for i in range(m) if (mono>>i)&1]
        terms.append('·'.join(vs) if vs else '1')
    return ' + '.join(terms[:8])+(' + …' if len(terms)>8 else '')
if __name__=="__main__":
    W=int(sys.argv[1]); N=min(63,2*W+21)
    Y,m=forced(W,N); names=[f"e{d}" for d in range(2,W+1,2)]
    print(f"W={W}: {1<<m} points, odd depths beyond W as F2 polynomials in {', '.join(names)}")
    for d in range(W+1 if W%2==0 else W+2, N+1, 2):
        tt=((Y>>U(d-1))&U(1)).astype(np.uint8)
        c=anf(tt,m); deg=max((bin(i).count('1') for i in np.nonzero(c)[0]),default=-1)
        lin=[names[i] for i in range(m) if c[1<<i] and all(not c[j] or j==(1<<i) or not (j>>i)&1 for j in np.nonzero(c)[0])]
        print(f"  depth {d:2d}: degree {deg:2d}, terms {int(c.sum()):4d}, ones {int(tt.sum()):4d}  | {show(c,m,names)}")
