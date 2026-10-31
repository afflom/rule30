# Additive invariants of the sideways left-system map on time cylinders Z/P:
# (a,b) -> (b,c), c(phi+1) = a(phi) ^ (b(phi) | c(phi)), unique when b != 0.
import numpy as np, itertools, random, sys
def side(a,b):
    P=len(a); i=b.index(1); c=[None]*P
    c[(i+1)%P]=a[i]^1
    for s in range(1,P):
        ph=(i+s)%P; c[(ph+1)%P]=a[ph]^(b[ph]|c[ph])
    return c
def win(a,b,m):
    P=len(a); return [sum((a[(i+j)%P]<<(2*j))|(b[(i+j)%P]<<(2*j+1)) for j in range(m)) for i in range(P)]
def rank_mod2(rows):
    basis=[]
    for r in rows:
        for bb in basis: r=min(r,r^bb)
        if r: basis.append(r)
    return len(basis)
random.seed(1)
for m in range(1,5):
    nv=4**m; EQ=[]; EF=[]
    for P in range(m,m+8):
        states=itertools.product([0,1],repeat=2*P) if 2*P<=14 else ([random.getrandbits(1) for _ in range(2*P)] for _ in range(6000))
        for s in states:
            a=list(s[:P]); b=list(s[P:])
            if 1 not in b: continue
            c=side(a,b)
            v=np.zeros(nv,int)
            for w in win(a,b,m): v[w]+=1
            for w in win(b,c,m): v[w]-=1
            EQ.append(v); EF.append(sum(1<<i for i in range(nv) if v[i]%2))
    rQ=np.linalg.matrix_rank(np.array(EQ,float)); rF=rank_mod2(EF)
    # trivial: coboundaries in phi (functions of m-1 columns: 4^(m-1)) plus "j-coboundaries" h(b-window)-h(a-window)? count reported raw
    print(f"m={m}: solution dim over Q {nv-rQ}, over F2 {nv-rF}; phi-coboundary+const dim {4**(m-1)}"); sys.stdout.flush()
