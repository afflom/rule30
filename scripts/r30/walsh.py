import numpy as np, sys
from anf import forced, U
from math import comb
for W in range(4,int(sys.argv[1])+1,2):
    N=min(63,2*W+21); Y,m=forced(W,N)
    ds=[d for d in range(W+1 if W%2==0 else W+2, N+1, 2)][:12]
    S=np.array([((Y>>U(d-1))&U(1)).astype(np.int64) for d in ds])      # conditions psi_d(e), shape (n, 2^m)
    n=len(ds); sgn=1-2*S                                                 # (-1)^psi
    # graded signed count: G(j) = 2^-m * sum_{|T|=j} sum_e (-1)^{psi_T(e)}  ;  sum_j G(j) = 2^n * #common zeros / 2^m
    prod=np.ones((1,1<<m),dtype=np.int64); G=np.zeros(n+1)
    # dynamic programming over conditions: poly in a formal variable u marking |T|
    poly=[np.ones(1<<m,dtype=np.int64)]                                  # poly[j][e] = sum_{|T|=j} (-1)^{psi_T(e)}
    for i in range(n):
        new=[np.zeros(1<<m,dtype=np.int64) for _ in range(len(poly)+1)]
        for j,p in enumerate(poly): new[j]+=p; new[j+1]+=p*sgn[i]
        poly=new
    G=[int(p.sum()) for p in poly]
    zeros=sum(G)//(1<<n)
    print(f"W={W:2d}: 2^m*G(j) for j=0..{n}: {G}   -> common zeros {zeros}")
