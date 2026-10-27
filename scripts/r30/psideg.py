import itertools, sys
from nss import tables, in_span
for W in range(2,int(sys.argv[1])+1,2):
    T,m,ds=tables(W); n=1<<m; ONE=(1<<n)-1
    common=ONE; need=None
    for i,t in enumerate(T):
        common&=~t
        if common==0: need=i+1; break
    C=T[:need+4]                                     # the conditions in use (a few beyond the first sufficient set)
    res=None
    for r in range(1,len(C)+1):
        vecs=[]
        for size in range(1,r+1):
            for S in itertools.combinations(range(len(C)),size):
                v=ONE
                for i in S: v&=C[i]
                vecs.append(v)
        if in_span(ONE,vecs): res=r; break
    print(f"W={W:2d}: least degree r of a polynomial P in the conditions with P(psi) = 1 identically and P(0) = 0: {res}  (conditions used {len(C)})",flush=True)
