import numpy as np
from lp_rank2 import data, fit, K
A,P=[],[]
for lo,hi in [(1,12),(13,16)]:
    a,p=data(lo,hi); A.append(a); P.append(p)
A=np.vstack(A); P=np.vstack(P)
At,Pt=data(17,19)
k=np.arange(1,K+1,dtype=float)
for rr in [1.5,2.0,3.0]:
    Bm=np.column_stack([(k%2==1)*rr**k,(k%2==0)*rr**k,(k%2==1),(k%2==0),(k==1)]).astype(float)
    r=fit(A,P,Bm); th=r.x; w=Bm@th
    v1=(At@w<1-1e-6).sum(); v2=(Pt@w<-1e-6).sum()
    print(f"r={rr}: theta={np.round(th,4).tolist()}  out-of-sample widths 17-19: {v1} of {len(At)} steps fail, {v2} of {len(Pt)} states negative")
