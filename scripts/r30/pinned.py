import numpy as np
from extrapolate import evolve
def analyze(monos,r,T=3000,K=512,show=12):
    rows,mid,M=evolve(monos,r,T)
    J=r*T+r*T//2
    ys=[(rows[t]>>(mid-r*t))&((1<<J)-1) for t in range(T+1)]
    # ether pattern from the last K rows (periods divide K for depths that have settled)
    E=lambda j,t: (ys[T-K+((t-(T-K))%K)]>>j)&1
    out=[]
    for t in range(T-K-show*40,T-K,40):
        dam=[j for j in range(0,min(J,r*t+40)) if ((ys[t]>>j)&1)!=E(j,t)]
        e=dam[0] if dam else None
        out.append((t, None if e is None else e-r*t, len(dam)))
    return out
for m in [[(-2,),(-1,),(0,),(-1,1)], [(-2,),(-1,),(-1,0),(1,2),(-1,0,1),(-1,0,2)], [(-2,),(-1,),(1,),(-1,2),(0,2),(1,2),(-1,0,1),(-1,1,2),(0,1,2)]]:
    print(m)
    for o in analyze(m,2): print("   t",o[0],"edge - center",o[1],"damaged cells left of center+40:",o[2])
