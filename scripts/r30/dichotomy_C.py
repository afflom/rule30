# Left-activity dichotomy on a second family: random radius-2 left-permutive rules with terms up to degree 3.
import numpy as np, itertools, random
from extrapolate import evolve, center_ep, symmetric
def left_density(monos,T):
    rows,mid,M=evolve(monos,2,T); sh=lambda v,o: v>>o if o>0 else v<<(-o)
    nl=[m for m in monos if len(m)>=2]; num=den=0
    for t in range(T//2,T):
        x=rows[t]; act=0
        for m in nl:
            term=M
            for o in m: term&=sh(x,o)
            act|=term
        lo=mid-2*t; win=((1<<(mid-lo))-1)<<lo
        num+=bin(act&win).count('1'); den+=mid-lo
    return num/den
random.seed(7); cells=[-1,0,1,2]
allm=[(o,) for o in cells]+list(itertools.combinations(cells,2))+list(itertools.combinations(cells,3))
out=[]
for _ in range(300):
    monos=[(-2,)]+[m for m in allm if random.random()<0.35]
    offs=set(o for m in monos for o in m)
    if max(offs)<=0 or not any(len(m)>=2 for m in monos): continue
    rows,mid,M=evolve(monos,2,1200)
    periodic=center_ep(rows,mid) is not None
    d1=left_density(monos,300); d2=left_density(monos,600)
    out.append((periodic,symmetric(monos),d1,d2,monos))
P=[o for o in out if o[0] and not o[1]]; A=[o for o in out if not o[0]]
thin=lambda o: o[3]<0.03 or o[3]<0.85*o[2]          # density small or falling with T
print(f"{len(out)} nonlinear rules: periodic non-symmetric {len(P)}, aperiodic {len(A)}")
print(f"  periodic non-symmetric with thinning left activity: {sum(thin(o) for o in P)}/{len(P)}")
bad=[o for o in P if not thin(o)]
print("  exceptions:",[(round(o[2],3),round(o[3],3),o[4]) for o in bad][:5])
print(f"  aperiodic with thinning left activity: {sum(thin(o) for o in A)}/{len(A)}")
