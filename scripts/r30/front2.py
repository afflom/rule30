import numpy as np, itertools, random
from front import front
from extrapolate import evolve, center_ep, symmetric
random.seed(1); C=[]
cells=[-1,0,1,2]
allm=[(o,) for o in cells]+list(itertools.combinations(cells,2))+list(itertools.combinations(cells,3))
for _ in range(150): C.append([(-2,)]+[m for m in allm if random.random()<0.35])
for monos in C:
    offs=set(o for m in monos for o in m)
    if not offs or min(offs)>=0 or max(offs)<=0 or not any(len(m)>=2 for m in monos): continue
    f,ys,rows,mid=front(monos,2)
    p=center_ep(rows,mid)
    if f is not None and ((p is not None and f[0]>0) or (p is None and f[0]<=0)):
        print("EP" if p else "AP", p, f, monos)
# long run of the aperiodic-inside rule
m=[(-2,), (-1,), (2,), (0, 2), (1, 2), (0, 1, 2)]
rows,mid,M=evolve(m,2,24000)
c=[(v>>mid)&1 for v in rows]
print("long center EP:",center_ep(rows,mid))
