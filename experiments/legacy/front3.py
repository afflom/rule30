import numpy as np, itertools, random, sys
from front import front
from extrapolate import center_ep, symmetric
off=[-1,0,1,2]; mons=[(i,) for i in range(4)]+list(itertools.combinations(range(4),2))
A=[[(-2,)]+[tuple(off[i] for i in mons[k]) for k in range(10) if code>>k&1] for code in range(1,1<<10)]
random.seed(7); cells=[-1,0,1,2]
allm=[(o,) for o in cells]+list(itertools.combinations(cells,2))+list(itertools.combinations(cells,3))
C=[[(-2,)]+[m for m in allm if random.random()<0.35] for _ in range(400)]
for name,fam in [("A: radius-2 left-permutive deg<=2 (all 1023)",A),("C': radius-2 left-permutive deg<=3 (400, seed 7)",C)]:
    stats={'EPin':0,'EPout':[], 'EPunres':0,'APin':[],'APout':0,'APunres':0,'sym':0}
    for monos in fam:
        offs=set(o for m in monos for o in m)
        if max(offs)<=0 or not any(len(m)>=2 for m in monos): continue
        if symmetric(monos): stats['sym']+=1; continue
        f,ys,rows,mid=front(monos,2,T=3000)
        p=center_ep(rows,mid) is not None
        if f is None: stats['EPunres' if p else 'APunres']+=1
        elif p:
            if f[0]<=1: stats['EPin']+=1
            else: stats['EPout'].append((f,monos))
        else:
            if f[0]<=1: stats['APin'].append((f,monos))
            else: stats['APout']+=1
    print(name); print("  EP center: inside(lag<=1)",stats['EPin'],"outside",len(stats['EPout']),"unresolved",stats['EPunres'])
    for o in stats['EPout'][:8]: print("     EP outside:",o)
    print("  aperiodic: outside",stats['APout'],"inside",len(stats['APin']),"unresolved",stats['APunres'], " symmetric skipped",stats['sym'])
    for o in stats['APin'][:8]: print("     AP inside:",o)
    sys.stdout.flush()
