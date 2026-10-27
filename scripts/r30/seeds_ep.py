# Chaotic-zero-state rules: do any finite seeds give an EP column inside the seed span?
import numpy as np, itertools, random, sys
from extrapolate import center_ep
def evolve_seed(monos,r,T,seed,w):
    mid=r*T+4; M=(1<<(2*mid+w+1))-1; x=seed<<mid; rows=[x]
    sh=lambda v,o: v>>o if o>0 else v<<(-o)
    for t in range(T):
        y=0
        for m in monos:
            term=M
            for o in m: term&=sh(x,o)
            y^=term
        x=y&M; rows.append(x)
    return rows,mid
def col_ep(rows,pos,n):
    c=np.array([(v>>pos)&1 for v in rows],np.uint8)
    for P in range(1,n//4):
        neq=np.nonzero(c[:-P]!=c[P:])[0]; tau=0 if len(neq)==0 else int(neq[-1])+1
        if tau<=n//2: return P
    return None
off=[-1,0,1,2]; mons=[(i,) for i in range(4)]+list(itertools.combinations(range(4),2))
A=[[(-2,)]+[tuple(off[i] for i in mons[k]) for k in range(10) if code>>k&1] for code in range(1,1<<10)]
random.seed(2); random.shuffle(A)
found=[]; tested=0
T=800
for monos in A:
    if not any(len(m)>=2 for m in monos): continue
    rows,mid=evolve_seed(monos,2,T,1,1)
    if col_ep(rows,mid,T) is not None: continue        # want chaotic single-seed centers
    # chaotic left activity check: skip
    tested+=1
    for seed in range(1,256,2):
        w=seed.bit_length()
        rows,mid=evolve_seed(monos,2,T,seed,w)
        for p in range(w):
            P=col_ep(rows,mid+p,T)
            if P is not None: found.append((monos,bin(seed),p,P))
    if tested>=40: break
print("rules tested",tested,"EP columns found",len(found))
for f in found[:20]: print(f)
