# Edge principle: does nonlinear activity generated at the left edge (depth <= t/4 from the left edge)
# forbid an eventually periodic center?  Test on families with and without permutivity.
import numpy as np, itertools, random
from extrapolate import evolve, center_ep, symmetric
def edge_density(monos,r,T):
    rows,mid,M=evolve(monos,r,T); sh=lambda v,o: v>>o if o>0 else v<<(-o)
    nl=[m for m in monos if len(m)>=2]; num=den=0
    for t in range(T//2,T):
        x=rows[t]; act=0
        for m in nl:
            term=M
            for o in m: term&=sh(x,o)
            act|=term
        if x==0: continue
        # left edge = lowest set bit of the row
        e=(x&-x).bit_length()-1; w=max(1,t//4)
        win=((1<<w)-1)<<e
        num+=bin(act&win).count('1'); den+=w
    return num/max(den,1)
def study(name,rules,r,T=600):
    out=[]
    for monos in rules:
        offs=set(o for m in monos for o in m)
        if not offs or min(offs)>=0 or max(offs)<=0 or not any(len(m)>=2 for m in monos): continue
        rows,mid,M=evolve(monos,r,2*T)
        if rows[-1]==0 or rows[-1]==((1<<(2*mid+1))-1): continue
        p=center_ep(rows,mid) is not None
        d1=edge_density(monos,r,T//2); d2=edge_density(monos,r,T)
        out.append((p,symmetric(monos),d1,d2,monos))
    P=[o for o in out if o[0] and not o[1]]
    pos=[o for o in P if o[3]>0.05 and o[3]>0.85*o[2]]
    A=[o for o in out if not o[0]]
    print(f"{name}: {len(out)} rules; periodic non-symmetric {len(P)}; of these with persistent edge activity: {len(pos)}")
    for o in pos[:6]: print("    ",round(o[2],3),round(o[3],3),o[4])
    print(f"   aperiodic {len(A)}: with persistent edge activity {sum(1 for o in A if o[3]>0.05 and o[3]>0.85*o[2])}")
B=[]
for rule in range(0,256,2):
    tab=[(rule>>i)&1 for i in range(8)]; a=tab[:]
    for i in range(3):
        for m in range(8):
            if m>>i&1: a[m]^=a[m^(1<<i)]
    B.append([tuple(o for o,bit in zip((1,0,-1),(1,2,4)) if m&bit) for m in range(1,8) if a[m]])
study("radius-1 quiescent (all)",B,1)
random.seed(11); cells5=[-2,-1,0,1,2]
allm5=[(o,) for o in cells5]+list(itertools.combinations(cells5,2))+list(itertools.combinations(cells5,3))
D=[[m for m in allm5 if random.random()<0.25] for _ in range(400)]
study("radius-2 general, degree <= 3 (random 400)",D,2)
