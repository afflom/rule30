# Test the coupling invariant beyond the family: general radius-r quiescent rules given by ANF.
import numpy as np, itertools, random
def make(r, monos):                       # monos: tuples of offsets in [-r, r]
    return monos
def evolve(monos, r, T):
    mid=r*T+4; M=(1<<(2*mid+1))-1; x=1<<mid; rows=[x]
    sh=lambda v,o: v>>o if o>0 else v<<(-o)
    for t in range(T):
        y=0
        for m in monos:
            term=M
            for o in m: term&=sh(x,o)
            y^=term
        x=y&M; rows.append(x)
    return rows, mid, M
def center_ep(rows,mid):
    c=np.array([(v>>mid)&1 for v in rows],np.uint8); n=len(c)
    for P in range(1,n//4):
        neq=np.nonzero(c[:-P]!=c[P:])[0]; tau=0 if len(neq)==0 else int(neq[-1])+1
        if tau<=n//2: return P
    return None
def coupling(rows,mid,M,lin,r,k,lo_off,hi_off):
    sh=lambda v,o: v>>o if o>0 else v<<(-o)
    h=1<<k; T=len(rows)-1; num=den=cn=cd=0
    for s in range(T//3,T-h,max(1,(T-h-T//3)//150)):
        L=0
        for o in lin: L^=sh(rows[s],o*h)
        E=(rows[s+h]^L)&M
        lo=mid+lo_off*(s+h); hi=mid+hi_off*(s+h)
        if hi<lo: continue
        win=((1<<(hi-lo+1))-1)<<lo
        num+=bin(E&win).count('1'); den+=hi-lo+1; cn+=(E>>mid)&1; cd+=1
    return num/max(den,1), cn/max(cd,1)
def symmetric(monos):
    s=set(tuple(sorted(m)) for m in monos); return s==set(tuple(sorted(-o for o in m)) for m in monos)
def study(name, rules, r, T=1200):
    rows_out=[]
    for monos in rules:
        offs=set(o for m in monos for o in m)
        if not offs or min(offs)>=0 or max(offs)<=0: continue        # center must be interior to the cone
        rows,mid,M=evolve(monos,r,T)
        lin=[m[0] for m in monos if len(m)==1]
        lo_off=min(offs); hi_off=max(offs)
        gc,gz=coupling(rows,mid,M,lin,r,4,lo_off,hi_off)
        rows_out.append((center_ep(rows,mid) is None, gc, gz, symmetric(monos), monos))
    A=[x for x in rows_out if x[0]]; P=[x for x in rows_out if not x[0]]
    Pn=[x for x in P if not x[3]]
    print(f"{name}: {len(rows_out)} rules (aperiodic {len(A)}, periodic {len(P)})")
    print(f"   periodic, not symmetric: max cone coupling {max([x[1] for x in Pn],default=0):.3f}, max center coupling {max([x[2] for x in Pn],default=0):.3f}")
    print(f"   aperiodic: fraction with cone coupling > 0.26: {np.mean([x[1]>0.26 for x in A]):.3f}")
    hi=[x for x in Pn if x[1]>0.26]
    print(f"   periodic non-symmetric rules above 0.26: {len(hi)}", [x[4] for x in hi[:5]])
    return rows_out
# family B: all quiescent radius-1 rules, from their ANF
B=[]
for rule in range(0,256,2):
    tab=[(rule>>i)&1 for i in range(8)]; a=tab[:]
    for i in range(3):
        for m in range(8):
            if m>>i&1: a[m]^=a[m^(1<<i)]
    monos=[tuple(o for o,bit in zip((1,0,-1),(1,2,4)) if m&bit) for m in range(1,8) if a[m]]
    # bit0 = right cell (offset +1 -> x>>1), bit1 = center, bit2 = left (offset -1)
    B.append(monos)
study("radius-1 quiescent rules",B,1)
# family C: random radius-2 left-permutive rules with up to cubic terms
random.seed(1); C=[]
cells=[-1,0,1,2]
allm=[(o,) for o in cells]+list(itertools.combinations(cells,2))+list(itertools.combinations(cells,3))
for _ in range(400):
    pick=[m for m in allm if random.random()<0.35]
    C.append([(-2,)]+pick)
study("radius-2 left-permutive, degree <= 3 (random 400)",C,2)
# family D: random radius-2 rules with no permutivity requirement, degree <= 3
D=[]
cells5=[-2,-1,0,1,2]
allm5=[(o,) for o in cells5]+list(itertools.combinations(cells5,2))+list(itertools.combinations(cells5,3))
for _ in range(400): D.append([m for m in allm5 if random.random()<0.25])
study("radius-2 general, degree <= 3 (random 400)",D,2)
