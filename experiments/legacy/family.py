# Radius-2, left-permutive, degree <= 2 rules: f = a + g(b,c,d,e) over F2, g(0)=0, deg g <= 2.
# Which have an eventually periodic single-seed center?  Which invariants of g decide it (data)?
import itertools, numpy as np, collections
T=2048
V=['b','c','d','e']; lin=[(i,) for i in range(4)]; quad=list(itertools.combinations(range(4),2))
mons=lin+quad
def run(code):
    # rows as ints, bit index = position + T + 2 ; neighbours a=x(p-2), b=x(p-1), c=x(p), d=x(p+1), e=x(p+2)
    mid=T+2; x=1<<mid; cen=[]
    for t in range(T):
        cen.append((x>>mid)&1)
        sh={0:x<<1, 1:x, 2:x>>1, 3:x>>2}          # b at p: x(p-1) -> x<<1 ; c: x ; d: x>>1 ; e: x>>2
        a=x<<2; y=a
        for k,m in enumerate(mons):
            if code>>k&1:
                term=sh[m[0]]
                for v in m[1:]: term&=sh[v]
                y^=term
        x=y & ((1<<(2*mid+3))-1)
    return np.array(cen,np.uint8)
def ep(c):
    n=len(c)
    for P in range(1,513):
        neq=np.nonzero(c[:-P]!=c[P:])[0]; tau=0 if len(neq)==0 else int(neq[-1])+1
        if tau<=n//2: return P
    return None
if __name__=="__main__":
    res={}
    for code in range(1,1<<len(mons)):
        res[code]=ep(run(code))
    aper=[c for c,p in res.items() if p is None]
    print(f"{len(res)} rules; no eventual period <= 512 in {T} steps: {len(aper)}")
    def desc(code):
        return '+'.join(''.join(V[i] for i in mons[k]) for k in range(len(mons)) if code>>k&1)
    by=collections.Counter()
    for c in aper:
        nl=sum(1 for k in range(4) if c>>k&1); nq=sum(1 for k in range(4,10) if c>>k&1)
        by[(nl,nq)]+=1
    tot=collections.Counter()
    for c in res:
        nl=sum(1 for k in range(4) if c>>k&1); nq=sum(1 for k in range(4,10) if c>>k&1); tot[(nl,nq)]+=1
    print("(linear terms, quadratic terms): aperiodic / total")
    for key in sorted(tot): print(key, by[key],'/',tot[key])
    print("aperiodic with exactly one quadratic term:",[desc(c) for c in aper if sum(1 for k in range(4,10) if c>>k&1)==1][:40])
