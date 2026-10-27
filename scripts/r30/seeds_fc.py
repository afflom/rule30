import numpy as np, itertools, random
from seeds_ep import evolve_seed, col_ep, A
def fc_check(monos,seed,p,r=2,T=3000,K=512):
    w=seed.bit_length(); rows,mid=evolve_seed(monos,r,T,seed,w)
    J=r*T
    ys=[(rows[t]>>(mid-r*t))&((1<<J)-1) for t in range(T+1)]
    def E(j,t): return (ys[T-K+((t-(T-K))%K)]>>j)&1
    # settled depth bound: depths whose last change is before T-K (check K-periodicity over last K)
    stable=~(ys[T]^ys[T-K]) & ~(ys[T-1]^ys[T-1-K])
    out=[]
    for t in range(T//3, int(0.45*T), (int(0.45*T)-T//3)//6):
        cen=r*t+p
        dam=[j for j in range(cen+20) if ((ys[t]>>j)&1)!=E(j,t)]
        out.append(None if not dam else dam[0]-cen)
    return out
# rerun search compactly
random.seed(2); B=A[:]; random.shuffle(B)
cases={}
T=800; n=0
for monos in B:
    if not any(len(m)>=2 for m in monos): continue
    rows,mid=evolve_seed(monos,2,T,1,1)
    if col_ep(rows,mid,T) is not None: continue
    n+=1
    for seed in range(1,256,2):
        w=seed.bit_length(); rows,mid=evolve_seed(monos,2,T,seed,w)
        for p in range(w):
            if col_ep(rows,mid+p,T) is not None:
                cases.setdefault(tuple(monos),[]).append((seed,p)); break
    if n>=40: break
viol=0; tot=0
for monos,lst in cases.items():
    for seed,p in lst[:3]:
        r=fc_check(list(monos),seed,p); tot+=1
        bad=[x for x in r if x is not None and x<0]
        if bad: viol+=1; print("damage LEFT of EP column:",monos,bin(seed),p,r)
print("cases",tot,"violations",viol)
