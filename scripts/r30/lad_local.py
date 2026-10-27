# Nonlinear activity near an eventually periodic column (finite seeds, chaotic radius-2 rules),
# compared with rule 30 near its center.
import numpy as np, itertools, random
from seeds_ep import evolve_seed, col_ep, A
def activity_near(monos,r,seed,p,T=2000,half=40):
    w=seed.bit_length(); rows,mid=evolve_seed(monos,r,T,seed,w)
    sh=lambda v,o: v>>o if o>0 else v<<(-o)
    nl=[m for m in monos if len(m)>=2]; M=(1<<(rows[0].bit_length()+4*r*T))-1
    tot=0; cnt=0
    for t in range(T//2,T):
        x=rows[t]; act=0
        for m in nl:
            term=-1
            for o in m: term&=sh(x,o)
            act|=term
        lo=mid+p-half; win=((1<<(2*half+1))-1)<<lo
        cnt+=bin(act&win).count('1'); tot+=2*half+1
    return cnt/tot, col_ep(rows,mid+p,T)
random.seed(2); B=A[:]; random.shuffle(B)
res=[]; n=0
for monos in B:
    if not any(len(m)>=2 for m in monos): continue
    rows,mid=evolve_seed(monos,2,800,1,1)
    if col_ep(rows,mid,800) is not None: continue
    n+=1
    for seed in range(1,256,2):
        w=seed.bit_length(); rows,mid=evolve_seed(monos,2,800,seed,w)
        for p in range(w):
            if col_ep(rows,mid+p,800) is not None:
                a,P=activity_near(monos,2,seed,p)
                res.append((a,P,monos,bin(seed),p)); break
        if len(res)>=40: break
    if n>=40 or len(res)>=40: break
res.sort()
print("EP columns found:",len(res))
print("activity within 40 cells of the EP column: min %.4f median %.4f max %.4f"%(res[0][0],res[len(res)//2][0],res[-1][0]))
for x in res[-5:]: print("  highest:",round(x[0],4),"period",x[1],x[2],x[3],"col",x[4])
# rule 30 near its center
r30=[(-1,),(0,),(1,),(0,1)]
rows,mid=evolve_seed(r30,1,2000,1,1)
sh=lambda v,o: v>>o if o>0 else v<<(-o)
cnt=tot=0
for t in range(1000,2000):
    x=rows[t]; act=x&sh(x,1); win=((1<<81)-1)<<(mid-40)
    cnt+=bin(act&win).count('1'); tot+=81
print("rule 30 activity within 40 cells of the center: %.4f"%(cnt/tot))
