import numpy as np
from family import mons, ep, V, run
T=512
def orbit(code):
    mid=T+2; x=1<<mid; rows=[]; M=(1<<(2*mid+3))-1
    for t in range(T):
        rows.append(x); sh={0:x<<1,1:x,2:x>>1,3:x>>2}; y=x<<2
        for k,m in enumerate(mons):
            if code>>k&1:
                term=sh[m[0]]
                for v in m[1:]: term&=sh[v]
                y^=term
        x=y&M
    return rows
def desc(code): return 'a'+''.join('+'+''.join(V[i] for i in mons[k]) for k in range(10) if code>>k&1)
lin={c:orbit(c) for c in range(16)}
if __name__=="__main__":
    nonlin=[c for c in range(1,1<<10) if c>>4]
    ep_nl=[c for c in nonlin if ep(run(c))]                 # 2048-step classification, P <= 512, tau <= 1024
    match=[c for c in ep_nl if orbit(c) in lin.values()]
    other=[c for c in ep_nl if c not in match]
    print(f"nonlinear rules: {len(nonlin)}; eventually periodic center: {len(ep_nl)}")
    print(f"  seed orbit identical to a linear rule's orbit: {len(match)}")
    print(f"  not identical to any linear orbit: {len(other)}: {[desc(c) for c in other[:15]]}")
