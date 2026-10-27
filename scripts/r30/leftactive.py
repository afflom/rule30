# Is the nonlinear part of the rule literally inactive on the left half (away from the center) whenever the
# center column is eventually periodic?  Measure the deepest left cell where a quadratic monomial fires, late in time.
import numpy as np
from family import mons, run, ep
from interior import depends
from linearizable import desc
OFF={0:-1,1:0,2:1,3:2}
T=400
def deepest_left_activity(code):
    mid=2*T+8; M=(1<<(2*mid+1))-1; x=1<<mid; sh=lambda v,o: v>>o if o>0 else v<<(-o)
    quad=[m for k,m in enumerate(mons) if len(m)==2 and code>>k&1]
    deep=[]
    for t in range(T):
        s={i:sh(x,OFF[i]) for i in range(4)}
        if t>=T//2:
            act=0
            for m in quad: act|=s[m[0]]&s[m[1]]
            left=act & ((1<<mid)-1)                          # positions p<0
            deep.append(0 if left==0 else mid-((left&-left).bit_length()-1))   # depth of the leftmost active cell
        y=sh(x,-2)
        for k,m in enumerate(mons):
            if code>>k&1:
                term=s[m[0]]
                for v in m[1:]: term&=s[v]
                y^=term
        x=y&M
    return max(deep), deep[-1]
rules=[c for c in range(16,1<<10) if depends(c,2) or depends(c,3)]
P=[];A=[]
for c in rules:
    per=ep(run(c)); md,last=deepest_left_activity(c)
    (A if per is None else P).append((c,md,last))
print(f"periodic-center rules: {len(P)}")
print("  deepest left activity (late times): distribution of max depth:",
      np.histogram([m for _,m,_ in P],[0,1,3,6,11,21,51,101,201,1000])[0].tolist(), "bins [0,1,3,6,11,21,51,101,201,1000)")
print("  rules whose left activity reaches depth > 50:",[(desc(c),m) for c,m,_ in P if m>50][:10])
print(f"aperiodic-center rules: {len(A)}; with left activity reaching depth > 50: {sum(1 for _,m,_ in A if m>50)}")
print("  aperiodic rules with NO left activity beyond depth 10:",[desc(c) for c,m,_ in A if m<=10][:12], len([1 for _,m,_ in A if m<=10]))
