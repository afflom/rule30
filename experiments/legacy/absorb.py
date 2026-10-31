# The 2-adic facet's own clock for each periodic word: the right half driven by w^inf from a white
# start (the kit's drv).  Does column 1 acquire a periodic clock (at white times of the driver)?
import numpy as np
from strip import primitive_classes
def drive(w,T=6000):
    P=len(w); x=0; col1=[]
    for t in range(T):
        c=w[t%P]
        col1.append(x&1)
        x=(((x<<1)|c) ^ (x | (x>>1)))     # bit k = position k+1; left neighbour of position 1 is the driver
    return np.array(col1,np.uint8)
def clock(seq,P,w):
    n=len(seq); white=np.array([w[t%P]==0 for t in range(n)])
    for m in range(1,129):
        Q=m*P
        if 3*Q>n: break
        diff=(seq[:-Q]!=seq[Q:])&white[:-Q]
        neq=np.nonzero(diff)[0]
        tau=0 if len(neq)==0 else int(neq[-1])+1
        if tau<=n//2: return Q,tau
    return None
res=[]
for w in primitive_classes(8):
    if 1 not in w or 0 not in w: continue
    r=clock(drive(w),len(w),w); res.append((w,r))
clocked=[(w,r) for w,r in res if r]; free=[w for w,r in res if not r]
print(f"{len(res)} words (length 2-8): column 1 periodic at the driver's white times: {len(clocked)}; no clock found: {len(free)}")
print("examples with a clock (word: period, birth):",[(''.join(map(str,w)),r) for w,r in clocked[:12]])
print("examples without:",[''.join(map(str,w)) for w in free[:20]])
