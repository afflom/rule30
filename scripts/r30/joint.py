# Joint facets: finite configurations on BOTH sides (support in [-a, a]); how long can the center
# column follow w^infinity (any phase, from time 0)?  Compare with the left half alone (lhc.py).
import numpy as np, sys
from strip import primitive_classes
def joint(w,a,L=70):
    n=2*a+1; N=1<<n; width=n+2*L+2; c0=L+1+a
    idx=np.arange(N,dtype=np.uint32)
    X=np.zeros((N,width),np.uint8)
    for i in range(n): X[:,L+1+i]=(idx>>i)&1
    cen=np.zeros((N,L),np.uint8)
    for t in range(L):
        cen[:,t]=X[:,c0]
        l=np.roll(X,1,axis=1); r=np.roll(X,-1,axis=1)
        X=l^(X|r)
    P=len(w); best=0
    for ph in range(P):
        target=np.array([w[(ph+t)%P] for t in range(L)],np.uint8)
        mism=(cen!=target)
        first=np.where(mism.any(axis=1),mism.argmax(axis=1),L)
        best=max(best,int(first.max()))
    return best
words=primitive_classes(5)
As=[2,3,4,5,6,7,8]
print("word  | longest match of the center to w^inf from time 0, finite support [-a,a], a = "+" ".join(map(str,As)))
for w in words:
    if 1 not in w: continue
    print(''.join(map(str,w)).ljust(6),'|',[joint(w,a) for a in As],flush=True)
