import numpy as np
from strip import primitive_classes
def joint_window(w,a,L=90):
    n=2*a+1; N=1<<n; width=n+2*L+2; c0=L+1+a
    idx=np.arange(N,dtype=np.uint32); X=np.zeros((N,width),np.uint8)
    for i in range(n): X[:,L+1+i]=(idx>>i)&1
    cen=np.zeros((N,L),np.uint8)
    for t in range(L):
        cen[:,t]=X[:,c0]; X=np.roll(X,1,axis=1)^(X|np.roll(X,-1,axis=1))
    P=len(w); best=0
    for ph in range(P):
        target=np.array([w[(ph+t)%P] for t in range(L)],np.uint8)
        ok=(cen==target)                       # match against the phase-aligned word at each time
        # longest run of True per row, over all rows (window anywhere in [0, L))
        run=np.zeros(N,np.int32); bestrow=np.zeros(N,np.int32)
        for t in range(L):
            run=np.where(ok[:,t],run+1,0); bestrow=np.maximum(bestrow,run)
        best=max(best,int(bestrow.max()))
    return best
As=[3,4,5,6,7,8]
print("word  | longest window (any start) where the center equals w^inf; support [-a,a], a = "+" ".join(map(str,As)))
for w in primitive_classes(4):
    if 1 not in w: continue
    print(''.join(map(str,w)).ljust(6),'|',[joint_window(w,a) for a in As],flush=True)
