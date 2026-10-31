# LHC(w): the left half, driven at its boundary by the center's black pairs e = w AND shift(w),
# must show column -1 = NOT w(t+1) at every black time of w.  Survival of finite starts, by width.
import sys, numpy as np
from strip import primitive_classes
U=np.uint64
def survival(w,W,Tmax=400):
    P=len(w); e=[w[t]&w[(t+1)%P] for t in range(P)]
    best=0
    X0=np.arange(1,1<<W,dtype=np.uint64)
    for ph in range(P):
        X=X0.copy(); alive=np.ones(len(X),bool); t=0; life=np.zeros(len(X),np.int64)
        while alive.any() and t<Tmax:
            ph_t=(ph+t)%P
            if w[ph_t]==1:
                need=1-w[(ph_t+1)%P]
                ok=((X&U(1))==U(need))
                newly=alive&~ok; life[newly]=t; alive&=ok
            # step: depth k = bit k-1; boundary depth 0 = e
            x0=U(e[ph_t])
            X=(X>>U(1)) ^ (X | ((X<<U(1))|x0))
            t+=1
            if t>60: break       # 64-bit horizon: width W + t must stay below 64
        life[alive]=t
        best=max(best,int(life.max()))
    return best
words=[w for w in primitive_classes(6)]
Ws=[4,6,8,10,12,14]
print("word   | max survival (steps) of finite left starts of width W = "+" ".join(map(str,Ws)))
for w in words:
    r=[survival(w,W) for W in Ws]
    print(''.join(map(str,w)).ljust(7),'|',r,flush=True)
