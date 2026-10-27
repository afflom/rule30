# Is the coarse perturbation of periodic-center permutive rules a single product channel?
import numpy as np
from family import mons, run, ep
from linearizable import desc
OFF={0:-1,1:0,2:1,3:2}
d=np.load('coupling_all.npy')
def orbit(code,T=500):
    mid=2*T+8; M=(1<<(2*mid+1))-1; x=1<<mid; rows=[x]
    sh=lambda v,o: v>>o if o>0 else v<<(-o)
    for t in range(T):
        s={i:sh(x,OFF[i]) for i in range(4)}; y=sh(x,-2)
        for k,m in enumerate(mons):
            if code>>k&1:
                term=s[m[0]]
                for v in m[1:]: term&=s[v]
                y^=term
        x=y&M; rows.append(x)
    return rows,mid,M
def best_product(code,k,T=500):
    rows,mid,M=orbit(code,T); sh=lambda v,o: v>>o if o>0 else v<<(-o)
    lin=[-2]+[OFF[m[0]] for kk,m in enumerate(mons) if len(m)==1 and code>>kk&1]
    h=1<<k; Es=[];Xs=[]
    for s in range(T//3,T-h,11):
        L=0
        for o in lin: L^=sh(rows[s],o*h)
        Es.append((rows[s+h]^L)&M); Xs.append(rows[s])
    lo=mid-2*(T-h); hi=mid+2*(T-h); win=((1<<(hi-lo+1))-1)<<lo
    def agree(a,b):
        num=den=0
        for E,X in zip(Es,Xs):
            P=sh(X,a)&sh(X,b)
            num+=bin(~(E^P)&win).count('1'); den+=hi-lo+1
        return num/den
    R=4*h
    best=max(((agree(a,b),a,b) for a in range(-R,R+1) for b in range(a+1,R+1)),key=lambda z:z[0])
    return best
pick=[r for r in d if r[1]==0 and 0.15<r[3]<0.26][:6]
print("periodic-center permutive rules with coupling near 1/4: best two-cell product x(p+a)x(p+b) for E_k")
for c,a,g0,g5 in pick:
    c=int(c); res=[best_product(c,k) for k in (1,2,3)]
    print(f"  {desc(c):22s} g5={g5:.3f}  k=1: {res[0][0]:.3f} {res[0][1:]}  k=2: {res[1][0]:.3f} {res[1][1:]}  k=3: {res[2][0]:.3f} {res[2][1:]}")
