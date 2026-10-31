# Scale-2^k form of rule 30:  X_{s+2^k} = (z^-2^k + 1 + z^2^k) X_s + E_k(s)   (exact, over F2).
# Is the block correction E_k(s) the rule-30 monomial at scale 2^k, X_s(p) X_s(p+2^k)?  Or some other
# product of two cells of row s?  Measure agreement inside the light cone.
import numpy as np
T=1100; W=2*T+5; mid=T+2
X=np.zeros((T+1,W),np.uint8); X[0,mid]=1
for t in range(T):
    x=X[t]; X[t+1,1:-1]=x[:-2]^(x[1:-1]|x[2:])
for k in range(0,7):
    h=1<<k; agree={}; n=0
    E_all=[]; rows=[]
    for s in range(64,T-h,7):
        x=X[s]; E=X[s+h].copy()
        E[h:-h]^=x[:-2*h]^x[h:-h]^x[2*h:]                          # subtract the linear part (spacing h)
        lo=mid-(s+h); hi=mid+(s+h)+1                               # light cone of row s+h
        E_all.append(E[lo:hi]); rows.append((x,lo,hi))
    E_all=np.concatenate(E_all)
    best=[]
    for a in range(-2*h,2*h+1):
        for b in range(a+1,2*h+2):
            cand=np.concatenate([ (np.roll(x,-a)&np.roll(x,-b))[lo:hi] for x,lo,hi in rows])
            best.append(((cand==E_all).mean(),a,b))
    best.sort(reverse=True)
    dens=E_all.mean()
    print(f"scale 2^{k}: density of E_k {dens:.3f}; best products x(p+a)x(p+b): "+", ".join(f"({a},{b}) agree {v:.3f}" for v,a,b in best[:3]))
