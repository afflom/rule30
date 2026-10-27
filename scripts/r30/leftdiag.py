import numpy as np
T=1<<13; J=400
D=np.zeros((J,T),np.uint8); c=np.zeros(T,np.uint8); y=1
for t in range(T):
    c[t]=(y>>t)&1
    top=2*t
    for j in range(min(J,top+1)): D[j,t]=(y>>(top-j))&1
    y=y^((y<<1)|(y<<2))
def per_trans(x,lo):
    x=x[lo:]; n=len(x)
    for e in range(0,11):
        P=1<<e
        neq=np.nonzero(x[:-P]!=x[P:])[0]
        tau=0 if len(neq)==0 else int(neq[-1])+1
        if tau <= n//2: return e,tau+lo
    return None,None
rows=[]
for j in range(J):
    f,tl=per_trans(D[j],(j+1)//2)
    rows.append((j,f,tl))
print(" j  log2(left period)  transient  transient-j   (c(j) = D_j(j))")
for j,f,tl in rows[:40]+rows[40::20]: print(f"{j:3d} {f} {tl} {None if tl is None else tl-j}")
import collections
print("periods (log2) over j<400:",collections.Counter(f for _,f,_ in rows))
ex=[tl-j for j,f,tl in rows if tl is not None and j>=8]
print("transient - j over 8<=j<400: min",min(ex),"max",max(ex))
