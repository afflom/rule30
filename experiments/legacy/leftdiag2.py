import numpy as np, collections
T=1<<14; J=4096
D=np.zeros((J,T),np.uint8); y=1
for t in range(T):
    top=2*t                      # bit index of the left edge
    n=min(J,top+1)
    v=y>>(top+1-n)               # top n digits, left edge = most significant
    b=np.unpackbits(np.frombuffer(v.to_bytes((n+7)//8,'big'),np.uint8))[-n:]
    D[:n,t]=b
    y=y^((y<<1)|(y<<2))
def per_trans(x,lo):
    x=x[lo:]; n=len(x)
    for e in range(0,13):
        P=1<<e
        if 3*P>n: return None,None
        neq=np.nonzero(x[:-P]!=x[P:])[0]
        tau=0 if len(neq)==0 else int(neq[-1])+1
        if tau <= n-2*P: return e,tau+lo
    return None,None
out=[]
for j in range(0,J):
    f,tl=per_trans(D[j],(j+1)//2)
    out.append((j,f,tl))
print("depth j: log2 eventual period, transient tau_j, tau_j/j")
for j,f,tl in out[::256]+out[-3:]: print(j,f,tl, None if (tl is None or j==0) else round(tl/j,3))
firsts={}
for j,f,tl in out:
    if f is not None and f not in firsts: firsts[f]=j
print("first depth at which each period 2^f appears:",firsts)
v=[(j,tl) for j,f,tl in out if tl and j>200]
print("tau_j/j range for 200<j:",round(min(t/j for j,t in v),3),round(max(t/j for j,t in v),3), " undetected:",sum(1 for _,f,_ in out if f is None))
