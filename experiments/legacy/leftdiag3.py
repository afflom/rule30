import numpy as np
T=1<<15; J=8192
D=np.zeros((J,T),np.uint8); y=1
for t in range(T):
    top=2*t; n=min(J,top+1)
    v=y>>(top+1-n)
    D[:n,t]=np.unpackbits(np.frombuffer(v.to_bytes((n+7)//8,'big'),np.uint8))[-n:]
    y=y^((y<<1)|(y<<2))
np.save('D.npy',D)
def per_trans(x,lo):
    x=x[lo:]; n=len(x)
    for e in range(0,12):
        P=1<<e
        neq=np.nonzero(x[:-P]!=x[P:])[0]
        tau=0 if len(neq)==0 else int(neq[-1])+1
        if tau <= n//2: return e,tau+lo
    return None,None
res=[]
for j in range(1,J,1):
    f,tl=per_trans(D[j],(j+1)//2); res.append((j,f,tl))
firsts={}
for j,f,tl in res:
    if f is not None and f not in firsts: firsts[f]=j
print("first depth with eventual period 2^f:",firsts)
bad=[j for j,f,tl in res if f is None]
print("depths with no detected period (tau > half the window):",len(bad), bad[:5], bad[-5:])
for lo,hi in [(100,400),(400,1000),(1000,2000),(2000,4000),(4000,6000),(6000,8191)]:
    r=[tl/j for j,f,tl in res if f is not None and lo<=j<hi]
    if r: print(f"tau_j/j for {lo}<=j<{hi}: min {min(r):.4f} mean {np.mean(r):.4f} max {max(r):.4f}")
