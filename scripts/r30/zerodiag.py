import numpy as np
J=100000; T=170000; M=(1<<J)-1; y=1; keep=[]
for t in range(T):
    if t>=T-64: keep.append(y)
    y=((y<<2)^((y<<1)|y))&M
nb=(J+7)//8
rows=np.array([np.unpackbits(np.frombuffer(v.to_bytes(nb,'little'),dtype=np.uint8),bitorder='little')[:J] for v in keep])
base=T-64; pat=np.zeros((J,64),dtype=np.uint8)
for i in range(64): pat[:,(base+i)%64]=rows[i]
def per(v):
    for p in [1,2,4,8,16,32,64]:
        if all(v[k]==v[(k+p)%64] for k in range(64)): return p
for z in [2,7,28,399,53207,58286,87866]:
    Pm=per(pat[z-1]); 
    print(f"zero diagonal {z}: E_z==0 {pat[z].sum()==0}; period of E_(z-1) = {Pm}; parity of E_(z-1) over its period = {pat[z-1][:Pm].sum()%2}; period of E_(z+1) = {per(pat[z+1])}")
# rule 30 center vs the ether's center E_t(t)
N=60000; W=2*N+3; x=1<<(N+1); Mw=(1<<W)-1; c=[]
for t in range(N):
    c.append((x>>(N+1))&1)
    x=((x<<1)^(x|(x>>1)))&Mw
c=np.array(c,dtype=np.uint8)
e=np.array([pat[t][t%64] for t in range(N)],dtype=np.uint8)
d=(c!=e)
for a,b in [(0,1000),(1000,10000),(10000,30000),(30000,60000)]: print(f"center damaged fraction on [{a},{b}): {d[a:b].mean():.4f}")
