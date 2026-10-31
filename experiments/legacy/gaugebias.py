# Gauge content of the center: bias of c(t) on residue classes t mod m (2-gauge, 3-gauge, {2,3} and 5).
import numpy as np
N=200000; W=2*N+3; x=1<<(N+1); M=(1<<W)-1; c=np.zeros(N,dtype=np.int8)
for t in range(N):
    c[t]=(x>>(N+1))&1
    x=((x<<1)^(x|(x>>1)))&M
s=2*c-1
for m in [2,3,4,5,6,8,9,12,16,18,24,27,32,36,48,64,81]:
    dev=[abs(s[r::m].mean())*np.sqrt(len(s[r::m])) for r in range(m)]
    print(f"m={m:3d}: max |bias| in sigma units over residues = {max(dev):.2f}")
np.save("center200k.npy",c)
