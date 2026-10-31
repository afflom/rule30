import numpy as np
J=100000; T=160000; M=(1<<J)-1; y=1; keep=[]
for t in range(T):
    if t>=T-64: keep.append(y)
    y=((y<<2)^((y<<1)|y))&M
nb=(J+7)//8
rows=np.array([np.unpackbits(np.frombuffer(v.to_bytes(nb,'little'),dtype=np.uint8),bitorder='little')[:J] for v in keep])  # rows[i] = y_{T-64+i}
# E_j(phi) for phi = t mod 32 (absolute)
base=T-64; E={}
pat=np.zeros((J,32),dtype=np.uint8)
for i in range(32,64):
    t=base+i; pat[:,t%32]=rows[i]
codes=[int(''.join(map(str,pat[j])),2) for j in range(J)]
seen={}
for j in range(1,J):
    key=(codes[j-1],codes[j])
    if key in seen and j>400:
        print("pair repeats: first at",seen[key],"again at",j,"cycle length",j-seen[key]); break
    seen.setdefault(key,j)
else: print("no repeat of (E_{j-1},E_j) up to",J)
dens=pat[400:53000].mean(); print("ether black density (depth 400..53000): %.4f"%dens)
# black-pair (c and r) density in the ether, in space at fixed time: cells j and j+1 at the same t
bp=(pat[400:53000-1]&pat[401:53000]).mean(); print("activity (c&r over adjacent diagonals at same t): %.4f"%bp)
