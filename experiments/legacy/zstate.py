# Zero-state readouts for rule 30: z(j) = E_j(j), transparent set S = {j : E_{j-1}(j) = 0}
import numpy as np
J=100000; T=170000; M=(1<<J)-1; y=1; keep=[]
for t in range(T):
    if t>=T-64: keep.append(y)
    y=((y<<2)^((y<<1)|y))&M
nb=(J+7)//8
rows=np.array([np.unpackbits(np.frombuffer(v.to_bytes(nb,'little'),dtype=np.uint8),bitorder='little')[:J] for v in keep])
base=T-64; pat=np.zeros((J,64),dtype=np.uint8)
for i in range(64): pat[:,(base+i)%64]=rows[i]
np.save("ether_pat_100000.npy",pat)
j=np.arange(1,J); z=pat[j,j%64]; s=(pat[j-1,j%64]==0)
print("density of S: %.4f; z density on S: %.4f"%(s.mean(), z[s].mean()))
lo=2000
best=[]
for q in range(1,513):
    js=j[lo:][s[lo:]]; zs=z[lo:][s[lo:]]
    r=js%q; dis=0
    for a in range(q):
        v=zs[r==a]
        if len(v): dis+=min(v.sum(),len(v)-v.sum())
    best.append((dis/len(zs),q))
best.sort(); print("best periodic fits of z on S (fraction disagreeing, q):",[(round(a,4),b) for a,b in best[:6]])
