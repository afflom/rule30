# Left diagonals of rule 30 in diagonal coordinates: y_t bit j = x_t(j - t).
# y_{t+1}[j] = y_t[j-2] ^ (y_t[j-1] | y_t[j]); depths <= J are closed under the evolution.
import numpy as np, sys, time
J=int(sys.argv[1]); T=int(sys.argv[2]); K=1024
M=(1<<J)-1
y=1; ring=[0]*K
last=np.full(J,-1,dtype=np.int64)   # last t with y_t[j] != y_{t-K}[j]
nb=(J+7)//8
t0=time.time()
for t in range(T):
    ring[t%K]=y
    if t>=K:
        d=y^ring[(t-K)%K] if False else y^old
    old=ring[(t+1)%K] if t+1>=K else 0
    if t>=K:
        if d:
            bits=np.unpackbits(np.frombuffer(d.to_bytes(nb,'little'),dtype=np.uint8),bitorder='little')[:J]
            last[bits.astype(bool)]=t
    y=((y<<2)^((y<<1)|y))&M
print("sim",round(time.time()-t0,1),"s",file=sys.stderr)
# least periods from the last 512 rows (powers of two up to 512)
rows=[ring[(T-1-i)%K] for i in range(K)]   # rows[i] = y_{T-1-i}
per=np.zeros(J,dtype=np.int64)
assigned=0
for p in [1,2,4,8,16,32,64,128,256,512]:
    ok=M
    for i in range(K-p): ok&=~(rows[i]^rows[i+p])
    bits=np.unpackbits(np.frombuffer((ok&M).to_bytes(nb,'little'),dtype=np.uint8),bitorder='little')[:J].astype(bool)
    new=bits&(per==0); per[new]=p
np.save(f"leftdyn_{J}_{T}.npy",np.stack([per,last]))
zero=[j for j in range(J) if per[j]==1 and ((rows[0]>>j)&1)==0]
print("unsettled-by-window (no period<=512):",int((per==0).sum()))
rec=[];m=0
for j in range(J):
    if per[j]>m: m=per[j]; rec.append((j,int(m)))
print("period records (depth, period):",rec)
print("zero diagonals:",len(zero),zero[:60])
ok=last<T-2*K
print("settled with margin:",int(ok.sum()),"of",J)
js=np.arange(J); tau=last+1
for a,b in [(100,1000),(1000,5000),(5000,20000),(20000,J)]:
    s=slice(a,min(b,J)); 
    if a<J: print(f"tau_j/j on [{a},{b}): max {np.max(tau[s]/js[s]):.3f} mean {np.mean(tau[s]/js[s]):.3f}")
