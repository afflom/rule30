import numpy as np, time
N=1000000; W=2*N+3; x=1<<(N+1); M=(1<<W)-1; c=np.zeros(N,dtype=np.int8); mid=N+1
t0=time.time()
for t in range(N):
    c[t]=(x>>mid)&1
    x=((x<<1)^(x|(x>>1)))&M
np.save("center1m.npy",c); print("done",time.time()-t0)
