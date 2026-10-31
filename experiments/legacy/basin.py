import numpy as np
def step_all(P):
    w=np.arange(1<<P,dtype=np.int64); m=(1<<P)-1
    up=((w>>1)|((w&1)<<(P-1)))&m; dn=((w<<1)|(w>>(P-1)))&m
    return up ^ (w|dn)
for P in range(1,21):
    nxt=step_all(P); N=1<<P
    depth=np.full(N,-1,np.int64); depth[0]=0
    # reverse BFS from 0
    order=np.argsort(nxt,kind='stable'); srt=nxt[order]
    frontier=np.array([0]); d=0
    while len(frontier):
        d+=1
        lo=np.searchsorted(srt,frontier,'left'); hi=np.searchsorted(srt,frontier,'right')
        pre=np.concatenate([order[a:b] for a,b in zip(lo,hi)]) if len(frontier) else np.array([],np.int64)
        pre=pre[depth[pre]<0]; depth[pre]=d; frontier=pre
    inb=(depth>=0).sum()
    print(f"P={P:2d}: states reaching white {inb:7d} of {N:7d}; max steps to white {depth.max():2d}; counts by steps {np.bincount(depth[depth>=0]).tolist()}")
