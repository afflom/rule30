# right diagonals R k t = cell(t, t-k); eventual period and settle time
import numpy as np
T=6000; W=2*T+3
row=np.zeros(W,dtype=np.uint8); c=T+1; row[c]=1
K=1200
R=np.zeros((K,T),dtype=np.uint8)
for t in range(T):
    for k in range(min(K,t+1)):
        R[k,t]=row[c+t-k]
    l=np.roll(row,1); r=np.roll(row,-1)
    row=l^(row|r)
def ev(seq):
    n=len(seq)
    for p in range(1,n//3):
        # smallest settle s with seq[s:]==seq[s+p:]... check periodic tail of last 2/3
        tail=seq[n//3:]
        if np.array_equal(tail[p:],tail[:-p]):
            s=n//3
            while s>0 and seq[s-1]==seq[s-1+p]: s-=1
            return p,s
    return None,None
for k in list(range(0,40))+[100,200,400,800,1000,1199]:
    p,s=ev(R[k,k:])
    print(k,p,None if s is None else s+k)
