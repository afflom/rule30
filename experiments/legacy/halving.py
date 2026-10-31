import numpy as np
def run(W):
    X=np.arange(1<<W,dtype=np.uint64)                      # every start of width <= W (depth k = bit k-1)
    X=X[X>0]
    counts=[]; t=0
    while len(X):
        if t%2==0:
            X=X[(X & np.uint64(1))==1]                     # constraint: column -1 black at even times
            counts.append((t,len(X)))
        X=(X>>np.uint64(1)) ^ (X | (X<<np.uint64(1)))
        t+=1
        if t>63: raise SystemExit("horizon exceeded")
    return counts
for W in range(2,23):
    c=run(W)
    tail=[n for (t,n) in c if t>=W-1]
    print(f"W={W:2d} alive at even t>=W-1: {tail}  (2^floor(W/2)={2**(W//2)})")
