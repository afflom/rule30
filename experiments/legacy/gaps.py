import random
from zbl import Z, recon
def alt_bits(fb,n):
    a=0
    for t in range(n): a|=(1 if t%2==0 else fb[t//2])<<t
    return a
def gap_excess(Y,N):
    """max over white runs at depths W+1..b (depth W black) of  b - 2W"""
    bits=[(Y>>i)&1 for i in range(N)]          # bits[i] = depth i+1
    best=-10**9; W=None; i=0
    while i<N:
        if bits[i]: W=i+1; i+=1; continue
        j=i
        while j<N and not bits[j]: j+=1
        if j<N and W is not None: best=max(best,j-2*W)   # run covers depths i+1..j, preceded by black at depth W
        i=j
    return best
N=1200; random.seed(1); worst=-10**9
for trial in range(300):
    fb=[random.getrandbits(1) for _ in range(N)]
    Y=recon(alt_bits(fb,N+2),N); worst=max(worst,gap_excess(Y,N))
print("random free bits, 300 survivors to depth 1200: max (gap end - 2*gap start) =",worst)
# adversarial: free bits chosen greedily to keep the start white as long as possible
def greedy(N):
    fb=[]
    for j in range(N//2+1):
        # choose f_j to make the depth-(2j+2) bit white when possible
        best=None
        for v in (0,1):
            Y=recon(alt_bits(fb+[v]+[0]*(N),2*j+4),2*j+2)
            if not (Y>>(2*j+1))&1: best=v
        fb.append(0 if best is None else best)
    return fb
fb=greedy(400); Y=recon(alt_bits(fb+[0]*10,402),400)
print("greedy-white survivor: first 80 depths", ''.join(str((Y>>i)&1) for i in range(80)), "excess", gap_excess(Y,400))
