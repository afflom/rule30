from zbl import Z, recon
from collections import defaultdict
def alt(f,n):
    a=0
    for t in range(n): a|=(1 if t%2==0 else f(t//2))<<t
    return a
def life(X,K):
    for k in range(K+1):
        if not X&1: return 2*k
        X=Z(Z(X))
    return None
N=1600; K=300
stats=defaultdict(lambda:[0,0])
for p in range(1,9):
  for q in range(0,3):
    for w in range(1<<p):
      for pre in range(1<<q):
        f=lambda j: (pre>>j)&1 if j<q else (w>>((j-q)%p))&1
        X=recon(alt(f,N+2),N)
        bits=[(X>>i)&1 for i in range(N)]
        P=next((P for P in range(1,65) if all(bits[i]==bits[i+P] for i in range(N//2,N-P))),None)
        if P is None: continue
        # pure background with the same spatial alignment, extended to depth 1
        D=2*K+10; B=0
        for i in range(D): B|=bits[N//2 + ((i-N//2)%P)]<<i
        r=life(B,K)
        stats[P][0]+=1; stats[P][1]+= (r is None)
for P,(n,s) in sorted(stats.items()): print(f"tail period {P:2d}: {n:4d} rational survivors; pure background itself survives to t={2*K}: {s}/{n}")
