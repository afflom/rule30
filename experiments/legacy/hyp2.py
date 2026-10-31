from zbl import Z, recon
from ring import ring_step
def alt(f,n):
    a=0
    for t in range(n): a|=(1 if t%2==0 else f(t//2))<<t
    return a
def life(X,K):
    for k in range(K+1):
        if not X&1: return 2*k
        X=Z(Z(X))
    return None
N=1600; K=300; D=2*K+10
seen={}
for p in range(1,9):
  for q in range(0,3):
    for w in range(1<<p):
      for pre in range(1<<q):
        f=lambda j: (pre>>j)&1 if j<q else (w>>((j-q)%p))&1
        X=recon(alt(f,N+2),N); bits=[(X>>i)&1 for i in range(N)]
        P=next((P for P in range(1,65) if all(bits[i]==bits[i+P] for i in range(N//2,N-P))),None)
        if P in (14,60):
            word=sum(bits[N//2+i]<<i for i in range(P))
            seen.setdefault(P,set()).add(word)
for P,words in sorted(seen.items()):
    for word in sorted(words)[:4]:
        s=word; best=0; alive=False; L=0
        for ph in range(128):
            for r in range(P):
                rw=((s>>r)|(s<<(P-r)))&((1<<P)-1)
                B=sum(((rw>>(i%P))&1)<<i for i in range(D))
                l=life(B,K)
                if l is None: alive=True; break
                best=max(best,l)
            if alive: break
            s=ring_step(s,P)
        print(f"P={P} word {format(word,'0%db'%P)[::-1]}: some phase of the pure background survives: {alive}  (longest life {best})")
