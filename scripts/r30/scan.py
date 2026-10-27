import sys, time
from recon import depth
def per(word,P,M):
    c=0
    for t in range(M+1): c |= ((word>>(t%P))&1)<<t
    return c
rule=int(sys.argv[1]); Pmax=int(sys.argv[2])
for P in range(1,Pmax+1):
    t0=time.time(); worst=(0,None); unref=[]
    hist={}
    for w in range(1<<P):
        if not w&1: continue
        d=None
        for M in (64,512,4096):
            d=depth(rule,per(w,P,M),M)
            if d is not None: break
        if d is None: unref.append(w); continue
        hist[d]=hist.get(d,0)+1
        if d>worst[0]: worst=(d,w)
    print(f"P={P:2d} max depth={worst[0]:4d} word={format(worst[1],'0'+str(P)+'b')[::-1] if worst[1] is not None else '-'} unrefuted={len(unref)} hist={dict(sorted(hist.items()))} ({time.time()-t0:.1f}s)",flush=True)
