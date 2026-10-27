import sys, itertools
def make_step(k):
    M=(1<<k)-1
    tab={}
    for c in (0,1):
        for s in range(1<<k):
            outs=set()
            for beyond in (0,1):
                x=[c]+[(s>>i)&1 for i in range(k)]+[beyond]   # x[0]=column 0, x[1..k] strip, x[k+1] beyond
                n=0
                for p in range(1,k+1):
                    n|=(x[p-1]^(x[p]|x[p+1]))<<(p-1)
                outs.add(n)
            tab[(c,s)]=outs
    return tab
def image(S,c,tab):
    out=set()
    for s in S: out|=tab[(c,s)]
    return frozenset(out)
def excluded(w,k,tab):
    P=len(w); S=frozenset(range(1<<k)); seen={}
    seq=[]
    while S not in seen:
        seen[S]=len(seq); seq.append(S)
        for c in w: S=image(S,c,tab)
    cyc=seq[seen[S]:]
    for S0 in cyc:
        S=S0
        for phase,c in enumerate(w):
            if c==0:
                bits={s&1 for s in S}
                if len(bits)>1: return False
            S=image(S,c,tab)
    return True
def primitive_classes(L):
    out=[]
    for n in range(1,L+1):
        seen=set()
        for v in range(1<<n):
            w=tuple((v>>i)&1 for i in range(n))
            rots={w[i:]+w[:i] for i in range(n)}
            if any(r in seen for r in rots): continue
            seen|=rots
            if any(n%d==0 and w==w[:d]*(n//d) for d in range(1,n)): continue
            if 0 not in w: continue                     # all-black: period 1, excluded by the kit
            out.append(min(rots))
    return out
if __name__=="__main__":
    L=int(sys.argv[1]); ks=[int(x) for x in sys.argv[2].split(',')]
    words=primitive_classes(L)
    tabs={k:make_step(k) for k in ks}
    res={}
    for w in words:
        res[w]=next((k for k in ks if excluded(w,k,tabs[k])),None)
    by_len={}
    for w,k in res.items(): by_len.setdefault(len(w),[0,0]); by_len[len(w)][0 if k else 1]+=1
    print("length: excluded by a strip relaxation / not excluded")
    for n in sorted(by_len): print(f"  {n:2d}: {by_len[n][0]:5d} / {by_len[n][1]:5d}")
    resid=[w for w,k in res.items() if not k]
    print("not excluded, up to length 6:",[''.join(map(str,w)) for w in resid if len(w)<=6])
