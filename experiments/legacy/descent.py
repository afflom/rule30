from zbl import Z
def finite_preimages(y,W):
    out=[]
    for x1 in (0,1):
        x=[0,x1]
        for k in range(1,W+6): x.append(((y>>(k-1))&1) ^ (x[k] | x[k-1]))
        xs=x[1:]
        if not any(xs[W-1:W+5]):                     # white beyond depth W-1: genuinely finite
            v=sum(b<<i for i,b in enumerate(xs[:W-1]))
            if Z(v)==y: out.append(v)
    return out
def life(X):
    t=0
    while True:
        if t%2==0 and not X&1: return t
        X=Z(X); t+=1
for W in range(4,19):
    tot=haspre=0
    for X in range(1<<(W-1),1<<W):
        L=life(X)
        if L < 2*W-4: continue                      # keep only the long-lived starts of width W
        tot+=1
        ok=any(Y&1 for Y1 in finite_preimages(X,W) for Y in finite_preimages(Y1,W-1))
        haspre+=ok
    print(f"W={W:2d}: starts living past 2W-4: {tot:4d}; with a finite, odd Z^2-preimage: {haspre}")
