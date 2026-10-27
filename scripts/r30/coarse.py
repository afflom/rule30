# Does rule 30 have abstractions that keep its form? Israeli-Goldenfeld coarse-graining:
# block size N, projection pi: {0,1}^N -> {0,1}, time step N; need g with pi(F^N(3 blocks)) = g(pi(l), pi(c), pi(r)).
import itertools
def F(cells):                          # one rule-30 step on a finite list (shrinks by 2)
    return [cells[i-1]^(cells[i]|cells[i+1]) for i in range(1,len(cells)-1)]
def centre_block(l,c,r,N):
    x=list(l)+list(c)+list(r)
    for _ in range(N): x=F(x)
    return tuple(x)                    # 3N - 2N = N cells: the new middle block
def coarse(N):
    blocks=list(itertools.product((0,1),repeat=N))
    nb=[[[centre_block(l,c,r,N) for r in blocks] for c in blocks] for l in blocks]
    found=[]
    for code in range(1,(1<<(1<<N))-1):          # nonconstant projections
        pi={b:(code>>i)&1 for i,b in enumerate(blocks)}
        g={}; ok=True
        for i,l in enumerate(blocks):
            for j,c in enumerate(blocks):
                for k,r in enumerate(blocks):
                    key=(pi[l],pi[c],pi[r]); val=pi[nb[i][j][k]]
                    if g.setdefault(key,val)!=val: ok=False; break
                if not ok: break
            if not ok: break
        if ok and len(g)==8:
            rule=sum(g[(a,b,c)]<<(4*a+2*b+c) for a,b,c in itertools.product((0,1),repeat=3))
            found.append((code,rule))
    return found
for N in (2,3,4):
    f=coarse(N)
    print(f"block size {N}: {len(f)} nontrivial projections; coarse rules: {sorted(set(r for _,r in f))}")
