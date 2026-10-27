import itertools, random, collections
from seeds_ep import evolve_seed, col_ep
cells=[-1,0,1,2]
allm=[(o,) for o in cells]+list(itertools.combinations(cells,2))+list(itertools.combinations(cells,3))
random.seed(9)
C=[[(-2,)]+[m for m in allm if random.random()<0.35] for _ in range(400)]
per=collections.Counter(); per_nonchaotic=collections.Counter(); n=0; ex={}
for monos in C:
    if not any(len(m)>=2 for m in monos): continue
    rows,mid=evolve_seed(monos,2,1200,1,1)
    chaotic = col_ep(rows,mid,1200) is None
    tgt=per if chaotic else per_nonchaotic
    if chaotic: n+=1
    for seed in range(1,256,2):
        w=seed.bit_length(); rows,mid=evolve_seed(monos,2,1200,seed,w)
        for p in range(-2,w+2):
            P=col_ep(rows,mid+p,1200)
            if P is not None:
                tgt[P]+=1
                if chaotic and P>1: ex.setdefault(P,(monos,bin(seed),p))
    if n>=50: break
print("degree<=3 family: chaotic rules",n)
print("  EP column periods in chaotic rules:",sorted(per.items()))
print("  EP column periods in non-chaotic rules:",sorted(per_nonchaotic.items())[:12])
for P,e in sorted(ex.items()): print("  chaotic period",P,e)
