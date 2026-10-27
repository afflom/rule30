import itertools, random, collections
from seeds_ep import evolve_seed, col_ep, A
random.seed(5); B=A[:]; random.shuffle(B)
per=collections.Counter(); examples={}; n=0
for monos in B:
    if not any(len(m)>=2 for m in monos): continue
    rows,mid=evolve_seed(monos,2,800,1,1)
    if col_ep(rows,mid,800) is not None: continue
    n+=1
    for seed in range(1,512,2):
        w=seed.bit_length(); rows,mid=evolve_seed(monos,2,800,seed,w)
        for p in range(-2,w+2):
            P=col_ep(rows,mid+p,800)
            if P is not None:
                per[P]+=1; examples.setdefault(P,(monos,bin(seed),p))
    if n>=60: break
print("chaotic single-seed rules examined:",n)
print("periods of eventually periodic columns (finite seeds):",sorted(per.items()))
for P,e in sorted(examples.items()): print("  period",P,"example",e)
