import itertools, random, collections
from seeds_ep import evolve_seed, col_ep, A
random.seed(5); B=A[:]; random.shuffle(B)
stats=collections.Counter(); n=0; shown=0
for monos in B:
    if not any(len(m)>=2 for m in monos): continue
    rows,mid=evolve_seed(monos,2,800,1,1)
    if col_ep(rows,mid,800) is not None: continue
    n+=1
    for seed in range(1,512,2):
        w=seed.bit_length(); rows,mid=evolve_seed(monos,2,800,seed,w)
        last=rows[-1]
        hi=last.bit_length()-1-mid; lo=(last&-last).bit_length()-1-mid   # rightmost/leftmost black cell at t=800
        for p in range(-2,w+2):
            P=col_ep(rows,mid+p,800)
            if P is not None:
                v=(rows[-1]>>(mid+p))&1
                inside = lo < p < hi
                # density of black cells in a window around p at late times
                dens=sum(bin((rows[t]>>(mid+p-20))&((1<<41)-1)).count('1') for t in range(600,800))/(41*200)
                stats[(inside, v, round(dens,1))]+=1
                if shown<6 and inside:
                    print("example: rule",monos,"seed",bin(seed),"col",p,"value",v,"pattern spans",lo,hi,"local density %.2f"%dens); shown+=1
    if n>=60: break
print(sorted(stats.items()))
