import numpy as np
from seeds_ep import evolve_seed, col_ep
r=2
for monos,seed,p in [([(-2,),(0,),(2,),(-1,0),(0,1),(0,2)],0b11,0),([(-2,),(1,),(-1,0),(-1,1),(0,1),(1,2)],0b101,1)]:
    T=6000; K=1024; w=seed.bit_length(); rows,mid=evolve_seed(monos,r,T,seed,w)
    print(monos,bin(seed),p,"column EP over 6000:",col_ep(rows,mid+p,T))
    J=r*T; ys=[(rows[t]>>(mid-r*t))&((1<<J)-1) for t in range(T+1)]
    # settled depths: y_t[j]==y_{t-K}[j] for all t in [T-2K, T]
    st=(1<<J)-1
    for t in range(T-K,T+1): st&=~(ys[t]^ys[t-K])
    first_unsettled=(~st & ((1<<J)-1)); fu=(first_unsettled&-first_unsettled).bit_length()-1
    print("   all depths below",fu,"are K-periodic over the last 2K steps")
    for t in [1000,2000,3000]:
        cen=r*t+p
        dam=[j for j in range(min(cen+5,fu)) if ((ys[t]>>j)&1)!=((ys[T-K+((t-(T-K))%K)]>>j)&1)]
        print("   t",t,"center depth",cen,"damage edge",dam[0] if dam else None,"(edge-center",(dam[0]-cen) if dam else None,")")
    for t in [1000,1500,1900]:
        cen=r*t+p
        dam=[j for j in range(cen+1) if ((ys[t]>>j)&1)!=((ys[T-K+((t-(T-K))%K)]>>j)&1)]
        print("   t",t,"damaged depths count",len(dam),"in [0,center]; first few",dam[:12], "density in [t,center] %.3f"%(len([d for d in dam if d>=t])/(cen-t+1)))
