# Rule 30's running coupling to scale 2^10, cone-wide and on the center column alone.
import numpy as np
T=6000; mid=T+4; M=(1<<(2*mid+1))-1
x=1<<mid; rows=[x]
for t in range(T):
    x=((x<<1)^(x|(x>>1)))&M; rows.append(x)
def sh(v,o): return v>>o if o>0 else v<<(-o)
for k in range(0,11):
    h=1<<k; num=den=0; cnum=cden=0
    for s in range(T//3, T-h, max(1,(T-h-T//3)//400)):
        L=sh(rows[s],-h)^rows[s]^sh(rows[s],h)          # rule 150 at spacing h
        E=(rows[s+h]^L)&M
        lo=mid-(s+h); hi=mid+(s+h); win=((1<<(hi-lo+1))-1)<<lo
        num+=bin(E&win).count('1'); den+=hi-lo+1
        cnum+=(E>>mid)&1; cden+=1
    print(f"scale 2^{k:2d}: cone coupling {num/den:.4f}   center-column coupling {cnum/cden:.4f}  ({cden} samples)")
