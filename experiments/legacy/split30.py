import numpy as np
T=3000; mid=T+4; M=(1<<(2*mid+1))-1; x=1<<mid; rows=[x]
for t in range(T): x=((x<<1)^(x|(x>>1)))&M; rows.append(x)
sh=lambda v,o: v>>o if o>0 else v<<(-o)
for k in range(0,9):
    h=1<<k; nl=dl=nr=dr=0
    for s in range(T//3,T-h,max(1,(T-h-T//3)//300)):
        E=(rows[s+h]^(sh(rows[s],-h)^rows[s]^sh(rows[s],h)))&M
        loL=mid-(s+h); hiL=mid-1; loR=mid+1; hiR=mid+(s+h)
        wl=((1<<(hiL-loL+1))-1)<<loL; wr=((1<<(hiR-loR+1))-1)<<loR
        nl+=bin(E&wl).count('1'); dl+=hiL-loL+1; nr+=bin(E&wr).count('1'); dr+=hiR-loR+1
    print(f"rule 30, scale 2^{k}: left-side coupling {nl/dl:.3f}   right-side coupling {nr/dr:.3f}")
