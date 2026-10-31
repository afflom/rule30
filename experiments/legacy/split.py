# Where in the cone does the perturbation live?  Coupling on the left side (p<0) and right side (p>0) separately.
import numpy as np
from family import mons
from channels import orbit, OFF
d=np.load('coupling_all.npy')
def split(code,k=4,T=500):
    rows,mid,M=orbit(code,T); sh=lambda v,o: v>>o if o>0 else v<<(-o)
    lin=[-2]+[OFF[m[0]] for kk,m in enumerate(mons) if len(m)==1 and code>>kk&1]
    R=max([0]+[OFF[i] for kk,m in enumerate(mons) if code>>kk&1 for i in m])
    h=1<<k; nl=dl=nr=dr=0
    for s in range(T//3,T-h,9):
        L=0
        for o in lin: L^=sh(rows[s],o*h)
        E=(rows[s+h]^L)&M
        loL=mid-2*(s+h); hiL=mid-1; loR=mid+1; hiR=mid+R*(s+h)
        wl=((1<<(hiL-loL+1))-1)<<loL; nl+=bin(E&wl).count('1'); dl+=hiL-loL+1
        if hiR>=loR:
            wr=((1<<(hiR-loR+1))-1)<<loR; nr+=bin(E&wr).count('1'); dr+=hiR-loR+1
    return nl/dl, (nr/dr if dr else 0)
rng=np.random.default_rng(3)
idx=rng.choice(len(d),220,replace=False)
A=[];P=[]
for i in idx:
    c,a,g0,g5=d[i]; l,r=split(int(c)); (A if a else P).append((l,r,g5))
A=np.array(A);P=np.array(P)
print(f"aperiodic centers ({len(A)}): left-side coupling mean {A[:,0].mean():.3f} (min {A[:,0].min():.3f}); right-side mean {A[:,1].mean():.3f} (min {A[:,1].min():.3f})")
print(f"periodic centers ({len(P)}):  left-side coupling mean {P[:,0].mean():.3f} (max {P[:,0].max():.3f}); right-side mean {P[:,1].mean():.3f} (max {P[:,1].max():.3f})")
for name,X in (("aperiodic",A),("periodic",P)):
    print(name, "fraction with right-side coupling > 0.26:", round(float((X[:,1]>0.26).mean()),3), " left-side > 0.26:", round(float((X[:,0]>0.26).mean()),3))
