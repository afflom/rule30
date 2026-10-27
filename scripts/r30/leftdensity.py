import numpy as np
from family import mons, run, ep
from interior import depends
from linearizable import desc
from split import split
OFF={0:-1,1:0,2:1,3:2}
T=600
def left_activity_density(code):
    mid=2*T+8; M=(1<<(2*mid+1))-1; x=1<<mid; sh=lambda v,o: v>>o if o>0 else v<<(-o)
    quad=[m for k,m in enumerate(mons) if len(m)==2 and code>>k&1]
    num=den=0
    for t in range(T):
        s={i:sh(x,OFF[i]) for i in range(4)}
        if t>=T//2:
            act=0
            for m in quad: act|=s[m[0]]&s[m[1]]
            lo=mid-2*t; win=((1<<(mid-lo))-1)<<lo
            num+=bin(act&win).count('1'); den+=mid-lo
        y=sh(x,-2)
        for k,m in enumerate(mons):
            if code>>k&1:
                term=s[m[0]]
                for v in m[1:]: term&=s[v]
                y^=term
        x=y&M
    return num/den
def symmetric(code):
    # f = a + g(b,c,d,e); mirror maps offsets -2..2 -> 2..-2 : a<->e, b<->d
    return False
exc=['a+b+e+bc','a+b+e+bc+bd','a+d+e+cd','a+b+c+e+bc+cd','a+b+d+e+bc+cd','a+c+d+e+bc+cd','a+b+c+d+e+bc+cd','a+d+e+bd+cd','a+c+d+e+ce','a+b+e+bc+ce']
rules=[c for c in range(16,1<<10) if depends(c,2) or depends(c,3)]
P=[c for c in rules if ep(run(c))]
dens=[(desc(c),left_activity_density(c)) for c in P]
hi=[x for x in dens if x[1]>0]
print("periodic-center rules with any late left activity:",len(hi))
for n,v in sorted(hi,key=lambda z:-z[1]): print(f"   {n:24s} left activity density {v:.4f}")
A=[c for c in rules if not ep(run(c))]
ad=np.array([left_activity_density(c) for c in A[:200]])
print("aperiodic (first 200): left activity density min %.4f, median %.4f"%(ad.min(),np.median(ad)))
mid=0
# rule 30 for comparison: active cr products on the left half
T2=600; m2=T2+4; MM=(1<<(2*m2+1))-1; x=1<<m2; num=den=0
for t in range(T2):
    if t>=T2//2:
        act=x&(x>>1); lo=m2-t; win=((1<<(m2-lo))-1)<<lo
        num+=bin(act&win).count('1'); den+=m2-lo
    x=((x<<1)^(x|(x>>1)))&MM
print("rule 30: left activity density of its product c*r: %.4f"%(num/den))
