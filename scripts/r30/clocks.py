# Which lines of the single-seed pattern carry an eventually periodic clock of their own?
import numpy as np
from fractions import Fraction
T=12000; W=2*T+3; mid=T+1; mask=(1<<W)-1
rows=[1<<mid]
for t in range(T): x=rows[-1]; rows.append(((x<<1)^(x|(x>>1)))&mask)
def cell(t,p): return (rows[t]>>(mid+p))&1
def ep(seq,maxP=1024):
    s=np.array(seq,np.uint8); n=len(s)
    for P in range(1,maxP+1):
        if 4*P>n: break
        neq=np.nonzero(s[:-P]!=s[P:])[0]
        tau=0 if len(neq)==0 else int(neq[-1])+1
        if tau<=n//2: return P,tau
    return None
print("slope  offset  | eventual period, birth (in the line's own steps)")
for a,b in [(1,1),(-1,1),(0,1),(1,2),(-1,2),(1,3),(-1,3),(2,3),(-2,3),(1,4),(-1,4),(3,4),(-3,4)]:
    for p0 in (0,):
        n=T//b; seq=[cell(b*k,p0+a*k) for k in range(n)]
        start=0
        while start<n and abs(p0+a*start)>b*start: start+=1     # outside the light cone: white
        r=ep(seq[start:])
        print(f"{a:+d}/{b}  {p0:3d}  | {r}")
