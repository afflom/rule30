# Carry tower: no carry (rule 150), local carry (rule 30), propagated carry; diagonal readout bit t of F^t(1).
import numpy as np
T=4000
maps={
 "x^2x^4x (rule 150, no carry)": lambda x: x^(x<<1)^(x<<2),
 "x^(2x|4x) (rule 30, carry kept in place)": lambda x: x^((x<<1)|(x<<2)),
 "x^(2x+4x) (carry propagated inside the OR)": lambda x: x^((x<<1)+(x<<2)),
 "x+2x+4x = 7x (full carry)": lambda x: 7*x,
 "3x": lambda x: 3*x,
}
def ep(c):
    n=len(c)
    for P in range(1,n//4):
        neq=np.nonzero(c[:-P]!=c[P:])[0]; tau=0 if len(neq)==0 else int(neq[-1])+1
        if tau<=n//2: return P,tau
    return None
for name,f in maps.items():
    x=1; c=[]
    for t in range(T):
        c.append((x>>t)&1); x=f(x)
    c=np.array(c,dtype=np.uint8)
    print(f"{name:45s} density {c.mean():.3f}  EP: {ep(c)}")
