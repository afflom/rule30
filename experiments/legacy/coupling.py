# Running coupling: how far is each rule's seed orbit from its own linear part, scale by scale?
# g_k = density, inside the dependency cone, of E_k(s) = X_{s+2^k} - L^{2^k} X_s  (L = linear part; Frobenius).
import numpy as np, itertools
from family import mons, ep, run
from interior import depends
T=700
OFF={0:-1,1:0,2:1,3:2}                 # b,c,d,e -> offsets; a has offset -2 (always present, linear)
def shift(x,o): return x>>o if o>0 else x<<(-o)
def coupling(code,ks=range(0,7)):
    mid=2*T+8; M=(1<<(2*mid+1))-1; x=1<<mid; rows=[x]
    lin=[-2]+[OFF[m[0]] for k,m in enumerate(mons) if len(m)==1 and code>>k&1]
    R=max([0]+[OFF[i] for k,m in enumerate(mons) if code>>k&1 for i in m])
    for t in range(T):
        sh={i:shift(x,OFF[i]) for i in range(4)}; y=shift(x,-2)
        for k,m in enumerate(mons):
            if code>>k&1:
                term=sh[m[0]]
                for v in m[1:]: term&=sh[v]
                y^=term
        x=y&M; rows.append(x)
    g=[]
    for k in ks:
        h=1<<k; num=den=0
        for s in range(T//4, T-h, 9):
            L=0
            for o in lin: L^=shift(rows[s],o*h)
            E=(rows[s+h]^L)&M
            lo=mid-2*(s+h); hi=mid+R*(s+h)
            win=((1<<(hi-lo+1))-1)<<lo
            num+=bin(E&win).count('1'); den+=hi-lo+1
        g.append(num/den)
    return g
if __name__=="__main__":
    print("rule 30 (radius 1, for reference) is outside this family; family rules f = a + g(b,c,d,e):")
    rules=[c for c in range(16,1<<10) if (depends(c,2) or depends(c,3))]
    rng=np.random.default_rng(0); sample=list(rng.choice(rules,160,replace=False))
    rows=[]
    for c in sample:
        p=ep(run(int(c))); g=coupling(int(c)); rows.append((p is None,g))
    A=np.array([g for a,g in rows if a]); P=np.array([g for a,g in rows if not a])
    np.set_printoptions(precision=3,suppress=True)
    print(f"aperiodic center ({len(A)} rules): mean g_k, k=0..6:",A.mean(0)); print("   min:",A.min(0))
    print(f"periodic center ({len(P)} rules):  mean g_k, k=0..6:",P.mean(0)); print("   max:",P.max(0))
