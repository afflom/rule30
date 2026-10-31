# Settled-ether front vs the center, across left-permutive families.
# y_t[j] = x_t(-r t + j). tau_j = settling time of left diagonal j. Center at time t is diagonal r t.
import numpy as np, itertools, random, sys
from extrapolate import evolve, center_ep, symmetric
def front(monos,r,T=4000,K=512):
    rows,mid,M=evolve(monos,r,T)
    J=r*T//2
    ys=[(rows[t]>>(mid-r*t))&((1<<J)-1) for t in range(T+1)]
    last=np.full(J,-1)
    nb=(J+7)//8
    for t in range(K,T+1):
        d=ys[t]^ys[t-K]
        if d:
            b=np.unpackbits(np.frombuffer(d.to_bytes(nb,'little'),dtype=np.uint8),bitorder='little')[:J].astype(bool)
            last[b]=t
    tau=last-K+1; tau[last<0]=0      # upper estimate shift removed: tau = first t from which y_t = y_{t+K}
    js=np.arange(J)
    ok=last< T-K                      # settled within the window
    sel=(js>=J//4)&(js<J//2)
    if not ok[sel].all(): return None,ys,rows,mid
    lag=(tau[sel]-js[sel]/r)          # >0: center-diagonal settles after the center reads it
    return (float(np.max(lag)), float(np.mean(tau[sel]/js[sel]*r))), ys, rows, mid
def run(name,rules,r):
    res=[]
    for monos in rules:
        offs=set(o for m in monos for o in m)
        if not offs or min(offs)>=0 or max(offs)<=0 or not any(len(m)>=2 for m in monos): continue
        f,ys,rows,mid=front(monos,r)
        p=center_ep(rows,mid) is not None
        res.append((p,symmetric(monos),f,monos))
    for lab,cond in [("periodic, non-sym",lambda o:o[0] and not o[1]),("periodic, sym",lambda o:o[0] and o[1]),("aperiodic",lambda o:not o[0])]:
        g=[o for o in res if cond(o)]
        uns=[o for o in g if o[2] is None]
        s=[o for o in g if o[2] is not None]
        inside=[o for o in s if o[2][0]<=0]
        print(f"{name} | {lab}: {len(g)}; front unresolved {len(uns)}; center inside settled ether {len(inside)}/{len(s)}; r*tau/j range {min([o[2][1] for o in s],default=0):.2f}..{max([o[2][1] for o in s],default=0):.2f}")
        if lab!="periodic, sym":
            for o in [o for o in s if (o[2][0]>0)==(lab.startswith('periodic'))][:4]: print("      counter:",o[2],o[3])
if __name__=="__main__":
    B=[]
    for rule in range(0,256,2):
        tab=[(rule>>i)&1 for i in range(8)]; a=tab[:]
        for i in range(3):
            for m in range(8):
                if m>>i&1: a[m]^=a[m^(1<<i)]
        monos=[tuple(o for o,bit in zip((1,0,-1),(1,2,4)) if m&bit) for m in range(1,8) if a[m]]
        if (-1,) in monos and not any(-1 in m and len(m)>1 for m in monos): B.append(monos)
    run("radius-1 left-permutive",B,1)
    random.seed(1); C=[]
    cells=[-1,0,1,2]
    allm=[(o,) for o in cells]+list(itertools.combinations(cells,2))+list(itertools.combinations(cells,3))
    for _ in range(int(sys.argv[1]) if len(sys.argv)>1 else 150):
        C.append([(-2,)]+[m for m in allm if random.random()<0.35])
    run("radius-2 left-permutive deg<=3",C,2)
