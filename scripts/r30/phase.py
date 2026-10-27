# 2-adic phase of the frozen left structure: driven left half (driver u, finite start) vs real zero-state
import numpy as np, random
exec(open('drivenfront.py').read().split("def settle_times")[0])
def run2(u,T,start_bits):
    # start: left half at time 0 given as bits j<m (diagonal coords = depth from edge); we embed by
    # running from a row: y holds bits D j t for j<=t; generic start = row at time m given as list of cells
    m=len(start_bits); y=0
    for j,b in enumerate(start_bits): y|=b<<j
    rows=[]
    for t in range(m-1,m-1+T):
        rows.append(y)
        n=((y<<2)^((y<<1)|y)) & ((1<<(t+1))-1)
        y=n|(u(t+1)<<(t+1))
    return rows
def late(rows,J,T0):
    T=len(rows); nb=(T0+T+8)//8; last=rows[-64:]
    A=np.array([np.unpackbits(np.frombuffer(r.to_bytes(nb,'little'),dtype=np.uint8),bitorder='little')[:J] for r in last],dtype=np.uint8).T
    base=T0+T-64; P=np.zeros((J,64),dtype=np.uint8)
    for i in range(64): P[:,(base+i)%64]=A[:,i]
    return P
T=4000; J=2000
W=2*T+5; r=np.zeros(W,dtype=np.uint8); c0=T+2; r[c0]=1; cen=[]
for t in range(T+2):
    cen.append(int(r[c0])); r=np.roll(r,1)^(r|np.roll(r,-1))
ref=late(run(lambda t:cen[t],T),J,0)
def phases(P):
    res=[]
    for lo,hi,C in [(3,8,2),(8,29,4),(29,400,8),(400,J,16)]:
        ok=[a for a in range(C) if all(np.array_equal(P[j],np.roll(ref[j],a)) for j in range(lo,hi))]
        res.append(ok)
    return res
random.seed(1)
for trial in range(8):
    m=random.randint(5,40)
    sb=[1]+[random.randint(0,1) for _ in range(m-1)]   # bit0 = edge (D 0 = 1)
    # D_1 must be consistent? any row is a valid row with edge at depth 0
    drv=random.choice([('zero',lambda t:0),('one',lambda t:1),('alt',lambda t:t%2)])
    P=late(run2(drv[1],T,sb),J,len(sb)-1)
    zd=[j for j in range(J) if not P[j].any()]
    print(drv[0],"m=%d"%m,"phases",phases(P),"zero diags",zd)
