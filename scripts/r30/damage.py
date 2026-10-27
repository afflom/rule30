import random, numpy as np
def step(x,M): return ((x<<1)^((x)|(x>>1)))&M   # bit i = position i; left = lower bit? check below
# convention: bit i = position i. new(p) = x(p-1) ^ (x(p) | x(p+1)); x(p-1) -> bit p of (x<<1); x(p+1) -> bit p of (x>>1)
random.seed(3); W=40000; M=(1<<W)-1
speeds=[]
for trial in range(6):
    x=random.getrandbits(W); p0=W//2
    y=x^(1<<p0); T=8000; edges=[]
    for t in range(T):
        d=x^y
        lo=(d&-d).bit_length()-1; edges.append(lo)
        x=step(x,M); y=step(y,M)
    e=np.array(edges); speeds.append((e[0]-e[-1])/T)
    hi=(x^y).bit_length()-1
print("left damage edge speed in random background:",np.round(speeds,4),"mean %.4f"%np.mean(speeds))
# rule 30 front slope for other finite seeds (left diagonals in diagonal coordinates)
def front_slope(seed_bits,J=20000,T=34000,K=512):
    # y_t bit j = x_t(j - t + L) where L = leftmost seed cell
    Mj=(1<<J)-1; y=seed_bits; ring={}; last=np.full(J,-1); nb=(J+7)//8; hist=[]
    for t in range(T):
        hist.append(y)
        if t>=K:
            d=y^hist[t-K]
            if d:
                b=np.unpackbits(np.frombuffer(d.to_bytes(nb,'little'),dtype=np.uint8),bitorder='little')[:J].astype(bool); last[b]=t
            hist[t-K]=None
        y=((y<<2)^((y<<1)|y))&Mj
    tau=last+1-K; j=np.arange(J); s=slice(J//2,J)
    return float(np.polyfit(j[s],tau[s],1)[0]), bool((last[s]<T-K).all())
random.seed(5)
for w in [1,3,5,8,12]:
    for _ in range(2):
        seed=1|random.getrandbits(w)<<1 if w>1 else 1
        print("seed",bin(seed),"front slope %.4f settled %s"%front_slope(seed))
