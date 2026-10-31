import random, numpy as np, sys
seed=int(sys.argv[1]); random.seed(seed)
W=260000; M=(1<<W)-1; T=100000
x=random.getrandbits(W); y=x^(1<<(W-20000))
e0=W-20000; es=[]
for t in range(T):
    x=((x<<1)^(x|(x>>1)))&M; y=((y<<1)^(y|(y>>1)))&M
    if t%1000==999:
        d=x^y; es.append((d&-d).bit_length()-1)
es=np.array(es); print(seed, "speed %.5f"%((e0-es[-1])/T), "second half %.5f"%((es[len(es)//2]-es[-1])/(T/2)))
